import Principia.Cluster
import Principia.ValueBound

/-!
# The cluster's numbers within the bound on an exact value

The cluster rule and the resolving step (`Principia.Cluster`) form numbers from a request's
scores, SEs, thresholds and spacing: each `sd(a, b)²` (`se_a² + se_b²`, or a paired SE's
square), each gap and step, `Z² sd²`, the spacing's square, the squarings by which
`sqrtSumLt` compares a gap with a sum of square roots, each step in spacings, the resolving
step's `CUSP MAX u` and `IN MAX u`, and, where the result is written, `fixed6`'s scaling by
10^6 and `Surd.floor`'s `c² b`. The reader admits numbers of about 47,000 bits, so a square,
and a square's square, can cross the bound on an exact value's size (`Principia.ValueBound`).

Here the computation is walked first, in the plain functions' order, each of those values
formed through `ValueBound.mul`, `add`, `sub` and `div`, so that one which could cross the
bound is refused "exact value too large" before it is formed (`clusterChecks`,
`resolvingChecks`, the result's text included: `renderWithin`, `resolvingWithin`). Only then
are the plain functions run, and they recompute only values already known to lie within the
bound. A refusal of the input's own (v1's words) met during the walk stops it; the plain
function then gives that refusal. When the checked functions answer they answer what the
plain ones do (`cluster_ok`, `resolvingStep_ok`), whose theorems therefore hold of every
answer given. Comparisons form no value and are not checked, as in `Principia.Strike.Bounded`.
-/

namespace Principia.Cluster.Bounded

open Principia.ValueBound (Bounded tooLarge)

/-- A walk that may meet one of v1's refusals, or the bound's. -/
abbrev Checked := ExceptT ClusterError Bounded

/-- One of v1's refusals: the walk stops there. -/
def refuse {α : Type} (e : ClusterError) : Checked α := throwThe ClusterError e

/-- A checked value, in the walk. -/
def lift {α : Type} (x : Bounded α) : Checked α := ExceptT.lift x

/-! ## The written numbers (`Surd.fixed6`) -/

/-- The values `Surd.sign` forms: `a²` and `c² b`, when the parts' signs differ. -/
def signWithin (x : Surd) : Bounded Unit :=
  if x.c = 0 ∨ x.b = 0 then pure ()
  else if x.a = 0 then pure ()
  else if ratSign x.a = ratSign x.c then pure ()
  else do
    let _ ← ValueBound.mul x.a x.a
    let cc ← ValueBound.mul x.c x.c
    let _ ← ValueBound.mul cc x.b
    pure ()

/-- The values `Surd.floor` forms: `c² b`, `a ± r` and the difference its sign is taken of. -/
def floorWithin (x : Surd) : Bounded Unit := do
  let cc ← ValueBound.mul x.c x.c
  let ccb ← ValueBound.mul cc x.b
  let r : Int := Nat.sqrt ccb.floor.toNat
  if 0 ≤ x.c then
    let s ← ValueBound.add x.a r
    let d ← ValueBound.sub x.a ((s.floor + 1 : Int) : Rat)
    signWithin ⟨d, x.c, x.b⟩
  else
    let s ← ValueBound.sub x.a r
    let d ← ValueBound.sub x.a (s.floor : Rat)
    signWithin ⟨d, x.c, x.b⟩

/-- The values `Surd.roundHalfEven` forms. -/
def roundWithin (x : Surd) : Bounded Unit := do
  floorWithin x
  let h ← ValueBound.add (x.floor : Rat) (1 / 2)
  let d ← ValueBound.sub x.a h
  signWithin ⟨d, x.c, x.b⟩

/-- The values `Surd.fixed6` forms: the scaling by 10^6 and what the rounding forms. -/
def fixed6Within (x : Surd) : Bounded Unit := do
  let a ← ValueBound.mul 1000000 x.a
  let c ← ValueBound.mul 1000000 x.c
  roundWithin ⟨a, c, x.b⟩
  signWithin x

/-- The values `fmt` forms. -/
def fmtWithin : Option Surd → Bounded Unit
  | none => pure ()
  | some x => fixed6Within x

/-! ## The cluster rule -/

/-- `sdSq`, its squares and sum checked. -/
def sdSq (table : Option (List ((RowKey × RowKey) × Rat))) (a b : Row) : Checked Rat :=
  match table with
  | none => do
    let x ← lift (ValueBound.mul a.se a.se)
    let y ← lift (ValueBound.mul b.se b.se)
    lift (ValueBound.add x y)
  | some t =>
    match t.find? (·.1 == pairKey a.key b.key) with
    | some (_, s) => lift (ValueBound.mul s s)
    | none => refuse .paired

/-- `sqrtSumLt`, the values it forms checked. -/
def sqrtSumLt (A B a : Rat) : Bounded Bool :=
  if 0 < a then do
    let aa ← ValueBound.mul a a
    let t1 ← ValueBound.sub aa A
    let t ← ValueBound.sub t1 B
    if 0 < t then do
      let fa ← ValueBound.mul 4 A
      let fab ← ValueBound.mul fa B
      let tt ← ValueBound.mul t t
      pure (decide (fab < tt))
    else pure false
  else pure false

/-- `below`, checked. -/
def below (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat) (ref row : Row) :
    Checked Bool := do
  let q ← sdSq table ref row
  let zz ← lift (ValueBound.mul z z)
  let zzq ← lift (ValueBound.mul zz q)
  let d ← lift (ValueBound.sub ref.score row.score)
  lift (sqrtSumLt 0 zzq d)

/-- `spacingSq`, checked. -/
def spacingSq (table : Option (List ((RowKey × RowKey) × Rat))) (z floor : Rat) :
    List Row → Checked (Rat × SpacingSource)
  | r1 :: r2 :: r3 :: _ => do
    let g1 ← lift (ValueBound.sub r1.score r2.score)
    let g2 ← lift (ValueBound.sub r2.score r3.score)
    let g := min g1 g2
    let q := max (← sdSq table r1 r2) (← sdSq table r2 r3)
    let gg ← lift (ValueBound.mul g g)
    let ff ← lift (ValueBound.mul floor floor)
    let (u2, src) := if gg < ff then (ff, SpacingSource.floor) else (gg, SpacingSource.gap)
    let zz ← lift (ValueBound.mul z z)
    let zzq ← lift (ValueBound.mul zz q)
    if u2 < zzq then pure (zzq, .noise) else pure (u2, src)
  | _ => pure (0, .notSet)

/-- `scan`, checked. -/
def scan (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    ScanState → Row → List Row → Checked (List ClusterClass)
  | _, _, [] => pure []
  | .closed, _, r :: rs => do
    let rest ← scan table t u2 .closed r rs
    pure (.outside :: rest)
  | .atCusp c, _, r :: rs => do
    if ← below table t.z c r then
      let rest ← scan table t u2 .closed r rs
      pure (.outside :: rest)
    else
      let rest ← scan table t u2 (.atCusp c) r rs
      pure (.cusp :: rest)
  | .scanning, prev, r :: rs => do
    let step ← lift (ValueBound.sub prev.score r.score)
    let q ← sdSq table prev r
    let zz ← lift (ValueBound.mul t.z t.z)
    let noise ← lift (ValueBound.mul zz q)
    let cc ← lift (ValueBound.mul t.cuspMax t.cuspMax)
    let outAt ← lift (ValueBound.mul cc u2)
    if ← lift (sqrtSumLt outAt noise step) then
      let rest ← scan table t u2 .closed r rs
      pure (.outside :: rest)
    else
      let ii ← lift (ValueBound.mul t.inMax t.inMax)
      let cuspAt ← lift (ValueBound.mul ii u2)
      if ← lift (sqrtSumLt cuspAt noise step) then
        let rest ← scan table t u2 (.atCusp r) r rs
        pure (.cusp :: rest)
      else
        let rest ← scan table t u2 .scanning r rs
        pure (.inside :: rest)

/-- `repClasses`, checked. -/
def repClasses (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    List Row → Checked (List ClusterClass)
  | [] => pure []
  | [_] => pure [.inside]
  | _ :: r2 :: rs => do
    let rest ← scan table t u2 .scanning r2 rs
    pure (.inside :: .inside :: rest)

/-- `otherClass`, checked. -/
def otherClass (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat)
    (lowIn lowCusp : Option Row) (r : Row) : Checked ClusterClass := do
  let cuspOrOut : Checked ClusterClass :=
    match lowCusp with
    | some c => do if ← below table z c r then pure .outside else pure .cusp
    | none => pure .outside
  match lowIn with
  | some i => if ← below table z i r then cuspOrOut else pure .inside
  | none => cuspOrOut

/-- The values `repLines` forms from rank 3 on, the step and the step in spacings, and
their text. -/
def repStepsWithin (u2 : Rat) : Nat → Option Row → List Row → Bounded Unit
  | k, prev, r :: rs => do
    match k, prev with
    | 0, _ | 1, _ | _, none => pure ()
    | _, some p =>
      let s ← ValueBound.sub p.score r.score
      fmtWithin (some (.ofRat s))
      if 0 < u2 then
        let q ← ValueBound.div s u2
        fmtWithin (some ⟨0, q, u2⟩)
    repStepsWithin u2 (k + 1) (some r) rs
  | _, _, [] => pure ()

/-- The values `render` forms: the spacing, every row's score and SE, and the
representatives' steps. -/
def renderWithin (u2 : Rat) (reps rows : List Row) : Bounded Unit := do
  fixed6Within (Surd.sqrt u2)
  for r in rows do
    fixed6Within (.ofRat r.score)
    fixed6Within (.ofRat r.se)
  repStepsWithin u2 0 none reps

/-- `cluster` walked, each value it and `render` form checked. -/
def clusterChecks (rows : List Row) (t : Thresholds) (floor : Rat)
    (paired : Option (List PairedSe)) : Checked Unit := do
  match checkInput rows t floor with
  | .error e => refuse e
  | .ok _ => pure ()
  let table ← match paired with
    | none => pure none
    | some ps =>
      match pairedTable (rows.map Row.key) ps [] with
      | .ok tb => pure (some tb)
      | .error e => refuse e
  let reps := representatives rows
  let (u2, _) ← spacingSq table t.z floor reps
  let classes ← repClasses table t u2 reps
  let lowIn := lowest .inside reps classes
  let lowCusp := lowest .cusp reps classes
  let repKeys := reps.map Row.key
  let others := sortBy otherBefore (rows.filter (fun r => !repKeys.contains r.key))
  for r in others do
    let _ ← otherClass table t.z lowIn lowCusp r
  lift (renderWithin u2 reps rows)

/-- `Cluster.cluster` within the bound: refused "exact value too large" when a value it or
its text forms could cross the bound. -/
def cluster (rows : List Row) (t : Thresholds := {}) (floor : Rat := 0)
    (paired : Option (List PairedSe) := none) : Bounded (Except ClusterError Result) := do
  let _ ← (clusterChecks rows t floor paired).run
  pure (Cluster.cluster rows t floor paired)

/-! ## The resolving step -/

/-- The resolving step's checks of the spacing, the SEs and the thresholds, in v1's order,
before the paired SEs': they form no value. -/
def resolvingInput (spacing : Rat) (ses : List Rat) (t : Thresholds) : Except ClusterError Unit := do
  unless 0 ≤ spacing do throw .spacing
  unless ses.all (0 ≤ ·) do throw .ses
  unless t.valid do throw .parameters

/-- The values the resolving step and its text form from the spacing and the SEs. -/
def resolvingChecks (spacing : Rat) (ses : List Rat) (t : Thresholds)
    (paired : Option (List Rat)) : Checked Unit := do
  match resolvingInput spacing ses t with
  | .error e => refuse e
  | .ok _ => pure ()
  if let some p := paired then
    unless p.length = ses.length - 1 && p.all (0 ≤ ·) do refuse .paired
  let adj ← lift ((ses.zip ses.tail).zipIdx.mapM fun ((a, b), i) =>
    match paired with
    | none => do
      let x ← ValueBound.mul a a
      let y ← ValueBound.mul b b
      ValueBound.add x y
    | some p => let s := p.getD i 0; ValueBound.mul s s)
  match adj.drop 1 with
  | [] => pure ()
  | q0 :: qs =>
    let outAt ← lift (ValueBound.mul t.cuspMax spacing)
    let cuspAt ← lift (ValueBound.mul t.inMax spacing)
    for q in q0 :: qs do
      lift (fixed6Within ⟨outAt, t.z, q⟩)
      lift (fixed6Within ⟨cuspAt, t.z, q⟩)
    if 0 < spacing then
      let qMin := qs.foldl min q0
      let o ← lift (ValueBound.div outAt spacing)
      let c ← lift (ValueBound.div cuspAt spacing)
      let z ← lift (ValueBound.div t.z spacing)
      lift (fixed6Within ⟨o, z, qMin⟩)
      lift (fixed6Within ⟨c, z, qMin⟩)

/-- `Cluster.resolvingStep` within the bound: refused "exact value too large" when a value
it or its text forms could cross the bound. -/
def resolvingStep (spacing : Rat) (ses : List Rat) (t : Thresholds := {})
    (paired : Option (List Rat) := none) :
    Bounded (Except ClusterError (Option ResolvingStep)) := do
  let _ ← (resolvingChecks spacing ses t paired).run
  pure (Cluster.resolvingStep spacing ses t paired)

/-! ## PROVED: an answer is the plain function's -/

theorem bind_ok {α β : Type} {x : Bounded α} {f : α → Bounded β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- The cluster rule answered within the bound is the plain function's. -/
theorem cluster_ok {rows : List Row} {t : Thresholds} {floor : Rat}
    {paired : Option (List PairedSe)} {r : Except ClusterError Result}
    (h : cluster rows t floor paired = .ok r) : r = Cluster.cluster rows t floor paired := by
  unfold cluster at h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  rfl

/-- The resolving step answered within the bound is the plain function's. -/
theorem resolvingStep_ok {spacing : Rat} {ses : List Rat} {t : Thresholds}
    {paired : Option (List Rat)} {r : Except ClusterError (Option ResolvingStep)}
    (h : resolvingStep spacing ses t paired = .ok r) :
    r = Cluster.resolvingStep spacing ses t paired := by
  unfold resolvingStep at h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  rfl

end Principia.Cluster.Bounded
