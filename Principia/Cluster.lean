import Principia.Wire
import Principia.Parameters
import Principia.Cluster.Surd

/-!
# The top-performer cluster

TPS 5.19.8 and 5.19.9: the cluster rule and the resolving step,
ported from v1's `tpc_cluster` 0.3.0 (`cluster`, `_check`, `_check_paired`,
`resolving_step`, `render`, `render_resolving`). Corpus:
the cluster corpus, run by the cluster test runner.

The rule, as v1 states it:

* R1 Each model's REPRESENTATIVE is its row with the highest score, then the lower
  SE, then the lower configuration id.
* R2 Representatives are ranked by score descending, SE ascending, model id
  ascending; ranks 1 and 2 are IN.
* R3 With `g1 = s1 - s2`, `g2 = s2 - s3`, the SPACING is
  `u = max(min(g1, g2), SPACING FLOOR, Z max(sd(1, 2), sd(2, 3)))`; the term that
  set it is GAP, FLOOR or NOISE (NONE with fewer than three models).
* R4 For rank `k ≥ 3` the STEP is `s(k-1) - s(k)` and its noise `Z sd(k-1, k)`:
  OUT if `step - CUSP MAX u` exceeds the noise, else CUSP if `step - IN MAX u`
  does, else IN. The scan closes at the first CUSP or OUT.
* R5 After a CUSP, each following representative is CUSP down to the first that is
  significantly below the CUSP row; that one and every later one are OUT. After
  an OUT every later representative is OUT.
* R6 A row that is not its model's representative is IN unless significantly below
  the lowest IN representative, else CUSP unless significantly below the lowest
  CUSP representative, else OUT.
* R7 `sd(a, b)` is `√(se_a² + se_b²)` under ITEM-SAMPLING; under FIXED-SET it is the
  paired SE the input carries for the pair, and a pair the rule tests and the
  input lacks is refused.

"Significantly below" is `s_ref - s > Z sd(ref, row)`. Every comparison here is
exact (`Principia.Cluster.Surd`): the spacing is kept as its square, and each
verdict compares a rational gap with a sum of square roots by squaring, where v1
compared floating-point values. On v1's 67 cases the two agree.
-/

namespace Principia.Cluster

open Principia.Parameters

/-! ## Words -/

/-- A row's CLUSTER CLASS (TPS 5.19.8). -/
inductive ClusterClass where
  /-- `IN`. -/
  | inside
  /-- `CUSP`. -/
  | cusp
  /-- `OUT`. -/
  | outside
  deriving DecidableEq, Repr, Inhabited

instance : WireWord ClusterClass where
  members := [.inside, .cusp, .outside]
  toWire
    | .inside => "IN"
    | .cusp => "CUSP"
    | .outside => "OUT"
  read_toWire a := by cases a <;> decide

/-- The class's place in the order IN < CUSP < OUT. -/
def ClusterClass.rank : ClusterClass → Nat
  | .inside => 0
  | .cusp => 1
  | .outside => 2

/-- The term that set the spacing (TPS 5.19.9). -/
inductive SpacingSource where
  /-- `GAP`: the smaller of the two top gaps. -/
  | gap
  /-- `FLOOR`: the declared SPACING FLOOR. -/
  | floor
  /-- `NOISE`: Z times the larger of the two top noise terms. -/
  | noise
  /-- `NONE`: fewer than three models, no spacing. -/
  | notSet
  deriving DecidableEq, Repr, Inhabited

instance : WireWord SpacingSource where
  members := [.gap, .floor, .noise, .notSet]
  toWire
    | .gap => "GAP"
    | .floor => "FLOOR"
    | .noise => "NOISE"
    | .notSet => "NONE"
  read_toWire a := by cases a <;> decide

/-- Why an input is refused; `message` is v1's word for it. -/
inductive ClusterError where
  /-- An empty or repeated model and configuration id. -/
  | ids
  /-- A negative SE. -/
  | scoreOrSe
  /-- Thresholds outside `0 < IN MAX < CUSP MAX`, `Z ≥ 0`, `SPACING FLOOR ≥ 0`. -/
  | parameters
  /-- A paired SE that is malformed, repeated, negative, names an unknown row or
  a row with itself, or is missing for a pair the rule tests. -/
  | paired
  /-- A negative spacing given to the resolving step. -/
  | spacing
  /-- A negative SE given to the resolving step. -/
  | ses
  deriving DecidableEq, Repr

/-- v1's error word. -/
def ClusterError.message : ClusterError → String
  | .ids => "ids"
  | .scoreOrSe => "score or se"
  | .parameters => "parameters"
  | .paired => "paired"
  | .spacing => "spacing"
  | .ses => "ses"

/-! ## Inputs -/

/-- A declared `Ratio` as a rational. -/
def ofRatio (r : Ratio) : Rat := mkRat r.num r.den

/-- IN MAX, CUSP MAX and Z; by default the declared values
(`Principia.Parameters.clusterInMax`, `clusterCuspMax`, `clusterZ`). -/
structure Thresholds where
  /-- IN MAX, in spacings. -/
  inMax : Rat := ofRatio clusterInMax
  /-- CUSP MAX, in spacings. -/
  cuspMax : Rat := ofRatio clusterCuspMax
  /-- Z, the one-sided noise threshold. -/
  z : Rat := ofRatio clusterZ
  deriving Repr

/-- The thresholds are usable: `0 < IN MAX < CUSP MAX` and `Z ≥ 0`. -/
def Thresholds.valid (t : Thresholds) : Bool :=
  0 < t.inMax && t.inMax < t.cuspMax && 0 ≤ t.z

/-- A ROW: one model configuration's composite score and its SE. -/
structure Row where
  /-- The model id. -/
  model : String
  /-- The MODEL CONFIGURATION id. -/
  config : String
  /-- The COMPOSITE SCORE. -/
  score : Rat
  /-- Its SE, `≥ 0`. -/
  se : Rat
  deriving DecidableEq, Repr, Inhabited

/-- A row's identity, its model and configuration ids. -/
abbrev RowKey := String × String

/-- The row's identity. -/
def Row.key (r : Row) : RowKey := (r.model, r.config)

/-- Python's order on pairs of strings: by model, then configuration, each by code
point. -/
def keyLt (p q : RowKey) : Bool :=
  p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)

/-- An unordered pair of rows, smaller key first. -/
def pairKey (p q : RowKey) : RowKey × RowKey :=
  if keyLt p q then (p, q) else (q, p)

/-- Under FIXED-SET, the paired SE of one difference. -/
structure PairedSe where
  /-- One row. -/
  first : RowKey
  /-- The other row. -/
  second : RowKey
  /-- The SE of their difference, `≥ 0`. -/
  se : Rat
  deriving Repr

/-! ## The checks (v1's `_check` and `_check_paired`) -/

/-- Every row: ids not empty and not repeated, SE not negative; in row order. -/
def checkRows : List Row → List RowKey → Except ClusterError Unit
  | [], _ => pure ()
  | r :: rs, seen =>
    if r.model.isEmpty || r.config.isEmpty || seen.contains r.key then throw .ids
    else if r.se < 0 then throw .scoreOrSe
    else checkRows rs (r.key :: seen)

/-- The rows, then the thresholds and the floor. -/
def checkInput (rows : List Row) (t : Thresholds) (floor : Rat) :
    Except ClusterError Unit := do
  checkRows rows []
  unless t.valid && 0 ≤ floor do throw .parameters

/-- The paired SEs as a table keyed by unordered pair: each names two distinct
known rows, is not negative, and no pair comes twice. -/
def pairedTable (keys : List RowKey) :
    List PairedSe → List ((RowKey × RowKey) × Rat) → Except ClusterError (List ((RowKey × RowKey) × Rat))
  | [], acc => pure acc
  | p :: ps, acc =>
    let k := pairKey p.first p.second
    if !keys.contains p.first || !keys.contains p.second || p.first == p.second || p.se < 0
        || acc.any (·.1 == k) then throw .paired
    else pairedTable keys ps (acc ++ [(k, p.se)])

/-- R7: the square of `sd(a, b)`. -/
def sdSq (table : Option (List ((RowKey × RowKey) × Rat))) (a b : Row) : Except ClusterError Rat :=
  match table with
  | none => pure (a.se * a.se + b.se * b.se)
  | some t =>
    match t.find? (·.1 == pairKey a.key b.key) with
    | some (_, s) => pure (s * s)
    | none => throw .paired

/-- `row` is significantly below `ref`: `s_ref - s > Z sd(ref, row)`. -/
def below (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat) (ref row : Row) :
    Except ClusterError Bool := do
  let q ← sdSq table ref row
  pure (sqrtSumLt 0 (z * z * q) (ref.score - row.score))

/-! ## Representatives (R1, R2) -/

/-- R1: `r` is preferred to `s` as its model's representative (higher score, then
lower SE, then lower configuration id). -/
def repBefore (r s : Row) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se < s.se || (r.se == s.se && r.config < s.config)))

/-- R2: `r` ranks above `s` (score descending, SE ascending, model id ascending). -/
def rankBefore (r s : Row) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se < s.se || (r.se == s.se && r.model < s.model)))

/-- R6's order for the other rows: as R2, then configuration id. -/
def otherBefore (r s : Row) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se < s.se || (r.se == s.se &&
    (r.model < s.model || (r.model == s.model && r.config < s.config)))))

/-- Insert into a list sorted by `lt`, after every element not after `x`. -/
def insertBy (lt : Row → Row → Bool) (x : Row) : List Row → List Row
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

/-- Sort by `lt` (insertion sort; a month has a few dozen rows). -/
def sortBy (lt : Row → Row → Bool) (l : List Row) : List Row :=
  l.foldl (fun acc x => insertBy lt x acc) []

/-- Each model's best row, the models in order of first appearance. -/
def bestRows : List Row → List Row → List Row
  | [], acc => acc
  | r :: rs, acc =>
    match acc.find? (·.model == r.model) with
    | none => bestRows rs (acc ++ [r])
    | some b => bestRows rs (if repBefore r b then acc.map (fun x => if x.model == r.model then r else x) else acc)

/-- The representatives in rank order. -/
def representatives (rows : List Row) : List Row :=
  sortBy rankBefore (bestRows rows [])

/-! ## The spacing (R3) and the scan (R4, R5) -/

/-- R3: the square of the spacing, and the term that set it. Kept as a square, so
GAP, FLOOR and NOISE compare exactly. -/
def spacingSq (table : Option (List ((RowKey × RowKey) × Rat))) (z floor : Rat) :
    List Row → Except ClusterError (Rat × SpacingSource)
  | r1 :: r2 :: r3 :: _ => do
    let g := min (r1.score - r2.score) (r2.score - r3.score)
    let q := max (← sdSq table r1 r2) (← sdSq table r2 r3)
    let (u2, src) := if g * g < floor * floor then (floor * floor, SpacingSource.floor)
      else (g * g, SpacingSource.gap)
    if u2 < z * z * q then pure (z * z * q, .noise) else pure (u2, src)
  | _ => pure (0, .notSet)

/-- Where the scan stands: still open, closed at a CUSP row, or closed by an OUT. -/
inductive ScanState where
  /-- No CUSP or OUT yet. -/
  | scanning
  /-- Closed at this CUSP row. -/
  | atCusp (row : Row)
  /-- Closed by an OUT. -/
  | closed

/-- The least class the scan can still give. -/
def ScanState.rank : ScanState → Nat
  | .scanning => 0
  | .atCusp _ => 1
  | .closed => 2

/-- R4 and R5: the classes of the representatives after `prev`, from rank 3 on;
`u2` is the spacing's square. -/
def scan (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    ScanState → Row → List Row → Except ClusterError (List ClusterClass)
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
    let step := prev.score - r.score
    let noise := t.z * t.z * (← sdSq table prev r)
    if sqrtSumLt (t.cuspMax * t.cuspMax * u2) noise step then
      let rest ← scan table t u2 .closed r rs
      pure (.outside :: rest)
    else if sqrtSumLt (t.inMax * t.inMax * u2) noise step then
      let rest ← scan table t u2 (.atCusp r) r rs
      pure (.cusp :: rest)
    else
      let rest ← scan table t u2 .scanning r rs
      pure (.inside :: rest)

/-- The representatives' classes in rank order: ranks 1 and 2 IN, then the scan. -/
def repClasses (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    List Row → Except ClusterError (List ClusterClass)
  | [] => pure []
  | [_] => pure [.inside]
  | _ :: r2 :: rs => do
    let rest ← scan table t u2 .scanning r2 rs
    pure (.inside :: .inside :: rest)

/-! ## The result -/

/-- One line of the result: a representative with its rank, step and spacings, or
another row (no rank, step or spacings). -/
structure Line where
  /-- The rank, for a representative. -/
  rank : Option Nat
  /-- The row. -/
  row : Row
  /-- The step from the representative ranked just above (0 for ranks 1 and 2). -/
  step : Option Rat
  /-- The step in spacings (0 for ranks 1 and 2; none when the spacing is 0). -/
  spacings : Option Surd
  /-- The CLUSTER CLASS. -/
  cls : ClusterClass
  deriving Repr

/-- `cluster`'s result. -/
structure Result where
  /-- The square of the spacing `u`. -/
  spacingSq : Rat
  /-- The term that set it. -/
  source : SpacingSource
  /-- The representatives in rank order, then the other rows. -/
  lines : List Line
  deriving Repr

/-- The spacing `u`. -/
def Result.spacing (r : Result) : Surd := Surd.sqrt r.spacingSq

/-- Every line's class, in the result's order. -/
def Result.classes (r : Result) : List ClusterClass := r.lines.map (·.cls)

/-- The representatives' lines: ranks from 1, steps and spacings from rank 3. -/
def repLines (u2 : Rat) : Nat → Option Row → List Row → List ClusterClass → List Line
  | k, prev, r :: rs, c :: cs =>
    let (step, spacings) : Option Rat × Option Surd :=
      match k, prev with
      | 0, _ | 1, _ | _, none => (some 0, some 0)
      | _, some p =>
        let s := p.score - r.score
        (some s, if 0 < u2 then some ⟨0, s / u2, u2⟩ else none)
    ⟨some (k + 1), r, step, spacings, c⟩ :: repLines u2 (k + 1) (some r) rs cs
  | _, _, _, _ => []

/-- The last representative of a class: the lowest-scoring one. -/
def lowest (cls : ClusterClass) (reps : List Row) (classes : List ClusterClass) : Option Row :=
  ((reps.zip classes).filter (·.2 == cls)).getLast?.map (·.1)

/-- R6: a row that is not its model's representative. -/
def otherClass (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat)
    (lowIn lowCusp : Option Row) (r : Row) : Except ClusterError ClusterClass := do
  let cuspOrOut : Except ClusterError ClusterClass :=
    match lowCusp with
    | some c => do if ← below table z c r then pure .outside else pure .cusp
    | none => pure .outside
  match lowIn with
  | some i => if ← below table z i r then cuspOrOut else pure .inside
  | none => cuspOrOut

/-- The cluster rule (TPS 5.19.8): the spacing, the term that set it, and every
row's class. `paired` is `none` under ITEM-SAMPLING and the paired SEs under
FIXED-SET. -/
def cluster (rows : List Row) (t : Thresholds := {}) (floor : Rat := 0)
    (paired : Option (List PairedSe) := none) : Except ClusterError Result := do
  checkInput rows t floor
  let table ← match paired with
    | none => pure none
    | some ps => some <$> pairedTable (rows.map Row.key) ps []
  let reps := representatives rows
  let (u2, source) ← spacingSq table t.z floor reps
  let classes ← repClasses table t u2 reps
  let lowIn := lowest .inside reps classes
  let lowCusp := lowest .cusp reps classes
  let repKeys := reps.map Row.key
  let others := sortBy otherBefore (rows.filter (fun r => !repKeys.contains r.key))
  let otherLines ← others.mapM fun r => do
    let c ← otherClass table t.z lowIn lowCusp r
    pure (⟨none, r, none, none, c⟩ : Line)
  pure ⟨u2, source, repLines u2 0 none reps classes ++ otherLines⟩

/-- v1's text of a result: `spacing|u|SOURCE`, then one line per row,
`rank|model|config|score|se|step|spacings|CLASS`. -/
def render (r : Result) : String :=
  let line (l : Line) : String := "|".intercalate
    [(l.rank.map toString).getD "-", l.row.model, l.row.config, fmt (some (.ofRat l.row.score)),
      fmt (some (.ofRat l.row.se)), fmt (l.step.map .ofRat), fmt l.spacings, WireWord.toWire l.cls]
  "\n".intercalate (s!"spacing|{r.spacing.fixed6}|{WireWord.toWire r.source}" :: r.lines.map line)

/-! ## The resolving step (TPS 5.19.9) -/

/-- The resolving step and its companions. For each rank `k ≥ 3`,
`out_k = CUSP MAX u + Z sd(k-1, k)` and `cusp_k = IN MAX u + Z sd(k-1, k)`; the
RESOLVING STEP is the least `out_k`, shown in points and in spacings. All `out_k`
share `CUSP MAX u`, so the least is the one of least `sd`. -/
structure ResolvingStep where
  /-- The least `out_k`, in points. -/
  out : Surd
  /-- The same in spacings; none when `u` is 0. -/
  outSpacings : Option Surd
  /-- The least `cusp_k`, in points. -/
  cusp : Surd
  /-- The same in spacings. -/
  cuspSpacings : Option Surd
  /-- The greatest `out_k`. -/
  outMost : Surd
  /-- The greatest `cusp_k`. -/
  cuspMost : Surd
  /-- Each rank `k ≥ 3` with `out_k` and `cusp_k`. -/
  ranks : List (Nat × Surd × Surd)
  deriving Repr

/-- `resolving_step(spacing, ses, ...)`: `spacing` is the month's `u`, `ses` the
ranked representatives' SEs in rank order, `paired` under FIXED-SET the paired SE
of each adjacent difference. `none` with fewer than three ranks (status NONE). -/
def resolvingStep (spacing : Rat) (ses : List Rat) (t : Thresholds := {})
    (paired : Option (List Rat) := none) : Except ClusterError (Option ResolvingStep) := do
  unless 0 ≤ spacing do throw .spacing
  unless ses.all (0 ≤ ·) do throw .ses
  unless t.valid do throw .parameters
  if let some p := paired then
    unless p.length = ses.length - 1 && p.all (0 ≤ ·) do throw .paired
  -- The square of `sd(k-1, k)` for each rank `k ≥ 3`, with `k`.
  let adj := (ses.zip ses.tail).zipIdx.map fun ((a, b), i) =>
    (i + 2, match paired with
      | none => a * a + b * b
      | some p => let s := p.getD i 0; s * s)
  let qs := adj.drop 1
  match qs with
  | [] => pure none
  | q0 :: _ =>
    let out (q : Rat) : Surd := ⟨t.cuspMax * spacing, t.z, q⟩
    let cusp (q : Rat) : Surd := ⟨t.inMax * spacing, t.z, q⟩
    let sp (x : Surd) : Option Surd := if 0 < spacing then some (x.divRat spacing) else none
    let qMin := qs.foldl (fun m x => min m x.2) q0.2
    let qMax := qs.foldl (fun m x => max m x.2) q0.2
    pure (some {
      out := out qMin, outSpacings := sp (out qMin), cusp := cusp qMin,
      cuspSpacings := sp (cusp qMin), outMost := out qMax, cuspMost := cusp qMax,
      ranks := qs.map fun (k, q) => (k, out q, cusp q) })

/-- v1's text: `resolving|NONE`, or `resolving|out|out spacings|cusp|cusp spacings`,
`greatest|out|cusp` and one `rank|k|out|cusp` line per rank. -/
def renderResolving : Option ResolvingStep → String
  | none => "resolving|NONE"
  | some d => "\n".intercalate
    ([s!"resolving|{d.out.fixed6}|{fmt d.outSpacings}|{d.cusp.fixed6}|{fmt d.cuspSpacings}",
      s!"greatest|{d.outMost.fixed6}|{d.cuspMost.fixed6}"] ++
      d.ranks.map fun (k, o, c) => s!"rank|{k}|{o.fixed6}|{c.fixed6}")

/-! ## Theorems

The PROVED rows. The first two hold for every input; the rest are v1's boundary
cases, where a step lies exactly on a threshold, and the format's rounding,
checked by the kernel on the exact values. -/

theorem ordered_cons {x : ClusterClass} {rest : List ClusterClass} {lo s : Nat}
    (hx : lo ≤ x.rank) (hxs : x.rank ≤ s)
    (h : (∀ c ∈ rest, s ≤ c.rank) ∧ rest.Pairwise (fun a b => a.rank ≤ b.rank)) :
    (∀ c ∈ x :: rest, lo ≤ c.rank) ∧ (x :: rest).Pairwise (fun a b => a.rank ≤ b.rank) := by
  refine ⟨fun c hc => ?_, List.Pairwise.cons (fun b hb => Nat.le_trans hxs (h.1 b hb)) h.2⟩
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hx
  · exact Nat.le_trans (Nat.le_trans hx hxs) (h.1 c hc)

/-- R4, R5: the scan never goes back. Every class it gives is at least its
state's (after a CUSP, CUSP or OUT; after an OUT, OUT), and its classes come in
the order IN, CUSP, OUT. -/
theorem scan_ordered (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    ∀ (rs : List Row) (st : ScanState) (prev : Row) (cls : List ClusterClass),
    scan table t u2 st prev rs = .ok cls →
      (∀ c ∈ cls, st.rank ≤ c.rank) ∧ cls.Pairwise (fun a b => a.rank ≤ b.rank) := by
  intro rs
  induction rs with
  | nil =>
    intro st prev cls h
    cases st <;> simp [scan, pure, Except.pure] at h <;> subst h <;> simp
  | cons r rs ih =>
    intro st prev cls h
    cases st with
    | closed =>
      simp only [scan, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · rename_i rest hrest
        simp at h; subst h
        exact ordered_cons (Nat.le_refl _) (Nat.le_refl _) (ih _ _ _ hrest)
    | atCusp c =>
      simp only [scan, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · rename_i rest hrest
            simp at h; subst h
            exact ordered_cons (by simp [ScanState.rank, ClusterClass.rank]) (Nat.le_refl _)
              (ih _ _ _ hrest)
        · split at h
          · simp at h
          · rename_i rest hrest
            simp at h; subst h
            exact ordered_cons (Nat.le_refl _) (Nat.le_refl _) (ih _ _ _ hrest)
    | scanning =>
      simp only [scan, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · rename_i rest hrest
            simp at h; subst h
            exact ordered_cons (by simp [ScanState.rank, ClusterClass.rank]) (Nat.le_refl _)
              (ih _ _ _ hrest)
        · split at h
          · split at h
            · simp at h
            · rename_i rest hrest
              simp at h; subst h
              exact ordered_cons (by simp [ScanState.rank, ClusterClass.rank]) (Nat.le_refl _)
                (ih _ _ _ hrest)
          · split at h
            · simp at h
            · rename_i rest hrest
              simp at h; subst h
              exact ordered_cons (Nat.le_refl _) (Nat.le_refl _) (ih _ _ _ hrest)

/-- R2, R4, R5: ranks 1 and 2 are IN, and the representatives' classes, in rank
order, never go back: IN, then CUSP, then OUT. -/
theorem repClasses_ordered (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds)
    (u2 : Rat) (reps : List Row) (cls : List ClusterClass) (h : repClasses table t u2 reps = .ok cls) :
    (∀ c ∈ cls.take 2, c = .inside) ∧ cls.Pairwise (fun a b => a.rank ≤ b.rank) := by
  match reps, h with
  | [], h => simp [repClasses, pure, Except.pure] at h; subst h; simp
  | [_], h => simp [repClasses, pure, Except.pure] at h; subst h; simp
  | _ :: r2 :: rs, h =>
    simp only [repClasses, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    · rename_i rest hrest
      simp at h; subst h
      have hs := scan_ordered table t u2 rs .scanning r2 rest hrest
      have h1 := ordered_cons (x := .inside) (lo := 0) (s := 0) (Nat.le_refl _) (Nat.le_refl _) hs
      have h2 := ordered_cons (x := .inside) (lo := 0) (s := 0) (Nat.le_refl _) (Nat.le_refl _) h1
      exact ⟨by simp, h2.2⟩

/-- Three models with SE 0, the top gap 1 (so `u` is 1 by GAP), the third at `s3`. -/
def threeRows (s3 : Rat) : List Row :=
  [⟨"b1", "default", 10, 0⟩, ⟨"b2", "default", 9, 0⟩, ⟨"b3", "default", s3, 0⟩]

/-- A step of exactly IN MAX spacings is IN (v1's C12). -/
theorem step_at_in_max_is_in :
    (cluster (threeRows (13 / 2))).toOption.map Result.classes = some [.inside, .inside, .inside] := by
  decide +kernel

/-- A step of exactly CUSP MAX spacings is CUSP, not OUT (v1's C13). -/
theorem step_at_cusp_max_is_cusp :
    (cluster (threeRows (11 / 2))).toOption.map Result.classes = some [.inside, .inside, .cusp] := by
  decide +kernel

/-- A step of 3.6 spacings is OUT (v1's C14). -/
theorem step_past_cusp_max_is_out :
    (cluster (threeRows (27 / 5))).toOption.map Result.classes = some [.inside, .inside, .outside] := by
  decide +kernel

/-- Four models, `u` 1 by GAP; rank 4's noise is `Z √(0.3² + 0.4²) = 0.8225` exactly. -/
def fourRows (s4 : Rat) : List Row :=
  [⟨"b1", "default", 10, 0⟩, ⟨"b2", "default", 9, 0⟩, ⟨"b3", "default", 8, 3 / 10⟩,
    ⟨"b4", "default", s4, 2 / 5⟩]

/-- A step whose excess over CUSP MAX `u` equals its noise, a square root, is CUSP:
the noise must be exceeded, and here it is met exactly. -/
theorem step_at_noise_is_cusp :
    (cluster (fourRows (36775 / 10000))).toOption.map Result.classes =
      some [.inside, .inside, .inside, .cusp] := by
  decide +kernel

/-- The same step longer by 0.0001 is OUT. -/
theorem step_past_noise_is_out :
    (cluster (fourRows (36774 / 10000))).toOption.map Result.classes =
      some [.inside, .inside, .inside, .outside] := by
  decide +kernel

/-- The docs' specimen of the resolving step (TPS 5.19.9; v1's R01): `u` 1.6, SEs
0.6 with rank 6 at 0.7, gives 6.996 points and 4.37 spacings. -/
theorem resolving_specimen :
    (resolvingStep (8 / 5) [3 / 5, 3 / 5, 3 / 5, 3 / 5, 3 / 5, 7 / 10]).toOption.map renderResolving =
      some ("resolving|6.995829|4.372393|5.395829|3.372393\ngreatest|7.116615|5.516615\n" ++
        "rank|3|6.995829|5.395829\nrank|4|6.995829|5.395829\nrank|5|6.995829|5.395829\n" ++
        "rank|6|7.116615|5.516615") := by
  decide +kernel

/-- Six decimals of the exact value: a tie goes to the even neighbour (as `"%.6f"`
rounds a tie it meets exactly), and a negative value that rounds to zero keeps its
minus sign (as `"%.6f"` prints it). -/
theorem fixed6_rounding :
    (Surd.sqrt 2).fixed6 = "1.414214" ∧ (Surd.ofRat (5 / 10000000)).fixed6 = "0.000000" ∧
      (Surd.ofRat (15 / 10000000)).fixed6 = "0.000002" ∧
      (Surd.ofRat (-1 / 10000000)).fixed6 = "-0.000000" := by
  decide +kernel

end Principia.Cluster
