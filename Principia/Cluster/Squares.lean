import Principia.Cluster

/-!
# The cluster rule over squared standard errors

A ROW's measure (`Principia.Cluster.Rows`) keeps its SE as its exact square `se2`: under
ITEM-SAMPLING the SE of a composite of `m` benchmarks is `√(Σ se_i²) / m`, and its square is
rational where the SE itself, in general, is not. The cluster rule (`Principia.Cluster`)
reads each row's SE only through its square `se * se` and through the order of two SEs; so
the rule can be stated over `se2` with no root formed:

* `sd(a, b)²` under ITEM-SAMPLING is `se2_a + se2_b`; under FIXED-SET the paired SE is
  given as it is in `cluster`, and its square is formed there as it is formed in `cluster`;
* two SEs, both `≥ 0`, compare as their squares do (`sq_lt_sq`, `sq_eq_sq`), so R1, R2
  and R6's orders compare `se2`;
* a negative `se2` is refused with `cluster`'s word for a negative SE.

Everything else is `cluster`'s: the thresholds, the floor, the paired SEs, the
representatives, the spacing (still kept as its square, so `Surd.sqrt` of it on the page),
the scan, the classes and the refusal words. `renderSq` is v1's text, each row's SE shown as
`Surd.sqrt se2` to six decimals.

`clusterSq_ofRow` proves the two rules the same where every square is a rational square:
on the rows `rows.map RowSq.ofRow` (each `se2` equal to `se * se`, `se ≥ 0`) `clusterSq`
answers exactly `cluster`'s result with each row read as its square, and refuses exactly
when `cluster` does, with the same word (`clusterSq_agrees`). `cluster` and its
definitions are left as they are; these stand beside them.
-/

namespace Principia.Cluster

/-! ## Rows -/

/-- A ROW whose SE is given as its exact square `se2 ≥ 0`, as `cluster_rows` keeps it. -/
structure RowSq where
  /-- The model id. -/
  model : String
  /-- The MODEL CONFIGURATION id. -/
  config : String
  /-- The COMPOSITE SCORE. -/
  score : Rat
  /-- The square of its SE, `≥ 0`. -/
  se2 : Rat
  deriving DecidableEq, Repr, Inhabited

/-- The row's identity. -/
def RowSq.key (r : RowSq) : RowKey := (r.model, r.config)

/-- A row with a rational SE, its SE given as its square. -/
def RowSq.ofRow (r : Row) : RowSq := ⟨r.model, r.config, r.score, r.se * r.se⟩

/-! ## The checks -/

/-- Every row: ids not empty and not repeated, `se2` not negative; in row order. -/
def checkRowsSq : List RowSq → List RowKey → Except ClusterError Unit
  | [], _ => pure ()
  | r :: rs, seen =>
    if r.model.isEmpty || r.config.isEmpty || seen.contains r.key then throw .ids
    else if r.se2 < 0 then throw .scoreOrSe
    else checkRowsSq rs (r.key :: seen)

/-- The rows, then the thresholds and the floor. -/
def checkInputSq (rows : List RowSq) (t : Thresholds) (floor : Rat) :
    Except ClusterError Unit := do
  checkRowsSq rows []
  unless t.valid && 0 ≤ floor do throw .parameters

/-- R7: the square of `sd(a, b)`: `se2_a + se2_b`, or the paired SE's square. -/
def pairSdSq (table : Option (List ((RowKey × RowKey) × Rat))) (a b : RowSq) :
    Except ClusterError Rat :=
  match table with
  | none => pure (a.se2 + b.se2)
  | some t =>
    match t.find? (·.1 == pairKey a.key b.key) with
    | some (_, s) => pure (s * s)
    | none => throw .paired

/-- `row` is significantly below `ref`: `s_ref - s > Z sd(ref, row)`. -/
def belowSq (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat) (ref row : RowSq) :
    Except ClusterError Bool := do
  let q ← pairSdSq table ref row
  pure (sqrtSumLt 0 (z * z * q) (ref.score - row.score))

/-! ## Representatives (R1, R2) -/

/-- R1 over squares: higher score, then lower `se2`, then lower configuration id. -/
def repBeforeSq (r s : RowSq) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se2 < s.se2 || (r.se2 == s.se2 && r.config < s.config)))

/-- R2 over squares: score descending, `se2` ascending, model id ascending. -/
def rankBeforeSq (r s : RowSq) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se2 < s.se2 || (r.se2 == s.se2 && r.model < s.model)))

/-- R6's order over squares: as R2, then configuration id. -/
def otherBeforeSq (r s : RowSq) : Bool :=
  s.score < r.score || (r.score == s.score && (r.se2 < s.se2 || (r.se2 == s.se2 &&
    (r.model < s.model || (r.model == s.model && r.config < s.config)))))

/-- Insert into a list sorted by `lt`, after every element not after `x`. -/
def insertBySq (lt : RowSq → RowSq → Bool) (x : RowSq) : List RowSq → List RowSq
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBySq lt x ys

/-- Sort by `lt` (insertion sort, as `sortBy`). -/
def sortBySq (lt : RowSq → RowSq → Bool) (l : List RowSq) : List RowSq :=
  l.foldl (fun acc x => insertBySq lt x acc) []

/-- Each model's best row, the models in order of first appearance. -/
def bestRowsSq : List RowSq → List RowSq → List RowSq
  | [], acc => acc
  | r :: rs, acc =>
    match acc.find? (·.model == r.model) with
    | none => bestRowsSq rs (acc ++ [r])
    | some b => bestRowsSq rs (if repBeforeSq r b then acc.map (fun x => if x.model == r.model then r else x) else acc)

/-- The representatives in rank order. -/
def representativesSq (rows : List RowSq) : List RowSq :=
  sortBySq rankBeforeSq (bestRowsSq rows [])

/-! ## The spacing (R3) and the scan (R4, R5) -/

/-- R3: the square of the spacing, and the term that set it. -/
def spacingOfSq (table : Option (List ((RowKey × RowKey) × Rat))) (z floor : Rat) :
    List RowSq → Except ClusterError (Rat × SpacingSource)
  | r1 :: r2 :: r3 :: _ => do
    let g := min (r1.score - r2.score) (r2.score - r3.score)
    let q := max (← pairSdSq table r1 r2) (← pairSdSq table r2 r3)
    let (u2, src) := if g * g < floor * floor then (floor * floor, SpacingSource.floor)
      else (g * g, SpacingSource.gap)
    if u2 < z * z * q then pure (z * z * q, .noise) else pure (u2, src)
  | _ => pure (0, .notSet)

/-- Where the scan stands: still open, closed at a CUSP row, or closed by an OUT. -/
inductive ScanStateSq where
  /-- No CUSP or OUT yet. -/
  | scanning
  /-- Closed at this CUSP row. -/
  | atCusp (row : RowSq)
  /-- Closed by an OUT. -/
  | closed

/-- R4 and R5 over squares: the classes of the representatives after `prev`. -/
def scanSq (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    ScanStateSq → RowSq → List RowSq → Except ClusterError (List ClusterClass)
  | _, _, [] => pure []
  | .closed, _, r :: rs => do
    let rest ← scanSq table t u2 .closed r rs
    pure (.outside :: rest)
  | .atCusp c, _, r :: rs => do
    if ← belowSq table t.z c r then
      let rest ← scanSq table t u2 .closed r rs
      pure (.outside :: rest)
    else
      let rest ← scanSq table t u2 (.atCusp c) r rs
      pure (.cusp :: rest)
  | .scanning, prev, r :: rs => do
    let step := prev.score - r.score
    let noise := t.z * t.z * (← pairSdSq table prev r)
    if sqrtSumLt (t.cuspMax * t.cuspMax * u2) noise step then
      let rest ← scanSq table t u2 .closed r rs
      pure (.outside :: rest)
    else if sqrtSumLt (t.inMax * t.inMax * u2) noise step then
      let rest ← scanSq table t u2 (.atCusp r) r rs
      pure (.cusp :: rest)
    else
      let rest ← scanSq table t u2 .scanning r rs
      pure (.inside :: rest)

/-- The representatives' classes in rank order: ranks 1 and 2 IN, then the scan. -/
def repClassesSq (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    List RowSq → Except ClusterError (List ClusterClass)
  | [] => pure []
  | [_] => pure [.inside]
  | _ :: r2 :: rs => do
    let rest ← scanSq table t u2 .scanning r2 rs
    pure (.inside :: .inside :: rest)

/-! ## The result -/

/-- One line of the result, as `Line`, its row given with `se2`. -/
structure LineSq where
  /-- The rank, for a representative. -/
  rank : Option Nat
  /-- The row. -/
  row : RowSq
  /-- The step from the representative ranked just above (0 for ranks 1 and 2). -/
  step : Option Rat
  /-- The step in spacings (0 for ranks 1 and 2; none when the spacing is 0). -/
  spacings : Option Surd
  /-- The CLUSTER CLASS. -/
  cls : ClusterClass
  deriving Repr

/-- `clusterSq`'s result. -/
structure ResultSq where
  /-- The square of the spacing `u`. -/
  spacingSq : Rat
  /-- The term that set it. -/
  source : SpacingSource
  /-- The representatives in rank order, then the other rows. -/
  lines : List LineSq
  deriving Repr

/-- The spacing `u`. -/
def ResultSq.spacing (r : ResultSq) : Surd := Surd.sqrt r.spacingSq

/-- Every line's class, in the result's order. -/
def ResultSq.classes (r : ResultSq) : List ClusterClass := r.lines.map (·.cls)

/-- The representatives' lines: ranks from 1, steps and spacings from rank 3. -/
def repLinesSq (u2 : Rat) : Nat → Option RowSq → List RowSq → List ClusterClass → List LineSq
  | k, prev, r :: rs, c :: cs =>
    let (step, spacings) : Option Rat × Option Surd :=
      match k, prev with
      | 0, _ | 1, _ | _, none => (some 0, some 0)
      | _, some p =>
        let s := p.score - r.score
        (some s, if 0 < u2 then some ⟨0, s / u2, u2⟩ else none)
    ⟨some (k + 1), r, step, spacings, c⟩ :: repLinesSq u2 (k + 1) (some r) rs cs
  | _, _, _, _ => []

/-- The last representative of a class: the lowest-scoring one. -/
def lowestSq (cls : ClusterClass) (reps : List RowSq) (classes : List ClusterClass) : Option RowSq :=
  ((reps.zip classes).filter (·.2 == cls)).getLast?.map (·.1)

/-- R6 over squares: a row that is not its model's representative. -/
def otherClassSq (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat)
    (lowIn lowCusp : Option RowSq) (r : RowSq) : Except ClusterError ClusterClass := do
  let cuspOrOut : Except ClusterError ClusterClass :=
    match lowCusp with
    | some c => do if ← belowSq table z c r then pure .outside else pure .cusp
    | none => pure .outside
  match lowIn with
  | some i => if ← belowSq table z i r then cuspOrOut else pure .inside
  | none => cuspOrOut

/-- The cluster rule (TPS 5.19.8) over squared SEs: `cluster` with every row's `se * se`
read as its `se2`. `paired` is `none` under ITEM-SAMPLING and the paired SEs under
FIXED-SET, as in `cluster`. -/
def clusterSq (rows : List RowSq) (t : Thresholds := {}) (floor : Rat := 0)
    (paired : Option (List PairedSe) := none) : Except ClusterError ResultSq := do
  checkInputSq rows t floor
  let table ← match paired with
    | none => pure none
    | some ps => some <$> pairedTable (rows.map RowSq.key) ps []
  let reps := representativesSq rows
  let (u2, source) ← spacingOfSq table t.z floor reps
  let classes ← repClassesSq table t u2 reps
  let lowIn := lowestSq .inside reps classes
  let lowCusp := lowestSq .cusp reps classes
  let repKeys := reps.map RowSq.key
  let others := sortBySq otherBeforeSq (rows.filter (fun r => !repKeys.contains r.key))
  let otherLines ← others.mapM fun r => do
    let c ← otherClassSq table t.z lowIn lowCusp r
    pure (⟨none, r, none, none, c⟩ : LineSq)
  pure ⟨u2, source, repLinesSq u2 0 none reps classes ++ otherLines⟩

/-- v1's text of a result: `spacing|u|SOURCE`, then one line per row,
`rank|model|config|score|se|step|spacings|CLASS`, the SE shown as `√se2`. -/
def renderSq (r : ResultSq) : String :=
  let line (l : LineSq) : String := "|".intercalate
    [(l.rank.map toString).getD "-", l.row.model, l.row.config, fmt (some (.ofRat l.row.score)),
      fmt (some (Surd.sqrt l.row.se2)), fmt (l.step.map .ofRat), fmt l.spacings, WireWord.toWire l.cls]
  "\n".intercalate (s!"spacing|{r.spacing.fixed6}|{WireWord.toWire r.source}" :: r.lines.map line)

/-! ## The rows' squares: `cluster`'s values read as squares -/

/-- A line of `cluster`'s result, its row given as its square. -/
def LineSq.ofLine (l : Line) : LineSq := ⟨l.rank, RowSq.ofRow l.row, l.step, l.spacings, l.cls⟩

/-- `cluster`'s result, every row given as its square. -/
def ResultSq.ofResult (r : Result) : ResultSq := ⟨r.spacingSq, r.source, r.lines.map LineSq.ofLine⟩

/-- The scan's state, its row given as its square. -/
def ScanStateSq.ofState : ScanState → ScanStateSq
  | .scanning => .scanning
  | .atCusp r => .atCusp (RowSq.ofRow r)
  | .closed => .closed

/-! ## Theorems -/

/-- Two rationals `≥ 0` compare as their squares do. -/
theorem sq_lt_sq {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : a * a < b * b ↔ a < b := by
  constructor
  · intro h
    refine Rat.not_le.mp fun hba => Rat.not_le.mpr h ?_
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hba hb) (Rat.mul_le_mul_of_nonneg_right hba ha)
  · intro h
    have hb' : 0 < b := Rat.not_le.mp fun hb0 => Rat.not_le.mpr h (Rat.le_trans hb0 ha)
    refine Rat.not_le.mp fun hle => ?_
    have h1 : a * a ≤ a * b := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h) ha
    have h2 : a * b < b * b := Rat.mul_lt_mul_of_pos_right h hb'
    exact Rat.not_le.mpr h2 (Rat.le_trans hle h1)

/-- Two rationals `≥ 0` are equal exactly when their squares are. -/
theorem sq_eq_sq {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : a * a = b * b ↔ a = b := by
  constructor
  · intro h
    refine Rat.le_antisymm (Rat.not_lt.mp fun hlt => ?_) (Rat.not_lt.mp fun hlt => ?_)
    · have := (sq_lt_sq hb ha).mpr hlt
      rw [h] at this; exact Rat.lt_irrefl this
    · have := (sq_lt_sq ha hb).mpr hlt
      rw [h] at this; exact Rat.lt_irrefl this
  · intro h; rw [h]

theorem repBeforeSq_ofRow {r s : Row} (hr : 0 ≤ r.se) (hs : 0 ≤ s.se) :
    repBeforeSq (RowSq.ofRow r) (RowSq.ofRow s) = repBefore r s := by
  apply Bool.eq_iff_iff.mpr
  simp only [repBeforeSq, repBefore, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [RowSq.ofRow]
  rw [sq_lt_sq hr hs, sq_eq_sq hr hs]

theorem rankBeforeSq_ofRow {r s : Row} (hr : 0 ≤ r.se) (hs : 0 ≤ s.se) :
    rankBeforeSq (RowSq.ofRow r) (RowSq.ofRow s) = rankBefore r s := by
  apply Bool.eq_iff_iff.mpr
  simp only [rankBeforeSq, rankBefore, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [RowSq.ofRow]
  rw [sq_lt_sq hr hs, sq_eq_sq hr hs]

theorem otherBeforeSq_ofRow {r s : Row} (hr : 0 ≤ r.se) (hs : 0 ≤ s.se) :
    otherBeforeSq (RowSq.ofRow r) (RowSq.ofRow s) = otherBefore r s := by
  apply Bool.eq_iff_iff.mpr
  simp only [otherBeforeSq, otherBefore, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [RowSq.ofRow]
  rw [sq_lt_sq hr hs, sq_eq_sq hr hs]

theorem key_ofRow (r : Row) : (RowSq.ofRow r).key = r.key := rfl

theorem map_key_ofRow (l : List Row) : (l.map RowSq.ofRow).map RowSq.key = l.map Row.key := by
  simp [List.map_map, Function.comp_def, key_ofRow]

/-- The checks agree on rows whose SEs are `≥ 0`. -/
theorem checkRowsSq_ofRow : ∀ (rows : List Row) (seen : List RowKey), (∀ r ∈ rows, 0 ≤ r.se) →
    checkRowsSq (rows.map RowSq.ofRow) seen = checkRows rows seen
  | [], _, _ => rfl
  | r :: rs, seen, h => by
    have hr : 0 ≤ r.se := h r (by simp)
    have hn : ¬ r.se < 0 := Rat.not_lt.mpr hr
    have hn2 : ¬ r.se * r.se < 0 := Rat.not_lt.mpr (Rat.mul_nonneg hr hr)
    have ih := checkRowsSq_ofRow rs (r.key :: seen) (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, checkRowsSq, checkRows, key_ofRow, ih]
    simp [RowSq.ofRow, hn, hn2]

theorem checkInputSq_ofRow (rows : List Row) (t : Thresholds) (floor : Rat)
    (h : ∀ r ∈ rows, 0 ≤ r.se) :
    checkInputSq (rows.map RowSq.ofRow) t floor = checkInput rows t floor := by
  simp only [checkInputSq, checkInput, checkRowsSq_ofRow rows [] h]

theorem pairSdSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (a b : Row) :
    pairSdSq table (RowSq.ofRow a) (RowSq.ofRow b) = sdSq table a b := by
  cases table <;> rfl

theorem belowSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat) (a b : Row) :
    belowSq table z (RowSq.ofRow a) (RowSq.ofRow b) = below table z a b := by
  simp only [belowSq, below, pairSdSq_ofRow]; rfl

/-! ### The sort and the representatives -/

theorem mem_insertBy {lt : Row → Row → Bool} {x y : Row} :
    ∀ {ys : List Row}, y ∈ insertBy lt x ys → y = x ∨ y ∈ ys
  | [], h => by simpa [insertBy] using h
  | z :: zs, h => by
    unfold insertBy at h
    split at h
    · simpa using h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp)
      · rcases mem_insertBy h with e | m
        · exact Or.inl e
        · exact Or.inr (by simp [m])

theorem insertBySq_ofRow (lt : Row → Row → Bool) (ltq : RowSq → RowSq → Bool) (P : Row → Prop)
    (hP : ∀ a b, P a → P b → ltq (RowSq.ofRow a) (RowSq.ofRow b) = lt a b) (x : Row) (hx : P x) :
    ∀ (ys : List Row), (∀ y ∈ ys, P y) →
      insertBySq ltq (RowSq.ofRow x) (ys.map RowSq.ofRow) = (insertBy lt x ys).map RowSq.ofRow
  | [], _ => rfl
  | y :: ys, h => by
    have ih := insertBySq_ofRow lt ltq P hP x hx ys (fun z hz => h z (by simp [hz]))
    simp only [List.map_cons, insertBySq, insertBy, hP x y hx (h y (by simp))]
    split <;> simp [ih]

theorem sortBySq_ofRow (lt : Row → Row → Bool) (ltq : RowSq → RowSq → Bool) (P : Row → Prop)
    (hP : ∀ a b, P a → P b → ltq (RowSq.ofRow a) (RowSq.ofRow b) = lt a b) :
    ∀ (l acc : List Row), (∀ y ∈ l, P y) → (∀ y ∈ acc, P y) →
      (l.map RowSq.ofRow).foldl (fun acc x => insertBySq ltq x acc) (acc.map RowSq.ofRow) =
        (l.foldl (fun acc x => insertBy lt x acc) acc).map RowSq.ofRow
  | [], _, _, _ => rfl
  | x :: xs, acc, hl, hacc => by
    have hx : P x := hl x (by simp)
    simp only [List.map_cons, List.foldl_cons]
    rw [insertBySq_ofRow lt ltq P hP x hx acc hacc]
    apply sortBySq_ofRow lt ltq P hP xs _ (fun y hy => hl y (by simp [hy]))
    intro y hy
    rcases mem_insertBy hy with rfl | m
    · exact hx
    · exact hacc y m

theorem sortBy_ofRow (lt : Row → Row → Bool) (ltq : RowSq → RowSq → Bool) (P : Row → Prop)
    (hP : ∀ a b, P a → P b → ltq (RowSq.ofRow a) (RowSq.ofRow b) = lt a b) (l : List Row)
    (hl : ∀ y ∈ l, P y) :
    sortBySq ltq (l.map RowSq.ofRow) = (sortBy lt l).map RowSq.ofRow :=
  sortBySq_ofRow lt ltq P hP l [] hl (by simp)

theorem bestRowsSq_ofRow : ∀ (rows acc : List Row), (∀ y ∈ rows, 0 ≤ y.se) → (∀ y ∈ acc, 0 ≤ y.se) →
    bestRowsSq (rows.map RowSq.ofRow) (acc.map RowSq.ofRow) = (bestRows rows acc).map RowSq.ofRow
  | [], _, _, _ => rfl
  | r :: rs, acc, hr, hacc => by
    have hr0 : 0 ≤ r.se := hr r (by simp)
    have hrs : ∀ y ∈ rs, 0 ≤ y.se := fun y hy => hr y (by simp [hy])
    have hfind : (acc.map RowSq.ofRow).find? (·.model == (RowSq.ofRow r).model) =
        (acc.find? (·.model == r.model)).map RowSq.ofRow := by
      rw [List.find?_map]; rfl
    simp only [List.map_cons, bestRowsSq, bestRows, hfind]
    cases hb : acc.find? (·.model == r.model) with
    | none =>
      simp only [Option.map_none]
      have := bestRowsSq_ofRow rs (acc ++ [r]) hrs (by
        intro y hy; rcases List.mem_append.mp hy with m | m
        · exact hacc y m
        · simp at m; subst m; exact hr0)
      simpa using this
    | some b =>
      have hb0 : 0 ≤ b.se := hacc b (List.mem_of_find?_eq_some hb)
      simp only [Option.map_some, repBeforeSq_ofRow hr0 hb0]
      split
      · have hmap : (acc.map RowSq.ofRow).map
            (fun x => if x.model == (RowSq.ofRow r).model then RowSq.ofRow r else x) =
            (acc.map (fun x => if x.model == r.model then r else x)).map RowSq.ofRow := by
          simp only [List.map_map]
          congr 1; funext x
          by_cases hx : x.model = r.model <;> simp [hx, RowSq.ofRow]
        rw [hmap]
        apply bestRowsSq_ofRow rs _ hrs
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        split
        · exact hr0
        · exact hacc x hx
      · exact bestRowsSq_ofRow rs acc hrs hacc

theorem representativesSq_ofRow (rows : List Row) (h : ∀ y ∈ rows, 0 ≤ y.se) :
    representativesSq (rows.map RowSq.ofRow) = (representatives rows).map RowSq.ofRow := by
  have hb := bestRowsSq_ofRow rows [] h (by simp)
  simp only [List.map_nil] at hb
  unfold representativesSq representatives
  rw [hb]
  apply sortBy_ofRow rankBefore rankBeforeSq (fun r => 0 ≤ r.se)
    (fun a b ha hb => rankBeforeSq_ofRow ha hb)
  -- Every representative is one of the rows.
  have : ∀ (rows acc : List Row), (∀ y ∈ rows, 0 ≤ y.se) → (∀ y ∈ acc, 0 ≤ y.se) →
      ∀ y ∈ bestRows rows acc, 0 ≤ y.se := by
    intro rows
    induction rows with
    | nil => intro acc _ hacc; exact hacc
    | cons r rs ih =>
      intro acc hr hacc
      have hrs : ∀ y ∈ rs, 0 ≤ y.se := fun y hy => hr y (by simp [hy])
      simp only [bestRows]
      split
      · apply ih _ hrs
        intro y hy; rcases List.mem_append.mp hy with m | m
        · exact hacc y m
        · simp at m; subst m; exact hr _ List.mem_cons_self
      · apply ih _ hrs
        split
        · intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          split
          · exact hr _ List.mem_cons_self
          · exact hacc x hx
        · exact hacc
  exact this rows [] h (by simp)

/-! ### The spacing, the scan and the classes -/

theorem spacingOfSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (z floor : Rat)
    (reps : List Row) :
    spacingOfSq table z floor (reps.map RowSq.ofRow) = spacingSq table z floor reps := by
  match reps with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | r1 :: r2 :: r3 :: rs =>
    simp only [List.map_cons, spacingOfSq, spacingSq, pairSdSq_ofRow]
    rfl

theorem scanSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds) (u2 : Rat) :
    ∀ (rs : List Row) (st : ScanState) (prev : Row),
      scanSq table t u2 (ScanStateSq.ofState st) (RowSq.ofRow prev) (rs.map RowSq.ofRow) =
        scan table t u2 st prev rs := by
  intro rs
  induction rs with
  | nil => intro st prev; cases st <;> rfl
  | cons r rs ih =>
    intro st prev
    have ihc := ih .closed r
    have ihs := ih .scanning r
    have iha := fun c => ih (.atCusp c) r
    simp only [ScanStateSq.ofState] at ihc ihs iha
    cases st with
    | closed => simp only [List.map_cons, ScanStateSq.ofState, scanSq, scan, ihc]
    | atCusp c =>
      simp only [List.map_cons, ScanStateSq.ofState, scanSq, scan, belowSq_ofRow, ihc, iha]
    | scanning =>
      simp only [List.map_cons, ScanStateSq.ofState, scanSq, scan, pairSdSq_ofRow, ihc, ihs]
      have := iha r
      simp only [RowSq.ofRow] at this ⊢
      rw [this]
      rfl

theorem repClassesSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (t : Thresholds)
    (u2 : Rat) (reps : List Row) :
    repClassesSq table t u2 (reps.map RowSq.ofRow) = repClasses table t u2 reps := by
  match reps with
  | [] => rfl
  | [_] => rfl
  | _ :: r2 :: rs =>
    have := scanSq_ofRow table t u2 rs .scanning r2
    simp only [ScanStateSq.ofState] at this
    simp only [List.map_cons, repClassesSq, repClasses, this]

theorem lowestSq_ofRow (cls : ClusterClass) (reps : List Row) (classes : List ClusterClass) :
    lowestSq cls (reps.map RowSq.ofRow) classes = (lowest cls reps classes).map RowSq.ofRow := by
  unfold lowestSq lowest
  rw [List.zip_map_left, List.filter_map, List.getLast?_map, Option.map_map, Option.map_map]
  rfl

theorem otherClassSq_ofRow (table : Option (List ((RowKey × RowKey) × Rat))) (z : Rat)
    (lowIn lowCusp : Option Row) (r : Row) :
    otherClassSq table z (lowIn.map RowSq.ofRow) (lowCusp.map RowSq.ofRow) (RowSq.ofRow r) =
      otherClass table z lowIn lowCusp r := by
  cases lowIn <;> cases lowCusp <;> simp [otherClassSq, otherClass, belowSq_ofRow]

theorem repLinesSq_ofRow (u2 : Rat) : ∀ (k : Nat) (prev : Option Row) (rs : List Row)
    (cs : List ClusterClass),
    repLinesSq u2 k (prev.map RowSq.ofRow) (rs.map RowSq.ofRow) cs =
      (repLines u2 k prev rs cs).map LineSq.ofLine
  | _, _, [], _ => by simp [repLinesSq, repLines]
  | _, _, _ :: _, [] => by simp [repLinesSq, repLines]
  | k, prev, r :: rs, c :: cs => by
    have ih := repLinesSq_ofRow u2 (k + 1) (some r) rs cs
    simp only [Option.map_some] at ih
    match k, prev with
    | 0, _ | 1, _ | _ + 2, none =>
      simp only [List.map_cons, repLinesSq, repLines, ih]
      simp [LineSq.ofLine, RowSq.ofRow]
    | _ + 2, some p =>
      simp only [List.map_cons, repLinesSq, repLines, Option.map_some, ih]
      simp [LineSq.ofLine, RowSq.ofRow]

theorem mapM_ofRow (g : RowSq → Except ClusterError LineSq) (f : Row → Except ClusterError Line)
    (hg : ∀ r, g (RowSq.ofRow r) = (f r).map LineSq.ofLine) :
    ∀ (l : List Row), (l.map RowSq.ofRow).mapM g = (l.mapM f).map (·.map LineSq.ofLine)
  | [] => rfl
  | r :: rs => by
    have ih := mapM_ofRow g f hg rs
    simp only [List.map_cons, List.mapM_cons, hg, ih]
    cases f r <;> cases rs.mapM f <;> rfl

/-! ### The rule -/

theorem map_ok' {ε α β : Type} (f : α → β) (v : α) :
    (f <$> (Except.ok v : Except ε α)) = Except.ok (f v) := rfl

theorem map_error' {ε α β : Type} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = Except.error e := rfl

/-- The rule after its checks, for one table: the rows' squares give `cluster`'s result. -/
theorem body_ofRow (rows : List Row) (h : ∀ r ∈ rows, 0 ≤ r.se) (t : Thresholds) (floor : Rat)
    (T : Option (List ((RowKey × RowKey) × Rat))) :
    Except.bind (spacingSq T t.z floor (representatives rows)) (fun p =>
      Except.bind (repClasses T t p.1 (representatives rows)) (fun cl =>
        Except.bind
          (List.mapM
            (fun r => Except.bind
              (otherClassSq T t.z (Option.map RowSq.ofRow (lowest .inside (representatives rows) cl))
                (Option.map RowSq.ofRow (lowest .cusp (representatives rows) cl)) r)
              (fun c => pure (LineSq.mk none r none none c)))
            (sortBySq otherBeforeSq
              (List.filter (fun r => !(List.map Row.key (representatives rows)).contains r.key)
                (List.map RowSq.ofRow rows))))
          (fun v => pure (ResultSq.mk p.1 p.2
            (repLinesSq p.1 0 none (List.map RowSq.ofRow (representatives rows)) cl ++ v))))) =
      Except.map ResultSq.ofResult
        (Except.bind (spacingSq T t.z floor (representatives rows)) (fun p =>
          Except.bind (repClasses T t p.1 (representatives rows)) (fun cl =>
            Except.bind
              (List.mapM
                (fun r => Except.bind
                  (otherClass T t.z (lowest .inside (representatives rows) cl)
                    (lowest .cusp (representatives rows) cl) r)
                  (fun c => pure (Line.mk none r none none c)))
                (sortBy otherBefore
                  (List.filter (fun r => !(List.map Row.key (representatives rows)).contains r.key) rows)))
              (fun v => pure (Result.mk p.1 p.2 (repLines p.1 0 none (representatives rows) cl ++ v)))))) := by
  cases spacingSq T t.z floor (representatives rows) with
  | error e => rfl
  | ok p =>
    simp only [Except.bind]
    cases repClasses T t p.fst (representatives rows) with
    | error e => rfl
    | ok classes =>
      simp only
      have hfilter : (rows.map RowSq.ofRow).filter
          (fun r => !((representatives rows).map Row.key).contains r.key) =
          (rows.filter (fun r => !((representatives rows).map Row.key).contains r.key)).map
            RowSq.ofRow := by
        rw [List.filter_map]; rfl
      rw [hfilter, sortBy_ofRow otherBefore otherBeforeSq (fun r => 0 ≤ r.se)
        (fun a b ha hb => otherBeforeSq_ofRow ha hb) _
        (fun y hy => h y (List.mem_filter.mp hy).1)]
      have hm := mapM_ofRow
        (fun r => Except.bind
          (otherClassSq T t.z (Option.map RowSq.ofRow (lowest .inside (representatives rows) classes))
            (Option.map RowSq.ofRow (lowest .cusp (representatives rows) classes)) r)
          (fun c => pure (LineSq.mk none r none none c)))
        (fun r => Except.bind
          (otherClass T t.z (lowest .inside (representatives rows) classes)
            (lowest .cusp (representatives rows) classes) r)
          (fun c => pure (Line.mk none r none none c)))
        (fun r => by
          simp only [otherClassSq_ofRow]
          cases otherClass T t.z _ _ r <;> rfl)
        (sortBy otherBefore
          (List.filter (fun r => !(List.map Row.key (representatives rows)).contains r.key) rows))
      simp only [Except.bind] at hm
      rw [hm]
      cases (List.mapM (m := Except ClusterError) (β := Line) _ (sortBy otherBefore _)) with
      | error e => rfl
      | ok ls =>
        have := repLinesSq_ofRow p.fst 0 none (representatives rows) classes
        simp only [Option.map_none] at this
        simp only [pure, Except.pure, Except.map, ResultSq.ofResult, List.map_append, this]

/-- On rows whose `se2` is `se * se` with `se ≥ 0`, `clusterSq` is `cluster`: the same
refusal, or the same result with every row given as its square. -/
theorem clusterSq_ofRow (rows : List Row) (h : ∀ r ∈ rows, 0 ≤ r.se) (t : Thresholds) (floor : Rat)
    (paired : Option (List PairedSe)) :
    clusterSq (rows.map RowSq.ofRow) t floor paired =
      (cluster rows t floor paired).map ResultSq.ofResult := by
  unfold clusterSq cluster
  rw [checkInputSq_ofRow rows t floor h, map_key_ofRow]
  simp only [representativesSq_ofRow rows h, spacingOfSq_ofRow, repClassesSq_ofRow,
    lowestSq_ofRow, map_key_ofRow]
  cases checkInput rows t floor with
  | error e => rfl
  | ok u =>
    simp only [bind, Except.bind]
    -- The table, `none` or the paired SEs' table, named `T` in both rules.
    cases paired with
    | none =>
      simp only [pure, Except.pure]
      generalize hT : (none : Option (List ((RowKey × RowKey) × Rat))) = T
      have hb := body_ofRow rows h t floor T
      simp only [Except.bind] at hb
      exact hb
    | some ps =>
      cases hp : pairedTable (List.map Row.key rows) ps [] with
      | error e => simp only [hp, map_error']; rfl
      | ok v =>
        simp only [hp, map_ok']
        have hb := body_ofRow rows h t floor (some v)
        simp only [Except.bind] at hb
        exact hb

/-- Where every row's `se2` is `se * se` with `se ≥ 0`,
`clusterSq` refuses exactly when `cluster` does, with the same word, and otherwise answers
the same spacing square and source and, row for row, the same rows, ranks, steps, spacings
and classes. -/
theorem clusterSq_agrees (rows : List Row) (h : ∀ r ∈ rows, 0 ≤ r.se) (t : Thresholds)
    (floor : Rat) (paired : Option (List PairedSe)) :
    match cluster rows t floor paired, clusterSq (rows.map RowSq.ofRow) t floor paired with
    | .error e, .error e' => e' = e
    | .ok r, .ok q =>
      q.spacingSq = r.spacingSq ∧ q.source = r.source ∧
        q.lines.map (·.rank) = r.lines.map (·.rank) ∧
        q.lines.map (·.row) = r.lines.map (RowSq.ofRow ·.row) ∧
        q.lines.map (·.step) = r.lines.map (·.step) ∧
        q.lines.map (·.spacings) = r.lines.map (·.spacings) ∧
        q.classes = r.classes
    | _, _ => False := by
  rw [clusterSq_ofRow rows h t floor paired]
  cases cluster rows t floor paired with
  | error e => rfl
  | ok r =>
    simp [Except.map, ResultSq.ofResult, ResultSq.classes, Result.classes, LineSq.ofLine,
      List.map_map, Function.comp_def]

end Principia.Cluster
