import Principia.Cluster.Bounded

/-!
# The ROW and its measure (TPS 5.19.6, 5.19.7)

A month's component scores are entries of one model at one MODEL CONFIGURATION on one
benchmark, each with its score and its SE. A ROW is one (model, configuration). Under the
CORE SET (its benchmarks, its SE DEFINITION and SE MAX) a ROW's COMPOSITE SCORE is the mean
of its scores on every CORE SET benchmark, and its SE under ITEM-SAMPLING is
`sqrt(sum of the squared component SEs) / m`, `m` the number of CORE SET benchmarks. The SE
is kept as its exact square `se2 = (sum of the squared SEs) / m²`; its text is the square
root written to six decimals (`Surd.fixed6`), as v1 wrote its numbers.

A ROW is UNLISTED when it misses a score on a CORE SET benchmark, when its SE is above SE MAX
(compared exactly, `se_max² < se2`), or when its model was released after the last update of
a source of a CORE SET benchmark, both dates given. Otherwise it is LISTED. Scores on a
benchmark outside the CORE SET take no part in the measure.

Not computed here, and answered OWED by the Calculator: the SE DEFINITION FIXED-SET (the
sources mark it VERIFY) and the binomial SE of a component that states an item count in
place of an SE (the sources do not fix its scale).

The values formed (the sums, the squares, the divisions, SE MAX's square and the texts'
scaling) are walked first within the bound on an exact value (`rowsWithin`), in the pattern
of `Principia.Cluster.Bounded`, and only then computed by the plain functions.
-/

namespace Principia.Cluster.Rows

/-- One component score: a model at a configuration on one benchmark, its score and SE. -/
structure Component where
  /-- The model. -/
  model : String
  /-- The MODEL CONFIGURATION. -/
  config : String
  /-- The benchmark. -/
  benchmark : String
  /-- The score. -/
  score : Rat
  /-- The source's SE, not negative. -/
  se : Rat
  deriving Repr

/-- The CORE SET's part the measure reads: its benchmarks and SE MAX. -/
structure CoreSet where
  /-- The CORE SET benchmarks, none twice. -/
  benchmarks : List String
  /-- SE MAX, in the composite's units. -/
  seMax : Rat
  deriving Repr

/-- Why a ROW is UNLISTED. -/
inductive Reason where
  /-- A CORE SET benchmark has no score for the ROW. -/
  | missingCore
  /-- The ROW's SE is above SE MAX. -/
  | seAboveMax
  /-- The model was released after a source's last update. -/
  | lateRelease
  deriving DecidableEq, Repr

/-- A reason's word. -/
def Reason.word : Reason → String
  | .missingCore => "MISSING CORE SCORE"
  | .seAboveMax => "SE ABOVE SE MAX"
  | .lateRelease => "RELEASED AFTER SOURCE UPDATE"

/-- A ROW's measure: its composite and `se2` when every core score is present, and the
reasons it is UNLISTED (none: LISTED). -/
structure Measure where
  /-- The model. -/
  model : String
  /-- The MODEL CONFIGURATION. -/
  config : String
  /-- The COMPOSITE SCORE. -/
  composite : Option Rat
  /-- The square of the SE. -/
  se2 : Option Rat
  /-- Why the ROW is UNLISTED; empty when it is LISTED. -/
  reasons : List Reason
  deriving Repr

/-- Whether a ROW is LISTED. -/
def Measure.listed (m : Measure) : Bool := m.reasons.isEmpty

/-- The ROWs, in the order of their first component. -/
def keys : List Component → List RowKey → List RowKey
  | [], acc => acc.reverse
  | c :: rest, acc =>
    if acc.contains (c.model, c.config) then keys rest acc else keys rest ((c.model, c.config) :: acc)

/-- The ROW's component on a benchmark. -/
def scoreOf (cs : List Component) (k : RowKey) (b : String) : Option Component :=
  cs.find? fun c => c.model == k.1 && c.config == k.2 && c.benchmark == b

/-- The ROW's components on every CORE SET benchmark, in the CORE SET's order, when all
are present. -/
def coreComponents (cs : List Component) (k : RowKey) (core : CoreSet) : Option (List Component) :=
  core.benchmarks.mapM (scoreOf cs k)

/-- The COMPOSITE SCORE: the mean of the scores. -/
def composite (xs : List Component) : Rat :=
  (xs.map (·.score)).sum / xs.length

/-- The square of the SE under ITEM-SAMPLING: `(sum of the squared SEs) / m²`. -/
def se2 (xs : List Component) : Rat :=
  (xs.map fun c => c.se * c.se).sum / ((xs.length : Rat) * xs.length)

/-- A model released after the last update of a CORE SET benchmark's source, both dates
given (dates `YYYY-MM-DD`, compared as text, which is their order). -/
def late (released updated : List (String × String)) (core : CoreSet) (model : String) : Bool :=
  match released.lookup model with
  | none => false
  | some d => core.benchmarks.any fun b =>
    match updated.lookup b with
    | some u => decide (u < d)
    | none => false

/-- A ROW's measure. -/
def measure (cs : List Component) (core : CoreSet) (released updated : List (String × String))
    (k : RowKey) : Measure :=
  let lateR := if late released updated core k.1 then [Reason.lateRelease] else []
  match coreComponents cs k core with
  | none => ⟨k.1, k.2, none, none, Reason.missingCore :: lateR⟩
  | some xs =>
    let s := se2 xs
    let seR := if core.seMax * core.seMax < s then [Reason.seAboveMax] else []
    ⟨k.1, k.2, some (composite xs), some s, seR ++ lateR⟩

/-- Every ROW's measure, in the order of their first component. -/
def rows (cs : List Component) (core : CoreSet) (released updated : List (String × String)) :
    List Measure :=
  (keys cs []).map (measure cs core released updated)

/-! ## Within the bound on an exact value -/

open Principia.ValueBound (Bounded)

/-- The values one ROW's measure forms, and its texts' values, each formed within the bound. -/
def rowWithin (cs : List Component) (core : CoreSet) (k : RowKey) : Bounded Unit :=
  match coreComponents cs k core with
  | none => pure ()
  | some xs => do
    let sum ← ValueBound.sumBy (fun c => ValueBound.ofRat c.score) xs
    let comp ← ValueBound.div sum xs.length
    let sq ← ValueBound.sumBy (fun c => ValueBound.mul c.se c.se) xs
    let mm ← ValueBound.mul xs.length xs.length
    let s ← ValueBound.div sq mm
    Bounded.fixed6Within (Surd.ofRat comp)
    Bounded.fixed6Within (Surd.sqrt s)

/-- The values every ROW's measure forms, SE MAX's square first. -/
def rowsWithin (cs : List Component) (core : CoreSet) : Bounded Unit := do
  let _ ← ValueBound.mul core.seMax core.seMax
  (keys cs []).forM (rowWithin cs core)

/-! ## Theorems -/

theorem mapM_some_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ a ∈ l, (f a).isSome
  | [], _, _, a, h => by simp at h
  | x :: rest, ys, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : rest.mapM f with
      | none => simp [hx, hr] at h
      | some zs =>
        rcases List.mem_cons.mp ha with rfl | hm
        · simp [hx]
        · exact mapM_some_isSome f rest zs hr a hm

/-- A LISTED ROW has a score on every CORE SET benchmark. -/
theorem listed_has_core (cs : List Component) (core : CoreSet) (r u : List (String × String))
    (k : RowKey) (h : (measure cs core r u k).listed = true) :
    ∀ b ∈ core.benchmarks, (scoreOf cs k b).isSome := by
  unfold measure at h
  cases hc : coreComponents cs k core with
  | none => simp [hc, Measure.listed] at h
  | some xs => exact mapM_some_isSome (scoreOf cs k) core.benchmarks xs hc

/-- A LISTED ROW's `se2` is at most SE MAX squared. -/
theorem listed_se2_le (cs : List Component) (core : CoreSet) (r u : List (String × String))
    (k : RowKey) (s : Rat) (h : (measure cs core r u k).listed = true)
    (hs : (measure cs core r u k).se2 = some s) : s ≤ core.seMax * core.seMax := by
  unfold measure at h hs
  cases hc : coreComponents cs k core with
  | none => simp [hc] at hs
  | some xs =>
    simp only [hc, Option.some.injEq] at hs
    subst hs
    by_cases hlt : core.seMax * core.seMax < se2 xs
    · simp [hc, hlt, Measure.listed] at h
    · exact Rat.not_lt.mp hlt

/-- The composite of one benchmark is that benchmark's score. -/
theorem composite_one (c : Component) : composite [c] = c.score := by
  have h1 : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1)
  simp [composite, Rat.add_zero, Rat.div_def, h1]

end Principia.Cluster.Rows
