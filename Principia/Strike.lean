import Principia.Parameters
import Principia.Strike.Numeric

/-!
# The strike rule: distance, SR3's mechanical tests, SR5, SR6 and SR8

The arithmetic of v1's strike rule (TPS 0.5.0, 4.4): SR4's distance, SR3's M-M and L-M
contradiction tests, SR5's ordering, SR6's independence count and audit threshold, and
SR8's scale factor. Ported from v1's `tpc_strike` (TPC-PY 0.3.0); SR9's compliance
checks are in `Principia.SR9`.

Exact arithmetic throughout. A value, an uncertainty and `k` are `Rat`s, read from the
decimal text of their source; v1 computed with floats. Where v1 compared against a
square root, a verdict here compares squares, and SR8's scale factor `S` is held as its
square (`ScaleFactor.square`), so no root is taken to reach a verdict. Where `S` is wanted
as a number, `ScaleFactor.digits` gives `√square` correctly rounded to a number of
significant digits. Those numeric primitives are in `Principia.Strike.Numeric`.

Not here: v1's `canon`, the canonical serialization (its own item); `sr3_scope`,
`conditions_of`, `comparison_set` and `sr8_groups`, which read the zones and the
register's records; the units wrappers, which bring two values to one unit and then call
`mmContradicts`, `lmContradicts` and `sr8ScaleFactor` (the units item).

PMA words: v1's TFK is the Research Assembly, its TMS the Criteria Set.

Vectors: the strike corpus and the SR8 order corpus, run by
the strike vector tests.
-/

namespace Principia.Strike

open Principia.Parameters (sr8MinGroup sr8OutlierFactor sr8Threshold nXMin)
open Numeric

/-! ## SR4: the distance d(r) = (a(r), s(r)) -/

/-- What SR4 reads of a record: its own ASSUMPTIONS and the records it CITES, both as
identifiers (TPS 4.4.5), and `s(r)`, its own derivation's step count under the
container's STEP CONVENTION. -/
structure StrikeRecord where
  /-- The record's own ASSUMPTIONS. -/
  assumptions : List String
  /-- The records it CITES. -/
  cites : List String
  /-- `s(r)`: its own derivation's step count. -/
  steps : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The records SR4 reads, by identifier; the first pair carrying an identifier is that
record. -/
abbrev Records := List (String × StrikeRecord)

/-- `acc` with each of `xs` added that it does not already hold. -/
def insertNew (acc xs : List String) : List String :=
  xs.foldl (fun a x => if a.contains x then a else x :: a) acc

/-- The stack walk of `assumptionClosure`. Each step pops one identifier: a record seen
before is skipped; a new one adds its ASSUMPTIONS and pushes its CITES. An identifier no
record carries ends the walk with `none`, as v1 raised; so does running out of `fuel`
pops, which `closureFuel` makes unreachable. -/
def closureWalk (records : Records) :
    Nat → List String → List String → List String → Option (List String)
  | _, [], _, acc => some acc
  | 0, _ :: _, _, _ => none
  | fuel + 1, cur :: stack, seen, acc =>
    if seen.contains cur then closureWalk records fuel stack seen acc
    else
      match records.lookup cur with
      | none => none
      | some r => closureWalk records fuel (r.cites ++ stack) (cur :: seen)
          (insertNew acc r.assumptions)

/-- The pops `closureWalk` needs at most: one for the start, and one for each identifier
pushed. A record is expanded once (it is then seen) and pushes only its CITES, so the
pushes are at most the CITES entries of all the records. -/
def closureFuel (records : Records) : Nat :=
  records.foldl (fun n p => n + p.2.cites.length) 1

/-- The order of identifiers: by code point, as v1 sorted. -/
def idLe (a b : String) : Bool := decide (a ≤ b)

/-- v1's `assumption_closure`: the ASSUMPTIONS of record `rid` and of every record it
cites, transitively, as distinct identifiers in code point order. A cycle of citations is
walked once. `none` when the walk reaches an identifier that no record carries. -/
def assumptionClosure (rid : String) (records : Records) : Option (List String) :=
  (closureWalk records (closureFuel records) [rid] [] []).map (·.mergeSort idLe)

/-- v1's `a_of_r`, SR4's `a(r)`: the number of distinct assumption identifiers in the
closure of `rid`, the Research Assembly's own (`assembly`) excluded (TPS 4.4.5). -/
def aOfR (rid : String) (records : Records) (assembly : List String := []) : Option Nat :=
  (assumptionClosure rid records).map fun c => (c.filter (!assembly.contains ·)).length

/-- SR4's distance `d(r) = (a(r), s(r))`, compared lexicographically, lower closer. -/
structure Distance where
  /-- `a(r)`. -/
  assumptions : Nat
  /-- `s(r)`. -/
  steps : Nat
  deriving Repr, DecidableEq, Inhabited

/-- v1's `d_of_r`: `d(rid)`; `none` when `a(rid)` is (a record missing). -/
def dOfR (rid : String) (records : Records) (assembly : List String := []) :
    Option Distance := do
  let a ← aOfR rid records assembly
  let r ← records.lookup rid
  pure ⟨a, r.steps⟩

/-- v1's `d_compare`: the lexicographic order of distances. `.lt` (v1's -1) when `d1` is
closer, `.gt` (1) when `d2` is, `.eq` (0) when they are equal. -/
def dCompare (d1 d2 : Distance) : Ordering :=
  if d1.assumptions < d2.assumptions then .lt
  else if d2.assumptions < d1.assumptions then .gt
  else if d1.steps < d2.steps then .lt
  else if d2.steps < d1.steps then .gt
  else .eq

/-- Every distance is equal to itself. -/
theorem dCompare_self (d : Distance) : dCompare d d = .eq := by
  simp [dCompare]

/-- Swapping the arguments swaps the answer. -/
theorem dCompare_swap (d1 d2 : Distance) : dCompare d2 d1 = (dCompare d1 d2).swap := by
  unfold dCompare
  repeat' split
  all_goals first | rfl | omega

/-- `.eq` exactly when the distances are equal. -/
theorem dCompare_eq_iff (d1 d2 : Distance) : dCompare d1 d2 = .eq ↔ d1 = d2 := by
  cases d1; cases d2
  unfold dCompare
  repeat' split
  all_goals simp_all <;> omega

/-- The order is transitive. -/
theorem dCompare_trans {d1 d2 d3 : Distance} (h12 : dCompare d1 d2 = .lt)
    (h23 : dCompare d2 d3 = .lt) : dCompare d1 d3 = .lt := by
  unfold dCompare at *
  repeat' split at h12
  all_goals repeat' split at h23
  all_goals first | contradiction | (repeat' split) <;> first | rfl | omega

/-! ## SR5: of two contradicting standing records, the closer stands -/

/-- SR5's outcome for two contradicting standing records. -/
inductive Sr5Outcome where
  /-- v1's `r1`: the first is closer and stands; the second is struck. -/
  | first
  /-- v1's `r2`: the second is closer and stands; the first is struck. -/
  | second
  /-- v1's `AUDIT`: equal distance opens an audit block. -/
  | audit
  deriving Repr, DecidableEq, Inhabited

/-- v1's word for the outcome. -/
def Sr5Outcome.toV1 : Sr5Outcome → String
  | .first => "r1"
  | .second => "r2"
  | .audit => "AUDIT"

/-- The outcome with the two records' places exchanged. -/
def Sr5Outcome.swap : Sr5Outcome → Sr5Outcome
  | .first => .second
  | .second => .first
  | .audit => .audit

/-- v1's `sr5_order`: the smaller distance stands; equal distance opens an audit block. -/
def sr5Order (d1 d2 : Distance) : Sr5Outcome :=
  match dCompare d1 d2 with
  | .lt => .first
  | .gt => .second
  | .eq => .audit

/-- SR5 does not depend on the order the two records are given in. -/
theorem sr5Order_swap (d1 d2 : Distance) : sr5Order d2 d1 = (sr5Order d1 d2).swap := by
  unfold sr5Order
  rw [dCompare_swap d1 d2]
  cases dCompare d1 d2 <;> rfl

/-- An audit block opens exactly on equal distances. -/
theorem sr5Order_audit_iff (d1 d2 : Distance) : sr5Order d1 d2 = .audit ↔ d1 = d2 := by
  rw [← dCompare_eq_iff]
  unfold sr5Order
  cases dCompare d1 d2 <;> simp

/-! ## SR6: the independence count and the audit threshold -/

/-- Whether two identifier sets share no identifier. -/
def disjoint {α : Type} [BEq α] (a b : List α) : Bool := a.all (!b.contains ·)

/-- The largest number of `sets` that are pairwise disjoint and disjoint from `used`:
each set is skipped, or taken when it shares nothing with what is taken. The
specification: it tries every sub-family, and `packingPruned` computes it. -/
def packing {α : Type} [BEq α] : List (List α) → List α → Nat
  | [], _ => 0
  | s :: rest, used =>
    if disjoint used s then max (packing rest used) (packing rest (used ++ s) + 1)
    else packing rest used

/-- No packing is larger than the family. -/
theorem packing_le_length {α : Type} [BEq α] (sets : List (List α)) (used : List α) :
    packing sets used ≤ sets.length := by
  induction sets generalizing used with
  | nil => simp [packing]
  | cons s rest ih =>
    have h1 := ih used
    have h2 := ih (used ++ s)
    simp only [packing, List.length_cons]
    split <;> omega

/-- v1's bounded search for the packing (`sr6_independence_count`'s `bt`): `count` sets
are taken so far, disjoint and making up `used`, and `best` is the largest count reached.
A search path is cut when taking every set left could not pass `best`; otherwise each set is
skipped first, then taken when it shares nothing with what is taken. It computes what
`packing` specifies (`packing_pruned_eq`). -/
def packingPruned {α : Type} [BEq α] : List (List α) → List α → Nat → Nat → Nat
  | [], _, count, best => max count best
  | s :: rest, used, count, best =>
    if count + (rest.length + 1) ≤ best then best
    else
      let best' := packingPruned rest used count best
      if disjoint used s then packingPruned rest (used ++ s) (count + 1) best' else best'

/-- The bounded search returns the better of `best` and `count` plus the packing left. -/
theorem packingPruned_eq {α : Type} [BEq α] (sets : List (List α)) (used : List α)
    (count best : Nat) :
    packingPruned sets used count best = max best (count + packing sets used) := by
  induction sets generalizing used count best with
  | nil => simp only [packingPruned, packing]; omega
  | cons s rest ih =>
    have hle := packing_le_length (s :: rest) used
    simp only [List.length_cons] at hle
    simp only [packingPruned]
    split
    · omega
    · rw [ih used count best]
      simp only [packing]
      split
      · rw [ih (used ++ s) (count + 1)]
        omega
      · omega

/-- **The pruned packing is the packing.** v1's bounded search, from nothing taken,
counts exactly the largest pairwise disjoint sub-family. -/
theorem packing_pruned_eq {α : Type} [BEq α] (sets : List (List α)) :
    packingPruned sets [] 0 0 = packing sets [] := by
  rw [packingPruned_eq]
  omega

/-- Disjointness survives a renaming that is one to one on the identifiers of both sets. -/
theorem disjoint_map {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (a b : List α) (hf : ∀ x ∈ a, ∀ y ∈ b, f x = f y → x = y) :
    disjoint (a.map f) (b.map f) = disjoint a b := by
  rw [Bool.eq_iff_iff]
  simp only [disjoint, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
    decide_eq_false_iff_not, not_exists, not_and]
  constructor
  · intro h x hx hxb
    exact h x hx x hxb rfl
  · intro h x hx y hy hxy
    exact h x hx (hf x hx y hy hxy.symm ▸ hy)

/-- No packing changes under a renaming that is one to one on a `pool` holding every
identifier of `sets` and `used`. -/
theorem packing_map {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (pool : List α) (hf : ∀ x ∈ pool, ∀ y ∈ pool, f x = f y → x = y)
    (sets : List (List α)) (used : List α) (hu : ∀ x ∈ used, x ∈ pool)
    (hs : ∀ s ∈ sets, ∀ x ∈ s, x ∈ pool) :
    packing (sets.map (List.map f)) (used.map f) = packing sets used := by
  induction sets generalizing used with
  | nil => rfl
  | cons s rest ih =>
    have hs' : ∀ x ∈ s, x ∈ pool := hs s (List.mem_cons_self ..)
    have hrest : ∀ t ∈ rest, ∀ x ∈ t, x ∈ pool := fun t ht => hs t (List.mem_cons_of_mem _ ht)
    have hus : ∀ x ∈ used ++ s, x ∈ pool := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hu x h
      · exact hs' x h
    have ih1 := ih used hu hrest
    have ih2 := ih (used ++ s) hus hrest
    rw [List.map_append] at ih2
    simp only [List.map_cons, packing, ih1, ih2,
      disjoint_map f used s (fun x hx y hy => hf x (hu x hx) y (hs' y hy))]

/-- Each identifier of `s` as its first position in `pool`. One to one on `pool`'s
identifiers, it changes no packing (`packing_intern`); the search then compares numbers,
so its time does not grow with the identifiers' length. -/
def intern {α : Type} [BEq α] (pool : List α) (s : List α) : List Nat := s.map pool.idxOf

/-- **Interning changes no packing.** Each identifier as its first position among all the
identifiers of `sets`. -/
theorem packing_intern {α : Type} [BEq α] [LawfulBEq α] (sets : List (List α)) :
    packing (sets.map (intern sets.flatten)) [] = packing sets [] := by
  have hf : ∀ x ∈ sets.flatten, ∀ y ∈ sets.flatten,
      sets.flatten.idxOf x = sets.flatten.idxOf y → x = y := by
    intro x hx y hy hxy
    have hx' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
    have hy' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
    simp only [hxy] at hx'
    exact hx'.symm.trans hy'
  exact packing_map sets.flatten.idxOf sets.flatten hf sets [] (by simp)
    (fun s hs x hx => List.mem_flatten.mpr ⟨s, hs, hx⟩)

/-- **What SR6 computes is the packing.** v1's bounded search over the interned sets
counts exactly the largest pairwise disjoint sub-family of the sets as given. -/
theorem packingPruned_intern (sets : List (List String)) :
    packingPruned (sets.map (intern sets.flatten)) [] 0 0 = packing sets [] := by
  rw [packing_pruned_eq, packing_intern]

/-- v1's guard on the exact packing: at most 24 contradictions after the SAME-MODEL ones
are dropped; v1 raised beyond it ("realistic contradiction sets are tiny"). -/
def sr6PackingGuard : Nat := 24

/-- v1's `sr6_independence_count`, SR6's `n_ind(r)`: the largest sub-family of the
contradictions of a record whose extra-assumption sets are pairwise disjoint, as
identifier sets (TPS 4.4.7). A contradiction flagged in `sameModel` is dropped first. `none` beyond `sr6PackingGuard`, as v1 raised, and when `sameModel` does not have
one flag per set: v1 paired them by `zip` and dropped the unpaired sets silently, a v2
divergence that no case of v1's corpus reaches. Computed by v1's bounded search
(`packingPruned`) over the sets kept, their identifiers interned (`intern`), which is
`packing` of the sets kept (`packingPruned_intern`). -/
def sr6IndependenceCount (sets : List (List String)) (sameModel : Option (List Bool) := none) :
    Option Nat := do
  let kept ← match sameModel with
    | none => some sets
    | some flags =>
      if flags.length = sets.length then
        some ((sets.zip flags).filterMap fun (s, sm) => if sm then none else some s)
      else none
  if sr6PackingGuard < kept.length then none
  else some (packingPruned (kept.map (intern kept.flatten)) [] 0 0)

/-- v1's `sr6_audit_opens`: an audit block opens on a record when `n_ind` reaches `N_x`.
`none` for an `N_x` below SR6's least, 2 (`Parameters.nXMin`), as v1 raised. -/
def sr6AuditOpens (nInd nX : Nat) : Option Bool :=
  if nX < nXMin then none else some (decide (nX ≤ nInd))

/-- For a declarable `N_x`, the block opens exactly when `n_ind` reaches it. -/
theorem sr6AuditOpens_eq {nInd nX : Nat} (h : nXMin ≤ nX) :
    sr6AuditOpens nInd nX = some (decide (nX ≤ nInd)) := by
  simp [sr6AuditOpens, Nat.not_lt.mpr h]

/-- More independent contradictions never close an audit that fewer opened. -/
theorem sr6AuditOpens_mono {n m nX : Nat} (h : sr6AuditOpens n nX = some true) (hnm : n ≤ m) :
    sr6AuditOpens m nX = some true := by
  unfold sr6AuditOpens at *
  by_cases hx : nX < nXMin
  · simp [hx] at h
  · simp only [hx, ite_false, Option.some.injEq, decide_eq_true_eq] at h ⊢
    omega

/-! ## SR8: the scale factor -/

/-- An M record's value with its combined standard uncertainty `u_c`, already in the
quantity's one unit. -/
structure Measurement where
  /-- `x`, the value. -/
  value : Rat
  /-- `u_c`, its combined standard uncertainty. -/
  uncertainty : Rat
  deriving Repr, DecidableEq, Inhabited

/-- SR8's scale factor `S`, held exactly as its square: `S = √square`. `S` is at least 1:
it is 1, or the root of a reduced chi-square above 1. -/
structure ScaleFactor where
  /-- `S²`. -/
  square : Rat
  /-- `S ≥ 1`. -/
  one_le_square : 1 ≤ square

/-- `S = 1`: no scaling. -/
def ScaleFactor.one : ScaleFactor := ⟨1, by decide⟩

instance : Inhabited ScaleFactor := ⟨.one⟩

/-- A `Parameters.Ratio` as a `Rat`. -/
def ratioValue (r : Parameters.Ratio) : Rat := (r.num : Rat) / (r.den : Rat)

/-- SR8's threshold on the reduced chi-square, `Parameters.sr8Threshold`, is 1. -/
theorem ratioValue_sr8Threshold : ratioValue sr8Threshold = 1 := by
  show ((1 : Nat) : Rat) / ((1 : Nat) : Rat) = 1
  grind

/-- v1's `sr8_scale_factor`: `S` for the standing M records of one quantity (TPS 4.4
SR8). Fewer than two records: 1. A record whose uncertainty is not positive: `none`, as
v1 raised. Otherwise the records with `u_i < 3 √N ū` (ū the mean uncertainty) are kept,
decided as `u_i² < 9 N ū²` since both sides are positive; fewer than two kept: 1. Over the
kept records, with weights `w_i = 1 / u_i²`, the weighted mean `x̄`, `χ² = Σ (x_i - x̄)² w_i`
and the reduced `χ² / (n - 1)`; `S²` is the reduced chi-square when it is above 1, and 1
otherwise. Exact: v1's operation order (`tpc_strike` 0.1.1, its SR8 order corpus) does
not arise. -/
def sr8ScaleFactor (ms : List Measurement) : Option ScaleFactor :=
  if ms.length < sr8MinGroup then some .one
  else if ms.any (·.uncertainty ≤ 0) then none
  else
    let n : Rat := ms.length
    let uMean := sumBy (·.uncertainty) ms / n
    let f : Rat := sr8OutlierFactor
    let kept := ms.filter fun m =>
      decide (m.uncertainty * m.uncertainty < f * f * n * (uMean * uMean))
    if kept.length < sr8MinGroup then some .one
    else
      let w (m : Measurement) : Rat := 1 / (m.uncertainty * m.uncertainty)
      let xBar := sumBy (fun m => m.value * w m) kept / sumBy w kept
      let chi2 := sumBy (fun m => (m.value - xBar) * (m.value - xBar) * w m) kept
      let reduced := chi2 / ((kept.length : Rat) - 1)
      if h : ratioValue sr8Threshold < reduced then
        some ⟨reduced, Rat.le_of_lt (ratioValue_sr8Threshold ▸ h)⟩
      else some .one

/-- Fewer than two records are never scaled. -/
theorem sr8ScaleFactor_short {ms : List Measurement} (h : ms.length < 2) :
    (sr8ScaleFactor ms).map (·.square) = some 1 := by
  simp [sr8ScaleFactor, Parameters.sr8MinGroup, h, ScaleFactor.one]

/-- `S` correctly rounded to `p` significant digits, as `(m, e)` with value `m · 10^e`. -/
def ScaleFactor.digits (S : ScaleFactor) (p : Nat) : Nat × Int := rootDigits S.square p

/-! ## SR3: the M-M and L-M tests -/

/-- v1's `mm_contradicts`, SR3's M-M test after SR8's scaling:
`|x1 - x2| > k · √((S u1)² + (S u2)²)`. The caller has brought both values to one unit of
one quantity (the units item). -/
def mmContradicts (x1 u1 x2 u2 k : Rat) (S : ScaleFactor := .one) : Bool :=
  exceedsBound ((x1 - x2) * (x1 - x2)) k (S.square * (u1 * u1 + u2 * u2))

/-- v1's `lm_contradicts`, SR3's L-M test: the M value fails the M-M test against the L
record's derived value, which carries no uncertainty: `|x_M - x_L| > k · S · u_M`. -/
def lmContradicts (xL xM uM k : Rat) (S : ScaleFactor := .one) : Bool :=
  exceedsBound ((xM - xL) * (xM - xL)) (k * uM) S.square

/-- The M-M test is symmetric in its two measurements. -/
theorem mmContradicts_symm (x1 u1 x2 u2 k : Rat) (S : ScaleFactor) :
    mmContradicts x1 u1 x2 u2 k S = mmContradicts x2 u2 x1 u1 k S := by
  unfold mmContradicts
  rw [show (x1 - x2) * (x1 - x2) = (x2 - x1) * (x2 - x1) by grind,
    show u1 * u1 + u2 * u2 = u2 * u2 + u1 * u1 by grind]

/-- SR8's scaling never creates an M-M contradiction: one that survives `S` is one
without it ("a contradiction that does not survive S is not a contradiction"). -/
theorem mmContradicts_unscaled {x1 u1 x2 u2 k : Rat} {S : ScaleFactor}
    (h : mmContradicts x1 u1 x2 u2 k S = true) : mmContradicts x1 u1 x2 u2 k .one = true := by
  unfold mmContradicts at *
  have hV : 0 ≤ u1 * u1 + u2 * u2 := by
    have := mul_self_nonneg u1; have := mul_self_nonneg u2; grind
  have hS := S.one_le_square
  refine exceedsBound_of_le ?_ ?_ h
  · show 1 * _ ≤ _
    have := Rat.mul_le_mul_of_nonneg_right hS hV
    grind
  · intro hw
    show 0 < 1 * _
    refine Rat.not_le.mp fun hle => ?_
    have h0 : u1 * u1 + u2 * u2 = 0 := by grind
    rw [h0] at hw
    grind

/-- SR8's scaling never creates an L-M contradiction. -/
theorem lmContradicts_unscaled {xL xM uM k : Rat} {S : ScaleFactor}
    (h : lmContradicts xL xM uM k S = true) : lmContradicts xL xM uM k .one = true := by
  unfold lmContradicts at *
  have hS := S.one_le_square
  exact exceedsBound_of_le hS (fun _ => by decide) h

/-! ## SR4's closure, read as reachability

`assumptionClosure` walks a stack of identifiers. Read as reachability through CITES, the
walk is exact. It adds only the ASSUMPTIONS of records reachable from where it starts
(`closureWalk_sound`). When it returns, it has added every reachable record's
(`closureWalk_complete`). With `closureFuel` it returns `none` only on reaching an identifier
no record carries (`assumptionClosure_none`), so the fuel never runs out. Hence SR4's
monotonicity (`aOfR_mono`): a record with the same CITES as another and every one of its
ASSUMPTIONS has an `a` at least as large, among the same records. SR9 C2 rests on it.
Nothing here changes what the walk computes. -/

/-- The records reachable from `stack` through CITES, never through an identifier in
`seen`: an identifier of the stack, or one that a reachable record CITES. -/
inductive Reach (records : Records) (seen : List String) (stack : List String) : String → Prop
  | base {x : String} : x ∈ stack → x ∉ seen → Reach records seen stack x
  | step {x y : String} {ry : StrikeRecord} : Reach records seen stack y →
      records.lookup y = some ry → x ∈ ry.cites → x ∉ seen → Reach records seen stack x

/-- Nothing is reachable from an empty stack. -/
theorem Reach.nil {records : Records} {seen : List String} {x : String}
    (h : Reach records seen [] x) : False := by
  induction h with
  | base hm _ => simp at hm
  | step _ _ _ _ ih => exact ih

/-- A larger stack reaches more. -/
theorem Reach.mono {records : Records} {seen stack stack' : List String} {x : String}
    (hs : ∀ y ∈ stack, y ∈ stack') (h : Reach records seen stack x) :
    Reach records seen stack' x := by
  induction h with
  | base hm hn => exact .base (hs _ hm) hn
  | step _ hy hx hn ih => exact .step ih hy hx hn

/-- An identifier already seen reaches nothing new. -/
theorem Reach.of_cons_seen {records : Records} {seen stack : List String} {cur x : String}
    (hcur : cur ∈ seen) (h : Reach records seen (cur :: stack) x) : Reach records seen stack x := by
  induction h with
  | @base x hm hn =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact absurd hcur hn
    · exact .base hm hn
  | step _ hy hx hn ih => exact .step ih hy hx hn

/-- What the walk reaches after expanding `cur` was reachable before it. -/
theorem Reach.of_expand {records : Records} {seen stack : List String} {cur x : String}
    {r : StrikeRecord} (hr : records.lookup cur = some r) (hcur : cur ∉ seen)
    (h : Reach records (cur :: seen) (r.cites ++ stack) x) : Reach records seen (cur :: stack) x := by
  induction h with
  | @base x hm hn =>
    have hn' : x ∉ seen := fun h => hn (List.mem_cons_of_mem _ h)
    rcases List.mem_append.mp hm with hm | hm
    · exact .step (.base (List.mem_cons_self ..) hcur) hr hm hn'
    · exact .base (List.mem_cons_of_mem _ hm) hn'
  | step _ hy hx hn ih => exact .step ih hy hx (fun h => hn (List.mem_cons_of_mem _ h))

/-- What was reachable before expanding `cur` is `cur`, or reachable after: a path through
`cur` continues from one of its CITES. -/
theorem Reach.to_expand {records : Records} {seen stack : List String} {cur x : String}
    {r : StrikeRecord} (hr : records.lookup cur = some r) (h : Reach records seen (cur :: stack) x) :
    x = cur ∨ Reach records (cur :: seen) (r.cites ++ stack) x := by
  induction h with
  | @base x hm hn =>
    by_cases hx : x = cur
    · exact .inl hx
    · rcases List.mem_cons.mp hm with h | hm
      · exact absurd h hx
      · refine .inr (.base (List.mem_append_right _ hm) ?_)
        simp only [List.mem_cons, not_or]; exact ⟨hx, hn⟩
  | @step x y ry _ hy hxc hn ih =>
    by_cases hx : x = cur
    · exact .inl hx
    · have hn' : x ∉ cur :: seen := by simp only [List.mem_cons, not_or]; exact ⟨hx, hn⟩
      rcases ih with rfl | ih
      · rw [hr] at hy
        cases hy
        exact .inr (.base (List.mem_append_left _ hxc) hn')
      · exact .inr (.step ih hy hxc hn')

/-- `insertNew` holds what it held and what it was given. -/
theorem mem_insertNew {a : String} : ∀ {acc xs : List String}, a ∈ insertNew acc xs ↔ a ∈ acc ∨ a ∈ xs
  | acc, [] => by simp [insertNew]
  | acc, x :: xs => by
    have ih := mem_insertNew (a := a) (acc := if acc.contains x then acc else x :: acc) (xs := xs)
    simp only [insertNew, List.foldl_cons] at ih ⊢
    rw [ih]
    split
    · rename_i hc
      have hx : x ∈ acc := List.contains_iff_mem.mp hc
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl hx
          · exact .inr h
    · simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h

/-- `insertNew` keeps its identifiers distinct. -/
theorem nodup_insertNew : ∀ {acc xs : List String}, acc.Nodup → (insertNew acc xs).Nodup
  | acc, [], h => h
  | acc, x :: xs, h => by
    simp only [insertNew, List.foldl_cons]
    apply nodup_insertNew
    split
    · exact h
    · rename_i hc
      exact List.nodup_cons.mpr ⟨fun hx => hc (List.contains_iff_mem.mpr hx), h⟩

/-- The walk adds only the ASSUMPTIONS of records reachable from where it starts. -/
theorem closureWalk_sound (records : Records) :
    ∀ (fuel : Nat) (stack seen acc res : List String),
      closureWalk records fuel stack seen acc = some res →
      ∀ a ∈ res, a ∈ acc ∨ ∃ x rx, Reach records seen stack x ∧ records.lookup x = some rx ∧
        a ∈ rx.assumptions
  | _, [], seen, acc, res, h => by
    simp only [closureWalk, Option.some.injEq] at h
    subst h
    exact fun a ha => .inl ha
  | 0, _ :: _, _, _, _, h => by simp [closureWalk] at h
  | fuel + 1, cur :: stack, seen, acc, res, h => by
    simp only [closureWalk] at h
    split at h
    · intro a ha
      rcases closureWalk_sound records fuel stack seen acc res h a ha with h1 | ⟨x, rx, hx, hl, ha⟩
      · exact .inl h1
      · exact .inr ⟨x, rx, hx.mono fun y hy => List.mem_cons_of_mem _ hy, hl, ha⟩
    · rename_i hc
      have hcur : cur ∉ seen := fun h => hc (List.contains_iff_mem.mpr h)
      split at h
      · cases h
      · rename_i r hr
        intro a ha
        rcases closureWalk_sound records fuel _ _ _ res h a ha with h1 | ⟨x, rx, hx, hl, ha'⟩
        · rcases mem_insertNew.mp h1 with h2 | h2
          · exact .inl h2
          · exact .inr ⟨cur, r, .base (List.mem_cons_self ..) hcur, hr, h2⟩
        · exact .inr ⟨x, rx, Reach.of_expand hr hcur hx, hl, ha'⟩

/-- When the walk returns, it holds what it started with and the ASSUMPTIONS of every
reachable record, each of which a record carries. -/
theorem closureWalk_complete (records : Records) :
    ∀ (fuel : Nat) (stack seen acc res : List String),
      closureWalk records fuel stack seen acc = some res →
      (∀ a ∈ acc, a ∈ res) ∧ ∀ x, Reach records seen stack x →
        ∃ rx, records.lookup x = some rx ∧ ∀ a ∈ rx.assumptions, a ∈ res
  | _, [], seen, acc, res, h => by
    simp only [closureWalk, Option.some.injEq] at h
    subst h
    exact ⟨fun a ha => ha, fun x hx => absurd hx.nil id⟩
  | 0, _ :: _, _, _, _, h => by simp [closureWalk] at h
  | fuel + 1, cur :: stack, seen, acc, res, h => by
    simp only [closureWalk] at h
    split at h
    · rename_i hc
      have hcur : cur ∈ seen := List.contains_iff_mem.mp hc
      obtain ⟨h1, h2⟩ := closureWalk_complete records fuel stack seen acc res h
      exact ⟨h1, fun x hx => h2 x (hx.of_cons_seen hcur)⟩
    · split at h
      · cases h
      · rename_i r hr
        obtain ⟨h1, h2⟩ := closureWalk_complete records fuel _ _ _ res h
        refine ⟨fun a ha => h1 a (mem_insertNew.mpr (.inl ha)), fun x hx => ?_⟩
        rcases hx.to_expand hr with rfl | hx
        · exact ⟨r, hr, fun a ha => h1 a (mem_insertNew.mpr (.inr ha))⟩
        · exact h2 x hx

/-- The walk's identifiers are distinct. -/
theorem closureWalk_nodup (records : Records) :
    ∀ (fuel : Nat) (stack seen acc res : List String), acc.Nodup →
      closureWalk records fuel stack seen acc = some res → res.Nodup
  | _, [], seen, acc, res, hn, h => by
    simp only [closureWalk, Option.some.injEq] at h
    subst h; exact hn
  | 0, _ :: _, _, _, _, _, h => by simp [closureWalk] at h
  | fuel + 1, cur :: stack, seen, acc, res, hn, h => by
    simp only [closureWalk] at h
    split at h
    · exact closureWalk_nodup records fuel stack seen acc res hn h
    · split at h
      · cases h
      · exact closureWalk_nodup records fuel _ _ _ res (nodup_insertNew hn) h

/-! ### The fuel never runs out -/

/-- What the walk can still push: each identifier's CITES, counted once (from its first
record, the one `lookup` finds), and only for identifiers not yet seen. -/
def pending (seen : List String) : Records → Nat
  | [] => 0
  | (k, e) :: rest => (if seen.contains k then 0 else e.cites.length) + pending (k :: seen) rest

/-- `pending` reads `seen` only as a set. -/
theorem pending_congr : ∀ {s s' : List String} (l : Records), (∀ x, x ∈ s ↔ x ∈ s') →
    pending s l = pending s' l
  | _, _, [], _ => rfl
  | s, s', (k, e) :: rest, h => by
    have hk : s.contains k = s'.contains k := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      exact h k
    simp only [pending, hk]
    congr 1
    exact pending_congr rest fun x => by simp only [List.mem_cons, h x]

/-- Expanding an identifier not yet seen spends exactly its CITES from `pending`. -/
theorem pending_expand : ∀ {seen : List String} {cur : String} {r : StrikeRecord} (l : Records),
    cur ∉ seen → l.lookup cur = some r → pending (cur :: seen) l + r.cites.length = pending seen l
  | _, _, _, [], _, h => by simp at h
  | seen, cur, r, (k, e) :: rest, hcur, h => by
    simp only [List.lookup] at h
    by_cases hk : cur = k
    · subst hk
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      have hc : seen.contains cur = false := by
        cases hc : seen.contains cur
        · rfl
        · exact absurd (List.contains_iff_mem.mp hc) hcur
      simp only [pending, List.contains_cons, beq_self_eq_true, Bool.true_or, ite_true, hc,
        Bool.false_eq_true, ite_false, Nat.zero_add]
      rw [pending_congr rest (s := cur :: cur :: seen) (s' := cur :: seen) (fun x => by simp)]
      omega
    · have hb : (cur == k) = false := by simp [hk]
      simp only [hb] at h
      have hkc : ((cur :: seen).contains k) = seen.contains k := by
        simp only [List.contains_cons]
        have : (k == cur) = false := by simp [Ne.symm hk]
        simp [this]
      simp only [pending, hkc]
      have ih := pending_expand (seen := k :: seen) rest
        (by simp only [List.mem_cons, not_or]; exact ⟨hk, hcur⟩) h
      rw [pending_congr rest (s := k :: cur :: seen) (s' := cur :: k :: seen)
        (fun x => by
          simp only [List.mem_cons]
          constructor <;> intro h <;> rcases h with h | h | h <;> simp [h])]
      omega

/-- With fuel for everything still on the stack and still pending, the walk returns `none`
only on reaching an identifier no record carries. -/
theorem closureWalk_none (records : Records) :
    ∀ (fuel : Nat) (stack seen acc : List String),
      stack.length + pending seen records ≤ fuel →
      closureWalk records fuel stack seen acc = none →
      ∃ x, Reach records seen stack x ∧ records.lookup x = none
  | _, [], _, _, _, h => by simp [closureWalk] at h
  | 0, _ :: _, _, _, hf, _ => by simp at hf
  | fuel + 1, cur :: stack, seen, acc, hf, h => by
    simp only [closureWalk] at h
    split at h
    · obtain ⟨x, hx, hl⟩ := closureWalk_none records fuel stack seen acc
        (by simp only [List.length_cons] at hf; omega) h
      exact ⟨x, hx.mono fun y hy => List.mem_cons_of_mem _ hy, hl⟩
    · rename_i hc
      have hcur : cur ∉ seen := fun h => hc (List.contains_iff_mem.mpr h)
      split at h
      · rename_i hr
        exact ⟨cur, .base (List.mem_cons_self ..) hcur, hr⟩
      · rename_i r hr
        have hp := pending_expand records hcur hr
        obtain ⟨x, hx, hl⟩ := closureWalk_none records fuel _ _ _
          (by simp only [List.length_append, List.length_cons] at hf ⊢; omega) h
        exact ⟨x, Reach.of_expand hr hcur hx, hl⟩

/-- `pending` never exceeds the CITES of all the records. -/
theorem pending_le : ∀ (seen : List String) (l : Records),
    pending seen l ≤ l.foldl (fun n p => n + p.2.cites.length) 0
  | _, [] => by simp [pending]
  | seen, (k, e) :: rest => by
    have h1 := pending_le (k :: seen) rest
    have h2 : ∀ (m : Nat) (l : Records), l.foldl (fun n p => n + p.2.cites.length) m =
        m + l.foldl (fun n p => n + p.2.cites.length) 0 := by
      intro m l
      induction l generalizing m with
      | nil => simp
      | cons p ps ih => simp only [List.foldl_cons]; rw [ih, ih (0 + _)]; omega
    simp only [pending, List.foldl_cons]
    rw [h2]
    split <;> omega

/-- `assumptionClosure` is `none` only when the walk reaches an identifier no record
carries: `closureFuel` is enough fuel. -/
theorem assumptionClosure_none {rid : String} {records : Records}
    (h : assumptionClosure rid records = none) :
    ∃ x, Reach records [] [rid] x ∧ records.lookup x = none := by
  unfold assumptionClosure at h
  cases hw : closureWalk records (closureFuel records) [rid] [] [] with
  | some c => simp [hw] at h
  | none =>
    refine closureWalk_none records _ [rid] [] [] ?_ hw
    have h1 := pending_le [] records
    have h2 : closureFuel records = 1 + records.foldl (fun n p => n + p.2.cites.length) 0 := by
      unfold closureFuel
      generalize records = l
      suffices ∀ m, l.foldl (fun n p => n + p.2.cites.length) m =
          m + l.foldl (fun n p => n + p.2.cites.length) 0 from this 1
      intro m
      induction l generalizing m with
      | nil => simp
      | cons p ps ih => simp only [List.foldl_cons]; rw [ih, ih (0 + _)]; omega
    simp only [List.length_cons, List.length_nil]
    omega

/-! ### SR4's monotonicity -/

/-- From two records with the same CITES, the same identifiers are reachable, the start
excepted. -/
theorem Reach.swap_start {records : Records} {rid rid' x : String} {r r' : StrikeRecord}
    (hr : records.lookup rid = some r) (hr' : records.lookup rid' = some r')
    (hc : r'.cites = r.cites) (h : Reach records [] [rid] x) :
    x = rid ∨ Reach records [] [rid'] x := by
  induction h with
  | base hm _ => exact .inl (List.mem_singleton.mp hm)
  | @step x y ry _ hy hx hn ih =>
    rcases ih with rfl | ih
    · rw [hr] at hy
      cases hy
      exact .inr (.step (.base (List.mem_singleton_self _) (List.not_mem_nil)) hr' (hc ▸ hx) hn)
    · exact .inr (.step ih hy hx hn)

/-- Distinct identifiers held by another list are no more than it holds. -/
theorem length_le_of_subset : ∀ {l1 l2 : List String}, l1.Nodup → (∀ a ∈ l1, a ∈ l2) →
    l1.length ≤ l2.length
  | [], _, _, _ => by simp
  | a :: t, l2, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ l2 := hs a (List.mem_cons_self ..)
    have ih := length_le_of_subset (l2 := l2.erase a) hn.2 fun b hb => by
      have hba : b ≠ a := fun h => hn.1 (h ▸ hb)
      exact (List.mem_erase_of_ne hba).mpr (hs b (List.mem_cons_of_mem _ hb))
    rw [List.length_erase_of_mem ha] at ih
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- **SR4's monotonicity.** Among the same records, a record `rid'` with the same CITES as
`rid` and every one of its ASSUMPTIONS has `a(rid') ≥ a(rid)`, and has one whenever `rid`
has. Adding an assumption to a record never lowers its `a`. -/
theorem aOfR_mono {records : Records} {rid rid' : String} {r r' : StrikeRecord}
    (hr : records.lookup rid = some r) (hr' : records.lookup rid' = some r')
    (hc : r'.cites = r.cites) (ha : ∀ a ∈ r.assumptions, a ∈ r'.assumptions)
    (assembly : List String) {n : Nat} (h : aOfR rid records assembly = some n) :
    ∃ n', aOfR rid' records assembly = some n' ∧ n ≤ n' := by
  unfold aOfR assumptionClosure at h
  cases hw : closureWalk records (closureFuel records) [rid] [] [] with
  | none => simp [hw] at h
  | some c0 =>
    simp only [hw, Option.map_some, Option.some.injEq] at h
    have hc0 := closureWalk_complete records _ _ _ _ c0 hw
    cases hw' : closureWalk records (closureFuel records) [rid'] [] [] with
    | none =>
      obtain ⟨x, hx, hl⟩ := assumptionClosure_none (rid := rid') (records := records)
        (by simp [assumptionClosure, hw'])
      rcases hx.swap_start hr' hr hc.symm with rfl | hx
      · rw [hr'] at hl; cases hl
      · obtain ⟨rx, hrx, _⟩ := hc0.2 x hx
        rw [hrx] at hl; cases hl
    | some c1 =>
      have hc1 := closureWalk_complete records _ _ _ _ c1 hw'
      refine ⟨((c1.mergeSort idLe).filter (!assembly.contains ·)).length, ?_, ?_⟩
      · simp [aOfR, assumptionClosure, hw']
      · subst h
        have hsub : ∀ a ∈ c0, a ∈ c1 := by
          intro a hac
          rcases closureWalk_sound records _ _ _ _ c0 hw a hac with h0 | ⟨x, rx, hx, hl, hax⟩
          · simp at h0
          · rcases hx.swap_start hr hr' hc with rfl | hx
            · rw [hr] at hl
              cases hl
              obtain ⟨rx', hrx', hall⟩ := hc1.2 _ (.base (List.mem_singleton_self _) List.not_mem_nil)
              rw [hr'] at hrx'
              cases hrx'
              exact hall a (ha a hax)
            · obtain ⟨rx', hrx', hall⟩ := hc1.2 x hx
              rw [hl] at hrx'
              cases hrx'
              exact hall a hax
        have hn0 : c0.Nodup := closureWalk_nodup records _ _ _ _ c0 List.nodup_nil hw
        rw [((List.mergeSort_perm c0 idLe).filter _).length_eq,
          ((List.mergeSort_perm c1 idLe).filter _).length_eq]
        refine length_le_of_subset (hn0.sublist (List.filter_sublist)) fun a hm => ?_
        rw [List.mem_filter] at hm ⊢
        exact ⟨hsub a hm.1, hm.2⟩

end Principia.Strike
