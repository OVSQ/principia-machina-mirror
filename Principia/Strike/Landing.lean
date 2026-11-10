import Principia.Strike.Conditions
import Principia.Units.Bounded
import Principia.Decimal

/-!
# The strike screen at landing

Custos lands a batch only when the strike rule would strike nothing it touches. The strike
itself (SR5's order, the withdrawal, the cascade, the audit blocks) is not written at
landing yet, so the screen answers which pairs it would have to strike, and a batch with
any is refused whole.

`screen records tfk incoming`: `records` is the register as it would stand, the batch
appended; `incoming` the batch's identifiers. A record is `reached` by the batch when it is
in the batch or in the closure of a batch record's CITES and ASSUMPTIONS over the register
(a citation of a record the strike refutes is refused, SR2, and the cascade strikes what
cites it). For each QUANTITY of a reached RESULT, SR3's comparison set (`comparisonSet`)
is formed over the register, the batch's records counted as standing; each pair of mode
TEST of which a reached record is a member is tested by SR3's two mechanical tests after
normalization (`mm_contradicts_units`, `lm_contradicts_units`), with the Criteria Set's `K`
and SR8's scale factor taken as 1. A pair of mode INSPECT (the entry's DOF not FIXed and
the AT empty) is cleared without a test: it is listed for row 21's inspection, outside SR3's
mechanical scope, and the strike rule never strikes it mechanically; so is a pair of mode
CONVENTION (equal CONDITIONS but for a point's KIND: the row-43 audit block). A tested pair
is held:

* `CONTRADICTS` where the test finds the contradiction;
* `UNDECIDED` where the test cannot clear it: `K` absent or not a positive decimal, a
  VALUE, U_C or UNIT that is missing, longer than `maxFieldChars`, does not normalize, or
  crosses the bound on an exact value, or a sign the bounds on π do not settle.

A tested pair is cleared only by the test answering no contradiction, or CONVENTION (units of
different KIND: an audit block, never a strike) (`verdict_eq_none`). Taking `S` as 1 holds
every pair a scaled test would find (`Principia.Strike.mmContradicts_unscaled`): SR8 only
ever clears. Holding more pairs than the strike would strike is a completeness defect; the
screen never clears a pair the test does not clear: where it answers, every TEST pair of a
compared quantity's comparison set that a batch record reaches and that the test does not
clear is in its answer (`screen_holds`), every reached RESULT's QUANTITY is compared
(`mem_quantitiesOf`) and every batch record is reached (`mem_reachOf_self`).

Each held pair is answered `[id1, id2, word, via]`, `via` the first batch record that
reaches a member of the pair.
-/

namespace Principia.Strike.Landing

open Principia.Strike (Rec field fieldIs strMembers keyedOf comparisonSet CompareMode
  Answer refuseBad strs)
open Principia.Units (Arg Outcome)

/-- The most characters of a VALUE, a U_C or a UNIT the screen tests (the Calculator's
bound on a UNIT); a pair with a longer one is held UNDECIDED. -/
def maxFieldChars : Nat := 1024

/-- The most quantities one screen compares: each is a comparison set over the register. -/
def maxQuantities : Nat := 8

/-- Why the screen holds a pair. -/
inductive Hold where
  /-- SR3's test finds the pair in contradiction. -/
  | contradicts
  /-- SR3's test cannot clear the pair. -/
  | undecided
  deriving DecidableEq, Repr

/-- The word of a hold. -/
def Hold.word : Hold → String
  | .contradicts => "CONTRADICTS"
  | .undecided => "UNDECIDED"

/-- A pair held: its two records, why, and the batch record that reaches it. -/
structure Held where
  a : String
  b : String
  hold : Hold
  via : String
  deriving DecidableEq, Repr

/-- A held pair as the answer writes it, `[id1, id2, word, via]`. -/
def Held.toValue (h : Held) : Canonical.Value := strs [h.a, h.b, h.hold.word, h.via]

/-- v1's `status_word`: HELD or REFUTED where the STATUS says so, else the GRADE. -/
def wordOf (r : Rec) : Option String :=
  let grade : Option String := match field r "GRADE" with
    | some (.str g) => some g
    | _ => none
  match field r "STATUS" with
  | some (.str s) => if s == "HELD" || s == "REFUTED" then some s else grade
  | _ => grade

/-- The status words SR3 reads: each record's, a batch record's PROVISIONAL (it would
stand once landed). -/
def wordsOf (keyed : List (String × Rec)) (incoming : List String) : Canonical.Value :=
  .obj (keyed.filterMap fun (i, r) =>
    if incoming.contains i then some (i, .str "PROVISIONAL")
    else (wordOf r).map fun w => (i, .str w))

/-- The identifiers a record names: its CITES and its ASSUMPTIONS. -/
def refsOf (r : Rec) : List String := strMembers (field r "CITES") ++ strMembers (field r "ASSUMPTIONS")

/-- The walk of what a record reaches. Fuel spent with identifiers still to visit answers
every identifier of the register besides: never fewer than it reaches. -/
def reachWalk (keyed : List (String × Rec)) : Nat → List String → List String → List String
  | 0, todo, seen => seen ++ todo ++ keyed.map (·.1)
  | _ + 1, [], seen => seen
  | n + 1, x :: todo, seen =>
    if seen.contains x then reachWalk keyed n todo seen
    else
      let next := match keyed.lookup x with
        | some r => refsOf r
        | none => []
      reachWalk keyed n (next ++ todo) (seen ++ [x])

/-- Enough fuel for the walk: one step per identifier named, and one to start. -/
def reachFuel (keyed : List (String × Rec)) : Nat :=
  2 + (keyed.map fun (_, r) => (refsOf r).length).sum

/-- What the record `i` reaches: itself and the closure of its CITES and ASSUMPTIONS. -/
def reachOf (keyed : List (String × Rec)) (i : String) : List String :=
  reachWalk keyed (reachFuel keyed) [i] []

/-- The QUANTITY of each reached RESULT, each once, in order of first appearance. -/
def quantitiesOf (keyed : List (String × Rec)) (reached : List String) : List String :=
  reached.foldl (fun acc i =>
    match keyed.lookup i with
    | some r =>
      match field r "QUANTITY" with
      | some (.str q) => if fieldIs r "CLASS" "RESULT" && !acc.contains q then acc ++ [q] else acc
      | _ => acc
    | none => acc) []

/-- The Criteria Set's `K`, a positive decimal; `none` otherwise. -/
def kOf (tfk : Canonical.Value) : Option Rat :=
  match tfk with
  | .obj z =>
    match z.lookup "TMS" with
    | some (.obj tms) =>
      match tms.lookup "PARAMETERS" with
      | some (.obj pm) =>
        match pm.lookup "K" with
        | some (.str k) => (Decimal.value k).filter (0 < ·)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- A record's string member as the units functions take it; `none` when it is longer than
`maxFieldChars`. -/
def textArg (r : Rec) (k : String) : Option Arg :=
  match field r k with
  | some (.str s) => if maxFieldChars < s.length then none else some (some s)
  | _ => some none

/-- The hold SR3's test leaves on a pair: none where it clears it. -/
def verdict : Principia.ValueBound.Bounded (Outcome Bool) → Option Hold
  | .ok (.ok false) => none
  | .ok (.convention _) => none
  | .ok (.ok true) => some .contradicts
  | _ => some .undecided

/-- SR3's test of a pair: M-M, or L-M with the L record's VALUE taken exact; the hold it
leaves. A pair whose records or `K` cannot be read is held UNDECIDED. -/
def pairHold (keyed : List (String × Rec)) (k : Option Rat) (a b : String) : Option Hold :=
  match k, keyed.lookup a, keyed.lookup b with
  | some k, some ra, some rb =>
    match textArg ra "VALUE", textArg ra "U_C", textArg ra "UNIT",
        textArg rb "VALUE", textArg rb "U_C", textArg rb "UNIT" with
    | some xa, some ua, some unitA, some xb, some ub, some unitB =>
      verdict (
        if fieldIs ra "REGIME" "L" then
          Principia.Units.Bounded.lmContradictsUnitsArg xa unitA xb ub unitB k
        else if fieldIs rb "REGIME" "L" then
          Principia.Units.Bounded.lmContradictsUnitsArg xb unitB xa ua unitA k
        else Principia.Units.Bounded.mmContradictsUnitsArg xa ua unitA xb ub unitB k)
    | _, _, _, _, _, _ => some .undecided
  | _, _, _ => some .undecided

/-- The first batch record that reaches `a` or `b`. -/
def viaOf (reaches : List (String × List String)) (a b : String) : Option String :=
  (reaches.find? fun (_, r) => r.contains a || r.contains b).map (·.1)

/-- The pairs of one comparison set the screen holds: mode TEST, reached, not cleared. -/
def heldOf (keyed : List (String × Rec)) (k : Option Rat) (reaches : List (String × List String))
    (pairs : List (String × String × CompareMode)) : List Held :=
  pairs.filterMap fun (a, b, m) =>
    if m != .test then none
    else match viaOf reaches a b with
      | none => none
      | some v => (pairHold keyed k a b).map fun h => ⟨a, b, h, v⟩

/-- Each quantity's comparison set, its held pairs; the first refusal ends it. -/
def screenQuantities (records words tfk : Canonical.Value) (keyed : List (String × Rec))
    (k : Option Rat) (reaches : List (String × List String)) : List String → Answer (List Held)
  | [] => .ok []
  | q :: qs =>
    match comparisonSet records words tfk (.str q) with
    | .refused r => .refused r
    | .owed w => .owed w
    | .ok pairs =>
      match screenQuantities records words tfk keyed k reaches qs with
      | .ok rest => .ok (heldOf keyed k reaches pairs ++ rest)
      | .refused r => .refused r
      | .owed w => .owed w

/-- The batch's reaches and the quantities they name, or `none` when `records` is not a
register. -/
def plan (records : Canonical.Value) (incoming : List String) :
    Option (List (String × Rec) × List (String × List String) × List String) :=
  (keyedOf records).map fun keyed =>
    let reaches := incoming.map fun i => (i, reachOf keyed i)
    (keyed, reaches, quantitiesOf keyed (reaches.flatMap (·.2)))

/-- The screen: the pairs the strike rule would have to strike that the batch reaches.
Refused: REC-50 (not a register), and as `comparison_set` refuses; owed past
`maxQuantities` quantities. -/
def screen (records tfk : Canonical.Value) (incoming : List String) : Answer (List Held) :=
  match plan records incoming with
  | none => refuseBad "records" records "a register"
  | some (keyed, reaches, qs) =>
    if maxQuantities < qs.length then
      .owed s!"the batch reaches more than {maxQuantities} quantities; the strike screen compares at most {maxQuantities}"
    else screenQuantities records (wordsOf keyed incoming) tfk keyed (kOf tfk) reaches qs

/-! ## Theorems -/

/-- A pair is cleared only by SR3's test answering no contradiction, or CONVENTION. -/
theorem verdict_eq_none (o : Principia.ValueBound.Bounded (Outcome Bool)) :
    verdict o = none ↔ o = .ok (.ok false) ∨ ∃ r, o = .ok (.convention r) := by
  constructor
  · intro h
    match o, h with
    | .ok (.ok false), _ => exact .inl rfl
    | .ok (.convention r), _ => exact .inr ⟨r, rfl⟩
  · rintro (rfl | ⟨r, rfl⟩) <;> rfl

/-- A contradiction the test finds is held. -/
theorem verdict_contradicts : verdict (.ok (.ok true)) = some .contradicts := rfl

/-- Without `K` every pair is held. -/
theorem pairHold_no_k (keyed : List (String × Rec)) (a b : String) :
    pairHold keyed none a b = some .undecided := rfl

/-- Every reached TEST pair the test does not clear is held. -/
theorem mem_heldOf {keyed : List (String × Rec)} {k : Option Rat}
    {reaches : List (String × List String)} {pairs : List (String × String × CompareMode)}
    {a b v : String} {h : Hold} (hp : (a, b, CompareMode.test) ∈ pairs)
    (hv : viaOf reaches a b = some v) (hh : pairHold keyed k a b = some h) :
    ⟨a, b, h, v⟩ ∈ heldOf keyed k reaches pairs := by
  unfold heldOf
  rw [List.mem_filterMap]
  exact ⟨(a, b, .test), hp, by simp [hv, hh]⟩

/-- The walk never loses the identifiers it was given: each is seen or answered. -/
theorem reachWalk_keeps (keyed : List (String × Rec)) :
    ∀ (n : Nat) (todo seen : List String) (x : String),
      x ∈ todo ∨ x ∈ seen → x ∈ reachWalk keyed n todo seen
  | 0, todo, seen, x, h => by
    simp only [reachWalk, List.mem_append]
    rcases h with h | h
    · exact .inl (.inr h)
    · exact .inl (.inl h)
  | _ + 1, [], seen, x, h => by
    simp only [reachWalk]
    rcases h with h | h
    · simp at h
    · exact h
  | n + 1, y :: todo, seen, x, h => by
    simp only [reachWalk]
    split
    · next hs =>
      apply reachWalk_keeps keyed n todo seen x
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr (List.contains_iff_mem.mp hs)
        · exact .inl h
      · exact .inr h
    · apply reachWalk_keeps keyed n _ _ x
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr (List.mem_append_right _ (List.mem_singleton_self _))
        · exact .inl (List.mem_append_right _ h)
      · exact .inr (List.mem_append_left _ h)

/-- A batch record reaches itself: an incoming record is always screened. -/
theorem mem_reachOf_self (keyed : List (String × Rec)) (i : String) : i ∈ reachOf keyed i :=
  reachWalk_keeps keyed _ [i] [] i (.inl (List.mem_singleton_self i))

/-- A pair one of whose members a batch record reaches has a `via`. -/
theorem viaOf_isSome {reaches : List (String × List String)} {i a b : String}
    {r : List String} (hi : (i, r) ∈ reaches) (hr : a ∈ r ∨ b ∈ r) :
    (viaOf reaches a b).isSome := by
  unfold viaOf
  rw [Option.isSome_map]
  apply List.find?_isSome.mpr
  refine ⟨(i, r), hi, ?_⟩
  rcases hr with h | h <;> simp [h]

/-- The fold of `quantitiesOf` keeps what it holds. -/
theorem quantitiesOf_fold_keeps (keyed : List (String × Rec)) :
    ∀ (reached acc : List String) (q : String), q ∈ acc →
      q ∈ reached.foldl (fun acc i =>
        match keyed.lookup i with
        | some r =>
          match field r "QUANTITY" with
          | some (.str q) => if fieldIs r "CLASS" "RESULT" && !acc.contains q then acc ++ [q] else acc
          | _ => acc
        | none => acc) acc
  | [], _, _, h => h
  | i :: rest, acc, q, h => by
    simp only [List.foldl_cons]
    apply quantitiesOf_fold_keeps keyed rest
    split
    · split
      · split
        · exact List.mem_append_left _ h
        · exact h
      · exact h
    · exact h

/-- The fold of `quantitiesOf` gathers the QUANTITY of every RESULT it passes. -/
theorem quantitiesOf_fold_mem (keyed : List (String × Rec)) {i q : String} {r : Rec}
    (hr : keyed.lookup i = some r) (hq : field r "QUANTITY" = some (.str q))
    (hc : fieldIs r "CLASS" "RESULT" = true) :
    ∀ (reached acc : List String), i ∈ reached →
      q ∈ reached.foldl (fun acc i =>
        match keyed.lookup i with
        | some r =>
          match field r "QUANTITY" with
          | some (.str q) => if fieldIs r "CLASS" "RESULT" && !acc.contains q then acc ++ [q] else acc
          | _ => acc
        | none => acc) acc
  | [], _, hi => by cases hi
  | j :: rest, acc, hi => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · apply quantitiesOf_fold_keeps keyed rest
      rw [hr]
      simp only [hq, hc, Bool.true_and]
      split
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · next hn =>
        simpa [List.contains_iff_mem] using hn
    · exact quantitiesOf_fold_mem keyed hr hq hc rest _ hi

/-- The QUANTITY of every reached RESULT is compared. -/
theorem mem_quantitiesOf {keyed : List (String × Rec)} {reached : List String} {i q : String}
    {r : Rec} (hi : i ∈ reached) (hr : keyed.lookup i = some r)
    (hq : field r "QUANTITY" = some (.str q)) (hc : fieldIs r "CLASS" "RESULT" = true) :
    q ∈ quantitiesOf keyed reached :=
  quantitiesOf_fold_mem keyed hr hq hc reached [] hi

/-- Every comparison set `screenQuantities` forms, its held pairs are in its answer. -/
theorem heldOf_sub_screenQuantities {records words tfk : Canonical.Value}
    {keyed : List (String × Rec)} {k : Option Rat} {reaches : List (String × List String)}
    {q : String} {pairs : List (String × String × CompareMode)}
    (hc : comparisonSet records words tfk (.str q) = .ok pairs) :
    ∀ (qs : List String) (hs : List Held),
      screenQuantities records words tfk keyed k reaches qs = .ok hs → q ∈ qs →
      ∀ x ∈ heldOf keyed k reaches pairs, x ∈ hs
  | [], _, _, hq => by cases hq
  | q' :: qs, hs, h, hq => by
    intro x hx
    simp only [screenQuantities] at h
    split at h
    · cases h
    · cases h
    · next pairs' hc' =>
      split at h
      · next rest hr =>
        cases h
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [hc] at hc'
          cases hc'
          exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (heldOf_sub_screenQuantities hc qs rest hr hq x hx)
      · cases h
      · cases h

/-- The screen's claim, end to end: where the screen answers, every TEST pair of a compared
quantity's comparison set that a batch record reaches and that SR3's test does not clear is
in its answer. With `mem_quantitiesOf` every reached RESULT's QUANTITY is compared, and with
`mem_reachOf_self` every batch record is reached. -/
theorem screen_holds {records tfk : Canonical.Value} {incoming : List String}
    {keyed : List (String × Rec)} {reaches : List (String × List String)} {qs : List String}
    {hs : List Held} {q a b : String} {pairs : List (String × String × CompareMode)}
    (hplan : plan records incoming = some (keyed, reaches, qs))
    (hscreen : screen records tfk incoming = .ok hs) (hq : q ∈ qs)
    (hc : comparisonSet records (wordsOf keyed incoming) tfk (.str q) = .ok pairs)
    (hp : (a, b, CompareMode.test) ∈ pairs) (hreach : ∃ i r, (i, r) ∈ reaches ∧ (a ∈ r ∨ b ∈ r))
    (hheld : (pairHold keyed (kOf tfk) a b).isSome) :
    ∃ h v, (⟨a, b, h, v⟩ : Held) ∈ hs := by
  obtain ⟨i, r, hi, hr⟩ := hreach
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (viaOf_isSome hi hr)
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hheld
  refine ⟨h, v, ?_⟩
  unfold screen at hscreen
  rw [hplan] at hscreen
  simp only at hscreen
  split at hscreen
  · cases hscreen
  · exact heldOf_sub_screenQuantities hc qs hs hscreen hq _ (mem_heldOf hp hv hh)

end Principia.Strike.Landing
