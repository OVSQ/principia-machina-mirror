import Principia.Units
import Principia.Units.Bounded
import Principia.ValueBound

/-!
# The record functions' numbers within the bound on an exact value

Two of the record functions form numbers from their arguments: a measurement normalized to
coherent SI (a RESULT's value and uncertainty, a verification's, the points of AT, read by
`field_values`, `l_finding_pair` and `verification_difference`), and the sums of squares
`budget_check` compares. Here each value they form is checked against the bound on an exact
value's size before it is formed, from the sizes of what forms it, and refused "exact value
too large" when it could cross the bound. When the checked computations answer, they answer
what the unchecked ones do (`normalizeWithin_ok`, `budgetWithin_ok`).

* A decimal's value is its digits times a power of ten. Its digits make a whole number of
  at least `10^(n-1)`, `n` the digits after leading zeros, and `10^k` holds more than `3k`
  bits; when either must cross the bound the value is refused, otherwise it is formed and
  checked whole. The first refusal can be conservative where a value's digits and a
  negative power of ten cancel.
* A unit's scale, and the products of the value and the uncertainty with it, are the units'
  own normalization within the bound (`Principia.Units.Bounded`): the scale is held in
  lowest terms, so its refusal is exact, and each product is checked from its operands'
  sizes, as every product within the bound is.
* `budget_check`'s whole numbers: each square, power of ten, product and sum is checked
  before it is formed, a product by its operands' bits, a power of ten by its exponent.
-/

namespace Principia.Record.Bounded

open Principia.ValueBound (Bounded tooLarge maxBits bits within)

/-! ## Whole numbers -/

/-- `x * y`, refused when it must hold more than the bound's bits: it holds at least
`bits x + bits y - 1`. Otherwise it is formed, at most one bit past the bound, and checked. -/
def natMul (x y : Nat) : Bounded Nat :=
  if bits x + bits y ≤ maxBits + 1 then
    if bits (x * y) ≤ maxBits then .ok (x * y) else .error tooLarge
  else .error tooLarge

/-- `x + y` of two numbers within the bound, formed (at most one bit past it) and checked. -/
def natAdd (x y : Nat) : Bounded Nat :=
  if bits (x + y) ≤ maxBits then .ok (x + y) else .error tooLarge

/-- `10^k`, refused when `3k` passes the bound's bits (`10^k > 2^(3k)`); otherwise formed and
checked. -/
def powTen (k : Nat) : Bounded Nat :=
  if 3 * k ≤ maxBits then
    if bits (10 ^ k) ≤ maxBits then .ok (10 ^ k) else .error tooLarge
  else .error tooLarge

theorem natMul_ok {x y z : Nat} (h : natMul x y = .ok z) : z = x * y := by
  unfold natMul at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem natAdd_ok {x y z : Nat} (h : natAdd x y = .ok z) : z = x + y := by
  unfold natAdd at h
  split at h
  · cases h; rfl
  · cases h

theorem powTen_ok {k z : Nat} (h : powTen k = .ok z) : z = 10 ^ k := by
  unfold powTen at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem bind_ok {α β : Type} {x : Bounded α} {f : α → Bounded β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-! ## A decimal's value -/

/-- The value `Decimal.value` gives a decimal read as these parts. -/
def partsValue (p : Decimal.Parts) : Rat :=
  let m : Rat := (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat)
  let v := m * Decimal.pow10 (p.ex - p.fp.length)
  if p.neg then -v else v

theorem decimalValue_eq (s : String) :
    Decimal.value s = (Decimal.readParts s.toList).map partsValue := rfl

/-- A decimal's digits after its leading zeros. -/
def sigDigits (p : Decimal.Parts) : Nat := ((p.ip ++ p.fp).dropWhile (· == '0')).length

/-- A decimal's value within the bound, or refused. -/
def decimalWithin (p : Decimal.Parts) : Bounded Rat :=
  if 3 * (sigDigits p - 1) ≤ maxBits ∧ 3 * (p.ex - p.fp.length).natAbs ≤ maxBits then
    ValueBound.ofRat (partsValue p)
  else .error tooLarge

theorem decimalWithin_ok {p : Decimal.Parts} {q : Rat} (h : decimalWithin p = .ok q) :
    q = partsValue p := by
  unfold decimalWithin at h
  split at h
  · exact ValueBound.ofRat_ok h
  · cases h

/-! ## A measurement normalized -/

open Principia.Units (Arg Measurement)

/-- A decimal argument's parts, `none` when it is not a string or not a decimal. -/
def argParts (a : Arg) : Option Decimal.Parts := a.bind fun s => Decimal.readParts s.toList

/-- The value's and the uncertainty's decimals within the bound, where both are decimals:
checked from their digits and exponents before the units' normalization forms them. -/
def decimalsWithin (v unc : Arg) : Bounded Unit :=
  match argParts v, argParts unc with
  | some pv, some pu => do
    let _ ← decimalWithin pv
    let _ ← decimalWithin pu
    pure ()
  | _, _ => pure ()

/-- `normalize_measurement` (`Units.normalizeMeasurementArg`) with every value it forms within
the bound: the decimals first, then the units' own normalization within the bound. -/
def normalizeWithin (v unc u : Arg) : Bounded (Except String Measurement) := do
  decimalsWithin v unc
  Principia.Units.Bounded.normalizeMeasurementArg v unc u

/-- When the checked normalization answers, it answers what `normalize_measurement` does. -/
theorem normalizeWithin_ok {v unc u : Arg} {r : Except String Measurement}
    (h : normalizeWithin v unc u = .ok r) : r = Units.normalizeMeasurementArg v unc u := by
  unfold normalizeWithin at h
  obtain ⟨_, _, h⟩ := bind_ok h
  exact Principia.Units.Bounded.normalizeMeasurementArg_ok h

/-! ## `budget_check`'s sums -/

/-- `budget_check`'s test, unchecked: `U_C`'s digits `mc` at exponent `ec`, each component's
digits `m` at exponent `e` (its square's), every exponent at least `b`: whether
`low 10^(eb-b) ≤ Σ m² 10^(e-b) ≤ high 10^(eb-b)`, `low` and `high` the squares of `U_C` half
a digit below and above, `eb = 2 ec - 2`. -/
def budgetPlain (mc : Nat) (eb b : Int) (terms : List (Nat × Int)) : Bool :=
  let low : Nat := (10 * (mc - 1) + 5) ^ 2
  let high : Nat := (10 * mc + 5) ^ 2
  let total : Nat := (terms.map fun (m, e) => m * m * 10 ^ (e - b).toNat).sum
  let scale : Nat := 10 ^ (eb - b).toNat
  decide (low * scale ≤ total) && decide (total ≤ high * scale)

/-- One component's term `m² 10^(e-b)`, within the bound. -/
def termWithin (b : Int) (t : Nat × Int) : Bounded Nat := do
  let m2 ← natMul t.1 t.1
  natMul m2 (← powTen (t.2 - b).toNat)

/-- The sum of the terms, left to right, each step within the bound. -/
def totalWithin (b : Int) (terms : List (Nat × Int)) : Bounded Nat :=
  terms.foldlM (fun s t => do natAdd s (← termWithin b t)) 0

/-- `budgetPlain`, every whole number it forms within the bound. -/
def budgetWithin (mc : Nat) (eb b : Int) (terms : List (Nat × Int)) : Bounded Bool := do
  let low ← natMul (10 * (mc - 1) + 5) (10 * (mc - 1) + 5)
  let high ← natMul (10 * mc + 5) (10 * mc + 5)
  let total ← totalWithin b terms
  let scale ← powTen (eb - b).toNat
  let lo ← natMul low scale
  let hi ← natMul high scale
  pure (decide (lo ≤ total) && decide (total ≤ hi))

theorem termWithin_ok {b : Int} {t : Nat × Int} {r : Nat} (h : termWithin b t = .ok r) :
    r = t.1 * t.1 * 10 ^ (t.2 - b).toNat := by
  unfold termWithin at h
  obtain ⟨m2, hm2, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
  rw [natMul_ok h, natMul_ok hm2, powTen_ok hp]

theorem totalWithin_go (b : Int) :
    ∀ (terms : List (Nat × Int)) (s0 r : Nat),
      terms.foldlM (fun s t => do natAdd s (← termWithin b t)) s0 = .ok r →
        r = s0 + (terms.map fun (m, e) => m * m * 10 ^ (e - b).toNat).sum
  | [], s0, r, h => by
    simp only [List.foldlM_nil] at h
    cases h; simp
  | t :: ts, s0, r, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨s1, hs1, h⟩ := bind_ok h
    obtain ⟨c, hc, hs1⟩ := bind_ok hs1
    rw [totalWithin_go b ts s1 r h, natAdd_ok hs1, termWithin_ok hc]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem totalWithin_ok {b : Int} {terms : List (Nat × Int)} {r : Nat}
    (h : totalWithin b terms = .ok r) :
    r = (terms.map fun (m, e) => m * m * 10 ^ (e - b).toNat).sum := by
  rw [totalWithin_go b terms 0 r h, Nat.zero_add]

/-- When the checked test answers, it answers what the unchecked one does. -/
theorem budgetWithin_ok {mc : Nat} {eb b : Int} {terms : List (Nat × Int)} {r : Bool}
    (h : budgetWithin mc eb b terms = .ok r) : r = budgetPlain mc eb b terms := by
  unfold budgetWithin at h
  obtain ⟨low, hlow, h⟩ := bind_ok h
  obtain ⟨high, hhigh, h⟩ := bind_ok h
  obtain ⟨total, htotal, h⟩ := bind_ok h
  obtain ⟨scale, hscale, h⟩ := bind_ok h
  obtain ⟨lo, hlo, h⟩ := bind_ok h
  obtain ⟨hi, hhi, h⟩ := bind_ok h
  cases h
  unfold budgetPlain
  rw [natMul_ok hlo, natMul_ok hhi, natMul_ok hlow, natMul_ok hhigh, totalWithin_ok htotal,
    powTen_ok hscale, Nat.pow_two, Nat.pow_two]

/-- A canonical decimal's digits, before any exponent, form a whole number within the bound:
at least `10^(n-1)` for `n` digits, so one whose digits must cross it is refused before they
are read as a number. -/
def digitsFit (c : String) : Bool :=
  let ds := (c.toList.dropWhile (· == '-')).takeWhile (· != 'e')
  3 * (ds.length - 1) ≤ maxBits

end Principia.Record.Bounded
