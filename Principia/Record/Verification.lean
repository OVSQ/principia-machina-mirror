import Principia.Form.Arithmetic
import Principia.Record.Bounded
import Principia.UnitsStrike

/-!
# The verification's difference, its uncertainty and its zeta, exactly

v1's `verification_difference` (tpm_record_functions 0.3.0, 14.2) computed, from the
TARGET's normalized measurement `(x_t, u_t)` and the EXTERNAL one `(x_e, u_e)`, in IEEE
doubles: VALUE = x_t - x_e, U = √(u_t² + u_e²), REC-95 when U = 0, ZETA = VALUE / U, each
written in canon's twelve-digit form, and the contradiction test `mm_contradicts(x_t, u_t,
x_e, u_e, k, S = 1)`. Here the numbers are exact (the Calculator's choice of exact values) and each text is
the exact value correctly rounded once to twelve significant digits, ties to even.

**One power of π** (every v1 case). A normalized value is `q × π^p`, and a measurement's
value and uncertainty share their unit's power of π. With it divided out, VALUE is
`(a1 - a2) π^p` and U is `√(b1² + b2²) π^p` for the coefficients `a1, b1, a2, b2`; the
rationals `d = a1 - a2` and `s = b1² + b2²` are formed within the bound on an exact value's
size (65,536 bits; `Principia.ValueBound`), and refused past it, "exact value
too large" (`sameParts`). U is 0 exactly when both uncertainties are (`uZero_iff`). ZETA is
`d / √s`, π cancelling: its square `d² / s` is rational, so its twelve digits are those of an
exact square root (`Exact.sqrtSig`), with VALUE's sign (`zeta_sign`); for `p = 0` so are U's.
The contradiction test is the strike rule's exact M-M test on the coefficients
(`contradicts_eq_mm`), so it is symmetric as that test is (`contradicts_symm`).

**Different powers of π** (a degree against a radian). The three quantities are the
declared forms' numbers (`Principia.Form.Num`): exact where they have an exact form, else
enclosed between bounds from Machin's formula; each text is settled when the bounds at some
precision up to 4096 bits round alike (`Num.twelve?`), the zero test likewise
(`Num.isZero?`), and the contradiction test is `Units.mmCompare`, decided with certainty
since `π^m` is transcendental. What 4096 bits do not settle is owed (`none`); no v1 case
comes near it.
-/

namespace Principia.Record.Verification

open Principia.ValueBound (Bounded)
open Principia.Form (Num)

/-! ## One power of π -/

/-- VALUE's and U²'s coefficients, `a1 - a2` and `b1² + b2²`, each formed within the bound. -/
def core (a1 b1 a2 b2 : Rat) : Bounded (Rat × Rat) := do
  let d ← ValueBound.sub a1 a2
  let s1 ← ValueBound.mul b1 b1
  let s2 ← ValueBound.mul b2 b2
  let s ← ValueBound.add s1 s2
  pure (d, s)

/-- ZETA's square, `d² / s`, formed within the bound. -/
def zetaSquare (d s : Rat) : Bounded Rat := do
  let dd ← ValueBound.mul d d
  ValueBound.div dd s

/-- The verification's numbers over one power of π, within the bound: `none` when U is 0
(REC-95, decided before ZETA is formed), else `(d, s, d² / s)`. -/
def sameParts (a1 b1 a2 b2 : Rat) : Bounded (Option (Rat × Rat × Rat)) := do
  let ds ← core a1 b1 a2 b2
  if ds.2 = 0 then return none
  let z ← zetaSquare ds.1 ds.2
  return some (ds.1, ds.2, z)

/-- The same numbers, unchecked. -/
def plainParts (a1 b1 a2 b2 : Rat) : Option (Rat × Rat × Rat) :=
  let d := a1 - a2
  let s := b1 * b1 + b2 * b2
  if s = 0 then none else some (d, s, d * d / s)

/-- canon's twelve-digit form as a canonical decimal (v1's `canon_decimal(canon(.))`); a
form whose exponent the decimal grammar does not read (five digits) is kept as it is. -/
def canonText (t : String) : String := (Decimal.canon t).getD t

/-- ZETA's sign and magnitude: `none` for zero, else whether it is negative and its
magnitude, `√(d² / s)` in canon's twelve-digit form. -/
def zetaOf (d z : Rat) : Option (Bool × String) :=
  if d = 0 then none else some (decide (d < 0), Exact.printSqrt12 z)

/-- ZETA's text. -/
def zetaText (d z : Rat) : String :=
  match zetaOf d z with
  | none => "0"
  | some (neg, mag) => canonText ((if neg then "-" else "") ++ mag)

/-- U's text for `p = 0`: `√s` to twelve digits, exactly. -/
def uText (s : Rat) : String := canonText (Exact.printSqrt12 s)

/-! ## Different powers of π -/

/-- The three texts from the declared forms' numbers: `none` when the bounds on π do not
settle one of them (owed), `some none` when U is 0 (REC-95), else VALUE's, U's and ZETA's
twelve-digit forms. -/
def numParts (xt ut xe ue : Exact) : Option (Option (String × String × String)) := do
  let d := Num.sub (.exact xt) (.exact xe)
  let s := Num.add (Num.mul (.exact ut) (.exact ut)) (Num.mul (.exact ue) (.exact ue))
  if ← Num.isZero? s then return none
  let u := Num.sqrt s
  let z := Num.div d u
  let vt ← d.twelve?
  let utx ← u.twelve?
  let zt ← z.twelve?
  return some (canonText vt, canonText utx, canonText zt)

/-- The coefficients the numbers over different powers of π are formed from, within the
bound: the values' difference and the uncertainties' squares, as `sameParts` checks them. -/
def numWithin (a1 b1 a2 b2 : Rat) : Bounded Unit := do
  let _ ← ValueBound.sub a1 a2
  let _ ← ValueBound.mul b1 b1
  let _ ← ValueBound.mul b2 b2
  pure ()

/-! ## The contradiction test -/

/-- SR3's M-M test on the two normalized measurements with `S = 1` (v1's
`mm_contradicts(x_t, u_t, x_e, u_e, k, 1.0)`): `none` when 4096 bits of π do not decide it. -/
def contradicts (m1 m2 : Units.Measurement) (k : Rat) : Option Bool :=
  Units.mmCompare m1 m2 k .one

/-! ## PROVED -/

theorem core_ok {a1 b1 a2 b2 d s : Rat} (h : core a1 b1 a2 b2 = .ok (d, s)) :
    d = a1 - a2 ∧ s = b1 * b1 + b2 * b2 := by
  unfold core at h
  obtain ⟨d', hd, h⟩ := Principia.Record.Bounded.bind_ok h
  obtain ⟨s1, h1, h⟩ := Principia.Record.Bounded.bind_ok h
  obtain ⟨s2, h2, h⟩ := Principia.Record.Bounded.bind_ok h
  obtain ⟨s', hs, h⟩ := Principia.Record.Bounded.bind_ok h
  cases h
  rw [ValueBound.sub_ok hd, ValueBound.add_ok hs, ValueBound.mul_ok h1, ValueBound.mul_ok h2]
  exact ⟨rfl, rfl⟩

theorem zetaSquare_ok {d s z : Rat} (h : zetaSquare d s = .ok z) : z = d * d / s := by
  unfold zetaSquare at h
  obtain ⟨dd, hdd, h⟩ := Principia.Record.Bounded.bind_ok h
  rw [ValueBound.div_ok h, ValueBound.mul_ok hdd]

/-- The bounded path, when it answers, answers what the unbounded computation gives. -/
theorem verification_ok {a1 b1 a2 b2 : Rat} {r : Option (Rat × Rat × Rat)}
    (h : sameParts a1 b1 a2 b2 = .ok r) : r = plainParts a1 b1 a2 b2 := by
  unfold sameParts at h
  obtain ⟨⟨d, s⟩, hc, h⟩ := Principia.Record.Bounded.bind_ok h
  obtain ⟨hd, hs⟩ := core_ok hc
  unfold plainParts
  rw [← hd, ← hs]
  by_cases h0 : s = 0
  · simp only [h0, ite_true] at h ⊢
    cases h; rfl
  · simp only [h0, ite_false] at h ⊢
    obtain ⟨z, hz, h⟩ := Principia.Record.Bounded.bind_ok h
    cases h
    rw [zetaSquare_ok hz]

/-- U is 0 exactly when both uncertainties are. -/
theorem uZero_iff (b1 b2 : Rat) : b1 * b1 + b2 * b2 = 0 ↔ b1 = 0 ∧ b2 = 0 := by
  have h1 := Strike.Numeric.mul_self_nonneg b1
  have h2 := Strike.Numeric.mul_self_nonneg b2
  constructor
  · intro h
    have e1 : b1 * b1 = 0 := by grind
    have e2 : b2 * b2 = 0 := by grind
    refine ⟨?_, ?_⟩
    · rcases Rat.mul_eq_zero.mp e1 with h | h <;> exact h
    · rcases Rat.mul_eq_zero.mp e2 with h | h <;> exact h
  · rintro ⟨rfl, rfl⟩
    grind

/-- REC-95 is answered exactly when both uncertainties are 0. -/
theorem plainParts_none_iff (a1 b1 a2 b2 : Rat) :
    plainParts a1 b1 a2 b2 = none ↔ b1 = 0 ∧ b2 = 0 := by
  unfold plainParts
  rw [← uZero_iff]
  by_cases h : b1 * b1 + b2 * b2 = 0 <;> simp [h]

/-- ZETA is 0 exactly when VALUE is, and otherwise has VALUE's sign. -/
theorem zeta_sign (d z : Rat) :
    (zetaOf d z).map (·.1) = if d = 0 then none else some (decide (d < 0)) := by
  unfold zetaOf
  by_cases h : d = 0 <;> simp [h]

/-- With one power of π the contradiction test is the strike rule's exact M-M test on the
coefficients. -/
theorem contradicts_eq_mm {m1 m2 : Units.Measurement} (k : Rat)
    (h : m1.piPower = m2.piPower) :
    contradicts m1 m2 k =
      some (Strike.mmContradicts m1.x.coef m1.u.coef m2.x.coef m2.u.coef k .one) := by
  unfold contradicts Units.mmCompare Units.Measurement.coefs
  simp [h]

/-- With one power of π the contradiction test is symmetric in its two measurements, as the
strike rule's is (`Strike.mmContradicts_symm`). -/
theorem contradicts_symm {m1 m2 : Units.Measurement} (k : Rat)
    (h : m1.piPower = m2.piPower) : contradicts m1 m2 k = contradicts m2 m1 k := by
  rw [contradicts_eq_mm k h, contradicts_eq_mm k h.symm, Strike.mmContradicts_symm]

end Principia.Record.Verification
