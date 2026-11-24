import Principia.Exact
import Principia.Canonical

/-!
# The twelve-digit form of an exact number

v1 compared some presented values through `canon`, the twelve-significant-digit form of
a double (tpc_strike `_canon_float`): T3 calls two FIX values of one TARGET equal when
their values in coherent SI have one text. The Calculator's values are exact,
`q × π^k` (`Principia.Exact`), so the text is the exact value's, rounded once
(`Principia.Canonical.ratioText`). For `k = 0` that is direct. For `k ≠ 0` the value is
irrational, never on a rounding boundary, and is bracketed between two rationals by
`Principia.Exact.piInterval`: rounding is monotone, so when both ends give one text the value
gives it too. At the precisions tried a value can still lie too near a boundary for the
ends to agree; the text is then `none`, never a guess.

This file is the one place a number's text enters the fundamental tests (the Declarer's choice of exact values).
-/

namespace Principia.ExactText

/-- The twelve-digit form of a rational. -/
def ratText (q : Rat) : String := Canonical.ratioText (q < 0) q.num.natAbs q.den

/-- `lo × 2^exp` and `hi × 2^exp`, as rationals. -/
def bounds (a : Exact.Interval) : Rat × Rat :=
  ((a.lo : Rat) * (2 : Rat) ^ a.exp, (a.hi : Rat) * (2 : Rat) ^ a.exp)

/-- Bounds of `q × π^k` at `p` bits: π^|k| bracketed, then scaled by `q` or divided
into it, the ends swapped where `q` is negative. -/
def valueBounds (p : Nat) (q : Rat) (k : Int) : Rat × Rat :=
  let (l, h) := bounds (Exact.Interval.pow p (Exact.piInterval p) k.natAbs)
  let (a, b) := if 0 ≤ k then (q * l, q * h) else (q / h, q / l)
  if q < 0 then (b, a) else (a, b)

/-- The precisions tried, in bits. -/
def precisions : List Nat := [64, 128, 256, 512, 1024, 2048]

/-- The twelve-digit form of `q × π^k`, or `none` when the precisions tried do not
decide it. -/
def twelveDigits? (a : Exact) : Option String :=
  if a.pi = 0 then some (ratText a.coef)
  else precisions.findSome? fun p =>
    let (lo, hi) := valueBounds p a.coef a.pi
    if 0 < (Exact.piInterval p).lo && ratText lo == ratText hi then some (ratText lo) else none

/-! ## Properties -/

/-- A value with no power of π is always decided: its text is its rational's. -/
theorem twelveDigits?_of_pi_zero (a : Exact) (h : a.pi = 0) :
    twelveDigits? a = some (ratText a.coef) := by
  simp [twelveDigits?, h]

/-- The precisions are tried in strictly ascending order. -/
theorem precisions_sorted : precisions.Pairwise (· < ·) := by
  decide

/-- Scaling by a power of two keeps an interval's ends in order. -/
theorem bounds_le (a : Exact.Interval) (h : a.lo ≤ a.hi) : (bounds a).1 ≤ (bounds a).2 := by
  have hpos : (0 : Rat) < (2 : Rat) ^ a.exp := Rat.zpow_pos (by decide)
  have hc : ((a.lo : Nat) : Rat) ≤ ((a.hi : Nat) : Rat) := by exact_mod_cast h
  exact Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt hpos)

/-- A negative multiple swaps the ends: the bounds are the non-negative case's, reversed. -/
theorem valueBounds_swap (p : Nat) (q : Rat) (k : Int) (hq : q < 0) :
    valueBounds p q k =
      (let lh := bounds (Exact.Interval.pow p (Exact.piInterval p) k.natAbs)
       if 0 ≤ k then (q * lh.1, q * lh.2) else (q / lh.2, q / lh.1)).swap := by
  unfold valueBounds
  split
  rename_i heq
  simp only [heq, hq, ↓reduceIte]
  split <;> rfl

end Principia.ExactText
