import Principia.Beta.Arguments
import Principia.Beta.Enclosure

/-!
# The Beta layer

v1's `tpc_beta` 0.1.0, the arithmetic the reliability score's evidence layer and the user
score share: CR11 "E the mean of Beta(a0 + F, b0 + A) with the 95 per cent equal-tailed
interval"; TPS 5.14 CR12 as amended, the same for the user score. The text fixes the
distribution, its mean and the interval's coverage and shape; v1 took the numerical method
by delegation (BT-1 to BT-4) and computed in IEEE doubles.

Every number is the exact value, the Declarer's choice of exact values. The mean is a rational;
`ln Γ`, `I_x(a, b)` and the quantile are the real numbers the text names, each given by
bounds narrowed until its twelve digits are settled (`Principia.Beta.Enclosure`), where v1
gave the result of its method in doubles: the Lanczos approximation (BT-1), Numerical
Recipes' continued fraction (BT-2), 100 halvings (BT-3). Where v1's printed value differs
from the exact one, the case is a recorded divergence with its cause
(the divergence list of the Beta corpus).

The functions, with v1's argument checks and refusal words, in v1's order:

* `beta_mean(a, b)`: `a / (a + b)`, `a, b > 0` (`shape`).
* `beta_interval(a, b, level)`: the quantiles at `(1 - level) / 2` and `1 - (1 - level) / 2`,
  `0 < level < 1` (`level`).
* `betainc(a, b, x)`: `I_x(a, b)`, `0 ≤ x ≤ 1` (`x`).
* `betainc_inv(a, b, p)`: the `x` with `I_x(a, b) = p`, `0 ≤ p ≤ 1` (`p`); 0 at 0, 1 at 1.
* `lgamma(x)`: `ln Γ(x)`, `x > 0` (`lgamma`).
* `canon(x)`: a number's twelve-digit form (`canon`).

Corpus: the Beta corpus (99 cases), run by the Beta test runner.
-/

namespace Principia.Beta

open Principia.Canonical

/-! ## The functions on numbers -/

/-- The mean of `Beta(a, b)`. -/
def mean (a b : Rat) : Rat := a / (a + b)

/-- The equal-tailed interval at `level`: the quantiles at `(1 - level) / 2` and at
`1 - (1 - level) / 2`. The shapes are given exactly or by bounds. -/
def interval (a b : Quantity) (level : Rat) : Quantity × Quantity :=
  let alpha := (1 - level) / 2
  (quantile a b alpha, quantile a b (1 - alpha))

/-! ## v1's functions, with its argument checks -/

/-- A number, or v1's word. -/
def num (v : Canonical.Value) (word : String) : Except String Rat := need (numberOf? v) word

/-- The arguments of v1 `beta_mean`: two shapes, both positive. -/
def betaMeanArgs (a b : Canonical.Value) : Except String (Rat × Rat) := do
  let a ← num a "shape"
  let b ← num b "shape"
  check (0 < a && 0 < b) "shape"
  return (a, b)

/-- v1 `beta_mean`. -/
def betaMean (a b : Canonical.Value) : Except String Rat := do
  let (a, b) ← betaMeanArgs a b
  return mean a b

/-- The arguments of v1 `beta_interval`, checked in v1's order: the shapes, positive, and
the level, strictly between 0 and 1. -/
def betaIntervalArgs (a b level : Canonical.Value) : Except String (Rat × Rat × Rat) := do
  let a ← num a "shape"
  let b ← num b "shape"
  let l ← num level "level"
  check (0 < a && 0 < b) "shape"
  check (0 < l && l < 1) "level"
  return (a, b, l)

/-- v1 `beta_interval`. -/
def betaInterval (a b level : Canonical.Value) : Except String (Quantity × Quantity) := do
  let (a, b, l) ← betaIntervalArgs a b level
  return interval (.exact a) (.exact b) l

/-- v1 `betainc`. -/
def betaincOf (a b x : Canonical.Value) : Except String Quantity := do
  let a ← num a "shape"
  let b ← num b "shape"
  let x ← num x "x"
  check (0 < a && 0 < b) "shape"
  check (0 ≤ x && x ≤ 1) "x"
  return betainc a b x

/-- v1 `betainc_inv`. -/
def betaincInv (a b p : Canonical.Value) : Except String Quantity := do
  let a ← num a "shape"
  let b ← num b "shape"
  let p ← num p "p"
  check (0 < a && 0 < b) "shape"
  check (0 ≤ p && p ≤ 1) "p"
  return quantile (.exact a) (.exact b) p

/-- v1 `lgamma`. -/
def lgammaOf (x : Canonical.Value) : Except String Quantity := do
  let x ← num x "lgamma"
  check (0 < x) "lgamma"
  return lgamma x

/-- v1 `canon` of a number argument: the number itself, exactly. -/
def canonOf (x : Canonical.Value) : Except String Rat := num x "canon"

/-! ## What Lean proves: the mean stays in its range and moves as the text says

The mean of `Beta(a, b)` lies strictly between 0 and 1, rises with `a` (the evidence FOR)
and falls with `b` (the evidence AGAINST): exactly, on every rational, where v1's doubles
could tie two different means. -/

theorem mean_eq_one_sub {a b : Rat} (h : 0 < a + b) : mean a b = 1 - b / (a + b) := by
  unfold mean
  have : a + b ≠ 0 := Rat.ne_of_gt h
  grind

theorem div_lt_div_of_lt_den {b c d : Rat} (hb : 0 < b) (hc : 0 < c) (h : c < d) :
    b / d < b / c := by
  have hd : 0 < d := by grind
  rw [Rat.lt_div_iff hc]
  have hpos : 0 < b / d := by rw [Rat.lt_div_iff hd]; grind
  have := Rat.mul_lt_mul_of_pos_left h hpos
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)] at this
  exact this

/-- The mean lies strictly between 0 and 1. -/
theorem mean_pos_lt_one {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < mean a b ∧ mean a b < 1 := by
  have h : 0 < a + b := by grind
  unfold mean
  constructor
  · rw [Rat.lt_div_iff h]; grind
  · rw [Rat.div_lt_iff h]; grind

/-- More evidence FOR raises the mean. -/
theorem mean_lt_of_lt_left {a a' b : Rat} (ha : 0 < a) (hb : 0 < b) (h : a < a') :
    mean a b < mean a' b := by
  have h1 : 0 < a + b := by grind
  have h2 : 0 < a' + b := by grind
  rw [mean_eq_one_sub h1, mean_eq_one_sub h2]
  have := div_lt_div_of_lt_den hb h1 (show a + b < a' + b by grind)
  grind

/-- More evidence AGAINST lowers the mean. -/
theorem mean_lt_of_lt_right {a b b' : Rat} (ha : 0 < a) (hb : 0 < b) (h : b < b') :
    mean a b' < mean a b := by
  have h1 : 0 < a + b := by grind
  unfold mean
  exact div_lt_div_of_lt_den ha h1 (show a + b < a + b' by grind)

end Principia.Beta
