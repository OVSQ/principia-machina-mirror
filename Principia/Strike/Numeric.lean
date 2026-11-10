/-!
# The strike rule's numbers

Every numeric primitive of the strike rule, in one place: sums, the decision of an
inequality against a square root, and the rounding of a square root to decimal digits. The
rest of `Principia.Strike` and `Principia.Strike.SR9` computes only through these and
`Rat`'s own field operations.

The standing choice is exact values (`Rat`), with any difference from v1's floating point
recorded as a v2 divergence beside its corpus. The Declarer's choice is whether the
Calculator's numbers stay exact or follow IEEE binary64 bit for bit; were it the latter,
this file is where the strike rule would change.

* `exceedsBound` decides `|d| > c · √v` from `d · d`, `c` and `v`, comparing squares, so a
  verdict never takes a root. `exceedsBound_of_root` shows it is the inequality itself
  whenever the root is rational, and `exceedsBound_of_le` that a larger bound never
  creates an excess.
* `rootDigits` gives `√q` correctly rounded to a number of significant digits, for a
  result that the corpora write as a decimal.
-/

namespace Principia.Strike.Numeric

/-- The sum of `f` over `l`, left to right. -/
def sumBy {α : Type} (f : α → Rat) (l : List α) : Rat := l.foldl (fun s a => s + f a) 0

/-- `√q` rounded to `p` significant digits, for `q ≥ 1`: `(m, e)` with value `m · 10^e` and
`m` of `p` digits. The leading digit's exponent `e₀` has `10^(2e₀) ≤ q < 10^(2e₀+2)`; with
`s = p - 1 - e₀`, `m` is `⌊√t⌋` for `t = q · 10^(2s)`, rounded up when `t > (m + ½)²`, that
is `4t > (2m + 1)²`, and a tie to an even `m`, as C's `printf` rounds. -/
def rootDigits (q : Rat) (p : Nat) : Nat × Int :=
  let e₀ : Int := (((Nat.repr q.floor.toNat).length - 1 : Nat) / 2 : Nat)
  let s : Int := (p : Int) - 1 - e₀
  let t : Rat := q * (10 : Rat) ^ (2 * s)
  let m := Nat.sqrt t.floor.toNat
  let c : Rat := 4 * t
  let h : Rat := ((2 * m + 1) * (2 * m + 1) : Nat)
  let r := if h < c ∨ (c = h ∧ m % 2 = 1) then m + 1 else m
  if r = 10 ^ p then (10 ^ (p - 1), -s + 1) else (r, -s)

/-- Whether `|d| > c · √v`, for `v ≥ 0`, decided exactly from `dd = d · d`, `c` and `v`.
For `c > 0` both sides are non-negative and their squares compare as they do; for `c < 0`
and `v > 0` the bound is negative and every `|d|` exceeds it; otherwise the bound is 0 and
`|d|` exceeds it when `d ≠ 0`. -/
def exceedsBound (dd c v : Rat) : Bool :=
  if 0 < c then decide (c * c * v < dd)
  else if c < 0 ∧ 0 < v then true
  else decide (0 < dd)

/-- A square is not negative. -/
theorem mul_self_nonneg (a : Rat) : 0 ≤ a * a := by
  rcases Rat.le_total (a := 0) (b := a) with h | h
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -a := by grind
    have := Rat.mul_nonneg h' h'
    grind

/-- Between non-negative numbers, squares compare as the numbers do. -/
theorem mul_self_lt_mul_self_iff {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * a < b * b ↔ a < b := by
  constructor
  · intro h
    refine Rat.not_le.mp fun hba => ?_
    have h1 : b * b ≤ b * a := Rat.mul_le_mul_of_nonneg_left hba hb
    have h2 : b * a ≤ a * a := Rat.mul_le_mul_of_nonneg_right hba ha
    grind
  · intro h
    have h1 : a * a ≤ a * b := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h) ha
    have h2 : b * a < b * b := Rat.mul_lt_mul_of_pos_left h (by grind)
    grind

/-- When the root is rational, `v = r · r` with `r ≥ 0`, the exact test is SR3's inequality
itself, `|d| > c · r`, for `e = |d|`. -/
theorem exceedsBound_of_root {e c r : Rat} (he : 0 ≤ e) (hr : 0 ≤ r) :
    exceedsBound (e * e) c (r * r) = decide (c * r < e) := by
  unfold exceedsBound
  by_cases hc : 0 < c
  · have hcr : 0 ≤ c * r := Rat.mul_nonneg (Rat.le_of_lt hc) hr
    rw [ite_eq_left hc, show c * c * (r * r) = (c * r) * (c * r) by grind]
    exact decide_eq_decide.mpr (mul_self_lt_mul_self_iff hcr he)
  · rw [ite_eq_right hc]
    by_cases h2 : c < 0 ∧ 0 < r * r
    · rw [ite_eq_left h2]
      have hr' : 0 < r := Rat.not_le.mp fun h => by
        have : r = 0 := by grind
        subst this
        grind
      have : r * c < r * 0 := Rat.mul_lt_mul_of_pos_left h2.1 hr'
      simp only [Bool.true_eq, decide_eq_true_eq]
      grind
    · rw [ite_eq_right h2]
      have hcr : c * r = 0 := by
        by_cases hc0 : c = 0
        · subst hc0; grind
        · have hr0 : r = 0 := by
            refine Classical.byContradiction fun hne => h2 ⟨by grind, ?_⟩
            exact Rat.mul_pos (by grind) (by grind)
          subst hr0; grind
      rw [hcr]
      have := mul_self_lt_mul_self_iff (Rat.le_refl (a := 0)) he
      simp only [show (0 : Rat) * 0 = 0 by grind] at this
      exact decide_eq_decide.mpr this

/-- A bound that grows (`v ≤ w`, `v` positive when `w` is) never creates an excess: what
exceeds the larger bound exceeds the smaller. -/
theorem exceedsBound_of_le {dd c v w : Rat} (hvw : v ≤ w)
    (hpos : 0 < w → 0 < v) (h : exceedsBound dd c w = true) : exceedsBound dd c v = true := by
  unfold exceedsBound at *
  by_cases hc : 0 < c
  · rw [ite_eq_left hc] at h ⊢
    have hcc : 0 ≤ c * c := mul_self_nonneg c
    have : c * c * v ≤ c * c * w := Rat.mul_le_mul_of_nonneg_left hvw hcc
    simp only [decide_eq_true_eq] at h ⊢
    grind
  · rw [ite_eq_right hc] at h ⊢
    by_cases h2 : c < 0 ∧ 0 < w
    · rw [ite_eq_left (And.intro h2.1 (hpos h2.2))]
    · rw [ite_eq_right h2] at h
      split
      · rfl
      · exact h

end Principia.Strike.Numeric
