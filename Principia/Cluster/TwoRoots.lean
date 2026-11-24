import Principia.Cluster.Squares

/-!
# Exact numbers with two square roots, and the resolving step over the spacing's square

The resolving step (TPS 5.19.9) gives `out_k = CUSP MAX u + Z sd(k-1, k)` and
`cusp_k = IN MAX u + Z sd(k-1, k)`. Where the month's spacing `u` is kept as its square `u²`
and each SE as its square (`Principia.Cluster.Squares`), `u` and `sd` are roots, and `out_k`
holds two: a `Surd2`, the number `a + c √b + d √e` with `a, c, b, d, e` rational and
`b, e ≥ 0`. A `Surd` holds one.

Its sign is decided by squaring, as `Surd.sign` decides one root: the first two terms are a
`Surd`, and the comparison of the two parts is the sign of a `Surd` again. Its floor is found
as `Surd.floor` finds one: an integer root `Nat.sqrt` of a whole number gives two neighbours,
and the exact sign picks one. Its text `fixed6` is v1's `"%.6f"` as `Surd.fixed6` gives it:
the exact value rounded to six decimals, a tie to the even neighbour, a minus sign on every
negative value (also one that rounds to zero). Nothing is rounded before the text.

`resolvingStepSq` is `resolvingStep` over `u²` and the SEs' squares; each form in spacings,
`out_k / u = CUSP MAX + Z √(sd² / u²)`, has one root and is a `Surd`. `renderResolvingSq` is
v1's text.

The theorems: (i) a `Surd2` with no second term has `Surd.sign` and `Surd.fixed6`
(`sign_ofSurd`, `fixed6_ofSurd`); (ii) one whose first radicand is a rational square `q²`
has the sign and the text of the `Surd` `(a + c q) + d √e` (`sign_sq`, `fixed6_sq`); (iii)
where `u²` and every squared SE are rational squares, `resolvingStepSq` refuses exactly when
`resolvingStep` does, with the same word, and otherwise prints its text
(`resolvingStepSq_agrees`). `fixed6_rounding` checks the rounding at its boundaries with two
roots. `resolvingStep` and its definitions are left as they are; these stand beside them.
-/

namespace Principia.Cluster


/-- The number `a + c √b + d √e`; the functions below read `b` and `e` as non-negative. -/
structure Surd2 where
  /-- The rational part. -/
  a : Rat
  /-- The coefficient of the first root. -/
  c : Rat := 0
  /-- The first radicand, `b ≥ 0`. -/
  b : Rat := 0
  /-- The coefficient of the second root. -/
  d : Rat := 0
  /-- The second radicand, `e ≥ 0`. -/
  e : Rat := 0
  deriving DecidableEq, Repr

namespace Surd2
/-- The first two terms, `a + c √b`, as a `Surd`. -/
def head (x : Surd2) : Surd := ⟨x.a, x.c, x.b⟩
/-- `x - q`. -/
def subRat (x : Surd2) (q : Rat) : Surd2 := ⟨x.a - q, x.c, x.b, x.d, x.e⟩
/-- `k x`. -/
def scale (x : Surd2) (k : Rat) : Surd2 := ⟨k * x.a, k * x.c, x.b, k * x.d, x.e⟩
/-- The sign of `h + d √e`, `h = a + c √b`, as `Surd.sign` decides `a + c √b` with `h` in
the place of `a`: the sign of `h` (a `Surd`) where the second term is absent; otherwise the
common sign where the two agree, and where they differ the sign of the larger, read from the
sign of `h² - d² e = (a² + c² b - d² e) + 2 a c √b`, again a `Surd`. -/
def sign (x : Surd2) : Int :=
  if x.d = 0 ∨ x.e = 0 then x.head.sign
  else
    let s := x.head.sign
    if s = 0 then ratSign x.d
    else if s = ratSign x.d then s
    else
      let w : Surd := ⟨x.a * x.a + x.c * x.c * x.b - x.d * x.d * x.e, 2 * x.a * x.c, x.b⟩
      if 0 < w.sign then s else if w.sign < 0 then ratSign x.d else 0
/-- The floor, as `Surd.floor` finds it with `h = a + c √b` in the place of `a`:
`r = Nat.sqrt ⌊d² e⌋` is `⌊|d| √e⌋`, so the floor is `⌊h ± r⌋` (a `Surd`'s floor) or its
neighbour, and the sign of the difference picks it. -/
def floor (x : Surd2) : Int :=
  if x.d = 0 ∨ x.e = 0 then x.head.floor
  else
    let r : Int := Nat.sqrt (x.d * x.d * x.e).floor.toNat
    if 0 ≤ x.d then
      let base := (⟨x.a + r, x.c, x.b⟩ : Surd).floor
      if 0 ≤ (x.subRat (base + 1)).sign then base + 1 else base
    else
      let base := (⟨x.a - r, x.c, x.b⟩ : Surd).floor
      if 0 ≤ (x.subRat base).sign then base else base - 1
/-- The nearest integer, a tie to the even one. -/
def roundHalfEven (x : Surd2) : Int :=
  let n := x.floor
  let d := (x.subRat ((n : Rat) + 1 / 2)).sign
  if 0 < d then n + 1 else if d < 0 then n else if n % 2 = 0 then n else n + 1
/-- Six decimals, as v1's `"%.6f"` of the exact value. -/
def fixed6 (x : Surd2) : String :=
  let m := (x.scale 1000000).roundHalfEven.natAbs
  let frac := toString (m % 1000000)
  (if x.sign < 0 then "-" else "") ++ toString (m / 1000000) ++ "." ++
    "".pushn '0' (6 - frac.length) ++ frac
end Surd2

/-! ## Theorems: the order and the rounding -/

/-- The rational sign is positive exactly for a positive rational. -/
theorem ratSign_pos_iff (q : Rat) : 0 < ratSign q ↔ 0 < q := by
  unfold ratSign; split <;> (try split) <;> simp_all <;> grind
/-- The rational sign is negative exactly for a negative rational. -/
theorem ratSign_neg_iff (q : Rat) : ratSign q < 0 ↔ q < 0 := by
  unfold ratSign; split <;> (try split) <;> simp_all <;> grind
/-- The rational sign is not negative exactly for a rational that is not. -/
theorem ratSign_nonneg_iff (q : Rat) : 0 ≤ ratSign q ↔ 0 ≤ q := by
  unfold ratSign; split <;> (try split) <;> simp_all <;> grind

/-- `n ≤ x < n + 1` makes `n` the floor of `x`. -/
theorem floor_eq_of {x : Rat} {n : Int} (h1 : (n : Rat) ≤ x) (h2 : x < n + 1) : x.floor = n := by
  have k1 := Rat.le_floor_iff.mpr h1
  have k2 := Rat.floor_lt_iff.mpr (show x < ((n + 1 : Int) : Rat) by push_cast; exact h2)
  omega

/-- A rational lies in `[⌊x⌋, ⌊x⌋ + 1)`. -/
theorem floor_bounds (x : Rat) : (x.floor : Rat) ≤ x ∧ x < (x.floor : Rat) + 1 := by
  have := Rat.lt_floor_add_one x
  push_cast at this
  exact ⟨Rat.floor_le x, this⟩

/-- For `s ≥ 0`, `Nat.sqrt ⌊s²⌋` is `⌊s⌋`: it lies in `(s - 1, s]`. -/
theorem sqrt_floor_bounds {s : Rat} (hs : 0 ≤ s) :
    ((Nat.sqrt (s * s).floor.toNat : Int) : Rat) ≤ s ∧
      s < ((Nat.sqrt (s * s).floor.toNat : Int) : Rat) + 1 := by
  have hss : 0 ≤ s * s := Rat.mul_nonneg hs hs
  have hf0 : 0 ≤ (s * s).floor := Rat.le_floor_iff.mpr (by simpa using hss)
  generalize hN : (s * s).floor.toNat = N
  have hNf : (N : Int) = (s * s).floor := by rw [← hN]; exact Int.toNat_of_nonneg hf0
  have h1 := Nat.sqrt_le N
  have h2 := Nat.lt_succ_sqrt N
  generalize Nat.sqrt N = r at h1 h2
  have i1 : ((r * r : Nat) : Int) ≤ (s * s).floor := by rw [← hNf]; exact Int.ofNat_le.mpr h1
  have i2 : (s * s).floor < (((r + 1) * (r + 1) : Nat) : Int) := by
    rw [← hNf]; exact Int.ofNat_lt.mpr h2
  have q1 := Rat.le_floor_iff.mp i1
  have q2 := Rat.floor_lt_iff.mp i2
  push_cast at q1 q2
  have hr : (0 : Rat) ≤ ((r : Int) : Rat) := by exact_mod_cast Nat.zero_le r
  constructor
  · refine Rat.not_lt.mp fun h => ?_
    have := (sq_lt_sq hs hr).mpr h
    exact Rat.not_le.mpr this (by push_cast; exact q1)
  · refine (sq_lt_sq hs (by grind)).mp ?_
    push_cast
    exact q2

/-- For `p, n > 0`, `p - n` has the sign of `p² - n²`. -/
theorem sub_sign_of_sq {p n : Rat} (hp : 0 < p) (hn : 0 < n) :
    (n * n < p * p → 0 < p - n) ∧ (p * p < n * n → p - n < 0) ∧ (p * p = n * n → p - n = 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (sq_lt_sq (Rat.le_of_lt hn) (Rat.le_of_lt hp)).mp h; grind
  · have := (sq_lt_sq (Rat.le_of_lt hp) (Rat.le_of_lt hn)).mp h; grind
  · have := (sq_eq_sq (Rat.le_of_lt hp) (Rat.le_of_lt hn)).mp h; grind

/-- Where `c √b` is a rational `t` (`c² b = t²`, `t` of `c`'s sign), `Surd.sign` of
`a + c √b` is the sign of `a + t`. -/
theorem Surd.sign_root {a c b t : Rat} (ht : c * c * b = t * t) (h1 : 0 ≤ c → 0 ≤ t)
    (h2 : c ≤ 0 → t ≤ 0) : (⟨a, c, b⟩ : Surd).sign = ratSign (a + t) := by
  unfold Surd.sign
  simp only []
  by_cases hz : c = 0 ∨ b = 0
  · have t0 : t * t = 0 := by rcases hz with h | h <;> simp [h] at ht <;> grind
    have : t = 0 := by rcases Rat.mul_eq_zero.mp t0 with h | h <;> exact h
    simp [hz, this, Rat.add_zero]
  · have hc : c ≠ 0 := fun h => hz (Or.inl h)
    have hb : b ≠ 0 := fun h => hz (Or.inr h)
    have htz : t ≠ 0 := by
      intro h0
      have : c * c * b = 0 := by rw [ht, h0]; grind
      rcases Rat.mul_eq_zero.mp this with h | h
      · rcases Rat.mul_eq_zero.mp h with h | h <;> exact hc h
      · exact hb h
    simp only [hz, ite_false]
    have hct : ratSign c = ratSign t := by
      unfold ratSign
      by_cases hc' : 0 < c
      · have : 0 < t := by grind
        grind
      · have : c < 0 := by grind
        have : t < 0 := by grind
        grind
    by_cases ha : a = 0
    · simp [ha, hct, Rat.zero_add]
    simp only [ha, ite_false]
    rw [hct, ht]
    by_cases hs : ratSign a = ratSign t
    · simp only [hs, ite_true]
      unfold ratSign at hs ⊢
      by_cases hpa : 0 < a <;> by_cases hpt : 0 < t <;> grind
    · simp only [hs, ite_false]
      unfold ratSign at hs
      by_cases hpa : 0 < a
      · have htn : t < 0 := by grind
        have k := sub_sign_of_sq hpa (show 0 < -t by grind)
        have e1 : -t * -t = t * t := by grind
        rw [e1] at k
        have e2 : a - -t = a + t := by grind
        rw [e2] at k
        unfold ratSign
        by_cases r1 : t * t < a * a
        · simp [r1, k.1 r1, hpa]
        · by_cases r2 : a * a < t * t
          · have := k.2.1 r2; simp [r1, r2, htn]; grind
          · have := k.2.2 (by grind); simp [r1, r2, this]
      · have han : a < 0 := by grind
        have htp : 0 < t := by grind
        have k := sub_sign_of_sq htp (show 0 < -a by grind)
        have e1 : -a * -a = a * a := by grind
        rw [e1] at k
        have e2 : t - -a = a + t := by grind
        rw [e2] at k
        unfold ratSign
        by_cases r1 : t * t < a * a
        · have := k.2.1 r1; simp [r1, han, hpa]; grind
        · by_cases r2 : a * a < t * t
          · simp [r1, r2, htp, k.1 r2]
          · have := k.2.2 (by grind); simp [r1, r2, this]

/-- Where `c √b` is a rational `t`, `Surd.floor` of `a + c √b` is `⌊a + t⌋`. -/
theorem Surd.floor_root {a c b t : Rat} (ht : c * c * b = t * t) (h1 : 0 ≤ c → 0 ≤ t)
    (h2 : c ≤ 0 → t ≤ 0) : (⟨a, c, b⟩ : Surd).floor = (a + t).floor := by
  unfold Surd.floor
  simp only [ht, Surd.subRat]
  by_cases hc : 0 ≤ c
  · have ht0 : 0 ≤ t := h1 hc
    obtain ⟨r1, r2⟩ := sqrt_floor_bounds ht0
    simp only [hc, ite_true]
    generalize ((Nat.sqrt (t * t).floor.toNat : Int) : Rat) = R at r1 r2
    obtain ⟨b1, b2⟩ := floor_bounds (a + R)
    generalize (a + R).floor = B at b1 b2
    rw [Surd.sign_root ht h1 h2]; simp only [ratSign_nonneg_iff]
    by_cases hk : 0 ≤ a - ((B : Rat) + 1) + t
    · simp only [hk, ite_true]
      exact (floor_eq_of (by push_cast; grind) (by push_cast; grind)).symm
    · simp only [hk, ite_false]
      exact (floor_eq_of (by grind) (by grind)).symm
  · have ht0 : t ≤ 0 := h2 (by grind)
    have e : -t * -t = t * t := by grind
    obtain ⟨r1, r2⟩ := sqrt_floor_bounds (show 0 ≤ -t by grind)
    rw [e] at r1 r2
    simp only [hc, ite_false]
    generalize ((Nat.sqrt (t * t).floor.toNat : Int) : Rat) = R at r1 r2
    obtain ⟨b1, b2⟩ := floor_bounds (a - R)
    generalize (a - R).floor = B at b1 b2
    rw [Surd.sign_root ht h1 h2]; simp only [ratSign_nonneg_iff]
    by_cases hk : 0 ≤ a - (B : Rat) + t
    · simp only [hk, ite_true]
      exact (floor_eq_of (by grind) (by grind)).symm
    · simp only [hk, ite_false]
      exact (floor_eq_of (by push_cast; grind) (by push_cast; grind)).symm

/-- `c √(q²)` is the rational `c q`, of `c`'s sign, for `q ≥ 0`. -/
theorem root_sq {c q : Rat} (hq : 0 ≤ q) :
    c * c * (q * q) = (c * q) * (c * q) ∧ (0 ≤ c → 0 ≤ c * q) ∧ (c ≤ 0 → c * q ≤ 0) := by
  refine ⟨by grind, fun h => Rat.mul_nonneg h hq, fun h => ?_⟩
  have := Rat.mul_nonneg (show 0 ≤ -c by grind) hq
  grind

namespace Surd2

/-- (ii), the sign: where the first radicand is `q²`, `q ≥ 0`, the sign is the `Surd`
`(a + c q) + d √e`'s. -/
theorem sign_sq {a c q d e : Rat} (hq : 0 ≤ q) :
    (⟨a, c, q * q, d, e⟩ : Surd2).sign = (⟨a + c * q, d, e⟩ : Surd).sign := by
  obtain ⟨k1, k2, k3⟩ := root_sq (c := c) hq
  unfold Surd2.sign
  simp only [head]
  rw [Surd.sign_root k1 k2 k3]
  by_cases hde : d = 0 ∨ e = 0
  · simp only [hde, ite_true]
    unfold Surd.sign
    simp [hde]
  · simp only [hde, ite_false]
    obtain ⟨w1, w2, w3⟩ := root_sq (c := 2 * a * c) hq
    rw [Surd.sign_root w1 w2 w3]
    have ew : a * a + c * c * (q * q) - d * d * e + 2 * a * c * q =
        (a + c * q) * (a + c * q) - d * d * e := by grind
    rw [ew]
    generalize a + c * q = A
    unfold Surd.sign
    simp only [hde, ite_false, ratSign_eq_zero_iff, ratSign_pos_iff, ratSign_neg_iff]
    have p1 : (0 < A * A - d * d * e) ↔ d * d * e < A * A := by grind
    have p2 : (A * A - d * d * e < 0) ↔ A * A < d * d * e := by grind
    simp only [p1, p2]

/-- (ii), the floor: where the first radicand is `q²`, `q ≥ 0`, the floor is the `Surd`
`(a + c q) + d √e`'s. -/
theorem floor_sq {a c q d e : Rat} (hq : 0 ≤ q) :
    (⟨a, c, q * q, d, e⟩ : Surd2).floor = (⟨a + c * q, d, e⟩ : Surd).floor := by
  obtain ⟨k1, k2, k3⟩ := root_sq (c := c) hq
  unfold Surd2.floor
  simp only [head]
  by_cases hde : d = 0 ∨ e = 0
  · simp only [hde, ite_true]
    rw [Surd.floor_root k1 k2 k3]
    have z1 : d * d * e = 0 * 0 := by rcases hde with h | h <;> simp [h]
    rw [Surd.floor_root (a := a + c * q) z1 (fun _ => Rat.le_refl) (fun _ => Rat.le_refl),
      Rat.add_zero]
  · simp only [hde, ite_false, Surd.floor_root k1 k2 k3, subRat, sign_sq hq]
    unfold Surd.floor
    simp only [Surd.subRat]
    generalize ((Nat.sqrt (d * d * e).floor.toNat : Int) : Rat) = R
    have e1 : a + R + c * q = a + c * q + R := by grind
    have e2 : a - R + c * q = a + c * q - R := by grind
    have e3 : ∀ m : Rat, a - m + c * q = a + c * q - m := fun m => by grind
    simp only [e1, e2, e3]
    rfl

end Surd2

/-- A positive factor keeps the sign. -/
theorem ratSign_mul_pos {k c : Rat} (hk : 0 < k) : ratSign (k * c) = ratSign c := by
  have p : 0 < k * c ↔ 0 < c := by
    constructor
    · intro h
      refine Rat.not_le.mp fun hc => Rat.not_le.mpr h ?_
      have := Rat.mul_nonneg (Rat.le_of_lt hk) (show 0 ≤ -c by grind)
      grind
    · intro h; exact Rat.mul_pos hk h
  have n : k * c < 0 ↔ c < 0 := by
    constructor
    · intro h
      refine Rat.not_le.mp fun hc => Rat.not_le.mpr h ?_
      exact Rat.mul_nonneg (Rat.le_of_lt hk) hc
    · intro h
      have := Rat.mul_pos hk (show 0 < -c by grind)
      grind
  unfold ratSign
  simp only [p, n]

namespace Surd

/-- Two `Surd`s with one floor and one sign at every rational round alike. -/
theorem roundHalfEven_eq {x y : Surd} (hf : x.floor = y.floor)
    (hs : ∀ m, (x.subRat m).sign = (y.subRat m).sign) : x.roundHalfEven = y.roundHalfEven := by
  simp only [roundHalfEven, hf, hs]

/-- Two `Surd`s with one sign, and one floor and one sign at every rational once scaled,
print alike. -/
theorem fixed6_eq {x y : Surd} (hs : x.sign = y.sign)
    (hf : (x.scale 1000000).floor = (y.scale 1000000).floor)
    (hm : ∀ m, ((x.scale 1000000).subRat m).sign = ((y.scale 1000000).subRat m).sign) :
    x.fixed6 = y.fixed6 := by
  simp only [fixed6, roundHalfEven_eq hf hm, hs]

/-- `Surd.sign` reads the root term only through its sign, its square `c² b` and whether
it is absent. -/
theorem sign_same {a c c' b b' : Rat} (hs : ratSign c = ratSign c') (hq : c * c * b = c' * c' * b')
    (hz : (c = 0 ∨ b = 0) ↔ (c' = 0 ∨ b' = 0)) : (⟨a, c, b⟩ : Surd).sign = (⟨a, c', b'⟩ : Surd).sign := by
  unfold sign
  simp only [hz, hs, hq]

/-- So does `Surd.floor`. -/
theorem floor_same {a c c' b b' : Rat} (hs : ratSign c = ratSign c') (hq : c * c * b = c' * c' * b')
    (hz : (c = 0 ∨ b = 0) ↔ (c' = 0 ∨ b' = 0)) : (⟨a, c, b⟩ : Surd).floor = (⟨a, c', b'⟩ : Surd).floor := by
  unfold floor
  have h0 : (0 ≤ c) ↔ (0 ≤ c') := by rw [← ratSign_nonneg_iff, hs, ratSign_nonneg_iff]
  simp only [subRat, hq, h0, sign_same (a := _) hs hq hz]
  rfl

/-- So does `Surd.fixed6`: `a + c √b` and `a + c' √b'` with one root term print alike. -/
theorem fixed6_same {a c c' b b' : Rat} (hs : ratSign c = ratSign c') (hq : c * c * b = c' * c' * b')
    (hz : (c = 0 ∨ b = 0) ↔ (c' = 0 ∨ b' = 0)) : (⟨a, c, b⟩ : Surd).fixed6 = (⟨a, c', b'⟩ : Surd).fixed6 := by
  have hK : (0 : Rat) < 1000000 := by decide
  have hs' : ratSign (1000000 * c) = ratSign (1000000 * c') := by
    rw [ratSign_mul_pos hK, ratSign_mul_pos hK, hs]
  have hq' : 1000000 * c * (1000000 * c) * b = 1000000 * c' * (1000000 * c') * b' := by grind
  have hz' : (1000000 * c = 0 ∨ b = 0) ↔ (1000000 * c' = 0 ∨ b' = 0) := by
    have e1 : (1000000 * c = 0) ↔ c = 0 := by grind
    have e2 : (1000000 * c' = 0) ↔ c' = 0 := by grind
    rw [e1, e2]; exact hz
  refine fixed6_eq (sign_same hs hq hz) (floor_same hs' hq' hz') fun m => ?_
  exact sign_same hs' hq' hz'

end Surd

namespace Surd2

/-- A `Surd2` and a `Surd` with one floor and one sign at every rational round alike. -/
theorem roundHalfEven_eq {x : Surd2} {y : Surd} (hf : x.floor = y.floor)
    (hs : ∀ m, (x.subRat m).sign = (y.subRat m).sign) : x.roundHalfEven = y.roundHalfEven := by
  simp only [roundHalfEven, Surd.roundHalfEven, hf, hs]

/-- A `Surd2` and a `Surd` with one sign, and one floor and one sign at every rational once
scaled, print alike. -/
theorem fixed6_eq {x : Surd2} {y : Surd} (hs : x.sign = y.sign)
    (hf : (x.scale 1000000).floor = (y.scale 1000000).floor)
    (hm : ∀ m, ((x.scale 1000000).subRat m).sign = ((y.scale 1000000).subRat m).sign) :
    x.fixed6 = y.fixed6 := by
  simp only [fixed6, Surd.fixed6, roundHalfEven_eq hf hm, hs]

/-- (i), the sign: with no second term, `Surd.sign`'s. -/
theorem sign_ofSurd (a c b : Rat) : (⟨a, c, b, 0, 0⟩ : Surd2).sign = (⟨a, c, b⟩ : Surd).sign := by
  simp [sign, head]

/-- With no second radicand, `Surd.floor`'s. -/
theorem floor_ofSurd (a c b d : Rat) : (⟨a, c, b, d, 0⟩ : Surd2).floor = (⟨a, c, b⟩ : Surd).floor := by
  simp [floor, head]

/-- (i), the text: with no second term, `Surd.fixed6`'s. -/
theorem fixed6_ofSurd (a c b : Rat) : (⟨a, c, b, 0, 0⟩ : Surd2).fixed6 = (⟨a, c, b⟩ : Surd).fixed6 := by
  refine fixed6_eq (sign_ofSurd a c b) (floor_ofSurd _ _ _ _) fun m => ?_
  simp [sign, head, subRat, scale, Surd.scale, Surd.subRat]

/-- (ii), the text: where the first radicand is `q²`, `q ≥ 0`, the text is the `Surd`
`(a + c q) + d √e`'s. -/
theorem fixed6_sq {a c q d e : Rat} (hq : 0 ≤ q) :
    (⟨a, c, q * q, d, e⟩ : Surd2).fixed6 = (⟨a + c * q, d, e⟩ : Surd).fixed6 := by
  have ek : ∀ k : Rat, k * a + k * c * q = k * (a + c * q) := fun k => by grind
  refine fixed6_eq (sign_sq hq) ?_ fun m => ?_
  · show (⟨1000000 * a, 1000000 * c, q * q, 1000000 * d, e⟩ : Surd2).floor = _
    rw [floor_sq hq, ek]; rfl
  · show (⟨1000000 * a - m, 1000000 * c, q * q, 1000000 * d, e⟩ : Surd2).sign = _
    rw [sign_sq hq]
    have : 1000000 * a - m + 1000000 * c * q = 1000000 * (a + c * q) - m := by grind
    rw [this]; rfl

end Surd2

/-! ## The resolving step over the spacing's square -/

/-- `ResolvingStep` with the spacing kept as its square: each `out_k = CUSP MAX u + Z sd`
and `cusp_k = IN MAX u + Z sd` holds two roots, `√(u²)` and `√(sd²)`; each form in
spacings, `out_k / u = CUSP MAX + Z √(sd² / u²)`, holds one. -/
structure ResolvingStepSq where
  /-- The least `out_k`, in points. -/
  out : Surd2
  /-- The same in spacings; none when `u` is 0. -/
  outSpacings : Option Surd
  /-- The least `cusp_k`, in points. -/
  cusp : Surd2
  /-- The same in spacings. -/
  cuspSpacings : Option Surd
  /-- The greatest `out_k`. -/
  outMost : Surd2
  /-- The greatest `cusp_k`. -/
  cuspMost : Surd2
  /-- Each rank `k ≥ 3` with `out_k` and `cusp_k`. -/
  ranks : List (Nat × Surd2 × Surd2)
  deriving Repr

/-- `resolvingStep` over squares: `spacingSq` is `u²`, `ses2` the ranked
representatives' squared SEs in rank order, `paired` under FIXED-SET the paired SE of each
adjacent difference, as `resolvingStep` takes it. The checks, their order and their words are
`resolvingStep`'s, a negative square refused as a negative spacing or SE is; `sd(k-1, k)²` is
`se2_(k-1) + se2_k`, or the paired SE's square. -/
def resolvingStepSq (spacingSq : Rat) (ses2 : List Rat) (t : Thresholds := {})
    (paired : Option (List Rat) := none) : Except ClusterError (Option ResolvingStepSq) := do
  unless 0 ≤ spacingSq do throw .spacing
  unless ses2.all (0 ≤ ·) do throw .ses
  unless t.valid do throw .parameters
  if let some p := paired then
    unless p.length = ses2.length - 1 && p.all (0 ≤ ·) do throw .paired
  let adj := (ses2.zip ses2.tail).zipIdx.map fun ((a, b), i) =>
    (i + 2, match paired with
      | none => a + b
      | some p => let s := p.getD i 0; s * s)
  let qs := adj.drop 1
  match qs with
  | [] => pure none
  | q0 :: _ =>
    let out (q : Rat) : Surd2 := ⟨0, t.cuspMax, spacingSq, t.z, q⟩
    let cusp (q : Rat) : Surd2 := ⟨0, t.inMax, spacingSq, t.z, q⟩
    let sp (m q : Rat) : Option Surd :=
      if 0 < spacingSq then some ⟨m, t.z, q / spacingSq⟩ else none
    let qMin := qs.foldl (fun m x => min m x.2) q0.2
    let qMax := qs.foldl (fun m x => max m x.2) q0.2
    pure (some {
      out := out qMin, outSpacings := sp t.cuspMax qMin, cusp := cusp qMin,
      cuspSpacings := sp t.inMax qMin, outMost := out qMax, cuspMost := cusp qMax,
      ranks := qs.map fun (k, q) => (k, out q, cusp q) })

/-- `renderResolving`'s text. -/
def renderResolvingSq : Option ResolvingStepSq → String
  | none => "resolving|NONE"
  | some d => "\n".intercalate
    ([s!"resolving|{d.out.fixed6}|{fmt d.outSpacings}|{d.cusp.fixed6}|{fmt d.cuspSpacings}",
      s!"greatest|{d.outMost.fixed6}|{d.cuspMost.fixed6}"] ++
      d.ranks.map fun (k, o, c) => s!"rank|{k}|{o.fixed6}|{c.fixed6}")

/-- The adjacent pairs of the squares are the squares of the adjacent pairs. -/
theorem adj_map_sq (ses : List Rat) (f : (Rat × Rat) × Nat → Nat × Rat) :
    (((ses.map fun s => s * s).zip (ses.map fun s => s * s).tail).zipIdx).map f =
      ((ses.zip ses.tail).zipIdx).map fun ((a, b), i) => f ((a * a, b * b), i) := by
  rw [← List.map_tail, List.zip_map, List.zipIdx_map, List.map_map]
  rfl

/-- A form in spacings over the square, `m + z √(q / u²)`, prints as `(m u + z √q) / u`. -/
theorem spacings_sq {m z q u : Rat} (hu : 0 < u) :
    (⟨m, z, q / (u * u)⟩ : Surd).fixed6 = (Surd.divRat ⟨m * u, z, q⟩ u).fixed6 := by
  have hu0 : u ≠ 0 := fun h => Rat.lt_irrefl (h ▸ hu)
  show _ = (⟨m * u / u, z / u, q⟩ : Surd).fixed6
  rw [Rat.mul_div_cancel hu0]
  have hi : 0 < u⁻¹ := Rat.inv_pos.mpr hu
  refine Surd.fixed6_same ?_ ?_ ?_
  · rw [Rat.div_def, Rat.mul_comm, ratSign_mul_pos hi]
  · grind
  · have e1 : q / (u * u) = 0 ↔ q = 0 := by
      constructor
      · intro h
        have : q / (u * u) * (u * u) = q := Rat.div_mul_cancel (by grind)
        grind
      · intro h; rw [h]; grind
    have e2 : z / u = 0 ↔ z = 0 := by
      constructor
      · intro h
        have : z / u * u = z := Rat.div_mul_cancel hu0
        grind
      · intro h; rw [h]; grind
    rw [e1, e2]

/-- (iii): where the spacing's square is `u * u` with `u ≥ 0` and every squared SE is
`se * se` with `se ≥ 0`, `resolvingStepSq` refuses exactly when `resolvingStep` does, with the
same word, and otherwise `renderResolvingSq` gives `renderResolving`'s text. -/
theorem resolvingStepSq_agrees (u : Rat) (ses : List Rat) (t : Thresholds)
    (paired : Option (List Rat)) (hu : 0 ≤ u) (hs : ∀ s ∈ ses, 0 ≤ s) :
    (resolvingStepSq (u * u) (ses.map fun s => s * s) t paired).map renderResolvingSq =
      (resolvingStep u ses t paired).map renderResolving := by
  have h1 : 0 ≤ u * u := Rat.mul_nonneg hu hu
  have h2 : (ses.map fun s => s * s).all (0 ≤ ·) = true := by
    simp only [List.all_map, List.all_eq_true]
    intro s hs'
    simpa using Rat.mul_nonneg (hs s hs') (hs s hs')
  have h3 : ses.all (0 ≤ ·) = true := by
    simp only [List.all_eq_true]; intro s hs'; simpa using hs s hs'
  unfold resolvingStepSq resolvingStep
  simp only [h1, hu, h2, h3, List.length_map, adj_map_sq, ite_true]
  have hsp : (0 < u * u) ↔ 0 < u := by
    constructor
    · intro h; refine Rat.not_le.mp fun h' => Rat.not_le.mpr h ?_
      have : u = 0 := Rat.le_antisymm h' hu
      rw [this, Rat.mul_zero]; exact Rat.le_refl
    · intro h; exact Rat.mul_pos h h
  have hfix : ∀ (c q : Rat), (⟨0, c, u * u, t.z, q⟩ : Surd2).fixed6 = (⟨c * u, t.z, q⟩ : Surd).fixed6 :=
    fun c q => by rw [Surd2.fixed6_sq hu, Rat.zero_add]
  have hfmt : ∀ (c q : Rat), fmt (if 0 < u * u then some (⟨c, t.z, q / (u * u)⟩ : Surd) else none) =
      fmt (if 0 < u then some (Surd.divRat ⟨c * u, t.z, q⟩ u) else none) := by
    intro c q
    by_cases h : 0 < u
    · simp only [hsp, h, ite_true, fmt, spacings_sq h]
    · simp only [hsp, h, ite_false]
  cases t.valid
  · rfl
  cases paired with
  | none =>
    generalize List.drop 1 (List.map (fun x => (x.snd + 2, x.1.fst * x.1.fst + x.1.snd * x.1.snd))
      (ses.zip ses.tail).zipIdx) = qs
    cases qs
    · rfl
    · simp only [Except.map, pure, Except.pure, ite_true, renderResolvingSq, renderResolving, hfix,
        hfmt, Function.comp_def, List.map_map]
  | some p =>
    simp only [ite_true]
    split
    · generalize List.drop 1 (List.map (fun x => (x.snd + 2, p.getD x.snd 0 * p.getD x.snd 0))
        (ses.zip ses.tail).zipIdx) = qs
      cases qs
      · rfl
      · simp only [Except.map, pure, Except.pure, renderResolvingSq, renderResolving, hfix, hfmt,
          Function.comp_def, List.map_map]
    · rfl

/-- The refusal half of (iii), by itself: under its conditions the two refuse with the same
word. -/
theorem resolvingStepSq_refuses (u : Rat) (ses : List Rat) (t : Thresholds)
    (paired : Option (List Rat)) (hu : 0 ≤ u) (hs : ∀ s ∈ ses, 0 ≤ s) (e : ClusterError) :
    resolvingStepSq (u * u) (ses.map fun s => s * s) t paired = .error e ↔
      resolvingStep u ses t paired = .error e := by
  have h := resolvingStepSq_agrees u ses t paired hu hs
  revert h
  cases resolvingStepSq (u * u) (ses.map fun s => s * s) t paired <;>
    cases resolvingStep u ses t paired <;>
    simp [Except.map]
  intro h; rw [h]

/-- Six decimals with two roots at the rounding's boundaries: `√8 - 2 √2` is `0`, so
`a + √8 - 2 √2` is `a` exactly and a tie at the seventh decimal goes to the even neighbour,
up or down; `√3 - √2 - 0.31783725` is `-4.80...e-9`, a negative value that rounds to zero and
keeps its minus sign; `√3 - √2` is `0.317837245...`. -/
theorem Surd2.fixed6_rounding :
    (⟨5 / 10000000, 1, 8, -2, 2⟩ : Surd2).fixed6 = "0.000000" ∧
      (⟨15 / 10000000, 1, 8, -2, 2⟩ : Surd2).fixed6 = "0.000002" ∧
      (⟨-5 / 10000000, 1, 8, -2, 2⟩ : Surd2).fixed6 = "-0.000000" ∧
      (⟨-31783725 / 100000000, 1, 3, -1, 2⟩ : Surd2).fixed6 = "-0.000000" ∧
      (⟨0, 1, 3, -1, 2⟩ : Surd2).fixed6 = "0.317837" := by
  decide +kernel

end Principia.Cluster
