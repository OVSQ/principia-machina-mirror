import Principia.Form.Evaluation

/-!
# The declared forms within the bound on an exact value

The Calculator's rule: a form's input past the bound is refused (a literal, `literalValue`; a
binding, `readBindings`), and an intermediate value that would pass it is enclosed, never
formed exactly (`Principia.Form.Num`). The theorems here state the second half operation by
operation: every operation of the evaluator that answers an exact number from exact numbers
within the bound answers one within it (`sizeOf ≤ maxBits`, the numerator's and the
denominator's bits together), and a literal and a binding the evaluator takes are within it.

`eval_exact_within` assembles them by induction over `Expr.eval`, and
`eval_exact_within_read` states it under bindings as `readBindings` reads them.
-/

namespace Principia.Form

/-! ## Bits -/

theorem lt_two_pow_bitsOf (n : Nat) : n < 2 ^ bitsOf n := Nat.lt_log2_self

theorem bitsOf_pos (n : Nat) : 0 < bitsOf n := by unfold bitsOf; omega

theorem bitsOf_le_of_lt_two_pow {n k : Nat} (hk : 0 < k) (h : n < 2 ^ k) : bitsOf n ≤ k := by
  unfold bitsOf
  by_cases hn : n = 0
  · subst hn; simp [Nat.log2_zero]; omega
  · have := (Nat.log2_lt hn).2 h; omega

theorem bitsOf_mono {m n : Nat} (h : m ≤ n) : bitsOf m ≤ bitsOf n :=
  bitsOf_le_of_lt_two_pow (bitsOf_pos n) (Nat.lt_of_le_of_lt h (lt_two_pow_bitsOf n))

theorem bitsOf_mul_le (m n : Nat) : bitsOf (m * n) ≤ bitsOf m + bitsOf n := by
  apply bitsOf_le_of_lt_two_pow (by have := bitsOf_pos m; omega)
  rw [Nat.pow_add]
  by_cases hm : m = 0
  · subst hm; simp; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  · exact Nat.mul_lt_mul_of_lt_of_lt (lt_two_pow_bitsOf m) (lt_two_pow_bitsOf n)

theorem bitsOf_pow_le (m : Nat) : ∀ n, 0 < n → bitsOf (m ^ n) ≤ n * bitsOf m
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => by simp
  | n + 2, _ => by
    have ih := bitsOf_pow_le m (n + 1) (Nat.succ_pos n)
    calc bitsOf (m ^ (n + 2)) = bitsOf (m ^ (n + 1) * m) := by rw [Nat.pow_succ]
      _ ≤ bitsOf (m ^ (n + 1)) + bitsOf m := bitsOf_mul_le _ _
      _ ≤ (n + 1) * bitsOf m + bitsOf m := Nat.add_le_add_right ih _
      _ = (n + 2) * bitsOf m := by rw [Nat.succ_mul (n + 1)]

/-! ## A rational's parts under the operations -/

theorem natAbs_num_mul_le (a b : Rat) : (a * b).num.natAbs ≤ a.num.natAbs * b.num.natAbs := by
  rw [Rat.num_mul, ← Int.natAbs_mul]
  exact Int.natAbs_ediv_le_natAbs _ _

theorem den_mul_le (a b : Rat) : (a * b).den ≤ a.den * b.den := by
  rw [Rat.den_mul]; exact Nat.div_le_self _ _

theorem natAbs_num_inv_le (a : Rat) : (a⁻¹).num.natAbs ≤ a.den := by
  rw [Rat.num_inv, Int.natAbs_mul]
  have : a.num.sign.natAbs ≤ 1 := by
    rcases Int.sign_trichotomy a.num with h | h | h <;> simp [h]
  calc a.num.sign.natAbs * (a.den : Int).natAbs ≤ 1 * (a.den : Int).natAbs :=
        Nat.mul_le_mul_right _ this
    _ = a.den := by simp

theorem bitsOf_den_inv_le (a : Rat) : bitsOf (a⁻¹).den ≤ bitsOf a.num.natAbs := by
  rw [Rat.den_inv]
  split
  · exact bitsOf_le_of_lt_two_pow (bitsOf_pos _) (by
      have := Nat.two_pow_pos (bitsOf a.num.natAbs)
      have h2 : 1 < 2 ^ bitsOf a.num.natAbs := by
        have hb := bitsOf_pos a.num.natAbs
        exact Nat.one_lt_two_pow (by omega)
      exact h2)
  · exact Nat.le_refl _

/-! ## Exact numbers -/

theorem sizeOf_of_zero (k : Int) : sizeOf (Exact.of 0 k) ≤ maxBits := by
  simp [Exact.of, sizeOf, bitsOf, maxBits]

theorem sizeOf_of_le (q : Rat) (k : Int) :
    sizeOf (Exact.of q k) ≤ bitsOf q.num.natAbs + bitsOf q.den := by
  unfold Exact.of
  split
  · rename_i h; subst h; simp [sizeOf, bitsOf]
  · exact Nat.le_refl _

theorem sizeOf_mul_le (x y : Exact) : sizeOf (Exact.mul x y) ≤ sizeOf x + sizeOf y := by
  unfold Exact.mul
  refine Nat.le_trans (sizeOf_of_le _ _) ?_
  unfold sizeOf
  have h1 := Nat.le_trans (bitsOf_mono (natAbs_num_mul_le x.coef y.coef)) (bitsOf_mul_le _ _)
  have h2 := Nat.le_trans (bitsOf_mono (den_mul_le x.coef y.coef)) (bitsOf_mul_le _ _)
  omega

theorem sizeOf_neg (x : Exact) : sizeOf (Exact.of (-x.coef) x.pi) ≤ sizeOf x :=
  Nat.le_trans (sizeOf_of_le _ _) (by simp [sizeOf])

theorem sizeOf_quot_le (x y : Exact) :
    sizeOf (Exact.of (x.coef / y.coef) (x.pi - y.pi)) ≤ sizeOf x + sizeOf y := by
  refine Nat.le_trans (sizeOf_of_le _ _) ?_
  rw [Rat.div_def]
  unfold sizeOf
  have h1 := Nat.le_trans (bitsOf_mono (natAbs_num_mul_le x.coef y.coef⁻¹)) (bitsOf_mul_le _ _)
  have h1' := bitsOf_mono (natAbs_num_inv_le y.coef)
  have h2 := Nat.le_trans (bitsOf_mono (den_mul_le x.coef y.coef⁻¹)) (bitsOf_mul_le _ _)
  have h2' := bitsOf_den_inv_le y.coef
  omega

/-! ## The evaluator's operations -/

/-- An exact number of the evaluator within the bound. -/
def Num.within : Num → Prop
  | .exact x => sizeOf x ≤ maxBits
  | _ => True

theorem Num.zero_within : Num.zero.within := by
  simp [Num.zero, Num.within, sizeOf, bitsOf, maxBits]

theorem Num.add_within {a b : Num} (ha : a.within) (hb : b.within) : (a.add b).within := by
  unfold Num.add
  split
  · rename_i x y
    split
    · exact hb
    · split
      · exact ha
      · split
        · simp only
          split
          · rename_i hs; simp only [Num.within]; exact hs
          · simp [Num.lift2, Num.within]
        · simp [Num.lift2, Num.within]
  · simp [Num.lift2]; split <;> simp [Num.within]

theorem Num.mul_within {a b : Num} : (a.mul b).within := by
  unfold Num.mul
  split
  · rename_i x y
    split
    · exact Num.zero_within
    · split
      · rename_i _ h; simp only [Num.within]
        exact Nat.le_trans (sizeOf_mul_le x y) h
      · simp [Num.lift2, Num.within]
  · split
    · exact Num.zero_within
    · simp [Num.lift2]; split <;> simp [Num.within]
  · split
    · exact Num.zero_within
    · simp [Num.lift2]; split <;> simp [Num.within]
  · simp [Num.lift2]; split <;> simp [Num.within]

theorem Num.div_within {a b : Num} : (a.div b).within := by
  unfold Num.div
  split
  · rename_i x y
    split
    · exact Num.zero_within
    · split
      · rename_i _ h; simp only [Num.within]
        exact Nat.le_trans (sizeOf_quot_le x y) h
      · simp [Num.lift2, Num.within]
  · split
    · exact Num.zero_within
    · simp [Num.lift2]; split <;> simp [Num.within]
  · simp [Num.lift2]; split <;> simp [Num.within]

theorem Num.neg_within {a : Num} (ha : a.within) : a.neg.within := by
  cases a with
  | exact x => exact Nat.le_trans (sizeOf_neg x) ha
  | approx => trivial
  | unknown => trivial

theorem Num.sub_within {a b : Num} (ha : a.within) (hb : b.within) : (a.sub b).within :=
  Num.add_within ha (Num.neg_within hb)

theorem Num.ofRat_small_within {q : Rat} (h : bitsOf q.num.natAbs + bitsOf q.den ≤ maxBits) :
    (Num.ofRat q).within := by
  simp only [Num.ofRat, Num.within, Exact.ofRat]
  exact Nat.le_trans (sizeOf_of_le _ _) h

theorem Num.one_within : (Num.exact Exact.one).within := by
  simp [Num.within, Exact.one, sizeOf, bitsOf, maxBits]

theorem Num.lift1_within {w : String} {f : Nat → Iv → Option Iv} {a : Num} :
    (Num.lift1 w f a).within := by
  unfold Num.lift1; split <;> simp [Num.within]

theorem Num.abs_within {a : Num} (ha : a.within) : a.abs.within := by
  cases a with
  | exact x =>
    simp only [Num.abs, Num.within]
    refine Nat.le_trans (sizeOf_of_le _ _) (Nat.le_trans ?_ ha)
    unfold sizeOf
    split <;> simp
  | approx => trivial
  | unknown => trivial

theorem Num.powNat_within {a : Num} {n : Nat} : (a.powNat n).within := by
  unfold Num.powNat
  split
  · rename_i x
    split
    · exact Num.one_within
    · split
      · exact Num.zero_within
      · split
        · rename_i _ _ h
          simp only [Num.within, Exact.zpow]
          refine Nat.le_trans (sizeOf_of_le _ _) (Nat.le_trans ?_ h)
          have hn : 0 < n := by omega
          rw [Rat.zpow_natCast, Rat.num_pow, Rat.den_pow, Int.natAbs_pow]
          have h1 := bitsOf_pow_le x.coef.num.natAbs n hn
          have h2 := bitsOf_pow_le x.coef.den n hn
          unfold sizeOf
          rw [Nat.mul_add]
          omega
        · split
          · simp [Num.within]
          · exact Num.lift1_within
  · exact Num.lift1_within

theorem Num.inv_within {a : Num} : a.inv.within := Num.div_within

theorem Num.exp_within {a : Num} : a.exp.within := by
  unfold Num.exp
  split
  · split
    · exact Num.one_within
    · split
      · simp [Num.within]
      · split
        · simp [Num.within]
        · exact Num.lift1_within
  · exact Num.lift1_within

theorem Num.ln_within {a : Num} : a.ln.within := by
  unfold Num.ln
  split
  · split
    · exact Num.zero_within
    · exact Num.lift1_within
  · exact Num.lift1_within

/-- `sinPi?`'s values are 0, ±1/2 and ±1. -/
theorem sinPi_small {r v : Rat} (h : Num.sinPi? r = some v) :
    bitsOf v.num.natAbs + bitsOf v.den ≤ maxBits := by
  unfold Num.sinPi? at h
  dsimp only at h
  split at h
  · cases h
  · split at h <;> cases h <;> decide +kernel

theorem Num.sin_within {a : Num} : a.sin.within := by
  unfold Num.sin
  split
  · split
    · rename_i h; exact Num.ofRat_small_within (sinPi_small (Option.bind_eq_some_iff.mp h |>.choose_spec.2))
    · exact Num.lift1_within
  · exact Num.lift1_within

theorem Num.cos_within {a : Num} : a.cos.within := by
  unfold Num.cos
  split
  · split
    · rename_i h; exact Num.ofRat_small_within (sinPi_small (Option.bind_eq_some_iff.mp h |>.choose_spec.2))
    · exact Num.lift1_within
  · exact Num.lift1_within

theorem Num.tan_within {a : Num} : a.tan.within := by
  unfold Num.tan
  split
  · split
    · dsimp only
      split
      · exact Num.lift1_within
      · split
        · exact Num.zero_within
        · exact Num.ofRat_small_within (by decide +kernel)
        · exact Num.ofRat_small_within (by decide +kernel)
        · simp [Num.within]
    · exact Num.lift1_within
  · exact Num.lift1_within

theorem Num.powRat_within {a : Num} {p : Int} {q : Nat} (ha : a.within) : (a.powRat p q).within := by
  unfold Num.powRat
  dsimp only
  split
  · split
    · split
      · exact Num.one_within
      · exact Num.zero_within
    · split
      · split
        · exact Num.powNat_within
        · exact Num.inv_within
      · split
        · split
          · rename_i h; exact h
          · exact Num.lift1_within
        · exact Num.lift1_within
  · split
    · split
      · exact Num.powNat_within
      · exact Num.inv_within
    · exact Num.lift1_within

theorem Num.sqrt_within {a : Num} (ha : a.within) : a.sqrt.within := Num.powRat_within ha

/-! ## The inputs -/

/-- A literal the evaluator takes is within the bound. -/
theorem literalValue_within {c : String} {q : Rat} (h : literalValue c = some q) :
    sizeOf (Exact.ofRat q) ≤ maxBits := by
  unfold literalValue at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-! ## The evaluation -/

/-- Every binding `readBindings` answers is within the bound. -/
theorem readBindings_within {bs : List (String × BindingArg)} {b : Bindings}
    (h : readBindings bs = .ok b) : ∀ p ∈ b, sizeOf p.2.value ≤ maxBits := by
  unfold readBindings at h
  have key : ∀ (l : List (String × BindingArg)) (acc : Answer Bindings),
      (∀ b', acc = .ok b' → ∀ p ∈ b', sizeOf p.2.value ≤ maxBits) →
      ∀ b', l.foldl (fun acc (x : String × BindingArg) =>
        acc.bind fun out =>
          match x.2 with
          | none => .ok out
          | some (v, u) =>
            match Units.Bounded.normalizeMeasurementArg v (some "0") u with
            | .ok (.ok m) =>
              if sizeOf m.x ≤ maxBits then .ok (out ++ [(x.1, ⟨m.x, kindsOf m.kind⟩)])
              else .refused ValueBound.tooLarge
            | .ok (.error r) => .refused r
            | .error _ => .refused ValueBound.tooLarge) acc = .ok b' →
        ∀ p ∈ b', sizeOf p.2.value ≤ maxBits := by
    intro l
    induction l with
    | nil => intro acc hacc b' h; exact hacc b' h
    | cons x t ih =>
      intro acc hacc b' h
      refine ih _ ?_ b' h
      intro b'' hb''
      cases acc with
      | ok out =>
        simp only [Answer.bind] at hb''
        revert hb''
        split
        · intro hb''; cases hb''; exact hacc _ rfl
        · split
          · split
            · intro hb''; cases hb''
              intro p hp
              rcases List.mem_append.mp hp with hp | hp
              · exact hacc _ rfl p hp
              · simp at hp; subst hp; assumption
            · intro hb''; cases hb''
          · intro hb''; cases hb''
          · intro hb''; cases hb''
      | _ => simp [Answer.bind] at hb''
  exact key _ (.ok []) (by intro b' h; cases h; simp) b h

/-- A bound identifier's value, from bindings within the bound, is within it. -/
theorem lookup_within {b : Bindings} (hb : ∀ p ∈ b, sizeOf p.2.value ≤ maxBits) {n : String}
    {bd : Bound} (h : b.lookup n = some bd) : sizeOf bd.value ≤ maxBits := by
  induction b with
  | nil => simp [List.lookup] at h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup] at h
    split at h
    · cases h; exact hb (k, bd) (by simp)
    · exact ih (fun p hp => hb p (by simp [hp])) h

/-- The bound for the declared forms: from bindings within the bound, every
exact number `Expr.eval` answers is within it; a value that would cross it is enclosed
(the Calculator's rule). -/
theorem eval_exact_within (budget : Option Nat) (b : Bindings)
    (hb : ∀ p ∈ b, sizeOf p.2.value ≤ maxBits) :
    ∀ (e : Expr) {s : Nat} {v : Num} {k : Kinds} {s' : Nat},
      e.eval budget b s = .ok (v, k, s') → v.within := by
  intro e
  induction e with
  | num c =>
    intro s v k s' h
    simp only [Expr.eval] at h
    split at h
    · rename_i q hq; cases h; exact literalValue_within hq
    · cases h
  | ident n =>
    intro s v k s' h
    simp only [Expr.eval] at h
    split at h
    · cases h
    · rename_i bd hl
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · cases h; exact lookup_within hb hl
  | paren e ih => intro s v k s' h; exact ih h
  | neg e ih =>
    intro s v k s' h
    simp only [Expr.eval, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i p hp; obtain ⟨va, ka⟩ := p; cases h; exact Num.neg_within (ih hp)
  | bin op l r ihl ihr =>
    intro s v k s' h
    simp only [Expr.eval, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i pa hpa
      obtain ⟨va, ka⟩ := pa
      have ha := ihl hpa
      split at h
      · cases h
      · rename_i pb hpb
        obtain ⟨vb, kb⟩ := pb
        have hb' := ihr hpb
        repeat' (first | (split at h) | (cases h) )
        all_goals first
          | exact Num.mul_within
          | exact Num.div_within
          | exact Num.add_within ha hb'
          | exact Num.sub_within ha hb'
          | contradiction
          | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw, Except.bind])
          | skip

  | pow base p q ih =>
    intro s v k s' h
    simp only [Expr.eval, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i pa hpa
      obtain ⟨va, ka⟩ := pa
      have ha := ih hpa
      repeat' (first | (split at h) | (cases h) )
      all_goals first
        | exact Num.powNat_within
        | exact Num.inv_within
        | exact Num.powRat_within ha
        | contradiction
        | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw, Except.bind])
        | skip
  | fn f a ih =>
    intro s v k s' h
    simp only [Expr.eval, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i pa hpa
      obtain ⟨va, ka⟩ := pa
      have ha := ih hpa
      repeat' (first | (split at h) | (cases h) )
      all_goals first
        | exact Num.abs_within ha
        | exact Num.sqrt_within ha
        | exact Num.ln_within
        | exact Num.exp_within
        | exact Num.sin_within
        | exact Num.cos_within
        | exact Num.tan_within
        | contradiction
        | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw, Except.bind])
        | skip
  | deriv x s n =>
    intro s v k s' h
    simp only [Expr.eval] at h
    split at h
    · cases h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · cases h; exact Num.zero_within

/-- The evaluator's statement whole: under bindings as `readBindings` reads them, every exact
number an expression evaluates to holds at most `maxBits` bits. -/
theorem eval_exact_within_read {bs : List (String × BindingArg)} {b : Bindings}
    (hb : readBindings bs = .ok b) {budget : Option Nat} {e : Expr} {s : Nat} {v : Num}
    {k : Kinds} {s' : Nat} (h : e.eval budget b s = .ok (v, k, s')) : v.within :=
  eval_exact_within budget b (readBindings_within hb) e h

end Principia.Form
