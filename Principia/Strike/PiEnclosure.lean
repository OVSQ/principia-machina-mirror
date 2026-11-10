import Principia.Strike.PiScale

/-!
# The enclosure of π, and the strike rule across powers of π, proved monotone

`Strike.PiScale.exceedsPi` decides SR3's test with `S²` a ratio of polynomials in π from
signs that `Exact.polySignAtPiPow` decides over enclosures of π. This file proves what
those decisions rest on, over `Rat` alone:

* the enclosures of π the sign search reads are nonempty, positive and nested, the finer
  inside the coarser (`piBounds_nested`), so one rational point `piPoint`, the low end of the
  finest, lies in every one;
* the value of a polynomial at a rational `t` (`PiPoly.eval`) commutes with `add`, `sub`
  and `mul` (`eval_add`, `eval_sub`, `eval_mul`);
* the fold of the sign search bounds the value at every `t` of the interval it reads
  (`fold_encloses`), so a sign the search decides is the sign of the value at `piPoint`
  (`sign_eval`);
* `exceeds_pi_of_le`: an excess decided at a scale square is never refused at a smaller
  one. With `exceeds_pi_of_le_nonpos` it covers every sign of `c`.

The statements are over the enclosures the search consults, which is what the function
decides on; no statement is made over the real number π.
-/

namespace Principia.Strike.PiScale

/-! ## Finite sums -/

/-- `f 0 + f 1 + ... + f (n - 1)`. -/
def fsum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => fsum f n + f n

theorem fsum_congr {f g : Nat → Rat} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    fsum f n = fsum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fsum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem fsum_zero {f : Nat → Rat} {n : Nat} (h : ∀ i, i < n → f i = 0) : fsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fsum]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]; grind

theorem fsum_add (f g : Nat → Rat) (n : Nat) :
    fsum (fun i => f i + g i) n = fsum f n + fsum g n := by
  induction n with
  | zero => simp only [fsum]; grind
  | succ n ih => simp only [fsum]; rw [ih]; grind

theorem fsum_mul_left (c : Rat) (f : Nat → Rat) (n : Nat) :
    fsum (fun i => c * f i) n = c * fsum f n := by
  induction n with
  | zero => simp [fsum]
  | succ n ih => simp only [fsum]; rw [ih]; grind

theorem fsum_split (f : Nat → Rat) (a b : Nat) :
    fsum f (a + b) = fsum f a + fsum (fun j => f (a + j)) b := by
  induction b with
  | zero => simp only [fsum, Nat.add_zero]; grind
  | succ b ih => rw [← Nat.add_assoc]; simp only [fsum]; rw [ih]; grind

theorem fsum_swap (g : Nat → Nat → Rat) (m n : Nat) :
    fsum (fun k => fsum (fun i => g i k) m) n = fsum (fun i => fsum (fun k => g i k) n) m := by
  induction m with
  | zero => simp only [fsum]; exact fsum_zero (fun _ _ => rfl)
  | succ m ih => simp only [fsum]; rw [fsum_add, ih]

/-- A sum whose terms vanish from `L` on is the sum to `L`. -/
theorem fsum_extend (f : Nat → Rat) {L N : Nat} (hLN : L ≤ N) (h : ∀ j, L ≤ j → f j = 0) :
    fsum f N = fsum f L := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hLN
  rw [fsum_split, fsum_zero (fun j _ => h (L + j) (by omega))]
  grind

/-- A sum shifted by `d` places: the powers gain `t^d`. -/
theorem fsum_shift (h : Nat → Rat) (t : Rat) {d L N : Nat} (hL : ∀ j, L ≤ j → h j = 0)
    (hN : d + L ≤ N) :
    fsum (fun i => (if d ≤ i then h (i - d) else 0) * t ^ i) N =
      t ^ d * fsum (fun j => h j * t ^ j) L := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_trans (Nat.le_add_right d L) hN)
  rw [fsum_split, fsum_zero (fun i hi => by rw [ite_eq_right (by omega)]; grind)]
  rw [fsum_congr (g := fun j => t ^ d * (h j * t ^ j)) (fun j _ => by
    rw [ite_eq_left (by omega), show d + j - d = j by omega]; grind)]
  rw [fsum_mul_left, fsum_extend _ (show L ≤ r by omega) (fun j hj => by rw [hL j hj]; grind)]
  grind

/-! ## The value of a polynomial at a rational point -/

/-- `c₀ + c₁ t + c₂ t² + ...`. -/
def cval (cs : List Rat) (t : Rat) : Rat := fsum (fun i => cs.getD i 0 * t ^ i) cs.length

/-- The value at `t` of `c₀ t^shift + c₁ t^(shift+1) + ...`. -/
def PiPoly.eval (p : PiPoly) (t : Rat) : Rat := t ^ p.shift * cval p.cs t

theorem getD_ge {l : List Rat} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem cval_extend (cs : List Rat) (t : Rat) {N : Nat} (h : cs.length ≤ N) :
    fsum (fun i => cs.getD i 0 * t ^ i) N = cval cs t :=
  fsum_extend _ h (fun j hj => by rw [getD_ge hj]; grind)

theorem cval_nil (t : Rat) : cval [] t = 0 := rfl

theorem cval_append_zeros (a zs : List Rat) (t : Rat) (hz : ∀ z ∈ zs, z = 0) :
    cval (a ++ zs) t = cval a t := by
  unfold cval
  rw [fsum_extend _ (show a.length ≤ (a ++ zs).length by simp) (fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hj]
    cases hz' : zs[j - a.length]? with
    | none => simp
    | some z => rw [hz z (List.mem_of_getElem? hz')]; simp)]
  exact fsum_congr (fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD])

/-- The coefficients from `lo`, read through `coefAt`, give the value. -/
theorem eval_coefAt (p : PiPoly) {t : Rat} (ht : t ≠ 0) {lo : Int} {N : Nat}
    (hlo : lo ≤ p.shift) (hN : p.shift + p.cs.length ≤ lo + N) :
    t ^ lo * fsum (fun i => p.coefAt (lo + i) * t ^ i) N = p.eval t := by
  have hd : p.shift = lo + ((p.shift - lo).toNat : Int) := by omega
  rw [fsum_congr (g := fun i => (if (p.shift - lo).toNat ≤ i then
      p.cs.getD (i - (p.shift - lo).toNat) 0 else 0) * t ^ i) (fun i _ => by
    unfold PiPoly.coefAt
    by_cases hi : (p.shift - lo).toNat ≤ i
    · rw [ite_eq_right (by omega), ite_eq_left hi,
        show (lo + (i : Int) - p.shift).toNat = i - (p.shift - lo).toNat by omega]
    · rw [ite_eq_left (by omega), ite_eq_right hi])]
  rw [fsum_shift _ t (L := p.cs.length) (fun j hj => getD_ge hj) (by omega)]
  unfold PiPoly.eval cval
  rw [← Rat.mul_assoc, ← Rat.zpow_natCast, ← Rat.zpow_add ht, ← hd]

/-- `t^lead` times the value past `lead` places whose coefficients are zero. -/
theorem cval_drop_zeros (cs : List Rat) (t : Rat) {n : Nat} (hn : n ≤ cs.length)
    (hz : ∀ i, i < n → cs.getD i 0 = 0) :
    cval cs t = t ^ n * cval (cs.drop n) t := by
  unfold cval
  rw [← fsum_shift (fun j => (cs.drop n).getD j 0) t (fun j hj => getD_ge hj)
    (show n + (cs.drop n).length ≤ cs.length by simp; omega)]
  refine fsum_congr (fun i _ => ?_)
  by_cases hi : n ≤ i
  · rw [ite_eq_left hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_drop, show n + (i - n) = i by omega]
  · rw [ite_eq_right hi, hz i (by omega)]

theorem takeWhile_zero {l : List Rat} : ∀ i, i < (l.takeWhile (· == 0)).length →
    l.getD i 0 = 0 := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons c l ih =>
    intro i hi
    by_cases hc : (c == 0) = true
    · simp only [List.takeWhile_cons, hc, ↓reduceIte, List.length_cons] at hi
      cases i with
      | zero => simp only [List.getD_cons_zero]; exact (beq_iff_eq.mp hc)
      | succ i => simp only [List.getD_cons_succ]; exact ih i (by omega)
    · simp only [List.takeWhile_cons, hc] at hi; simp at hi

theorem mem_takeWhile_zero {l : List Rat} {z : Rat} (h : z ∈ l.takeWhile (· == 0)) : z = 0 := by
  induction l with
  | nil => simp at h
  | cons c l ih =>
    by_cases hc : (c == 0) = true
    · simp only [List.takeWhile_cons, hc, ↓reduceIte, List.mem_cons] at h
      rcases h with h | h
      · subst h; exact beq_iff_eq.mp hc
      · exact ih h
    · simp only [List.takeWhile_cons, hc] at h; simp at h

/-- Dropping the zero coefficients at either end keeps the value. -/
theorem eval_norm (p : PiPoly) {t : Rat} (ht : t ≠ 0) : p.norm.eval t = p.eval t := by
  have hlead := takeWhile_zero (l := p.cs)
  have hle : (p.cs.takeWhile (· == 0)).length ≤ p.cs.length := by
    have := congrArg List.length (List.takeWhile_append_dropWhile (p := (· == 0)) (l := p.cs))
    rw [List.length_append] at this
    omega
  have hdrop := cval_drop_zeros p.cs t hle hlead
  generalize hr : p.cs.drop (p.cs.takeWhile (· == 0)).length = r at hdrop
  have hrev : r = ((r.reverse.dropWhile (· == 0)).reverse) ++
      (r.reverse.takeWhile (· == 0)).reverse := by
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have hzs : ∀ z ∈ (r.reverse.takeWhile (· == 0)).reverse, z = 0 := by
    intro z hz
    rw [List.mem_reverse] at hz
    exact mem_takeWhile_zero hz
  have hbody := cval_append_zeros ((r.reverse.dropWhile (· == 0)).reverse) _ t hzs
  rw [← hrev] at hbody
  unfold PiPoly.norm
  simp only [hr]
  split
  · rename_i he
    rw [List.isEmpty_iff.mp he, cval_nil] at hbody
    unfold PiPoly.eval
    rw [hdrop, hbody]
    simp [PiPoly.zero, cval_nil]
  · unfold PiPoly.eval
    simp only
    rw [← hbody, hdrop, ← Rat.mul_assoc, ← Rat.zpow_natCast, ← Rat.zpow_add ht]

/-! ## The evaluation homomorphism -/

open Principia.ValueBound (Bounded)

/-- A checked map that answers is the plain map of what each step answers. -/
theorem mapM_ok {α : Type} {f : α → Bounded Rat} {g : α → Rat}
    (hf : ∀ a c, f a = .ok c → c = g a) :
    ∀ (xs : List α) (l : List Rat), xs.mapM f = .ok l → l = xs.map g
  | [], l, h => by simp only [List.mapM_nil] at h; cases h; rfl
  | x :: xs, l, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok c =>
      rw [hx] at h
      change (xs.mapM f >>= fun r => pure (c :: r)) = .ok l at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok r =>
        rw [hxs] at h
        cases h
        rw [List.map_cons, hf x c hx, mapM_ok hf xs r hxs]

theorem getD_map_range (g : Nat → Rat) {n i : Nat} (h : i < n) :
    ((List.range n).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

/-- The value of coefficients `g 0, ..., g (n - 1)`. -/
theorem cval_map_range (g : Nat → Rat) (n : Nat) (t : Rat) :
    cval ((List.range n).map g) t = fsum (fun i => g i * t ^ i) n := by
  unfold cval
  rw [List.length_map, List.length_range]
  exact fsum_congr (fun i hi => by rw [getD_map_range g hi])

theorem eval_empty {p : PiPoly} (t : Rat) (h : p.cs.isEmpty = true) : p.eval t = 0 := by
  unfold PiPoly.eval; rw [List.isEmpty_iff.mp h, cval_nil]; grind

theorem eval_zero (t : Rat) : PiPoly.zero.eval t = 0 := eval_empty t rfl

/-- The sum's value is the sum of the values. -/
theorem eval_add {p q r : PiPoly} {t : Rat} (ht : t ≠ 0) (h : p.add q = .ok r) :
    r.eval t = p.eval t + q.eval t := by
  unfold PiPoly.add at h
  split at h
  · rename_i hp; cases h; rw [eval_empty t hp]; grind
  · split at h
    · rename_i _ hq; cases h; rw [eval_empty t hq]; grind
    · rename_i hp hq
      have hp' : p.cs.length ≠ 0 := fun h0 => hp (by
        rw [List.isEmpty_iff]; exact List.eq_nil_of_length_eq_zero h0)
      have hq' : q.cs.length ≠ 0 := fun h0 => hq (by
        rw [List.isEmpty_iff]; exact List.eq_nil_of_length_eq_zero h0)
      dsimp only at h
      generalize hlo : min p.shift q.shift = lo at h
      generalize hhi : max (p.shift + p.cs.length) (q.shift + q.cs.length) = hi at h
      cases hm : (List.range (hi - lo).toNat).mapM (fun (i : Nat) =>
          ValueBound.add (p.coefAt (lo + (i : Int))) (q.coefAt (lo + (i : Int)))) with
      | error e => rw [hm] at h; cases h
      | ok cs =>
        rw [hm] at h
        cases h
        have hcs := mapM_ok (g := fun (i : Nat) => p.coefAt (lo + (i : Int)) +
          q.coefAt (lo + (i : Int))) (fun i c hc => ValueBound.add_ok hc) _ cs hm
        rw [eval_norm _ ht]
        unfold PiPoly.eval
        simp only
        rw [hcs, cval_map_range]
        rw [fsum_congr (g := fun i => p.coefAt (lo + (i : Int)) * t ^ i +
          q.coefAt (lo + (i : Int)) * t ^ i) (fun i _ => by grind), fsum_add, Rat.mul_add]
        rw [eval_coefAt p ht (by omega) (by omega), eval_coefAt q ht (by omega) (by omega)]
        rfl

theorem eval_neg (p : PiPoly) (t : Rat) : p.neg.eval t = -p.eval t := by
  unfold PiPoly.eval PiPoly.neg cval
  simp only [List.length_map]
  rw [fsum_congr (g := fun i => -1 * (p.cs.getD i 0 * t ^ i)) (fun i _ => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases p.cs[i]? <;> simp <;> grind), fsum_mul_left]
  grind

/-- The difference's value is the difference of the values. -/
theorem eval_sub {p q r : PiPoly} {t : Rat} (ht : t ≠ 0) (h : p.sub q = .ok r) :
    r.eval t = p.eval t - q.eval t := by
  rw [eval_add ht h, eval_neg]; grind

theorem getElem!_toArray_getD {q : List Rat} {j : Nat} (h : j < q.length) :
    q.toArray[j]! = q.getD j 0 := by
  rw [List.getElem!_toArray, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp [h]

theorem bind_ok {α β : Type} {x : Bounded α} {f : α → Bounded β} {c : β}
    (h : x >>= f = .ok c) : ∃ a, x = .ok a ∧ f a = .ok c := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- The checked fold of `mul` for the coefficient of `t^k` answers the sum of the products
whose powers add to `k`. -/
theorem conv_fold (q : List Rat) (k : Nat) : ∀ (l : List Rat) (n : Nat) (s c : Rat),
    (l.zipIdx n).foldlM (fun s (ci : Rat × Nat) =>
      if ci.2 ≤ k ∧ k - ci.2 < q.toArray.size then do
        ValueBound.add s (← ValueBound.mul ci.1 q.toArray[k - ci.2]!)
      else pure s) s = .ok c →
    c = s + fsum (fun i => if n + i ≤ k then l.getD i 0 * q.getD (k - (n + i)) 0 else 0)
      l.length
  | [], n, s, c, h => by
    simp only [List.zipIdx_nil, List.foldlM_nil] at h; cases h; show _ = _ + 0; grind
  | a :: l, n, s, c, h => by
    rw [List.zipIdx_cons, List.foldlM_cons] at h
    obtain ⟨s', hs', h⟩ := bind_ok h
    have hv : s' = s + (if n ≤ k then a * q.getD (k - n) 0 else 0) := by
      split at hs'
      · rename_i hc
        obtain ⟨m, hm, ha⟩ := bind_ok hs'
        rw [ValueBound.add_ok ha, ValueBound.mul_ok hm, ite_eq_left hc.1,
          getElem!_toArray_getD (by rw [List.size_toArray] at hc; exact hc.2)]
      · rename_i hc
        cases hs'
        by_cases hk : n ≤ k
        · rw [ite_eq_left hk, getD_ge (by rw [List.size_toArray] at hc; omega)]; grind
        · rw [ite_eq_right hk]; grind
    have ih := conv_fold q k l (n + 1) s' c h
    rw [ih, hv, List.length_cons, Nat.add_comm l.length 1, fsum_split]
    simp only [fsum, Nat.add_zero, List.getD_cons_zero]
    rw [fsum_congr (g := fun j => if n + 1 + j ≤ k then l.getD j 0 * q.getD (k - (n + 1 + j)) 0
      else 0) (fun j _ => rfl)]
    grind

theorem fsum_mul_right (c : Rat) (f : Nat → Rat) (n : Nat) :
    fsum (fun i => f i * c) n = fsum f n * c := by
  rw [fsum_congr (g := fun i => c * f i) (fun i _ => Rat.mul_comm _ _), fsum_mul_left,
    Rat.mul_comm]

/-- The product's value is the product of the values. -/
theorem eval_mul {p q r : PiPoly} {t : Rat} (ht : t ≠ 0) (h : p.mul q = .ok r) :
    r.eval t = p.eval t * q.eval t := by
  unfold PiPoly.mul at h
  split at h
  · rename_i he
    cases h
    rw [eval_zero]
    rcases Bool.or_eq_true_iff.mp he with hp | hq
    · rw [eval_empty t hp]; grind
    · rw [eval_empty t hq]; grind
  · rename_i he
    have hp : p.cs.length ≠ 0 := fun h0 => he (by
      rw [List.eq_nil_of_length_eq_zero h0]; rfl)
    dsimp only at h
    cases hm : (List.range (p.cs.length + q.cs.length - 1)).mapM (fun k =>
        p.cs.zipIdx.foldlM (fun s (ci : Rat × Nat) =>
          if ci.2 ≤ k ∧ k - ci.2 < q.cs.toArray.size then do
            ValueBound.add s (← ValueBound.mul ci.1 q.cs.toArray[k - ci.2]!)
          else pure s) 0) with
    | error e => rw [hm] at h; cases h
    | ok cs =>
      rw [hm] at h
      cases h
      have hcs := mapM_ok (g := fun k => 0 + fsum (fun i => if 0 + i ≤ k then
          p.cs.getD i 0 * q.cs.getD (k - (0 + i)) 0 else 0) p.cs.length)
        (fun k c hc => conv_fold q.cs k p.cs 0 0 c hc) _ cs hm
      rw [eval_norm _ ht]
      unfold PiPoly.eval
      simp only
      rw [hcs, cval_map_range, Rat.zpow_add ht]
      have hN : ∀ i, i < p.cs.length → i + q.cs.length ≤ p.cs.length + q.cs.length - 1 := by
        intro i hi; omega
      rw [fsum_congr (g := fun k => fsum (fun i => (if i ≤ k then
          (fun j => p.cs.getD i 0 * q.cs.getD j 0) (k - i) else 0) * t ^ k) p.cs.length)
        (fun k _ => by
          rw [Rat.zero_add, ← fsum_mul_right]
          exact fsum_congr (fun i _ => by simp only [Nat.zero_add]))]
      rw [fsum_swap]
      rw [fsum_congr (g := fun i => p.cs.getD i 0 * t ^ i * cval q.cs t) (fun i hi => by
        rw [fsum_shift (fun j => p.cs.getD i 0 * q.cs.getD j 0) t (L := q.cs.length) (fun j hj => by rw [getD_ge hj]; grind)
          (hN i hi), fsum_congr (g := fun j => p.cs.getD i 0 * (q.cs.getD j 0 * t ^ j))
          (fun j _ => by grind), fsum_mul_left]
        unfold cval; grind)]
      rw [fsum_mul_right]
      unfold cval
      grind

/-! ## The enclosures of π the sign search reads -/

/-- The interval at `p` bits for `π^1`, its power unfolded. -/
def piBoundsAt (p : Nat) : Rat × Rat :=
  let i := Exact.Interval.mul p (Exact.Interval.mul p (Exact.Interval.exact 1)
    (Exact.Interval.exact 1)) (Exact.piInterval p)
  ((i.lo : Rat) * Exact.pow2 i.exp, (i.hi : Rat) * Exact.pow2 i.exp)

theorem interval_pow_one (p : Nat) (a : Exact.Interval) :
    Exact.Interval.pow p a 1 =
      Exact.Interval.mul p (Exact.Interval.mul p (Exact.Interval.exact 1)
        (Exact.Interval.exact 1)) a := by
  rw [Exact.Interval.pow]
  simp only [Nat.one_ne_zero, ↓reduceDIte, Nat.reduceDiv, Nat.reduceMod]
  rw [Exact.Interval.pow]
  simp

theorem piPowBounds_one (p : Nat) : Exact.piPowBounds 1 p = piBoundsAt p := by
  simp only [Exact.piPowBounds, piBoundsAt, Int.natAbs_one, interval_pow_one]
  rfl

/-- The point every enclosure the search reads contains: the low end of the finest. -/
def piPoint : Rat := (Exact.piPowBounds 1 4096).1

/-- The enclosures of π at the precisions `polySignAtPiPow` tries are nonempty and nested,
each finer one inside the coarser, and positive. -/
theorem piBounds_nested :
    0 < (Exact.piPowBounds 1 64).1 ∧
    (Exact.piPowBounds 1 64).1 ≤ (Exact.piPowBounds 1 256).1 ∧
    (Exact.piPowBounds 1 256).1 ≤ (Exact.piPowBounds 1 1024).1 ∧
    (Exact.piPowBounds 1 1024).1 ≤ (Exact.piPowBounds 1 4096).1 ∧
    (Exact.piPowBounds 1 4096).1 ≤ (Exact.piPowBounds 1 4096).2 ∧
    (Exact.piPowBounds 1 4096).2 ≤ (Exact.piPowBounds 1 1024).2 ∧
    (Exact.piPowBounds 1 1024).2 ≤ (Exact.piPowBounds 1 256).2 ∧
    (Exact.piPowBounds 1 256).2 ≤ (Exact.piPowBounds 1 64).2 := by
  simp only [piPowBounds_one]
  decide +kernel

/-- Every enclosure the search reads is nonnegative at its low end and contains `piPoint`. -/
theorem piPoint_mem : ∀ p ∈ [64, 256, 1024, 4096],
    0 ≤ (Exact.piPowBounds 1 p).1 ∧ (Exact.piPowBounds 1 p).1 ≤ piPoint ∧
      piPoint ≤ (Exact.piPowBounds 1 p).2 := by
  have h := piBounds_nested
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  unfold piPoint
  rcases hp with rfl | rfl | rfl | rfl <;> grind

theorem piPoint_pos : 0 < piPoint := by
  have h := piBounds_nested
  unfold piPoint
  grind

/-! ## The sign search decides the sign at `piPoint` -/

theorem pow_le_pow_of_le {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : Nat, a ^ i ≤ b ^ i
  | 0 => by grind
  | i + 1 => by
    have ih := pow_le_pow_of_le ha hab i
    have h0 : 0 ≤ a ^ i := Rat.pow_nonneg ha
    have h1 : a ^ i * a ≤ b ^ i * a := by
      rw [Rat.mul_comm (a ^ i), Rat.mul_comm (b ^ i)]
      exact Rat.mul_le_mul_of_nonneg_left ih ha
    have h2 : b ^ i * a ≤ b ^ i * b :=
      Rat.mul_le_mul_of_nonneg_left hab (Rat.le_trans h0 ih)
    rw [Rat.pow_succ, Rat.pow_succ]
    exact Rat.le_trans h1 h2

theorem term_bounds {tlo t thi c : Rat} (h0 : 0 ≤ tlo) (hl : tlo ≤ t) (hh : t ≤ thi)
    (i : Nat) :
    min (c * tlo ^ i) (c * thi ^ i) ≤ c * t ^ i ∧ c * t ^ i ≤ max (c * tlo ^ i) (c * thi ^ i) := by
  have hl' := pow_le_pow_of_le h0 hl i
  have hh' := pow_le_pow_of_le (Rat.le_trans h0 hl) hh i
  by_cases hc : 0 ≤ c
  · have := Rat.mul_le_mul_of_nonneg_left hl' hc
    have := Rat.mul_le_mul_of_nonneg_left hh' hc
    grind
  · have hc' : 0 ≤ -c := by grind
    have := Rat.mul_le_mul_of_nonneg_left hl' hc'
    have := Rat.mul_le_mul_of_nonneg_left hh' hc'
    grind

/-- The fold of the sign search bounds the value at every point of its interval. -/
theorem fold_encloses {tlo t thi : Rat} (h0 : 0 ≤ tlo) (hl : tlo ≤ t) (hh : t ≤ thi) :
    ∀ (l : List Rat) (n : Nat) (acc : Rat × Rat),
      ((l.zipIdx n).foldl (fun (acc : Rat × Rat) (ci : Rat × Nat) =>
        let a := ci.1 * tlo ^ ci.2
        let b := ci.1 * thi ^ ci.2
        (acc.1 + min a b, acc.2 + max a b)) acc).1 ≤
          acc.1 + fsum (fun i => l.getD i 0 * t ^ (n + i)) l.length ∧
      acc.2 + fsum (fun i => l.getD i 0 * t ^ (n + i)) l.length ≤
        ((l.zipIdx n).foldl (fun (acc : Rat × Rat) (ci : Rat × Nat) =>
          let a := ci.1 * tlo ^ ci.2
          let b := ci.1 * thi ^ ci.2
          (acc.1 + min a b, acc.2 + max a b)) acc).2
  | [], n, acc => by
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, fsum]
    constructor <;> grind
  | c :: l, n, acc => by
    rw [List.zipIdx_cons, List.foldl_cons]
    have ih := fold_encloses h0 hl hh l (n + 1)
      (acc.1 + min (c * tlo ^ n) (c * thi ^ n), acc.2 + max (c * tlo ^ n) (c * thi ^ n))
    have hb := term_bounds (c := c) h0 hl hh n
    have hs : fsum (fun i => (c :: l).getD i 0 * t ^ (n + i)) (c :: l).length =
        c * t ^ n + fsum (fun i => l.getD i 0 * t ^ (n + 1 + i)) l.length := by
      rw [List.length_cons, Nat.add_comm l.length 1, fsum_split]
      simp only [fsum, List.getD_cons_zero, Nat.add_zero]
      rw [fsum_congr (g := fun i => l.getD i 0 * t ^ (n + 1 + i)) (fun i _ => by
        rw [show 1 + i = i + 1 by omega, List.getD_cons_succ, show n + (i + 1) = n + 1 + i by omega])]
      grind
    rw [hs]
    simp only at ih ⊢
    constructor <;> grind

/-- What the sign search decides at the precisions `ps`, each of whose enclosures contains
`t`, is the sign of the value at `t`. -/
theorem search_sign {cs : List Rat} {t : Rat} :
    ∀ (ps : List Nat), (∀ p ∈ ps, 0 ≤ (Exact.piPowBounds 1 p).1 ∧
      (Exact.piPowBounds 1 p).1 ≤ t ∧ t ≤ (Exact.piPowBounds 1 p).2) → ∀ o,
    ps.findSome? (fun p =>
      let (tlo, thi) := Exact.piPowBounds 1 p
      let (lo, hi) := cs.zipIdx.foldl (fun (acc : Rat × Rat) (ci : Rat × Nat) =>
        let a := ci.1 * tlo ^ ci.2
        let b := ci.1 * thi ^ ci.2
        (acc.1 + min a b, acc.2 + max a b)) (0, 0)
      if 0 < lo then some Ordering.gt else if hi < 0 then some Ordering.lt else none) = some o →
    (o = .gt ∧ 0 < cval cs t) ∨ (o = .lt ∧ cval cs t < 0)
  | [], _, o, h => by simp at h
  | p :: ps, hps, o, h => by
    rw [List.findSome?_cons] at h
    obtain ⟨h0, hl, hh⟩ := hps p (List.mem_cons_self ..)
    have hf := fold_encloses h0 hl hh cs 0 (0, 0)
    have hv : fsum (fun i => cs.getD i 0 * t ^ (0 + i)) cs.length = cval cs t := by
      unfold cval; exact fsum_congr (fun i _ => by rw [Nat.zero_add])
    rw [hv] at hf
    split at h
    · rename_i o' ho
      cases h
      simp only at ho hf
      split at ho
      · cases ho; left; exact ⟨rfl, by grind⟩
      · split at ho
        · cases ho; right; exact ⟨rfl, by grind⟩
        · cases ho
    · exact search_sign ps (fun p hp => hps p (List.mem_cons_of_mem _ hp)) o h

/-- A sign `PiPoly.sign` decides is the sign of the value at `piPoint`. -/
theorem sign_eval {p : PiPoly} {o : Ordering} (h : p.sign = some o) :
    (o = .gt ∧ 0 < p.eval piPoint) ∨ (o = .lt ∧ p.eval piPoint < 0) ∨
      (o = .eq ∧ p.eval piPoint = 0) := by
  have hpos : 0 < piPoint ^ p.shift := Rat.zpow_pos piPoint_pos
  unfold PiPoly.sign Exact.polySignAtPiPow at h
  unfold PiPoly.eval
  split at h
  · rename_i hz
    cases h
    right; right
    refine ⟨rfl, ?_⟩
    unfold cval
    rw [fsum_zero (fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have := List.all_eq_true.mp hz _ (List.getElem_mem hi)
      simp only [beq_iff_eq] at this
      simp [this])]
    grind
  · rw [ite_eq_right (by decide)] at h
    rcases search_sign _ piPoint_mem o h with ⟨ho, hv⟩ | ⟨ho, hv⟩
    · left; exact ⟨ho, Rat.mul_pos hpos hv⟩
    · right; left
      refine ⟨ho, ?_⟩
      have := Rat.mul_pos hpos (show 0 < -cval p.cs piPoint by grind)
      grind

/-! ## SR3 across powers of π: a larger scale square never creates an excess -/

/-- The value at `piPoint` of the polynomials `exceedsPi` forms for `c > 0`, and the sign
it reads from them, when it answers. -/
theorem exceedsPi_gt_ok {dd ccv : PiPoly} {vPos : Bool} {s2 : PiRatio} {b : Bool}
    (hden : s2.den.sign = some .gt) (h : exceedsPi dd ccv .gt vPos s2 = .ok (some b)) :
    ∃ o : Ordering, (b = (o == .gt)) ∧
      ((o = .gt ∧ 0 < dd.eval piPoint * s2.den.eval piPoint -
          ccv.eval piPoint * s2.num.eval piPoint) ∨
        (o = .lt ∧ dd.eval piPoint * s2.den.eval piPoint -
          ccv.eval piPoint * s2.num.eval piPoint < 0) ∨
        (o = .eq ∧ dd.eval piPoint * s2.den.eval piPoint -
          ccv.eval piPoint * s2.num.eval piPoint = 0)) := by
  have ht : piPoint ≠ 0 := fun h0 => by have := piPoint_pos; grind
  unfold exceedsPi at h
  obtain ⟨lhs, hl, h⟩ := bind_ok h
  obtain ⟨rhs, hr, h⟩ := bind_ok h
  obtain ⟨diff, hd, h⟩ := bind_ok h
  rw [hden] at h
  cases hs : diff.sign with
  | none => rw [hs] at h; cases h
  | some o =>
    rw [hs] at h
    cases h
    refine ⟨o, rfl, ?_⟩
    have hv := sign_eval hs
    rw [eval_sub ht hd, eval_mul ht hl, eval_mul ht hr] at hv
    exact hv

/-- SR3 across powers of π, for `c > 0`: where the scale square `s2` is at most `s2'`
(both denominators decided positive, and the sign of `s2'.num · s2.den - s2.num · s2'.den`
decided not negative) and `c² v` is decided not negative, an excess decided at `s2'` is
never refused at `s2`. With `exceeds_pi_of_le_nonpos` it covers every sign of `c`. -/
theorem exceeds_pi_of_le {dd ccv x : PiPoly} {vPos : Bool} {s2 s2' : PiRatio}
    (hccv : ccv.sign = some .gt ∨ ccv.sign = some .eq)
    (hden : s2.den.sign = some .gt) (hden' : s2'.den.sign = some .gt)
    (hx : (do
      let a ← s2'.num.mul s2.den
      let b ← s2.num.mul s2'.den
      a.sub b) = .ok x)
    (hle : x.sign = some .gt ∨ x.sign = some .eq)
    (h : exceedsPi dd ccv .gt vPos s2' = .ok (some true)) :
    exceedsPi dd ccv .gt vPos s2 ≠ .ok (some false) := by
  intro hf
  have ht : piPoint ≠ 0 := fun h0 => by have := piPoint_pos; grind
  -- the values at piPoint
  have hQ : 0 < s2.den.eval piPoint := by
    rcases sign_eval hden with h | h | h <;> grind
  have hQ' : 0 < s2'.den.eval piPoint := by
    rcases sign_eval hden' with h | h | h <;> grind
  have hC : 0 ≤ ccv.eval piPoint := by
    rcases hccv with hc | hc <;> rcases sign_eval hc with h | h | h <;> grind
  obtain ⟨a, ha, hx⟩ := bind_ok hx
  obtain ⟨b, hb, hx⟩ := bind_ok hx
  have hX : 0 ≤ s2'.num.eval piPoint * s2.den.eval piPoint -
      s2.num.eval piPoint * s2'.den.eval piPoint := by
    have hv := eval_sub ht hx
    rw [eval_mul ht ha, eval_mul ht hb] at hv
    rw [← hv]
    rcases hle with hs | hs <;> rcases sign_eval hs with h | h | h <;> grind
  -- the excess at s2' and the refusal at s2
  obtain ⟨o', ho', hv'⟩ := exceedsPi_gt_ok hden' h
  have hE : 0 < dd.eval piPoint * s2'.den.eval piPoint -
      ccv.eval piPoint * s2'.num.eval piPoint := by
    rcases hv' with ⟨rfl, hv⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hv
    · cases ho'
    · cases ho'
  obtain ⟨o, ho, hv⟩ := exceedsPi_gt_ok hden hf
  have hR : dd.eval piPoint * s2.den.eval piPoint -
      ccv.eval piPoint * s2.num.eval piPoint ≤ 0 := by
    rcases hv with ⟨rfl, _⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · cases ho
    · grind
    · grind
  have h1 := Rat.mul_pos hQ hE
  have h2 := Rat.mul_nonneg hC hX
  have h3 := Rat.mul_nonneg (Rat.le_of_lt hQ') (show 0 ≤ -(dd.eval piPoint *
    s2.den.eval piPoint - ccv.eval piPoint * s2.num.eval piPoint) by grind)
  grind

end Principia.Strike.PiScale
