import Principia.Strike
import Principia.ValueBound

/-!
# The strike rule's numbers within the bound on an exact value

SR8's scale factor and SR3's M-M and L-M tests, computed as `Principia.Strike` computes
them, each step that forms a value from the inputs checked first against the bound on an
exact value's size (`Principia.ValueBound`), and refused "exact value too large" when it
could cross it. When they answer they answer what the plain functions do
(`sr8ScaleFactor_ok`, `mmContradicts_ok`, `lmContradicts_ok`), whose theorems therefore
hold of every answer given. A request's numbers can be small and still build a large value:
a hundred uncertainties whose exponents spread from -9999 to 250 put a sum's denominator
past the bound.
-/

namespace Principia.Strike.Bounded

open Principia.Parameters (sr8MinGroup sr8OutlierFactor sr8Threshold)
open Principia.ValueBound (Bounded tooLarge mulFits addFits)

/-- Refused for the bound unless `c` holds. -/
def need (c : Bool) : Bounded Unit := if c then .ok () else .error tooLarge

/-- SR8 over the records it keeps, as `Strike.sr8ScaleFactor` ends, each value it forms
checked first. -/
def sr8OfKept (kept : List Measurement) : Bounded (Option ScaleFactor) :=
  if kept.length < sr8MinGroup then .ok (some .one)
  else do
    let w (m : Measurement) : Rat := 1 / (m.uncertainty * m.uncertainty)
    need (kept.all fun m => mulFits m.uncertainty m.uncertainty && mulFits m.value (w m))
    let num ← ValueBound.sumBy (fun m => .ok (m.value * w m)) kept
    let den ← ValueBound.sumBy (fun m => .ok (w m)) kept
    let xBar ← ValueBound.div num den
    need (kept.all fun m => addFits m.value xBar &&
      mulFits (m.value - xBar) (m.value - xBar) &&
      mulFits ((m.value - xBar) * (m.value - xBar)) (w m))
    let chi2 ← ValueBound.sumBy
      (fun m => .ok ((m.value - xBar) * (m.value - xBar) * w m)) kept
    let reduced ← ValueBound.div chi2 ((kept.length : Rat) - 1)
    if h : ratioValue sr8Threshold < reduced then
      .ok (some ⟨reduced, Rat.le_of_lt (ratioValue_sr8Threshold ▸ h)⟩)
    else .ok (some .one)

/-- `Strike.sr8ScaleFactor`, each value it forms from the measurements checked first. -/
def sr8ScaleFactor (ms : List Measurement) : Bounded (Option ScaleFactor) :=
  if ms.length < sr8MinGroup then .ok (some .one)
  else if ms.any (·.uncertainty ≤ 0) then .ok none
  else do
    let n : Rat := ms.length
    let total ← ValueBound.sumBy (fun m => .ok m.uncertainty) ms
    let uMean ← ValueBound.div total n
    let f : Rat := sr8OutlierFactor
    let uu ← ValueBound.mul uMean uMean
    let bound ← ValueBound.mul (f * f * n) uu
    need (ms.all fun m => mulFits m.uncertainty m.uncertainty)
    sr8OfKept (ms.filter fun m => decide (m.uncertainty * m.uncertainty < bound))

/-- `Numeric.exceedsBound`, its products checked first. -/
def exceedsBound (dd c v : Rat) : Bounded Bool :=
  if 0 < c then do
    let cc ← ValueBound.mul c c
    let ccv ← ValueBound.mul cc v
    .ok (decide (ccv < dd))
  else if c < 0 ∧ 0 < v then .ok true
  else .ok (decide (0 < dd))

/-- `Strike.mmContradicts`, each value it forms checked first. -/
def mmContradicts (x1 u1 x2 u2 k : Rat) (S : ScaleFactor := .one) : Bounded Bool := do
  let d ← ValueBound.sub x1 x2
  let dd ← ValueBound.mul d d
  let a ← ValueBound.mul u1 u1
  let b ← ValueBound.mul u2 u2
  let ab ← ValueBound.add a b
  let v ← ValueBound.mul S.square ab
  exceedsBound dd k v

/-- `Strike.lmContradicts`, each value it forms checked first. -/
def lmContradicts (xL xM uM k : Rat) (S : ScaleFactor := .one) : Bounded Bool := do
  let d ← ValueBound.sub xM xL
  let dd ← ValueBound.mul d d
  let c ← ValueBound.mul k uM
  exceedsBound dd c S.square

/-! ## PROVED: an answer is the plain function's -/

theorem bind_ok {α β : Type} {x : Bounded α} {f : α → Bounded β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem need_ok {c : Bool} {u : Unit} (h : need c = .ok u) : c = true := by
  unfold need at h; split at h <;> simp_all

/-- A checked sum of plain terms is the plain sum. -/
theorem sumBy_pure {α : Type} (g : α → Rat) (l : List α) (r : Rat)
    (h : ValueBound.sumBy (fun a => .ok (g a)) l = .ok r) : r = Numeric.sumBy g l :=
  ValueBound.sumBy_ok (fun a => .ok (g a)) g (fun _ _ h => by cases h; rfl) l 0 r h

theorem exceedsBound_ok {dd c v : Rat} {b : Bool} (h : exceedsBound dd c v = .ok b) :
    b = Numeric.exceedsBound dd c v := by
  unfold exceedsBound at h
  unfold Numeric.exceedsBound
  by_cases hc : 0 < c
  · rw [ite_eq_left hc] at h ⊢
    obtain ⟨cc, hcc, h⟩ := bind_ok h
    obtain ⟨ccv, hccv, h⟩ := bind_ok h
    cases h
    rw [ValueBound.mul_ok hccv, ValueBound.mul_ok hcc]
  · rw [ite_eq_right hc] at h ⊢
    by_cases h2 : c < 0 ∧ 0 < v
    · rw [ite_eq_left h2] at h ⊢; cases h; rfl
    · rw [ite_eq_right h2] at h ⊢; cases h; rfl

theorem mmContradicts_ok {x1 u1 x2 u2 k : Rat} {S : ScaleFactor} {b : Bool}
    (h : mmContradicts x1 u1 x2 u2 k S = .ok b) : b = Strike.mmContradicts x1 u1 x2 u2 k S := by
  unfold mmContradicts at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨dd, hdd, h⟩ := bind_ok h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨b2, hb2, h⟩ := bind_ok h
  obtain ⟨ab, hab, h⟩ := bind_ok h
  obtain ⟨v, hv, h⟩ := bind_ok h
  rw [exceedsBound_ok h, ValueBound.mul_ok hv, ValueBound.add_ok hab, ValueBound.mul_ok ha,
    ValueBound.mul_ok hb2, ValueBound.mul_ok hdd, ValueBound.sub_ok hd]
  rfl

theorem lmContradicts_ok {xL xM uM k : Rat} {S : ScaleFactor} {b : Bool}
    (h : lmContradicts xL xM uM k S = .ok b) : b = Strike.lmContradicts xL xM uM k S := by
  unfold lmContradicts at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨dd, hdd, h⟩ := bind_ok h
  obtain ⟨c, hc, h⟩ := bind_ok h
  rw [exceedsBound_ok h, ValueBound.mul_ok hc, ValueBound.mul_ok hdd, ValueBound.sub_ok hd]
  rfl

/-- The end of `Strike.sr8ScaleFactor`, over the records it keeps. -/
def plainOfKept (kept : List Measurement) : Option ScaleFactor :=
  if kept.length < sr8MinGroup then some .one
  else
    let w (m : Measurement) : Rat := 1 / (m.uncertainty * m.uncertainty)
    let xBar := Numeric.sumBy (fun m => m.value * w m) kept / Numeric.sumBy w kept
    let chi2 := Numeric.sumBy (fun m => (m.value - xBar) * (m.value - xBar) * w m) kept
    let reduced := chi2 / ((kept.length : Rat) - 1)
    if h : ratioValue sr8Threshold < reduced then
      some ⟨reduced, Rat.le_of_lt (ratioValue_sr8Threshold ▸ h)⟩
    else some .one

theorem sr8OfKept_ok {kept : List Measurement} {r : Option ScaleFactor}
    (h : sr8OfKept kept = .ok r) : r = plainOfKept kept := by
  unfold sr8OfKept at h
  unfold plainOfKept
  by_cases h3 : kept.length < sr8MinGroup
  · rw [ite_eq_left h3] at h ⊢; cases h; rfl
  · rw [ite_eq_right h3] at h ⊢
    dsimp only at h ⊢
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨num, hnum, h⟩ := bind_ok h
    obtain ⟨den, hden, h⟩ := bind_ok h
    obtain ⟨xBar, hxBar, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨chi2, hchi2, h⟩ := bind_ok h
    obtain ⟨reduced, hreduced, h⟩ := bind_ok h
    have hx := ValueBound.div_ok hxBar
    rw [sumBy_pure _ _ num hnum, sumBy_pure _ _ den hden] at hx
    subst hx
    have hr := ValueBound.div_ok hreduced
    rw [sumBy_pure _ _ chi2 hchi2] at hr
    subst hr
    split at h <;> rename_i h4
    · rw [dite_eq_left h4]; cases h; rfl
    · rw [dite_eq_right h4]; cases h; rfl

/-- `Strike.sr8ScaleFactor` past its first two cases is `plainOfKept` of the records it
keeps. -/
theorem plain_split (ms : List Measurement) (h1 : ¬ ms.length < sr8MinGroup)
    (h2 : ¬ ms.any (·.uncertainty ≤ 0) = true) :
    Strike.sr8ScaleFactor ms = plainOfKept (ms.filter fun m =>
      decide (m.uncertainty * m.uncertainty < (sr8OutlierFactor : Rat) * sr8OutlierFactor *
        (ms.length : Rat) * (Numeric.sumBy (·.uncertainty) ms / (ms.length : Rat) *
          (Numeric.sumBy (·.uncertainty) ms / (ms.length : Rat))))) := by
  unfold Strike.sr8ScaleFactor
  rw [ite_eq_right h1, ite_eq_right h2]
  rfl

theorem sr8ScaleFactor_ok {ms : List Measurement} {r : Option ScaleFactor}
    (h : sr8ScaleFactor ms = .ok r) : r = Strike.sr8ScaleFactor ms := by
  unfold sr8ScaleFactor at h
  by_cases h1 : ms.length < sr8MinGroup
  · rw [ite_eq_left h1] at h; cases h
    unfold Strike.sr8ScaleFactor; rw [ite_eq_left h1]
  · rw [ite_eq_right h1] at h
    by_cases h2 : ms.any (·.uncertainty ≤ 0) = true
    · rw [ite_eq_left h2] at h; cases h
      unfold Strike.sr8ScaleFactor; rw [ite_eq_right h1, ite_eq_left h2]
    · rw [ite_eq_right h2] at h
      rw [plain_split ms h1 h2]
      dsimp only at h
      obtain ⟨total, htotal, h⟩ := bind_ok h
      obtain ⟨uMean, huMean, h⟩ := bind_ok h
      obtain ⟨uu, huu, h⟩ := bind_ok h
      obtain ⟨bound, hbound, h⟩ := bind_ok h
      obtain ⟨_, -, h⟩ := bind_ok h
      have hm := ValueBound.div_ok huMean
      rw [sumBy_pure (·.uncertainty) ms total htotal] at hm
      have hb := ValueBound.mul_ok hbound
      rw [ValueBound.mul_ok huu, hm] at hb
      rw [hb] at h
      exact sr8OfKept_ok h

end Principia.Strike.Bounded
