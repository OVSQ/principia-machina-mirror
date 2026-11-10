import Principia.UnitsStrike
import Principia.Strike.Bounded

/-!
# Units: the numbers within the bound on an exact value

The unit functions that form numbers from a request (`unit_scale`, `normalize_measurement`
and the three that go on to the strike rule), computed as the plain functions compute
them, each step that forms a value checked first against the bound on an exact value's
size, and refused "exact value too large" when it could cross it. When they answer they
answer what the plain functions do (`unitScaleArg_ok`, `normalizeMeasurementArg_ok`,
`mmContradictsUnitsArg_ok`, `lmContradictsUnitsArg_ok`, `sr8ScaleFactorUnitsArg_ok`).
Every refusal of the plain functions comes first, in their order: the bound is checked on
values the plain functions would have formed.

A unit's scale is held in lowest terms, as powers of the catalogue's prime-free parts, and
its numerator and its denominator are formed by whole powers and products, each checked by
bit lengths before it is formed. Every partial product is a factor of the whole, so one that
would pass the bound shows that the whole does: the refusal is exact, a scale whose
numerator or denominator has more bits than the bound and no other. A scale within the
double range can be such a scale: a short unit of a few prefixed angles has one whose
numerator and denominator run to a million bits.
-/

namespace Principia.Units.Bounded

open Principia.ValueBound (Bounded tooLarge maxBits bits addFits)
open Principia.Strike.Bounded (need bind_ok need_ok)

/-! ## Whole numbers within the bound -/

/-- `x * y` when it holds at most `maxBits` bits: refused by bit lengths before it is
formed when it must hold more, since `x * y` holds at least `bits x + bits y - 1` bits;
otherwise formed, at most one bit past the bound, and checked exactly. -/
def natMul (x y : Nat) : Option Nat :=
  if bits x + bits y ≤ maxBits + 1 then
    let z := x * y
    if bits z ≤ maxBits then some z else none
  else none

/-- `b ^ e` when it holds at most `maxBits` bits, by repeated squaring: each square and
product is a factor of the power, so none is formed past the bound. -/
def natPow (b : Nat) (e : Nat) : Option Nat :=
  if h : e = 0 then some 1
  else do
    let half ← natPow b (e / 2)
    let sq ← natMul half half
    if e % 2 = 0 then pure sq else natMul sq b
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The product of powers `b ^ e`, when it holds at most `maxBits` bits. -/
def sideValue (fs : List (Nat × Nat)) : Option Nat :=
  fs.foldlM (fun acc f => do natMul acc (← natPow f.1 f.2)) 1

/-- An unevaluated product's value, its numerator and its denominator each within the
bound, or refused. For a unit's scale, held in lowest terms, the refusal is exact. -/
def scaleValue (f : Exact.Product) : Bounded Exact :=
  match sideValue f.num, sideValue f.den with
  | some n, some d => .ok (Exact.of ((n : Rat) / (d : Rat)) f.pi)
  | _, _ => .error tooLarge

/-! ## The functions -/

/-- `unit_scale`, its scale formed within the bound. -/
def unitScaleArg (u : Arg) : Bounded (Except String Exact) :=
  match scaleChecks u with
  | .error r => .ok (.error r)
  | .ok f => (scaleValue f).map .ok

/-- `normalize_measurement`, its scale and its scaled values formed within the bound. -/
def normalizeMeasurementArg (v unc u : Arg) : Bounded (Except String Measurement) :=
  match normalizeChecks v unc u with
  | .error r => .ok (.error r)
  | .ok c => do
    let fe ← scaleValue c.scale
    let x ← ValueBound.mul c.x fe.coef
    let su ← ValueBound.mul c.u fe.coef
    pure (.ok { x := Exact.of x fe.pi, u := Exact.of su fe.pi,
                dimension := Dimension.canon (dimExps c.items), kind := kind c.items })

/-- Two measurements normalized within the bound, then paired as the plain functions pair
them. -/
def pairMeasurements (xa ua unitA xb ub unitB : Arg) :
    Bounded (Outcome (Measurement × Measurement)) := do
  match ← normalizeMeasurementArg xa ua unitA with
  | .error r => pure (.refused r)
  | .ok ma =>
    match ← normalizeMeasurementArg xb ub unitB with
    | .error r => pure (.refused r)
    | .ok mb =>
      pure (if ma.dimension != mb.dimension then .refused (dimensionRefusal ma.dimension mb.dimension)
        else if ma.kind != mb.kind then .convention (kindConvention ma.kind mb.kind)
        else .ok (ma, mb))

/-- SR3's M-M test on two normalized measurements, each value it forms checked first: with
one power of π, the strike rule's bounded test; otherwise the polynomial's coefficients, and
their differences, within the bound. -/
def mmCompare (m1 m2 : Measurement) (k : Rat) (S : Strike.ScaleFactor) :
    Bounded (Option Bool) :=
  let (a1, b1) := m1.coefs
  let (a2, b2) := m2.coefs
  let m := m2.piPower - m1.piPower
  if m = 0 then some <$> Strike.Bounded.mmContradicts a1 b1 a2 b2 k S
  else do
    let c0 ← ValueBound.mul a1 a1
    let t ← ValueBound.mul (-2) a1
    let c1 ← ValueBound.mul t a2
    let c2 ← ValueBound.mul a2 a2
    let kk ← ValueBound.mul k k
    let kks ← ValueBound.mul kk S.square
    let bb1 ← ValueBound.mul b1 b1
    let d0 ← ValueBound.mul kks bb1
    let bb2 ← ValueBound.mul b2 b2
    let d2 ← ValueBound.mul kks bb2
    need (addFits c0 d0 && addFits c1 0 && addFits c2 d2)
    pure (exceedsAtPiPow [c0, c1, c2] [d0, 0, d2] (ratSign k) (b1 != 0 || b2 != 0) m)

/-- SR3's L-M test on two normalized measurements, each value it forms checked first. -/
def lmCompare (mL mM : Measurement) (k : Rat) (S : Strike.ScaleFactor) :
    Bounded (Option Bool) :=
  let aL := mL.x.coef
  let (aM, bM) := mM.coefs
  let m := mM.piPower - mL.piPower
  if m = 0 then some <$> Strike.Bounded.lmContradicts aL aM bM k S
  else do
    let c0 ← ValueBound.mul aL aL
    let t ← ValueBound.mul (-2) aM
    let c1 ← ValueBound.mul t aL
    let c2 ← ValueBound.mul aM aM
    let kk ← ValueBound.mul k k
    let kkb ← ValueBound.mul kk bM
    let kkbb ← ValueBound.mul kkb bM
    let d2 ← ValueBound.mul kkbb S.square
    let kb ← ValueBound.mul k bM
    need (addFits c0 0 && addFits c1 0 && addFits c2 d2)
    pure (exceedsAtPiPow [c0, c1, c2] [0, 0, d2] (ratSign kb) true m)

/-- `mm_contradicts_units` within the bound. -/
def mmContradictsUnitsArg (x1 u1 unit1 x2 u2 unit2 : Arg) (k : Rat)
    (S : Strike.ScaleFactor := .one) : Bounded (Outcome Bool) := do
  match ← pairMeasurements x1 u1 unit1 x2 u2 unit2 with
  | .ok (ma, mb) =>
    match ← mmCompare ma mb k S with
    | some b => pure (.ok b)
    | none => pure (.refused undecided)
  | .convention r => pure (.convention r)
  | .refused r => pure (.refused r)

/-- `lm_contradicts_units` within the bound. -/
def lmContradictsUnitsArg (xL unitL xM uM unitM : Arg) (k : Rat)
    (S : Strike.ScaleFactor := .one) : Bounded (Outcome Bool) := do
  match ← pairMeasurements xL (some "0") unitL xM uM unitM with
  | .ok (mL, mM) =>
    match ← lmCompare mL mM k S with
    | some b => pure (.ok b)
    | none => pure (.refused undecided)
  | .convention r => pure (.convention r)
  | .refused r => pure (.refused r)

/-- The measurements normalized within the bound, in order, as the plain SR8 walks them. -/
def normalizeAll : List (Arg × Arg × Arg) → Option (String × String) → Option String →
    List Measurement → Bounded (Outcome (List Measurement))
  | [], _, conv, acc =>
    pure (match conv with
      | some r => .convention r
      | none => .ok acc.reverse)
  | (x, u, unit) :: rest, dk, conv, acc => do
    match ← normalizeMeasurementArg x u unit with
    | .error r => pure (.refused r)
    | .ok m =>
      match dk with
      | none => normalizeAll rest (some (m.dimension, m.kind)) conv (m :: acc)
      | some (d, k) =>
        if m.dimension != d then pure (.refused (dimensionRefusal d m.dimension))
        else
          let conv := if m.kind != k && conv.isNone then some (kindConvention k m.kind)
            else conv
          normalizeAll rest dk conv (m :: acc)

/-- `sr8_scale_factor_units` within the bound: the measurements normalized, and SR8 over
them, the strike rule's bounded scale factor. -/
def sr8ScaleFactorUnitsArg (ms : List (Arg × Arg × Arg)) : Bounded (Outcome ScaleAnswer) := do
  match ← normalizeAll ms none none [] with
  | .refused r => pure (.refused r)
  | .convention r => pure (.convention r)
  | .ok norm =>
    if norm.any (fun m => m.u.coef ≤ 0) then
      pure (.refused (escape "every M record needs an uncertainty above zero"))
    else
      match norm with
      | [] => pure (.ok (.exact .one))
      | m0 :: _ =>
        if norm.any (·.piPower != m0.piPower) then
          match mixedAnswer norm with
          | .ok a => pure (.ok a)
          | .error r => if r == tooLarge then .error tooLarge else pure (.refused r)
        else
          match ← Strike.Bounded.sr8ScaleFactor (norm.map fun m => ⟨m.x.coef, m.u.coef⟩) with
          | some S => pure (.ok (.exact S))
          | none => pure (.refused (escape "every M record needs an uncertainty above zero"))

/-! ## PROVED: an answer is the plain function's -/

theorem natMul_ok {x y z : Nat} (h : natMul x y = some z) : z = x * y := by
  unfold natMul at h
  split at h
  · dsimp only at h
    split at h
    · cases h; rfl
    · cases h
  · cases h

theorem natPow_ok (b : Nat) : ∀ (e : Nat) {r : Nat}, natPow b e = some r → r = b ^ e := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro r h
    rw [natPow] at h
    split at h
    · rename_i he; cases h; rw [he]; rfl
    · rename_i he
      cases hh : natPow b (e / 2) with
      | none => rw [hh] at h; cases h
      | some half =>
        rw [hh] at h
        change (natMul half half >>= fun sq =>
          if e % 2 = 0 then pure sq else natMul sq b) = some r at h
        have hhalf := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)) hh
        cases hs : natMul half half with
        | none => rw [hs] at h; cases h
        | some sq =>
          rw [hs] at h
          have hsq := natMul_ok hs
          have hdiv := Nat.div_add_mod e 2
          split at h
          · rename_i hev
            cases h
            rw [hsq, hhalf, ← Nat.pow_add]
            congr 1
            omega
          · rename_i hod
            have hr := natMul_ok h
            rw [hr, hsq, hhalf, ← Nat.pow_add, ← Nat.pow_succ]
            congr 1
            omega

/-- The plain product of powers, as `Exact.Product.value` forms each side. -/
def plainSide (fs : List (Nat × Nat)) : Nat := fs.foldl (fun acc f => acc * f.1 ^ f.2) 1

theorem value_eq (f : Exact.Product) :
    f.value = Exact.of ((plainSide f.num : Rat) / (plainSide f.den : Rat)) f.pi := rfl

theorem sideValue_go : ∀ (fs : List (Nat × Nat)) (acc r : Nat),
    fs.foldlM (fun acc f => do natMul acc (← natPow f.1 f.2)) acc = some r →
      r = fs.foldl (fun acc f => acc * f.1 ^ f.2) acc
  | [], acc, r, h => by
    simp only [List.foldlM_nil] at h
    cases h; rfl
  | f :: fs, acc, r, h => by
    simp only [List.foldlM_cons] at h
    cases hp : natPow f.1 f.2 with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      change (natMul acc p >>= fun a => fs.foldlM _ a) = some r at h
      cases hm : natMul acc p with
      | none => rw [hm] at h; cases h
      | some a =>
        rw [hm] at h
        rw [sideValue_go fs a r h, List.foldl_cons, natMul_ok hm, natPow_ok _ _ hp]

theorem sideValue_ok {fs : List (Nat × Nat)} {r : Nat} (h : sideValue fs = some r) :
    r = plainSide fs := sideValue_go fs 1 r h

theorem scaleValue_ok {f : Exact.Product} {x : Exact} (h : scaleValue f = .ok x) :
    x = f.value := by
  unfold scaleValue at h
  rw [value_eq]
  split at h
  · rename_i n d hn hd
    cases h
    rw [sideValue_ok hn, sideValue_ok hd]
  · cases h

theorem unitScaleArg_ok {u : Arg} {r : Except String Exact} (h : unitScaleArg u = .ok r) :
    r = Units.unitScaleArg u := by
  unfold unitScaleArg at h
  unfold Units.unitScaleArg
  split at h
  · rename_i e he; cases h; rw [he]; rfl
  · rename_i f hf
    rw [hf]
    cases hv : scaleValue f with
    | error e => rw [hv] at h; cases h
    | ok x =>
      rw [hv] at h; cases h
      rw [scaleValue_ok hv]; rfl

theorem normalizeMeasurementArg_ok {v unc u : Arg} {r : Except String Measurement}
    (h : normalizeMeasurementArg v unc u = .ok r) : r = Units.normalizeMeasurementArg v unc u := by
  unfold normalizeMeasurementArg at h
  unfold Units.normalizeMeasurementArg
  split at h
  · rename_i e he; cases h; rw [he]; rfl
  · rename_i c hc
    rw [hc]
    obtain ⟨fe, hfe, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨su, hsu, h⟩ := bind_ok h
    cases h
    have hfe' := scaleValue_ok hfe
    subst hfe'
    rw [ValueBound.mul_ok hx, ValueBound.mul_ok hsu]
    rfl

theorem pairMeasurements_ok {xa ua unitA xb ub unitB : Arg}
    {r : Outcome (Measurement × Measurement)}
    (h : pairMeasurements xa ua unitA xb ub unitB = .ok r) :
    r = Units.pairMeasurements xa ua unitA xb ub unitB := by
  unfold pairMeasurements at h
  unfold Units.pairMeasurements
  obtain ⟨na, hna, h⟩ := bind_ok h
  rw [← normalizeMeasurementArg_ok hna]
  cases na with
  | error e => cases h; rfl
  | ok ma =>
    obtain ⟨nb, hnb, h⟩ := bind_ok h
    rw [← normalizeMeasurementArg_ok hnb]
    cases nb with
    | error e => cases h; rfl
    | ok mb => cases h; rfl

theorem mmCompare_ok {m1 m2 : Measurement} {k : Rat} {S : Strike.ScaleFactor} {r : Option Bool}
    (h : mmCompare m1 m2 k S = .ok r) : r = Units.mmCompare m1 m2 k S := by
  unfold mmCompare at h
  unfold Units.mmCompare
  simp only [Measurement.coefs] at h ⊢
  split at h
  · rename_i hm
    rw [ite_eq_left hm]
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases h
    rw [Strike.Bounded.mmContradicts_ok hb]
  · rename_i hm
    rw [ite_eq_right hm]
    obtain ⟨c0, hc0, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨c1, hc1, h⟩ := bind_ok h
    obtain ⟨c2, hc2, h⟩ := bind_ok h
    obtain ⟨kk, hkk, h⟩ := bind_ok h
    obtain ⟨kks, hkks, h⟩ := bind_ok h
    obtain ⟨bb1, hbb1, h⟩ := bind_ok h
    obtain ⟨d0, hd0, h⟩ := bind_ok h
    obtain ⟨bb2, hbb2, h⟩ := bind_ok h
    obtain ⟨d2, hd2, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h
    rw [ValueBound.mul_ok hc0, ValueBound.mul_ok hc1, ValueBound.mul_ok ht, ValueBound.mul_ok hc2,
      ValueBound.mul_ok hd0, ValueBound.mul_ok hd2, ValueBound.mul_ok hkks, ValueBound.mul_ok hkk,
      ValueBound.mul_ok hbb1, ValueBound.mul_ok hbb2]

theorem lmCompare_ok {mL mM : Measurement} {k : Rat} {S : Strike.ScaleFactor} {r : Option Bool}
    (h : lmCompare mL mM k S = .ok r) : r = Units.lmCompare mL mM k S := by
  unfold lmCompare at h
  unfold Units.lmCompare
  simp only [Measurement.coefs] at h ⊢
  split at h
  · rename_i hm
    rw [ite_eq_left hm]
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases h
    rw [Strike.Bounded.lmContradicts_ok hb]
  · rename_i hm
    rw [ite_eq_right hm]
    obtain ⟨c0, hc0, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨c1, hc1, h⟩ := bind_ok h
    obtain ⟨c2, hc2, h⟩ := bind_ok h
    obtain ⟨kk, hkk, h⟩ := bind_ok h
    obtain ⟨kkb, hkkb, h⟩ := bind_ok h
    obtain ⟨kkbb, hkkbb, h⟩ := bind_ok h
    obtain ⟨d2, hd2, h⟩ := bind_ok h
    obtain ⟨kb, hkb, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    cases h
    rw [ValueBound.mul_ok hc0, ValueBound.mul_ok hc1, ValueBound.mul_ok ht, ValueBound.mul_ok hc2,
      ValueBound.mul_ok hd2, ValueBound.mul_ok hkkbb, ValueBound.mul_ok hkkb, ValueBound.mul_ok hkk,
      ValueBound.mul_ok hkb]

theorem mmContradictsUnitsArg_ok {x1 u1 unit1 x2 u2 unit2 : Arg} {k : Rat}
    {S : Strike.ScaleFactor} {r : Outcome Bool}
    (h : mmContradictsUnitsArg x1 u1 unit1 x2 u2 unit2 k S = .ok r) :
    r = Units.mmContradictsUnitsArg x1 u1 unit1 x2 u2 unit2 k S := by
  unfold mmContradictsUnitsArg at h
  unfold Units.mmContradictsUnitsArg
  obtain ⟨p, hp, h⟩ := bind_ok h
  rw [← pairMeasurements_ok hp]
  cases p with
  | ok mm =>
    obtain ⟨ma, mb⟩ := mm
    obtain ⟨c, hc, h⟩ := bind_ok h
    dsimp only
    rw [← mmCompare_ok hc]
    cases c with
    | some b => cases h; rfl
    | none => cases h; rfl
  | convention e => cases h; rfl
  | refused e => cases h; rfl

theorem lmContradictsUnitsArg_ok {xL unitL xM uM unitM : Arg} {k : Rat}
    {S : Strike.ScaleFactor} {r : Outcome Bool}
    (h : lmContradictsUnitsArg xL unitL xM uM unitM k S = .ok r) :
    r = Units.lmContradictsUnitsArg xL unitL xM uM unitM k S := by
  unfold lmContradictsUnitsArg at h
  unfold Units.lmContradictsUnitsArg
  obtain ⟨p, hp, h⟩ := bind_ok h
  rw [← pairMeasurements_ok hp]
  cases p with
  | ok mm =>
    obtain ⟨ma, mb⟩ := mm
    obtain ⟨c, hc, h⟩ := bind_ok h
    dsimp only
    rw [← lmCompare_ok hc]
    cases c with
    | some b => cases h; rfl
    | none => cases h; rfl
  | convention e => cases h; rfl
  | refused e => cases h; rfl

theorem normalizeAll_ok : ∀ (ms : List (Arg × Arg × Arg)) (dk : Option (String × String))
    (conv : Option String) (acc : List Measurement) {r : Outcome (List Measurement)},
    normalizeAll ms dk conv acc = .ok r → r = Units.sr8ScaleFactorUnitsArg.go ms dk conv acc
  | [], dk, conv, acc, r, h => by
    unfold normalizeAll at h
    cases h
    unfold Units.sr8ScaleFactorUnitsArg.go
    rfl
  | (x, u, unit) :: rest, dk, conv, acc, r, h => by
    unfold normalizeAll at h
    unfold Units.sr8ScaleFactorUnitsArg.go
    obtain ⟨n, hn, h⟩ := bind_ok h
    rw [← normalizeMeasurementArg_ok hn]
    cases n with
    | error e => cases h; rfl
    | ok m =>
      dsimp only
      cases dk with
      | none => exact normalizeAll_ok rest _ conv _ h
      | some p =>
        obtain ⟨d, k⟩ := p
        dsimp only at h ⊢
        split at h
        · rename_i hd; rw [ite_eq_left hd]; cases h; rfl
        · rename_i hd; rw [ite_eq_right hd]; exact normalizeAll_ok rest _ _ _ h

theorem sr8ScaleFactorUnitsArg_ok {ms : List (Arg × Arg × Arg)} {r : Outcome ScaleAnswer}
    (h : sr8ScaleFactorUnitsArg ms = .ok r) : r = Units.sr8ScaleFactorUnitsArg ms := by
  unfold sr8ScaleFactorUnitsArg at h
  unfold Units.sr8ScaleFactorUnitsArg
  obtain ⟨n, hn, h⟩ := bind_ok h
  rw [← normalizeAll_ok ms none none [] hn]
  cases n with
  | refused e => cases h; rfl
  | convention e => cases h; rfl
  | ok norm =>
    dsimp only at h ⊢
    split at h
    · rename_i hu; rw [ite_eq_left hu]; cases h; rfl
    · rename_i hu
      rw [ite_eq_right hu]
      cases norm with
      | nil => cases h; rfl
      | cons m0 rest =>
        dsimp only at h ⊢
        split at h
        · rename_i hp
          rw [ite_eq_left hp]
          cases hm : mixedAnswer (m0 :: rest) with
          | ok a => rw [hm] at h; cases h; rfl
          | error e =>
            rw [hm] at h
            dsimp only at h ⊢
            split at h
            · cases h
            · cases h; rfl
        · rename_i hp
          rw [ite_eq_right hp]
          obtain ⟨s, hs, h⟩ := bind_ok h
          rw [← Strike.Bounded.sr8ScaleFactor_ok hs]
          cases s with
          | some S => cases h; rfl
          | none => cases h; rfl

end Principia.Units.Bounded
