import Principia.Yardstick
import Principia.Record.Bounded

/-!
# The yardsticks' numbers within the bound on an exact value

A yardstick's key forms numbers from its arguments: each weight is a Criteria Set constant's
VALUE and each U_C a field-table cell, read as decimals; a record's steps are a count; and a
weighted sum forms each product `w * x` and each running sum (`Yardstick.Acc.add`). Here each
of them is checked against the bound on an exact value's size (`Principia.ValueBound`)
before it is formed, and refused "exact value too large" when it could cross it:

* every constant's VALUE and every U_C cell that reads as a decimal is read through
  `Record.Bounded.decimalWithin` before the Criteria Set is compiled, and every record's steps
  must lie within the bound (`inputsWithin`);
* each product and running sum of a weighted sum goes through `ValueBound.mul` and
  `ValueBound.add` (`bodyAcc`);
* `yardstickChecks` and `yardstickHarness` evaluate, before the checks run, every key the
  checks evaluate (`Yardstick.evaluated`, in v1's order) through the checked arithmetic, so
  the checks then recompute only values already known to lie within the bound.

`overflows`, version 1's double overflow, is kept: it is version 1's own refusal, apart from
the bound. When a checked function answers, it answers what the plain one does
(`yardstickKey_ok`, `yardstickChecks_ok`, `yardstickHarness_ok`), whose theorems therefore
hold of every answer given.
-/

namespace Principia.Yardstick.Bounded

open Principia.Zone
open Principia.Strike.SR9
open Principia.ValueBound (Bounded tooLarge)

/-! ## The inputs -/

/-- A decimal text within the bound; a text that is not a decimal forms no value here. -/
def textWithin (s : String) : Bounded Unit :=
  match Decimal.readParts s.toList with
  | none => .ok ()
  | some p => do
    let _ ← Record.Bounded.decimalWithin p
    pure ()

/-- Every constant's VALUE, every U_C cell and every record's steps within the bound. -/
def inputsWithin (tms : Value) (recs : SuiteRecords) : Bounded Unit := do
  for (_, v) in constants tms do
    textWithin v
  for (_, r) in recs do
    for (k, c) in r.fields do
      if k == "U_C" then textWithin c
    unless ValueBound.within (r.steps : Rat) do throw tooLarge

/-! ## The arithmetic of a weighted sum -/

/-- `Acc.add`, the product and the sum each checked first. -/
def accAdd (acc : Acc) (w x : Rat) : Bounded Acc := do
  let p ← ValueBound.mul w x
  let s ← ValueBound.add acc.value p
  pure ⟨s, acc.over || overflows x || overflows p || overflows s⟩

/-- `Body.acc`, each step checked. -/
def bodyAcc : Body → (Atom → Rat) → Bounded Acc
  | .atom x, val => pure ⟨val x, overflows (val x)⟩
  | .wsum parts, val => parts.foldlM (fun acc p => accAdd acc p.1 (val p.2)) ⟨0, false⟩

/-- `termValue`, its sum checked: the bound's refusal outside, version 1's stop inside. -/
def termValueB (rid : String) (v : View) (t : Term) : Bounded (Except Stop Rat) :=
  match t.body.atoms.mapM (atomValue rid v) with
  | .error e => .ok (.error e)
  | .ok _ => do
    let acc ← bodyAcc t.body (valuation rid v)
    if acc.over then pure (.error (.refused "a yardstick value is not finite"))
    else pure (.ok (if t.neg then -acc.value else acc.value))

/-- The values of a list of terms, the first stop ending them. -/
def termsValueB (rid : String) (v : View) : List Term → Bounded (Except Stop (List Rat))
  | [] => .ok (.ok [])
  | t :: ts => do
    match ← termValueB rid v t with
    | .error e => pure (.error e)
    | .ok q => do
      match ← termsValueB rid v ts with
      | .error e => pure (.error e)
      | .ok qs => pure (.ok (q :: qs))

/-- `keyOf`, checked. -/
def keyOfB (y : Compiled) (rid : String) (recs : SuiteRecords) (tfk : List String) :
    Bounded (Except Stop (List Rat)) :=
  match recs.lookup rid with
  | none => .ok (.error .raised)
  | some r =>
    match termsFor y rid r.domain with
    | .error e => .ok (.error e)
    | .ok terms => termsValueB rid ⟨r.sr1Fail, aOf rid recs tfk, r.steps, uCOf r⟩ terms

/-! ## The functions -/

/-- `yardstickKey` within the bound. -/
def yardstickKey (units : UnitHook) (tms : Value) (name rid : String) (recs : SuiteRecords)
    (tfk : List String) (table : List (String × List (String × String))) :
    Bounded (Option (Outcome (List Rat))) := do
  inputsWithin tms (placed recs table)
  match compile units tms name with
  | .error e => pure (Outcome.of (.error e))
  | .ok y => Outcome.of <$> keyOfB y rid (placed recs table) tfk

/-- Every input, and every key the checks evaluate, within the bound. -/
def preEvaluate (units : UnitHook) (tms : Value) (name : String) (s : Suite) : Bounded Unit := do
  inputsWithin tms s.records
  match compile units tms name with
  | .error _ => pure ()
  | .ok y =>
    for (rid, recs) in evaluated s do
      let _ ← keyOfB y rid recs s.assembly

/-- `yardstickChecks` within the bound: every key the checks evaluate, first. -/
def yardstickChecks (units : UnitHook) (tms : Value) (name : String) (s : Suite)
    (table : List (String × List (String × String))) : Bounded (Option (Outcome Checks)) :=
  preEvaluate units tms name { s with records := placed s.records table } >>= fun _ =>
    pure (Yardstick.yardstickChecks units tms name s table)

/-- `yardstickHarness` within the bound. -/
def yardstickHarness (units : UnitHook) (tms : Value) (name : String) (s : Suite)
    (table : List (String × List (String × String))) :
    Bounded (Option (Outcome (Bool × Bool × Bool × Nat))) := do
  let _ ← yardstickChecks units tms name s table
  pure (Yardstick.yardstickHarness units tms name s table)

/-! ## PROVED: an answer is the plain function's -/

theorem bind_ok {α β : Type} {x : Bounded α} {f : α → Bounded β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem accAdd_ok {acc a : Acc} {w x : Rat} (h : accAdd acc w x = .ok a) :
    a = acc.add w x := by
  unfold accAdd at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  cases h
  rw [ValueBound.add_ok hs, ValueBound.mul_ok hp]
  rfl

theorem foldlM_accAdd_ok (val : Atom → Rat) :
    ∀ (parts : List (Rat × Atom)) (acc a : Acc),
      parts.foldlM (fun acc p => accAdd acc p.1 (val p.2)) acc = .ok a →
        a = parts.foldl (fun acc p => acc.add p.1 (val p.2)) acc
  | [], acc, a, h => by
    simp only [List.foldlM_nil] at h
    cases h; rfl
  | p :: ps, acc, a, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := bind_ok h
    rw [List.foldl_cons, ← accAdd_ok h1]
    exact foldlM_accAdd_ok val ps acc1 a h

theorem bodyAcc_ok {b : Body} {val : Atom → Rat} {a : Acc} (h : bodyAcc b val = .ok a) :
    a = b.acc val := by
  cases b with
  | atom x => unfold bodyAcc at h; cases h; rfl
  | wsum parts =>
    unfold bodyAcc at h
    simp only [Body.acc]
    exact foldlM_accAdd_ok val parts _ a h

theorem termValueB_ok {rid : String} {v : View} {t : Term} {r : Except Stop Rat}
    (h : termValueB rid v t = .ok r) : r = termValue rid v t := by
  unfold termValueB at h
  unfold termValue
  cases hm : t.body.atoms.mapM (atomValue rid v) with
  | error e =>
    rw [hm] at h; cases h
    simp [bind, Except.bind]
  | ok xs =>
    rw [hm] at h
    obtain ⟨acc, hacc, h⟩ := bind_ok h
    have ha := bodyAcc_ok hacc
    subst ha
    simp only [bind, Except.bind]
    split at h
    · rename_i hover
      cases h
      simp [hover, throw, throwThe, MonadExceptOf.throw]
    · rename_i hover
      cases h
      simp [hover, pure, Except.pure]

theorem termsValueB_ok {rid : String} {v : View} :
    ∀ {ts : List Term} {r : Except Stop (List Rat)},
      termsValueB rid v ts = .ok r → r = ts.mapM (termValue rid v)
  | [], r, h => by unfold termsValueB at h; cases h; rfl
  | t :: ts, r, h => by
    unfold termsValueB at h
    obtain ⟨q, hq, h⟩ := bind_ok h
    have hq' := termValueB_ok hq
    rw [List.mapM_cons, ← hq']
    cases q with
    | error e => cases h; rfl
    | ok q =>
      simp only at h
      obtain ⟨qs, hqs, h⟩ := bind_ok h
      have hqs' := termsValueB_ok hqs
      rw [← hqs']
      cases qs with
      | error e => cases h; rfl
      | ok qs => cases h; rfl

theorem keyOfB_ok {y : Compiled} {rid : String} {recs : SuiteRecords} {tfk : List String}
    {r : Except Stop (List Rat)} (h : keyOfB y rid recs tfk = .ok r) :
    r = keyOf y rid recs tfk := by
  unfold keyOfB at h
  unfold keyOf keyOfView
  cases hl : recs.lookup rid with
  | none =>
    rw [hl] at h; cases h
    simp [throw, throwThe, MonadExceptOf.throw]
  | some rec =>
    rw [hl] at h
    simp only at h
    simp only [bind, Except.bind]
    cases ht : termsFor y rid rec.domain with
    | error e => rw [ht] at h; cases h; rfl
    | ok terms => rw [ht] at h; exact termsValueB_ok h

/-- A key answered within the bound is the plain function's. -/
theorem yardstickKey_ok {units : UnitHook} {tms : Value} {name rid : String}
    {recs : SuiteRecords} {tfk : List String} {table : List (String × List (String × String))}
    {r : Option (Outcome (List Rat))}
    (h : yardstickKey units tms name rid recs tfk table = .ok r) :
    r = Yardstick.yardstickKey units tms name rid recs tfk table := by
  unfold yardstickKey at h
  unfold Yardstick.yardstickKey
  obtain ⟨_, -, h⟩ := bind_ok h
  cases hc : compile units tms name with
  | error e =>
    rw [hc] at h; cases h
    simp [bind, Except.bind]
  | ok y =>
    rw [hc] at h
    simp only at h
    simp only [bind, Except.bind]
    cases hk : keyOfB y rid (placed recs table) tfk with
    | error e => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases h
      rw [keyOfB_ok hk]

/-- The checks answered within the bound are the plain function's. -/
theorem yardstickChecks_ok {units : UnitHook} {tms : Value} {name : String} {s : Suite}
    {table : List (String × List (String × String))} {r : Option (Outcome Checks)}
    (h : yardstickChecks units tms name s table = .ok r) :
    r = Yardstick.yardstickChecks units tms name s table := by
  unfold yardstickChecks at h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  rfl

/-- The harness answered within the bound is the plain function's. -/
theorem yardstickHarness_ok {units : UnitHook} {tms : Value} {name : String} {s : Suite}
    {table : List (String × List (String × String))}
    {r : Option (Outcome (Bool × Bool × Bool × Nat))}
    (h : yardstickHarness units tms name s table = .ok r) :
    r = Yardstick.yardstickHarness units tms name s table := by
  unfold yardstickHarness at h
  obtain ⟨_, -, h⟩ := bind_ok h
  cases h
  rfl

end Principia.Yardstick.Bounded
