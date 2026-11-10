import Principia.Wire

/-!
# DERIVATION and DERIVATION_CLASS

The Research Assembly's rule for a RESULT's DERIVATION is one of three forms from the
first schema, and Custos writes DERIVATION_CLASS, the class of the highest form
the deployed Calculator build verified. An unchecked form earns nothing: a form
the Calculator build cannot check lands as PROSE with an attachment (a lower form), and
a form it did not verify is credited as PROSE.

| Form (wire)  | Lean          | Payload                                             | Class (wire) |
|--------------|---------------|-----------------------------------------------------|--------------|
| `PROSE`      | `prose`       | step count and steps as text (v1), an attachment    | `INSPECTION` |
| `STRUCTURED` | `structured`  | rewrite steps, each citing a law or an ASSUMPTION   | `MECHANICAL` |
| `KERNEL`     | `kernelProof` | a Lean proof in export format, opaque text          | `PROVED`     |

The Lean name of the KERNEL form is a two-word compound (rule R2; the proof is
one the Lean kernel checks). The credit is a function of the derivation and a
checker's verdict on it. The STRUCTURED step language and its checker are
`Principia.StructuredCheck`, and `Principia.StructuredCredit` supplies the verdict
the credit reads; KERNEL checking follows T5. This file fixes the forms, their
order, the classes, the attachment and the credit rule.
-/

namespace Principia.Record

/-- DERIVATION's form (the Research Assembly's rule for a DERIVATION). Ordered PROSE < STRUCTURED < KERNEL, the
order of what a checker can establish. -/
inductive DerivationForm where
  /-- `PROSE`: the exhibited steps as text, with a step count (v1's form). -/
  | prose
  /-- `STRUCTURED`: rewrite steps in the declared-form grammar. -/
  | structured
  /-- `KERNEL`: a Lean proof in export format whose statement is the record's
  EQUATION over the Research Assembly's laws as hypotheses. -/
  | kernelProof
  deriving DecidableEq, Repr, Inhabited

/-- DERIVATION_CLASS: the check class credited to a derivation (the Research Assembly's rule for a
DERIVATION). Ordered INSPECTION < MECHANICAL < PROVED. -/
inductive DerivationClass where
  /-- `INSPECTION`: a person or an agent reads it. -/
  | inspection
  /-- `MECHANICAL`: the Calculator executed a check. -/
  | mechanical
  /-- `PROVED`: a property the Lean kernel has checked. -/
  | proved
  deriving DecidableEq, Repr, Inhabited

instance : WireWord DerivationForm where
  members := [.prose, .structured, .kernelProof]
  toWire
    | .prose => "PROSE"
    | .structured => "STRUCTURED"
    | .kernelProof => "KERNEL"
  read_toWire a := by cases a <;> decide

instance : WireWord DerivationClass where
  members := [.inspection, .mechanical, .proved]
  toWire
    | .inspection => "INSPECTION"
    | .mechanical => "MECHANICAL"
    | .proved => "PROVED"
  read_toWire a := by cases a <;> decide

/-! ## The orders -/

namespace DerivationClass

/-- Position in the order INSPECTION < MECHANICAL < PROVED. -/
def rank : DerivationClass → Nat
  | inspection => 0
  | mechanical => 1
  | proved => 2

instance : LE DerivationClass := ⟨fun a b => a.rank ≤ b.rank⟩
instance : LT DerivationClass := ⟨fun a b => a.rank < b.rank⟩

instance (a b : DerivationClass) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))
instance (a b : DerivationClass) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.rank < b.rank))

theorem le_refl (a : DerivationClass) : a ≤ a := by
  cases a <;> decide

theorem le_trans {a b c : DerivationClass} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

theorem le_antisymm {a b : DerivationClass} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  have h : a.rank = b.rank := Nat.le_antisymm hab hba
  cases a <;> cases b <;> first | rfl | simp [rank] at h

/-- The order is total: any two classes compare. -/
theorem le_total (a b : DerivationClass) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.rank b.rank

instance : Std.IsPreorder DerivationClass where
  le_refl := le_refl
  le_trans _ _ _ := le_trans

instance : Std.IsPartialOrder DerivationClass where
  le_antisymm _ _ := le_antisymm

instance : Std.IsLinearOrder DerivationClass where
  le_total := le_total

/-- INSPECTION is the least class. -/
theorem inspection_le (a : DerivationClass) : inspection ≤ a := by
  cases a <;> decide

/-- PROVED is the greatest class. -/
theorem le_proved (a : DerivationClass) : a ≤ proved := by
  cases a <;> decide

end DerivationClass

namespace DerivationForm

/-- Position in the order PROSE < STRUCTURED < KERNEL. -/
def rank : DerivationForm → Nat
  | prose => 0
  | structured => 1
  | kernelProof => 2

instance : LE DerivationForm := ⟨fun a b => a.rank ≤ b.rank⟩
instance : LT DerivationForm := ⟨fun a b => a.rank < b.rank⟩

instance (a b : DerivationForm) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.rank ≤ b.rank))
instance (a b : DerivationForm) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.rank < b.rank))

theorem le_refl (a : DerivationForm) : a ≤ a := by
  cases a <;> decide

theorem le_trans {a b c : DerivationForm} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

theorem le_antisymm {a b : DerivationForm} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  have h : a.rank = b.rank := Nat.le_antisymm hab hba
  cases a <;> cases b <;> first | rfl | simp [rank] at h

/-- The order is total: any two forms compare. -/
theorem le_total (a b : DerivationForm) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.rank b.rank

instance : Std.IsPreorder DerivationForm where
  le_refl := le_refl
  le_trans _ _ _ := le_trans

instance : Std.IsPartialOrder DerivationForm where
  le_antisymm _ _ := le_antisymm

instance : Std.IsLinearOrder DerivationForm where
  le_total := le_total

/-- PROSE is the least form. -/
theorem prose_le (a : DerivationForm) : prose ≤ a := by
  cases a <;> decide

/-- The check class a form earns once verified: PROSE INSPECTION, STRUCTURED
MECHANICAL, KERNEL PROVED. -/
def checkClass : DerivationForm → DerivationClass
  | prose => .inspection
  | structured => .mechanical
  | kernelProof => .proved

/-- `checkClass` is an order isomorphism: it preserves and reflects the order. -/
theorem checkClass_le_iff (a b : DerivationForm) :
    a.checkClass ≤ b.checkClass ↔ a ≤ b := by
  cases a <;> cases b <;> decide

/-- No two forms earn one class. -/
theorem checkClass_injective {a b : DerivationForm} (h : a.checkClass = b.checkClass) :
    a = b := by
  cases a <;> cases b <;> simp_all [checkClass]

/-- Every class is earned by some form. -/
theorem checkClass_surjective (c : DerivationClass) : ∃ f : DerivationForm, f.checkClass = c := by
  cases c
  · exact ⟨prose, rfl⟩
  · exact ⟨structured, rfl⟩
  · exact ⟨kernelProof, rfl⟩

end DerivationForm


/-! ## The derivation -/

/-- What a STRUCTURED step cites (the Research Assembly's rule: "each citing a law of the
Starting Set or an ASSUMPTION record"). -/
inductive StepCitation where
  /-- `LAW`: a law of the Starting Set, by its NAME. -/
  | law (name : String)
  /-- `ASSUMPTION`: an ASSUMPTION record of the register, by its identifier. -/
  | assumption (recordId : String)
  /-- `IDENTITY`: one identity of the Calculator's fixed list, by its name
  (`Principia.StructuredCheck.Identity`). Such a step cites no law or record:
  algebra (section 7, question 5 (c) of the record types' design note). -/
  | identity (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- One rewrite step of a STRUCTURED derivation. -/
structure StructuredStep where
  /-- The step's result: an EQUATION in the declared-form grammar, read by
  `Principia.StructuredCheck.readStep`. -/
  equation : String
  /-- The law, ASSUMPTION record or identity the step rests on. -/
  cites : StepCitation
  /-- Where the step rewrites: the side, `lhs` or `rhs`, then the path to the
  subterm, `l`, `r` (an operator's operands) and `a` (the operand of a minus
  sign, a function or a power's base) joined by dots, as `rhs.l.a`. Empty when
  the record does not say, which the checker refuses. -/
  site : String := ""
  /-- Whether the cited law or identity is applied left to right. -/
  forward : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Where a STRUCTURED derivation starts (section 10 of the record types' design note).
A payload that names no start starts from `e = e` for the RESULT's EQUATION's left side
`e`; one that names a law or an ASSUMPTION record starts from its EQUATION; one that
names an expression `e` starts from `e = e`. -/
inductive StructuredStart where
  /-- `e = e` for the RESULT's EQUATION's left side `e`: the payload names no start. -/
  | lhs
  /-- `LAW`: a law of the Starting Set, by its NAME; the derivation starts from its
  EQUATION. -/
  | law (name : String)
  /-- `ASSUMPTION`: an ASSUMPTION record, by its identifier; the derivation starts from
  its EQUATION. -/
  | assumption (recordId : String)
  /-- `EXPRESSION`: `e = e` for an expression `e` the record states in the declared-form
  grammar, read by `Principia.StructuredCheck.readStart`. -/
  | refl (expression : String)
  deriving DecidableEq, Repr, Inhabited

/-- A STRUCTURED or KERNEL payload carried beside PROSE (the Research Assembly's rule: a
form the Calculator build cannot check, or a proof it does not check, "lands as
PROSE with an attachment, never as checked"). An attachment is credited nothing:
the derivation it rides on is PROSE. -/
inductive Attachment where
  /-- A STRUCTURED payload: rewrite steps in order, from its start. -/
  | structured (steps : List StructuredStep) (start : StructuredStart)
  /-- A KERNEL payload: a proof in Lean's export format, opaque text. -/
  | kernelProof (exportText : String)
  deriving DecidableEq, Repr, Inhabited

/-- The form an attachment is written in. -/
def Attachment.form : Attachment → DerivationForm
  | .structured .. => .structured
  | .kernelProof .. => .kernelProof

/-- DERIVATION: the three-form sum. The table's bounds on each
payload (PROSE's step count from 1 to 1000000 and its text not blank, v1's
STEPS and NOTBLANK) are record_check's, ported with it. -/
inductive Derivation where
  /-- PROSE: v1's {STEPS, TEXT}, the step count under the STEP CONVENTION and the
  exhibited steps, with an optional attachment that earns nothing. -/
  | prose (steps : Nat) (text : String) (attachment : Option Attachment)
  /-- STRUCTURED: the rewrite steps in order, from its start. -/
  | structured (steps : List StructuredStep) (start : StructuredStart)
  /-- KERNEL: the proof in Lean's export format, opaque text until the KERNEL
  checker is chosen (after T5). -/
  | kernelProof (exportText : String)
  deriving DecidableEq, Repr, Inhabited

/-- The form a derivation is written in; PROSE with an attachment is PROSE. -/
def Derivation.form : Derivation → DerivationForm
  | .prose .. => .prose
  | .structured .. => .structured
  | .kernelProof .. => .kernelProof

/-! ## The credit

The credit is a function of the derivation and of a checker's verdict on that
derivation. A checker is `check : Derivation → Bool`, the deployed Calculator
build's verdict, produced inside the Calculator and never taken from the party
that pushed the record. The credit reads the verdict on the derivation it credits
and on nothing else (`Derivation.creditedClass_congr`), and only for a form that
has a checker: PROSE has none. -/

namespace DerivationForm

/-- The form credited to a form given a verdict on it: the form itself when
verified, PROSE otherwise. A helper of `Derivation.creditedForm`, which supplies
the verdict. -/
def credit (form : DerivationForm) (verified : Bool) : DerivationForm :=
  if verified then form else .prose

theorem credit_false (form : DerivationForm) : form.credit false = .prose := rfl

theorem credit_true (form : DerivationForm) : form.credit true = form := rfl

/-- A form's credit never exceeds the form. -/
theorem credit_le (form : DerivationForm) (verified : Bool) :
    form.credit verified ≤ form := by
  cases form <;> cases verified <;> decide

end DerivationForm

namespace Derivation

/-- The verdict the credit reads: the checker's verdict on this derivation, for a
form that has a checker. A PROSE derivation, attachment or not, is never
verified. -/
def verified (check : Derivation → Bool) (d : Derivation) : Bool :=
  d.form != .prose && check d

/-- The form credited to the derivation: its own form when the checker verified
it, PROSE otherwise. -/
def creditedForm (check : Derivation → Bool) (d : Derivation) : DerivationForm :=
  d.form.credit (d.verified check)

/-- DERIVATION_CLASS as Custos writes it: the check class of the credited form,
INSPECTION for PROSE, MECHANICAL for STRUCTURED, PROVED for KERNEL. -/
def creditedClass (check : Derivation → Bool) (d : Derivation) : DerivationClass :=
  (d.creditedForm check).checkClass

/-- The credit reads the checker's verdict on this derivation alone: two checkers
that agree on it credit it alike, whatever they say of any other derivation. -/
theorem creditedClass_congr {check check' : Derivation → Bool} (d : Derivation)
    (h : check d = check' d) : d.creditedClass check = d.creditedClass check' := by
  simp [creditedClass, creditedForm, verified, h]

/-- An unchecked form earns nothing: when the checker does not verify the
derivation, the credit is INSPECTION, whatever form it is written in. -/
theorem creditedClass_of_check_false (check : Derivation → Bool) (d : Derivation)
    (h : check d = false) : d.creditedClass check = .inspection := by
  simp [creditedClass, creditedForm, verified, h, DerivationForm.credit,
    DerivationForm.checkClass]

/-- A verified derivation earns its own form's class. -/
theorem creditedClass_of_check_true (check : Derivation → Bool) (d : Derivation)
    (h : check d = true) : d.creditedClass check = d.form.checkClass := by
  cases d <;> simp [creditedClass, creditedForm, verified, h, form,
    DerivationForm.credit]

/-- The credit never exceeds the class of the form the derivation is written
in. -/
theorem creditedClass_le_checkClass (check : Derivation → Bool) (d : Derivation) :
    d.creditedClass check ≤ d.form.checkClass :=
  (DerivationForm.checkClass_le_iff _ _).mpr (DerivationForm.credit_le _ _)

/-- Any credit above INSPECTION was checked: the checker verified this
derivation, and the credit is its own form's class. -/
theorem verified_of_inspection_lt (check : Derivation → Bool) (d : Derivation)
    (h : DerivationClass.inspection < d.creditedClass check) :
    check d = true ∧ d.creditedClass check = d.form.checkClass := by
  have key : ∀ (f : DerivationForm) (c : Bool),
      DerivationClass.inspection < (f.credit (f != .prose && c)).checkClass →
      c = true ∧ (f.credit (f != .prose && c)).checkClass = f.checkClass := by
    intro f c
    cases f <;> cases c <;> decide
  exact key d.form (check d) h

/-- PROSE earns INSPECTION and nothing more, with or without an attachment, and
whatever the checker says: an attachment earns nothing. -/
theorem creditedClass_prose (check : Derivation → Bool) (steps : Nat) (text : String)
    (attachment : Option Attachment) :
    (Derivation.prose steps text attachment).creditedClass check = .inspection := by
  simp [creditedClass, creditedForm, verified, form, DerivationForm.credit,
    DerivationForm.checkClass]

/-- Every derivation earns at least INSPECTION. -/
theorem inspection_le_creditedClass (check : Derivation → Bool) (d : Derivation) :
    DerivationClass.inspection ≤ d.creditedClass check :=
  DerivationClass.inspection_le _

/-- A checker that verifies the derivation whenever another does never credits
it less. -/
theorem creditedClass_mono {check check' : Derivation → Bool} (d : Derivation)
    (h : check d = true → check' d = true) :
    d.creditedClass check ≤ d.creditedClass check' := by
  cases hc : check d
  · rw [creditedClass_of_check_false check d hc]
    exact inspection_le_creditedClass _ _
  · rw [creditedClass_of_check_true check d hc,
      creditedClass_of_check_true check' d (h hc)]
    exact DerivationClass.le_refl _

/-- The credited form is the highest form the checker verified, PROSE counted as
read: it is PROSE or the derivation's own form verified, it is at least PROSE,
and when verified it is the derivation's own form. -/
theorem creditedForm_greatest (check : Derivation → Bool) (d : Derivation) :
    (d.creditedForm check = .prose ∨
      (check d = true ∧ d.creditedForm check = d.form)) ∧
    DerivationForm.prose ≤ d.creditedForm check ∧
    (check d = true → d.form ≤ d.creditedForm check) := by
  have key : ∀ (f : DerivationForm) (c : Bool),
      (f.credit (f != .prose && c) = .prose ∨
        (c = true ∧ f.credit (f != .prose && c) = f)) ∧
      DerivationForm.prose ≤ f.credit (f != .prose && c) ∧
      (c = true → f ≤ f.credit (f != .prose && c)) := by
    intro f c
    cases f <;> cases c <;> decide
  exact key d.form (check d)

end Derivation

end Principia.Record
