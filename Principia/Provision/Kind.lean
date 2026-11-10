import Principia.Provision.Text

/-!
# A Provision's kind

The Declarer's selection (the Research Assembly's rule on Provisions): a Provision is of one of
two kinds. An **Interaction** acts on the system modelled: its terms are forces composed into
the equations of motion of the DOFs it is bound to (GRAV-UNIFORM, AIR-QUADRATIC, AIR-LINEAR).
A **Convention** acts on nothing: it declares what the author's laws may take as given (MATH,
the dimensionless constant `pi_c`, the grammar having no pi). The interview's question stays
"which of these interactions act on your system?"; MATH is offered under "conventions".

Version 1 had no kinds: no field of a Provision's text or of a declaring act carries one, and
none of its functions reads one, so every answer of the Provisions' corpus stands as v1
gave it. The kinds of the first catalogue (TPS 5.22.17) are the Declarer's selection, recorded
here as `kindOf?`, which answers for those four alone.

Every Provision's kind is read from its text: one that writes no TERM and binds
no slot is a Convention, every other an Interaction (`Provision.kind`). The kind is read, never
written, so no field of the text and no digest moves. The first catalogue's four come out as the selection
names them; the vector runner checks it over their texts in the Provisions' corpus. The
edge the selection states stands: a Provision of constants alone that is physical would be
listed under Conventions.
-/

namespace Principia.Provision

/-- A Provision's kind. -/
inductive Kind where
  /-- It acts on the system: its terms are forces on the DOFs it is bound to. -/
  | interaction
  /-- It acts on nothing: a quantity the author's laws may take as given. -/
  | convention
  deriving DecidableEq, Repr

/-- The kind's word. -/
def Kind.word : Kind → String
  | .interaction => "Interaction"
  | .convention => "Convention"

/-- The first catalogue and each Provision's kind, in ID order. -/
def firstCatalogue : List (String × Kind) :=
  [("AIR-LINEAR", .interaction), ("AIR-QUADRATIC", .interaction), ("GRAV-UNIFORM", .interaction),
   ("MATH", .convention)]

/-- The kind of a Provision of the first catalogue; none for any other ID. -/
def kindOf? (id : String) : Option Kind := firstCatalogue.lookup id

/-- The Interactions of the first catalogue. -/
theorem firstCatalogue_interactions :
    (firstCatalogue.filter (·.2 == .interaction)).map (·.1) = ["AIR-LINEAR", "AIR-QUADRATIC", "GRAV-UNIFORM"] := by
  decide

/-- The Conventions of the first catalogue. -/
theorem firstCatalogue_conventions : (firstCatalogue.filter (·.2 == .convention)).map (·.1) = ["MATH"] := by
  decide

/-- A Provision's kind, read from its text: a Convention when it writes no TERM and binds
no slot, an Interaction otherwise. -/
def Provision.kind (M : Provision) : Kind :=
  if M.terms.isEmpty && M.slots.isEmpty then .convention else .interaction

/-- A Provision is a Convention exactly when it writes no TERM and binds no slot. -/
theorem Provision.kind_eq_convention (M : Provision) :
    M.kind = .convention ↔ M.terms = [] ∧ M.slots = [] := by
  unfold Provision.kind
  cases M.terms <;> cases M.slots <;> simp

/-- A Provision that writes a TERM is an Interaction. -/
theorem Provision.kind_of_term (M : Provision) (h : M.terms ≠ []) : M.kind = .interaction := by
  unfold Provision.kind
  cases hT : M.terms with
  | nil => exact absurd hT h
  | cons _ _ => simp

/-- MATH is a Convention. -/
theorem kindOf?_math : kindOf? "MATH" = some .convention := by decide

/-- Every ID of the first catalogue is a Provision ID, and they are listed in ID order without
repeats, as the interview lists them. -/
theorem firstCatalogue_ids :
    (firstCatalogue.all fun e => isProvisionId e.1) = true ∧
      strictlySorted (firstCatalogue.map (·.1)) = true := by
  decide

end Principia.Provision
