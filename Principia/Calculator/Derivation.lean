import Principia.Calculator.Interface
import Principia.Record.StructuredWire
import Principia.Strike.Conditions
import Principia.StructuredCredit

/-!
# Family `derivation`: checking a STRUCTURED derivation and crediting it

The Research Assembly's rule: credit only what was checked. The credit (`Derivation.creditedClass`) reaches
the command line with the checker, as calls that check and credit at once: no call takes a
verdict from its caller (section 6 of the record types' design note).

* `credit {"derivation", "equation", "assumptions", "starting_set", "register"}`: the
  STRUCTURED payload (its wire form, `Principia.Record.structuredOfValue`), the RESULT's
  EQUATION text, the record's ASSUMPTIONS (record identifiers), the Starting Set (v1's TPK
  object) and the register (a list of records). The answer is `{"VERDICT", "STEP", "WHY",
  "CLASS"}`: `VERDICT` the checker's verdict (`checkRecord`), `ACCEPTED`, `REFUSED` or
  `UNREADABLE`, with the step and the word for the last two; `CLASS` the credit,
  `MECHANICAL` when the checker accepts and `INSPECTION` otherwise (`creditedClass` under
  `structuredChecker` on the record's own laws, `recordLaws`). A payload the reader refuses
  is `BAD_ARGUMENT`, its detail ending with the reader's word.
* `credit_record {"record", "starting_set", "register"}`: a record's DERIVATION read by its
  shape (`Principia.Record.derivationOfValue`), with the record's EQUATION and
  ASSUMPTIONS (absent, none). STRUCTURED is credited as `credit` credits it; PROSE, with or
  without an attachment, answers `VERDICT` `NOT_STRUCTURED` and `CLASS` `INSPECTION`; KERNEL
  is refused `OWED`: its class is the KERNEL checker's, which this family does not run.
* `laws {"assumptions", "starting_set", "register"}`: the law table a derivation is checked
  against, `[[kind, name, equation], ...]`, `kind` `LAW` (a law of the Starting Set, by
  NAME) or `ASSUMPTION` (an ASSUMPTION record, by its identifier), `equation` the
  EQUATION as the checker holds it, in the declared forms' canonical spelling.

The theorems: `credit_mechanical_iff`, the command answers `CLASS` `MECHANICAL` exactly when
`structuredChecker (recordLaws s r a) e d` is true, so `mechanical_only_if_sources_hold`
holds of every `MECHANICAL` it writes (`credit_mechanical_sound`); `credit_never_proved`,
no call of the family answers `PROVED`.

Bounds, so that no accepted request runs long: at most `maxSteps` steps; every EQUATION
text (the RESULT's, a step's, a START's expression, a LAW's of the Starting Set and a
register record's) at most `maxEquation` code points; at most `maxKind` entries in each of
the Starting Set's kinds; at most `maxRegister` records in the register; at most
`maxAssumptions` ASSUMPTIONS. Each step is one parse of at most 4,096 code points (the
declared forms' bound, after NFC) and one rewrite of the tree, and the law table is
assembled once, so the cost is linear in the steps; the reader's bound of a mebibyte on a
request caps the text the steps hold in all. The slowest accepted requests found, on the
Calculator's command line (wall time, on a machine of two cores shared with other work), each
near the reader's mebibyte: 1,024 steps of about 500 code points each, commuting a sum back
and forth, 0.39 s; 250 steps of about 3,900 code points each, 0.38 s; 1,024 steps rewriting
under 60 nested operators, 0.27 s; a table of 64 LAWs of about 3,900 code points and 512
named ASSUMPTION records of about 900 in a register of 1,024, 0.23 s.
-/

namespace Principia.Calculator.Derivation

open Principia.Canonical
open Principia.Record
open Principia.StructuredCheck

/-! ## The family's bounds -/

/-- The most steps a STRUCTURED derivation holds. -/
def maxSteps : Nat := 1024

/-- The most code points an EQUATION's text holds before it is read (eom's bound). -/
def maxEquation : Nat := 16384

/-- The most entries each kind of the Starting Set holds. -/
def maxKind : Nat := 64

/-- The most records the register holds. -/
def maxRegister : Nat := 1024

/-- The most identifiers a record's ASSUMPTIONS hold. -/
def maxAssumptions : Nat := 512

/-- A text within `maxEquation` code points. -/
def textWithin (what : String) (s : String) : Except Refusal Unit :=
  if maxEquation < s.length then
    badArgument s!"{what} holds more than {maxEquation} code points (the Calculator's bound)"
  else pure ()

/-- The EQUATION member of an object, if it is a string. -/
def equationText? : Value → Option String
  | .obj ms => match ms.lookup "EQUATION" with
    | some (.str s) => some s
    | _ => none
  | _ => none

/-- Each object's EQUATION within `maxEquation`. -/
def equationsWithin (what : String) (xs : List Value) : Except Refusal Unit :=
  xs.forM fun x => match equationText? x with
    | some s => textWithin what s
    | none => pure ()

/-! ## The sources of the law table -/

/-- What a record's law table is assembled from (`recordLaws`): the Starting Set, the
register and the record's ASSUMPTIONS. -/
structure Sources where
  startingSet : Zone.Value
  register : List Zone.Value
  assumptions : List String

/-- The record's law table. -/
def Sources.laws (s : Sources) : LawTable := recordLaws s.startingSet s.register s.assumptions

/-- The Starting Set: an object, each kind within `maxKind`, each entry's EQUATION within
`maxEquation`, read as the zones read it. -/
def startingSetOf (v : Value) : Except Refusal Zone.Value := do
  let ms ← asObject "starting_set" v
  ms.forM fun (k, x) => match x with
    | .arr xs => do
      atMost s!"the Starting Set's {quote k}" maxKind xs
      equationsWithin s!"an entry of the Starting Set's {quote k}" xs
    | _ => pure ()
  pure (Principia.Strike.toZoneValue v)

/-- The register: a list within `maxRegister`, each record's EQUATION within `maxEquation`,
each record read as the zones read it. -/
def registerOf (v : Value) : Except Refusal (List Zone.Value) := do
  let rs ← asList "register" v
  atMost "register" maxRegister rs
  equationsWithin "a record of the register" rs
  pure (rs.map Principia.Strike.toZoneValue)

/-- ASSUMPTIONS: a list of identifiers within `maxAssumptions`. -/
def assumptionsOf (what : String) (v : Value) : Except Refusal (List String) := do
  let xs ← asList what v
  atMost what maxAssumptions xs
  xs.mapM (asString s!"an entry of {what}")

/-- The sources from a request's members. -/
def readSources (ms : List (String × Value)) (assumptions : List String) :
    Except Refusal Sources := do
  let s ← startingSetOf (← needed ms "starting_set")
  let r ← registerOf (← needed ms "register")
  pure ⟨s, r, assumptions⟩

/-! ## The payload -/

/-- A payload's STEPS within `maxSteps`, counted before they are read. -/
def stepsCounted : Value → Except Refusal Unit
  | .obj ms => match ms.lookup "STEPS" with
    | some (.arr xs) => atMost "the derivation's STEPS" maxSteps xs
    | _ => pure ()
  | _ => pure ()

/-- A STRUCTURED payload's texts within `maxEquation`: each step's EQUATION and the START's
expression. -/
def payloadWithin (steps : List StructuredStep) (start : StructuredStart) : Except Refusal Unit := do
  steps.forM fun st => textWithin "a step's EQUATION" st.equation
  match start with
  | .refl e => textWithin "the START's EXPRESSION" e
  | _ => pure ()

/-- A STRUCTURED payload, within the bounds; the reader's refusal is `BAD_ARGUMENT`, its
detail ending with the reader's word. -/
def readPayload (v : Value) : Except Refusal (List StructuredStep × StructuredStart) := do
  stepsCounted v
  match structuredOfValue v with
  | .error w => badArgument s!"the derivation is not a STRUCTURED payload: {w}"
  | .ok (steps, start) =>
    payloadWithin steps start
    pure (steps, start)

/-! ## The credit -/

/-- What the command answers of a derivation: the checker's verdict and the credit. -/
structure Credit where
  verdict : RecordVerdict
  cls : DerivationClass

/-- The verdict and the credit of a derivation, on the record's own laws. -/
def credit (s : Sources) (equation : String) (d : Derivation) : Credit :=
  ⟨checkRecord s.laws equation d, d.creditedClass (structuredChecker s.laws equation)⟩

/-- The answer's object: `CLASS`, `VERDICT`, and `STEP` and `WHY` for a verdict that has
them. -/
def Credit.toValue (c : Credit) : Value :=
  match c.verdict with
  | .accepted => .obj [("CLASS", .str (WireWord.toWire c.cls)), ("VERDICT", .str "ACCEPTED")]
  | .refused i w => .obj [("CLASS", .str (WireWord.toWire c.cls)), ("STEP", .int i),
      ("VERDICT", .str "REFUSED"), ("WHY", .str w)]
  | .unreadable i w => .obj [("CLASS", .str (WireWord.toWire c.cls)), ("STEP", .int i),
      ("VERDICT", .str "UNREADABLE"), ("WHY", .str w)]
  | .notStructured => .obj [("CLASS", .str (WireWord.toWire c.cls)),
      ("VERDICT", .str "NOT_STRUCTURED")]

/-- A `credit` request read: the sources, the RESULT's EQUATION and the payload. -/
def readCredit (v : Value) :
    Except Refusal (Sources × String × List StructuredStep × StructuredStart) := do
  let ms ← membersOf ["derivation", "equation", "assumptions", "starting_set", "register"] v
  let (steps, start) ← readPayload (← needed ms "derivation")
  let e ← asString "equation" (← needed ms "equation")
  textWithin "equation" e
  let a ← assumptionsOf "assumptions" (← needed ms "assumptions")
  let src ← readSources ms a
  pure (src, e, steps, start)

/-- `credit`: a STRUCTURED payload checked and credited. -/
def creditCall (v : Value) : Except Refusal Value :=
  match readCredit v with
  | .error r => .error r
  | .ok (src, e, steps, start) => .ok (credit src e (.structured steps start)).toValue

/-! ## The record -/

/-- A record's DERIVATION within the bounds: a STRUCTURED payload's, or a PROSE
derivation's attachment's (read, though it earns nothing). -/
def derivationWithin : Derivation → Except Refusal Unit
  | .structured steps start => payloadWithin steps start
  | _ => pure ()

/-- A `credit_record` request read: the sources, the record's EQUATION and its DERIVATION. -/
def readCreditRecord (v : Value) : Except Refusal (Sources × String × Derivation) := do
  let ms ← membersOf ["record", "starting_set", "register"] v
  let r ← asObject "record" (← needed ms "record")
  let e ← match r.lookup "EQUATION" with
    | some (.str e) => pure e
    | some _ => badArgument "the record's EQUATION is not a string"
    | none => badArgument "the record has no EQUATION"
  textWithin "the record's EQUATION" e
  let a ← match r.lookup "ASSUMPTIONS" with
    | some x => assumptionsOf "the record's ASSUMPTIONS" x
    | none => pure []
  let dv ← match r.lookup "DERIVATION" with
    | some x => pure x
    | none => badArgument "the record has no DERIVATION"
  stepsCounted dv
  let d ← match derivationOfValue dv with
    | .ok d => pure d
    | .error w => badArgument s!"the record's DERIVATION does not read: {w}"
  derivationWithin d
  let src ← readSources ms a
  pure (src, e, d)

/-- An OWED answer's detail for a KERNEL derivation. -/
def kernelOwed : String :=
  "the class of a KERNEL derivation waits on the KERNEL checker, which this command does " ++
    "not run: that class is written from that checker's verdict"

/-- `credit_record`: a record's DERIVATION, by its shape, checked and credited. -/
def creditRecordCall (v : Value) : Except Refusal Value :=
  match readCreditRecord v with
  | .error r => .error r
  | .ok (_, _, .kernelProof _) => .error ⟨.owed, kernelOwed⟩
  | .ok (src, e, .prose n t a) => .ok (credit src e (.prose n t a)).toValue
  | .ok (src, e, .structured steps start) => .ok (credit src e (.structured steps start)).toValue

/-! ## The law table -/

/-- A law of the table as a row: its kind, its name and its EQUATION's canonical spelling. -/
def lawRow : StepCitation × Equation → Value
  | (c, e) =>
    let (kind, name) := match c with
      | .law n => ("LAW", n)
      | .assumption r => ("ASSUMPTION", r)
      | .identity n => ("IDENTITY", n)
    .arr [.str kind, .str name, .str (Principia.Form.Tree.print (.eq e.lhs e.rhs))]

/-- A `laws` request read: the sources. -/
def readLaws (v : Value) : Except Refusal Sources := do
  let ms ← membersOf ["assumptions", "starting_set", "register"] v
  let a ← assumptionsOf "assumptions" (← needed ms "assumptions")
  readSources ms a

/-- `laws`: the law table a derivation is checked against. -/
def lawsCall (v : Value) : Except Refusal Value :=
  match readLaws v with
  | .error r => .error r
  | .ok src => .ok (.arr (src.laws.map lawRow))

/-- The family's functions. -/
def calls : Family := [
  ("credit", creditCall),
  ("credit_record", creditRecordCall),
  ("laws", lawsCall),
]

/-! ## What the credit's answer says -/

/-- The `CLASS` an answer states, if it states one. -/
def answerClass : Value → Option String
  | .obj ms => match ms.lookup "CLASS" with
    | some (.str c) => some c
    | _ => none
  | _ => none

theorem answerClass_toValue (c : Credit) :
    answerClass c.toValue = some (WireWord.toWire c.cls) := by
  obtain ⟨v, cls⟩ := c
  cases v <;> simp [Credit.toValue, answerClass, List.lookup]

theorem toWire_mechanical_iff (c : DerivationClass) :
    WireWord.toWire c = "MECHANICAL" ↔ c = .mechanical := by
  cases c <;> decide

theorem toWire_proved_iff (c : DerivationClass) :
    WireWord.toWire c = "PROVED" ↔ c = .proved := by
  cases c <;> decide

/-- The credit is MECHANICAL exactly when the checker accepts on the record's own laws. -/
theorem credit_cls_mechanical_iff (s : Sources) (e : String) (d : Derivation) :
    (credit s e d).cls = .mechanical ↔ structuredChecker s.laws e d = true := by
  show d.creditedClass (structuredChecker s.laws e) = .mechanical ↔ _
  constructor
  · intro h
    cases hc : structuredChecker s.laws e d
    · rw [Derivation.creditedClass_of_check_false _ d hc] at h
      cases h
    · rfl
  · intro h
    obtain ⟨steps, st, _, _, _, rfl, _⟩ := structuredChecker_true h
    exact mechanical_of_checked _ _ steps st h

/-- **The command answers MECHANICAL exactly when the checker accepts.** Every answer of
`credit` is the credit of the request's payload on the request's own sources, and it states
`CLASS` `MECHANICAL` exactly when `structuredChecker (recordLaws s r a) e d` is true. -/
theorem credit_mechanical_iff {req v : Value} (h : creditCall req = .ok v) :
    ∃ src e steps start, readCredit req = .ok (src, e, steps, start) ∧
      (answerClass v = some "MECHANICAL" ↔
        structuredChecker (recordLaws src.startingSet src.register src.assumptions) e
          (.structured steps start) = true) := by
  unfold creditCall at h
  split at h
  · cases h
  · rename_i src e steps start hr
    cases h
    refine ⟨src, e, steps, start, hr, ?_⟩
    rw [answerClass_toValue, Option.some.injEq, toWire_mechanical_iff]
    exact credit_cls_mechanical_iff src e _

/-- So `mechanical_only_if_sources_hold` holds of every MECHANICAL the command writes: the
RESULT's EQUATION reads, and it holds wherever the Starting Set's laws and the ASSUMPTION
records the request's ASSUMPTIONS name hold. -/
theorem credit_mechanical_sound {req v : Value} (h : creditCall req = .ok v)
    (hm : answerClass v = some "MECHANICAL") :
    ∃ src e goal, (∃ steps start, readCredit req = .ok (src, e, steps, start)) ∧
      Equation.parse e = .ok goal ∧
      ∀ (I : Interp) (σ : String → Rat),
        (∀ n q, IsStartingSetLaw src.startingSet n q → q.holds I σ) →
        (∀ r ∈ src.assumptions, ∀ q, IsAssumptionLaw src.register r q → q.holds I σ) →
        goal.holds I σ := by
  obtain ⟨src, e, steps, start, hr, hiff⟩ := credit_mechanical_iff h
  have hc := hiff.mp hm
  have hcls := mechanical_of_checked _ _ steps start hc
  obtain ⟨goal, hg, hs⟩ := mechanical_only_if_sources_hold src.startingSet src.register
    src.assumptions e _ hcls
  exact ⟨src, e, goal, ⟨steps, start, hr⟩, hg, hs⟩

/-- A derivation not in the KERNEL form is never credited PROVED. -/
theorem credit_cls_ne_proved (s : Sources) (e : String) (d : Derivation)
    (hd : d.form ≠ .kernelProof) : (credit s e d).cls ≠ .proved := by
  intro h
  have hle := Derivation.creditedClass_le_checkClass (structuredChecker s.laws e) d
  have h' : d.creditedClass (structuredChecker s.laws e) = .proved := h
  rw [h'] at hle
  cases d with
  | prose =>
    simp only [Derivation.form, DerivationForm.checkClass] at hle
    exact absurd hle (by decide)
  | structured =>
    simp only [Derivation.form, DerivationForm.checkClass] at hle
    exact absurd hle (by decide)
  | kernelProof => exact hd rfl

/-- **The family never answers PROVED.** No call of the family states `CLASS` `PROVED`:
PROVED is the KERNEL checker's class, and a KERNEL derivation is refused `OWED`. -/
theorem credit_never_proved {fn : String} {call : Call} {req v : Value}
    (hc : calls.lookup fn = some call) (h : call req = .ok v) :
    answerClass v ≠ some "PROVED" := by
  have key : ∀ c : Credit, c.cls ≠ .proved → answerClass c.toValue ≠ some "PROVED" := by
    intro c hc
    rw [answerClass_toValue, ne_eq, Option.some.injEq, toWire_proved_iff]
    exact hc
  simp only [calls, List.lookup] at hc
  split at hc
  · cases hc
    unfold creditCall at h
    split at h
    · cases h
    · cases h
      exact key _ (credit_cls_ne_proved _ _ _ (by simp [Derivation.form]))
  · split at hc
    · cases hc
      unfold creditRecordCall at h
      split at h
      · cases h
      · cases h
      · cases h
        exact key _ (credit_cls_ne_proved _ _ _ (by simp [Derivation.form]))
      · cases h
        exact key _ (credit_cls_ne_proved _ _ _ (by simp [Derivation.form]))
    · split at hc
      · cases hc
        unfold lawsCall at h
        split at h
        · cases h
        · cases h
          simp [answerClass]
      · cases hc

end Principia.Calculator.Derivation
