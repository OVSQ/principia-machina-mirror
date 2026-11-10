import Principia.StructuredCheck
import Principia.Record.Derivation

/-!
# The STRUCTURED checker and the credit

"Credit only what was checked". `Principia.Record.Derivation` credits a
derivation from a checker's verdict on it; this file supplies the verdict for a
STRUCTURED derivation from `Principia.StructuredCheck.check`.

* **Reading a record (`readStructured`).** A record's STRUCTURED derivation is its start,
  its list of `StructuredStep`s and the RESULT's EQUATION, all text. The start is
  `e = e` for the EQUATION's left side `e` when the payload names none, so the steps
  rewrite it into the right side (a law is brought in by a step that cites it); a law of
  the Starting Set or an ASSUMPTION record when it names one, the derivation then
  starting from its EQUATION; or `e = e` for an expression it states (`readStart`). Each
  step's site gives its side and path, its citation the rule (a law, an ASSUMPTION
  record or an identity), `forward` the direction, and its EQUATION is read by the
  declared-form grammar. What cannot be read is refused with its number and why: the
  RESULT's EQUATION or the start (0), or a step (from 1): no site, a site that does not
  read, an identity not on the list, an EQUATION or a start's expression that does not
  read.
* **The checker (`structuredChecker`).** True exactly when the record's derivation is
  STRUCTURED, reads, and `check` accepts it on the record's own laws.
* **The credit (`mechanical_only_if_checked`).** A derivation credited MECHANICAL
  under this checker is STRUCTURED, was read and accepted, and its RESULT's EQUATION
  holds under every interpretation and assignment under which the laws it cites hold.

The law table is the record's own laws: the Starting Set's laws by NAME and the
ASSUMPTION records the record's ASSUMPTIONS name (`recordLaws`, question 13 (a) of the
record types' design note, provisional).
-/

namespace Principia.StructuredCheck

open Principia.Form
open Principia.Record

/-- One step of a site's path. -/
def readDir : String → Except String Dir
  | "l" => .ok .left
  | "r" => .ok .right
  | "a" => .ok .arg
  | _ => .error "site-unreadable"

/-- A site's text: the side, then the path, joined by dots. -/
def readSite (s : String) : Except String (Side × List Dir) :=
  if s.isEmpty then .error "no-site" else
  match s.splitOn "." with
  | "lhs" :: p => do return (.lhs, ← p.mapM readDir)
  | "rhs" :: p => do return (.rhs, ← p.mapM readDir)
  | _ => .error "site-unreadable"

/-- A record's step in the step language, or why it cannot be read. -/
def readStep (st : StructuredStep) : Except String Step := do
  let (side, path) ← readSite st.site
  let rule ← match st.cites with
    | .law n => pure (Rule.cite (.law n) st.forward)
    | .assumption r => pure (Rule.cite (.assumption r) st.forward)
    | .identity n => match Identity.ofName? n with
      | some i => pure (Rule.identity i st.forward)
      | none => throw "unknown-identity"
  let result ← match Equation.parse st.equation with
    | .ok e => pure e
    | .error _ => throw "equation-unreadable"
  return { side, path, rule, result }

/-- The steps read in order, numbered from `i`; the first that cannot be read, with
why. -/
def readSteps : List StructuredStep → Nat → Except (Nat × String) (List Step)
  | [], _ => .ok []
  | st :: sts, i =>
    match readStep st with
    | .error w => .error (i, w)
    | .ok s => match readSteps sts (i + 1) with
      | .error e => .error e
      | .ok ss => .ok (s :: ss)

/-- A record's start in the step language, given the RESULT's EQUATION read: `e = e` for
its left side `e` when the payload names no start, the law or ASSUMPTION record it
names, or `e = e` for the expression it states; `start-unreadable` when that expression
does not read. -/
def readStart (goal : Equation) : StructuredStart → Except String Start
  | .lhs => .ok (.refl goal.lhs)
  | .law n => .ok (.cite (.law n))
  | .assumption r => .ok (.cite (.assumption r))
  | .refl text => match parseExpr text with
    | .ok e => .ok (.refl e)
    | .error _ => .error "start-unreadable"

/-- A record's STRUCTURED derivation in the step language: its start, the steps and the
goal, or the first thing that cannot be read (0 the RESULT's EQUATION, then the start,
`k` the `k`-th step). -/
def readStructured (equationText : String) (start : StructuredStart)
    (steps : List StructuredStep) : Except (Nat × String) (Start × List Step × Equation) :=
  match Equation.parse equationText with
  | .error _ => .error (0, "equation-unreadable")
  | .ok goal => match readStart goal start with
    | .error w => .error (0, w)
    | .ok st => match readSteps steps 1 with
      | .error e => .error e
      | .ok ss => .ok (st, ss, goal)

/-- What the checker says of a record's derivation. -/
inductive RecordVerdict where
  /-- STRUCTURED, read and accepted. -/
  | accepted
  /-- STRUCTURED and read, refused by `check` at a step, with why. -/
  | refused (step : Nat) (why : String)
  /-- STRUCTURED, but a step or the EQUATION cannot be read. -/
  | unreadable (step : Nat) (why : String)
  /-- PROSE or KERNEL: not this checker's. -/
  | notStructured
  deriving DecidableEq, Repr, Inhabited

/-- The checker's verdict on a record's derivation, given the record's own laws and
its RESULT's EQUATION. -/
def checkRecord (laws : LawTable) (equationText : String) : Derivation → RecordVerdict
  | .structured steps start =>
    match readStructured equationText start steps with
    | .error (i, w) => .unreadable i w
    | .ok (start, ss, goal) =>
      match check laws start ss goal with
      | .accepted => .accepted
      | .refused i w => .refused i w
  | _ => .notStructured

/-- The checker the credit reads (`Derivation.creditedClass`): true exactly when the
record's STRUCTURED derivation reads and `check` accepts it. -/
def structuredChecker (laws : LawTable) (equationText : String) (d : Derivation) : Bool :=
  match checkRecord laws equationText d with
  | .accepted => true
  | _ => false

theorem readStructured_goal {equationText : String} {st : StructuredStart}
    {steps : List StructuredStep} {start : Start} {ss : List Step} {goal : Equation}
    (h : readStructured equationText st steps = .ok (start, ss, goal)) :
    Equation.parse equationText = .ok goal := by
  unfold readStructured at h
  split at h
  · contradiction
  · rename_i g hg
    split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        exact hg

/-- A record's step never cites a law by instance: its citation is a law, an ASSUMPTION
record or an identity, read as an exact citation or an identity. The Starting Set's laws
and ASSUMPTION records state facts about one system's quantities, not identities over
every value, so an instance of one need not hold where it does; which may be instanced is
the Declarer's to choose. -/
theorem readStep_instanceCitation {st : StructuredStep} {s : Step} (h : readStep st = .ok s) :
    s.instanceCitation? = none := by
  obtain ⟨equation, cites, site, forward⟩ := st
  unfold readStep at h
  cases hs : readSite site with
  | error w => simp [hs, bind, Except.bind] at h
  | ok sp =>
    cases hp : Equation.parse equation <;>
      cases cites <;>
      (try rename_i n; cases hi : Identity.ofName? n) <;>
      simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;>
      (subst h; rfl)

/-- So no step read from a record cites by instance. -/
theorem readSteps_instances : ∀ {sts : List StructuredStep} {i : Nat} {ss : List Step},
    readSteps sts i = .ok ss → instances ss = []
  | [], i, ss, h => by simp [readSteps] at h; subst h; rfl
  | st :: sts, i, ss, h => by
    simp only [readSteps] at h
    split at h
    · contradiction
    · rename_i s hs
      split at h
      · contradiction
      · rename_i ss' hss
        simp only [Except.ok.injEq] at h
        subst h
        have h1 := readStep_instanceCitation hs
        have h2 := readSteps_instances hss
        simp only [instances, List.filterMap_cons, h1] at h2 ⊢
        exact h2

theorem readStructured_instances {equationText : String} {st : StructuredStart}
    {steps : List StructuredStep} {start : Start} {ss : List Step} {goal : Equation}
    (h : readStructured equationText st steps = .ok (start, ss, goal)) : instances ss = [] := by
  unfold readStructured at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i ss' hss
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact readSteps_instances hss

/-- The checker accepts exactly what `check` accepts once read. -/
theorem structuredChecker_true {laws : LawTable} {equationText : String} {d : Derivation}
    (h : structuredChecker laws equationText d = true) :
    ∃ steps st start ss goal, d = .structured steps st ∧
      readStructured equationText st steps = .ok (start, ss, goal) ∧
      check laws start ss goal = .accepted := by
  unfold structuredChecker checkRecord at h
  split at h
  · rename_i hc
    split at hc
    · rename_i steps st
      split at hc
      · contradiction
      · rename_i start ss goal hr
        split at hc
        · rename_i hk
          exact ⟨steps, st, start, ss, goal, rfl, hr, hk⟩
        · contradiction
    · contradiction
  · contradiction

/-- **Only what was checked is credited.** A derivation credited MECHANICAL under the
STRUCTURED checker is STRUCTURED, its steps and the RESULT's EQUATION read, `check`
accepts it on the record's own laws, and the EQUATION then holds under every
interpretation and assignment under which every law and ASSUMPTION record the
derivation cites holds (`check_sound`). -/
theorem mechanical_only_if_checked (laws : LawTable) (equationText : String) (d : Derivation)
    (h : d.creditedClass (structuredChecker laws equationText) = .mechanical) :
    ∃ steps st start ss goal, d = .structured steps st ∧
      readStructured equationText st steps = .ok (start, ss, goal) ∧
      check laws start ss goal = .accepted ∧
      Equation.parse equationText = .ok goal ∧
      ∀ (I : Interp) (σ : String → Rat),
        (∀ c ∈ citations start ss, ∀ e, lookup laws c = some e → e.holds I σ) →
        goal.holds I σ := by
  have hlt : DerivationClass.inspection < d.creditedClass (structuredChecker laws equationText) := by
    rw [h]; decide
  obtain ⟨hv, _⟩ := Derivation.verified_of_inspection_lt _ d hlt
  obtain ⟨steps, st, start, ss, goal, hd, hr, hk⟩ := structuredChecker_true hv
  exact ⟨steps, st, start, ss, goal, hd, hr, hk, readStructured_goal hr,
    fun I σ hl => check_sound laws start ss goal hk I σ hl
      (by simp [readStructured_instances hr])⟩

/-- And conversely: a STRUCTURED derivation the checker accepts is credited
MECHANICAL. -/
theorem mechanical_of_checked (laws : LawTable) (equationText : String)
    (steps : List StructuredStep) (st : StructuredStart)
    (h : structuredChecker laws equationText (.structured steps st) = true) :
    (Derivation.structured steps st).creditedClass (structuredChecker laws equationText) =
      .mechanical := by
  rw [Derivation.creditedClass_of_check_true _ _ h]
  rfl

/-! ## The record's laws

The law table a record's STRUCTURED derivation is checked against, assembled from the
two sources the rule names ("each citing a law of the Starting Set or an ASSUMPTION
record") and from nothing else:

* the Starting Set's LAWs, each by its NAME, with its EQUATION read by the declared-form
  grammar. A LAW without an EQUATION, or whose EQUATION does not read, is not in the
  table, and a step that cites it is refused (`missing-citation`).
* the ASSUMPTION records the record names in its ASSUMPTIONS (question 13 (a) of the
  record types' design note, provisional), each found in the register by its ID with
  CLASS ASSUMPTION, with its EQUATION (TPS 3.3.7: an ASSUMPTION record other than a
  SITUATION record may carry one). A record not found, of another class, or without an
  EQUATION that reads, is not in the table.

So a step citing an ASSUMPTION record that the record's ASSUMPTIONS do not name is
refused (`missing-citation`): question 13 (a)'s rule, which record_check is to apply at
the push, holds here at the credit as well. The register's records and the Starting Set
are read as v1's JSON (`Principia.Zone.Value`), as the zones' checks read them. -/

open Principia.Zone (getStr?)

/-- An EQUATION's text as the law table holds it, if it reads. -/
def readLaw (text : String) : Option Equation :=
  match Equation.parse text with
  | .ok e => some e
  | .error _ => none

/-- A LAW entry of the Starting Set as a law of the table: its NAME and its EQUATION,
when it has both and the EQUATION reads. -/
def entryLaw (e : Principia.Zone.Entry) : Option (StepCitation × Equation) :=
  match getStr? e "NAME", getStr? e "EQUATION" with
  | some n, some f => (readLaw f).map fun eq => (.law n, eq)
  | _, _ => none

/-- The Starting Set's laws: its LAWs with an EQUATION that reads, in their order. -/
def startingSetLaws (startingSet : Principia.Zone.Value) : LawTable :=
  (entriesOf startingSet "LAW").filterMap entryLaw

/-- Whether a register record is the ASSUMPTION record with this identifier. -/
def isAssumptionRecord (recordId : String) : Principia.Zone.Value → Bool
  | .obj e => getStr? e "ID" == some recordId && getStr? e "CLASS" == some "ASSUMPTION"
  | _ => false

/-- The law an ASSUMPTION record supplies: the first record of the register with its
identifier and CLASS ASSUMPTION, when it carries an EQUATION that reads. -/
def assumptionLaw (register : List Principia.Zone.Value) (recordId : String) :
    Option (StepCitation × Equation) :=
  match register.find? (isAssumptionRecord recordId) with
  | some (.obj e) => ((getStr? e "EQUATION").bind readLaw).map fun eq => (.assumption recordId, eq)
  | _ => none

/-- The law table of a record: the Starting Set's laws, then the laws of the ASSUMPTION
records its ASSUMPTIONS name, in that order. -/
def recordLaws (startingSet : Principia.Zone.Value) (register : List Principia.Zone.Value)
    (assumptions : List String) : LawTable :=
  startingSetLaws startingSet ++ assumptions.filterMap (assumptionLaw register)

/-- `e` is the EQUATION of the Starting Set's LAW `n`. -/
def IsStartingSetLaw (startingSet : Principia.Zone.Value) (n : String) (e : Equation) : Prop :=
  ∃ entry ∈ entriesOf startingSet "LAW", getStr? entry "NAME" = some n ∧
    ∃ f, getStr? entry "EQUATION" = some f ∧ Equation.parse f = .ok e

/-- `e` is the EQUATION of a register record with this identifier and CLASS
ASSUMPTION. -/
def IsAssumptionLaw (register : List Principia.Zone.Value) (recordId : String) (e : Equation) :
    Prop :=
  ∃ entry, Principia.Zone.Value.obj entry ∈ register ∧
    isAssumptionRecord recordId (.obj entry) = true ∧
    ∃ f, getStr? entry "EQUATION" = some f ∧ Equation.parse f = .ok e

theorem readLaw_eq_some {f : String} {e : Equation} (h : readLaw f = some e) :
    Equation.parse f = .ok e := by
  unfold readLaw at h
  split at h
  · rename_i e' he; cases h; exact he
  · contradiction

/-- **The table holds only what its sources say.** Every law of a record's table is the
EQUATION of a LAW of the Starting Set, by its NAME, or the EQUATION of an ASSUMPTION record
of the register that the record's ASSUMPTIONS name, by its identifier. -/
theorem mem_recordLaws {startingSet : Principia.Zone.Value} {register : List Principia.Zone.Value}
    {assumptions : List String} {c : StepCitation} {e : Equation}
    (h : (c, e) ∈ recordLaws startingSet register assumptions) :
    (∃ n, c = .law n ∧ IsStartingSetLaw startingSet n e) ∨
      (∃ r ∈ assumptions, c = .assumption r ∧ IsAssumptionLaw register r e) := by
  unfold recordLaws at h
  rcases List.mem_append.mp h with h | h
  · left
    unfold startingSetLaws at h
    obtain ⟨entry, hmem, he⟩ := List.mem_filterMap.mp h
    unfold entryLaw at he
    split at he
    · rename_i n f hn hf
      obtain ⟨eq, hr, heq⟩ := Option.map_eq_some_iff.mp he
      cases heq
      exact ⟨n, rfl, entry, hmem, hn, f, hf, readLaw_eq_some hr⟩
    · contradiction
  · right
    obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp h
    unfold assumptionLaw at he
    split at he
    · rename_i entry hfind
      obtain ⟨eq, hb, heq⟩ := Option.map_eq_some_iff.mp he
      cases heq
      obtain ⟨f, hf, hl⟩ := Option.bind_eq_some_iff.mp hb
      exact ⟨r, hr, rfl, entry, List.mem_of_find?_eq_some hfind,
        List.find?_some hfind, f, hf, readLaw_eq_some hl⟩
    · contradiction

theorem mem_of_lookup {laws : LawTable} {c : StepCitation} {e : Equation}
    (h : lookup laws c = some e) : (c, e) ∈ laws := by
  unfold lookup at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hb := List.find?_some (p := fun x : StepCitation × Equation => x.fst == c) hp
  have hm := List.mem_of_find?_eq_some hp
  rw [← beq_iff_eq.mp hb]
  exact hm

/-- **Credited MECHANICAL, the RESULT's EQUATION follows from the record's sources.**
When a record's derivation is credited MECHANICAL against its own law table, the
RESULT's EQUATION reads, and it holds under every interpretation and assignment under
which every LAW of the Starting Set and every ASSUMPTION record the record's ASSUMPTIONS
name hold, each by its EQUATION. -/
theorem mechanical_only_if_sources_hold (startingSet : Principia.Zone.Value)
    (register : List Principia.Zone.Value) (assumptions : List String) (equationText : String)
    (d : Derivation)
    (h : d.creditedClass
      (structuredChecker (recordLaws startingSet register assumptions) equationText) = .mechanical) :
    ∃ goal, Equation.parse equationText = .ok goal ∧
      ∀ (I : Interp) (σ : String → Rat),
        (∀ n e, IsStartingSetLaw startingSet n e → e.holds I σ) →
        (∀ r ∈ assumptions, ∀ e, IsAssumptionLaw register r e → e.holds I σ) →
        goal.holds I σ := by
  obtain ⟨_, _, start, ss, goal, _, _, _, hg, hsound⟩ :=
    mechanical_only_if_checked _ equationText d h
  refine ⟨goal, hg, fun I σ hlaw hasm => hsound I σ fun c _ e hc => ?_⟩
  rcases mem_recordLaws (mem_of_lookup hc) with ⟨n, _, hn⟩ | ⟨r, hr, _, ha⟩
  · exact hlaw n e hn
  · exact hasm r hr e ha

end Principia.StructuredCheck
