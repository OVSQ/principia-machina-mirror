import Principia.Wire

/-!
# Record classes, grades and statuses

The closed table of the Research Record Register, its class part: the eleven
record classes, the two forms a record takes, who writes each class, the grade
each class lands with, the grades it can reach and the statuses it carries.

Source: v1's tpm_record_schema 0.3.1 (the seed's version; 0.4.0 is named
as the later one), sections 3 and 6, and the lines `CLASS`, `LANDGRADE`, `GRADES` and
`STATUSES` of its table (section 7.5); TPS 0.5.0, 3.2.10 and 3.2.18. The record
classes' corpus is generated from those table lines.

PMA words: v1's TPX is Custos; v1's lead (AI-LEAD) is the Holder.
-/

namespace Principia.Record

/-- `CLASS`: the eleven record classes (tpm_record_schema 0.3.1, 3.1). Block
kinds (REPRODUCTION, EOM-0) and RELEASE kinds (LEDGER_MATCH) are not classes. -/
inductive RecordClass where
  /-- `RESULT`: a claim, with its derivation. -/
  | result
  /-- `ASSUMPTION`: one declared assumption. -/
  | assumption
  /-- `CORROBORATION`: a matching reproduction of a RESULT. -/
  | corroboration
  /-- `VERIFICATION`: a RESULT compared with an external value (regime M). -/
  | verification
  /-- `WITHDRAWAL`: a strike or a withdrawal; Custos's positional list. -/
  | withdrawal
  /-- `NAMED_GAP`: a gap Custos names; written by Custos alone. -/
  | namedGap
  /-- `ENTRY_STATUS`: the Holder's notes on a Correspondence Table entry. -/
  | entryStatus
  /-- `PROMOTION`: the records a landing promotes; Custos's positional list. -/
  | promotion
  /-- `MASTER`: the register's representation of the Research Assembly. -/
  | master
  /-- `HOLD`: the audit trail of a hold; Custos's positional list. -/
  | hold
  /-- `RELEASE`: the end of a hold; Custos's positional list. -/
  | release
  deriving DecidableEq, Repr, Inhabited

/-- `GRADE_VALUES`: a record's grade. Written once at landing, never rewritten in
place, inside the record digest; a later grade is set by the record that carries
it (a PROMOTION or a WITHDRAWAL) and the current grade is computed. HELD is never
a grade (tpm_record_schema 0.3.1, section 6). -/
inductive Grade where
  /-- `PROVISIONAL` -/
  | provisional
  /-- `ESTABLISHED` -/
  | established
  /-- `REFUTED` -/
  | refuted
  /-- `WITHDRAWN` -/
  | withdrawn
  /-- `NOT GRADED` (one wire word, with its space) -/
  | notGraded
  deriving DecidableEq, Repr, Inhabited

/-- `STATUS`: the in-place mark Custos writes, outside the record digest
(tpm_record_schema 0.3.1, 6.4; DI-RS-1 at its Option 1). -/
inductive RecordStatus where
  /-- `UNMARKED`: neither held nor struck; written at landing. -/
  | unmarked
  /-- `HELD` -/
  | held
  /-- `REFUTED`: the strike's mark. -/
  | refuted
  deriving DecidableEq, Repr, Inhabited

/-- The two forms a record takes (tpm_record_schema 0.3.1, 3.2 and 3.3). -/
inductive RecordLayout where
  /-- `KEYED`: a JSON object whose keys are the class's fields. -/
  | keyed
  /-- `LIST`: Custos's positional list, with its own digest form. -/
  | listForm
  deriving DecidableEq, Repr, Inhabited

instance : WireWord RecordClass where
  members := [.result, .assumption, .corroboration, .verification, .withdrawal,
    .namedGap, .entryStatus, .promotion, .master, .hold, .release]
  toWire
    | .result => "RESULT"
    | .assumption => "ASSUMPTION"
    | .corroboration => "CORROBORATION"
    | .verification => "VERIFICATION"
    | .withdrawal => "WITHDRAWAL"
    | .namedGap => "NAMED_GAP"
    | .entryStatus => "ENTRY_STATUS"
    | .promotion => "PROMOTION"
    | .master => "MASTER"
    | .hold => "HOLD"
    | .release => "RELEASE"
  read_toWire a := by cases a <;> decide

instance : WireWord Grade where
  members := [.provisional, .established, .refuted, .withdrawn, .notGraded]
  toWire
    | .provisional => "PROVISIONAL"
    | .established => "ESTABLISHED"
    | .refuted => "REFUTED"
    | .withdrawn => "WITHDRAWN"
    | .notGraded => "NOT GRADED"
  read_toWire a := by cases a <;> decide

instance : WireWord RecordStatus where
  members := [.unmarked, .held, .refuted]
  toWire
    | .unmarked => "UNMARKED"
    | .held => "HELD"
    | .refuted => "REFUTED"
  read_toWire a := by cases a <;> decide

instance : WireWord RecordLayout where
  members := [.keyed, .listForm]
  toWire
    | .keyed => "KEYED"
    | .listForm => "LIST"
  read_toWire a := by cases a <;> decide

namespace RecordClass

/-- The class's form: the four classes Custos keeps as positional lists, the
rest keyed (the table's `CLASS` lines, third column). -/
def layout : RecordClass → RecordLayout
  | withdrawal | promotion | hold | release => .listForm
  | _ => .keyed

/-- Pushed by the Holder and checked at the push and again at landing (the
table's `PUSH`); otherwise written by Custos alone and never pushed (`TPX` in
v1's table). A CORROBORATION Custos writes on a ledger or parrot MATCH is still
of this pushed class (TPS 3.2.18). -/
def pushed : RecordClass → Bool
  | result | assumption | corroboration | verification | entryStatus => true
  | _ => false

/-- `LANDGRADE`: the grade the class lands with. -/
def landingGrade : RecordClass → Grade
  | result | assumption | corroboration | verification => .provisional
  | _ => .notGraded

/-- `GRADES`: the grades the class can reach, in the table's order. -/
def grades : RecordClass → List Grade
  | result => [.provisional, .established, .refuted, .withdrawn]
  | assumption => [.provisional, .withdrawn]
  | corroboration => [.provisional, .refuted, .withdrawn]
  | verification => [.provisional, .withdrawn]
  | _ => [.notGraded]

/-- `STATUSES`: the statuses the class can carry, in the table's order; empty
for a class that carries no STATUS. -/
def statuses : RecordClass → List RecordStatus
  | result => [.unmarked, .held, .refuted]
  | assumption => [.unmarked, .held]
  | corroboration => [.unmarked, .held, .refuted]
  | verification => [.unmarked, .held]
  | entryStatus => [.unmarked, .held]
  | _ => []

/-- A class lands with a grade it can hold. -/
theorem landingGrade_mem_grades (c : RecordClass) : c.landingGrade ∈ c.grades := by
  cases c <;> decide

/-- A class lands NOT GRADED exactly when NOT GRADED is the only grade it can
hold: an ungraded class never gains a grade. -/
theorem landingGrade_notGraded_iff (c : RecordClass) :
    c.landingGrade = .notGraded ↔ c.grades = [.notGraded] := by
  cases c <;> decide

/-- Only a RESULT can become ESTABLISHED: Custos promotes a standing RESULT,
never an ASSUMPTION or a VERIFICATION (TPS 3.2.12). -/
theorem established_mem_grades_iff (c : RecordClass) :
    Grade.established ∈ c.grades ↔ c = .result := by
  cases c <;> decide

/-- The classes that carry STATUS are exactly the five an account authors and
the Holder pushes; Custos's own classes are never held or struck (6.4). -/
theorem statuses_ne_nil_iff_pushed (c : RecordClass) :
    c.statuses ≠ [] ↔ c.pushed = true := by
  cases c <;> decide

/-- Every class that carries STATUS can carry UNMARKED, the value written at
landing. -/
theorem unmarked_mem_statuses (c : RecordClass) (h : c.pushed = true) :
    RecordStatus.unmarked ∈ c.statuses := by
  cases c <;> simp_all [pushed, statuses]

/-- The strike's mark, STATUS REFUTED, is carried by RESULT and CORROBORATION
only (6.4). -/
theorem refuted_mem_statuses_iff (c : RecordClass) :
    RecordStatus.refuted ∈ c.statuses ↔ c = .result ∨ c = .corroboration := by
  cases c <;> decide

/-- A class that can be struck can also hold the grade REFUTED, which the
strike's WITHDRAWAL sets. -/
theorem refuted_grade_of_refuted_status (c : RecordClass)
    (h : RecordStatus.refuted ∈ c.statuses) : Grade.refuted ∈ c.grades := by
  cases c <;> simp_all [statuses, grades]

/-- Every positional list is Custos's own; none is pushed. -/
theorem pushed_eq_false_of_listForm (c : RecordClass) (h : c.layout = .listForm) :
    c.pushed = false := by
  cases c <;> simp_all [layout, pushed]

end RecordClass

end Principia.Record
