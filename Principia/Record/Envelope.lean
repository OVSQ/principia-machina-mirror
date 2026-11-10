import Principia.Record.Classes

/-!
# The envelope

Every keyed record opens with the envelope (v1's tpm_record_schema 0.3.1, section
4; TPS 0.5.0, 3.2.17). This file holds the envelope's rows of the record table:
which envelope fields each class carries and in what order, and per field its
value type, cardinality, whether it is required, who writes it and whether it
enters the record digest. The class's own fields (a RESULT's STATEMENT,
DERIVATION and the rest) and the per-value constraints (NOTBLANK, UTC, HEX64,
VERSION and the like) come with record_check (Phase 2).

The envelope's vector corpus is generated from the table's `FIELD` lines by a
script beside the library.

PMA words: v1's writer LEAD is the Holder (AI-LEAD), TPX is Custos, and v1's
envelope field TPS, the specification version a push conformed to, is PFS.
-/

namespace Principia.Record

/-- The value types of the record table, a closed list (v1's thirteen "type
classes", tpm_record_schema 0.3.1, section 2; renamed in prose, since a type
class is a Lean mechanism). -/
inductive ValueType where
  /-- `RID`: a register record identifier `<prefix>-n`. -/
  | recordId
  /-- `IDSET`: a set of register identifiers. -/
  | recordIdSet
  /-- `IDENT`: an ASCII identifier. -/
  | identifier
  /-- `TEXT`: a string, LF then NFC, no disallowed code point. -/
  | text
  /-- `DECIMAL`: a decimal string. -/
  | decimal
  /-- `UNIT`: a string in the unit grammar. -/
  | unit
  /-- `DIMENSION`: a string in the DIMENSION grammar. -/
  | dimension
  /-- `FORM`: a string in the declared-form grammar, mode equation. -/
  | declaredForm
  /-- `PREDICATE`: a string in the declared-form grammar, mode predicate. -/
  | predicate
  /-- `ENUM`: one member of a closed enumeration. -/
  | enumeration
  /-- `INT`: a JSON integer within its bounds. -/
  | integer
  /-- `BOOL`: true or false. -/
  | boolean
  /-- `OBJECT`: an object checked against a sub-table. -/
  | object
  deriving DecidableEq, Repr, Inhabited

/-- A field's cardinality, a column of the table (not a value type). -/
inductive Cardinality where
  /-- `ONE`: one value. -/
  | one
  /-- `SET`: members of a set, none repeated. -/
  | set
  /-- `LIST`: a list of objects. -/
  | list
  deriving DecidableEq, Repr, Inhabited

/-- Who writes a field (the table's WRITER column). -/
inductive FieldWriter where
  /-- `AUTHOR`: the record's content, the author's, presented by the Holder. -/
  | author
  /-- `HOLDER`: the identifier of a pushed record, which the Holder allocates
  (v1's `LEAD`). -/
  | holder
  /-- `CUSTOS`: a field Custos writes; refused at the push (v1's `TPX`). -/
  | custos
  deriving DecidableEq, Repr, Inhabited

/-- The envelope's fields, in the order of section 4.1. -/
inductive EnvelopeField where
  /-- `ID`: the record's identifier. -/
  | recordId
  /-- `CLASS`: the record class. -/
  | recordClass
  /-- `GRADE`: the grade at landing. -/
  | grade
  /-- `STATUS`: the in-place mark. -/
  | status
  /-- `BLOCK`: the work block that produced the record. -/
  | block
  /-- `AUTHOR`: the account whose work the record is. -/
  | author
  /-- `LANDED_BY`: the account that requested the landing, or Custos. -/
  | landedBy
  /-- `LANDED`: the server time of the landing. -/
  | landed
  /-- `VETTED_IN`: the Holder's incorporating block. -/
  | vettedIn
  /-- `CITES`: RESULT identifiers. -/
  | cites
  /-- `ASSUMPTIONS`: ASSUMPTION record identifiers. -/
  | assumptions
  /-- `LITERATURE`: BIB IDs, under a BIBLIOGRAPHY SETTING ON or CLOSED. -/
  | literature
  /-- `SUPERSEDES`: the record this one supersedes. -/
  | supersedes
  /-- `INHERITS`: the predecessor's full identifier, on a record a COPY-FORWARD
  writes. -/
  | inherits
  /-- `PFS`: the specification version the push conformed to (v1's `TPS`). -/
  | pfsVersion
  /-- `D_IS`: the instruction set digest the push presented. -/
  | instructionSetDigest
  /-- `DIGEST`: the record digest, outside its own preimage. -/
  | digest
  deriving DecidableEq, Repr, Inhabited

instance : WireWord ValueType where
  members := [.recordId, .recordIdSet, .identifier, .text, .decimal, .unit, .dimension,
    .declaredForm, .predicate, .enumeration, .integer, .boolean, .object]
  toWire
    | .recordId => "RID"
    | .recordIdSet => "IDSET"
    | .identifier => "IDENT"
    | .text => "TEXT"
    | .decimal => "DECIMAL"
    | .unit => "UNIT"
    | .dimension => "DIMENSION"
    | .declaredForm => "FORM"
    | .predicate => "PREDICATE"
    | .enumeration => "ENUM"
    | .integer => "INT"
    | .boolean => "BOOL"
    | .object => "OBJECT"
  read_toWire a := by cases a <;> decide

instance : WireWord Cardinality where
  members := [.one, .set, .list]
  toWire
    | .one => "ONE"
    | .set => "SET"
    | .list => "LIST"
  read_toWire a := by cases a <;> decide

instance : WireWord FieldWriter where
  members := [.author, .holder, .custos]
  toWire
    | .author => "AUTHOR"
    | .holder => "HOLDER"
    | .custos => "CUSTOS"
  read_toWire a := by cases a <;> decide

instance : WireWord EnvelopeField where
  members := [.recordId, .recordClass, .grade, .status, .block, .author, .landedBy,
    .landed, .vettedIn, .cites, .assumptions, .literature, .supersedes, .inherits,
    .pfsVersion, .instructionSetDigest, .digest]
  toWire
    | .recordId => "ID"
    | .recordClass => "CLASS"
    | .grade => "GRADE"
    | .status => "STATUS"
    | .block => "BLOCK"
    | .author => "AUTHOR"
    | .landedBy => "LANDED_BY"
    | .landed => "LANDED"
    | .vettedIn => "VETTED_IN"
    | .cites => "CITES"
    | .assumptions => "ASSUMPTIONS"
    | .literature => "LITERATURE"
    | .supersedes => "SUPERSEDES"
    | .inherits => "INHERITS"
    | .pfsVersion => "PFS"
    | .instructionSetDigest => "D_IS"
    | .digest => "DIGEST"
  read_toWire a := by cases a <;> decide

namespace EnvelopeField

/-- The field's value type (the TYPE column; one for every class). -/
def valueType : EnvelopeField → ValueType
  | recordId | supersedes | inherits => .recordId
  | recordClass | grade | status => .enumeration
  | cites | assumptions | literature => .recordIdSet
  | _ => .text

/-- The field's cardinality (the CARD column). -/
def cardinality : EnvelopeField → Cardinality
  | cites | assumptions | literature => .set
  | _ => .one

/-- Required at the stage its writer writes it (REQ R), or optional (REQ O). -/
def required : EnvelopeField → Bool
  | vettedIn | literature | supersedes | inherits | digest => false
  | _ => true

/-- Inside the record digest (DIG D), or outside it (DIG X): STATUS, written in
place, and DIGEST, outside its own preimage (v1's RD-RS-5). -/
def inDigest : EnvelopeField → Bool
  | status | digest => false
  | _ => true

/-- The writer of the field on a class the Holder pushes: the Holder allocates
the identifier, the author writes CLASS and the citation fields, Custos the
rest. -/
def pushWriter : EnvelopeField → FieldWriter
  | recordId => .holder
  | recordClass | cites | assumptions | literature | supersedes => .author
  | _ => .custos

/-- Only STATUS and DIGEST stay outside the record digest. -/
theorem inDigest_eq_false_iff (f : EnvelopeField) :
    f.inDigest = false ↔ f = .status ∨ f = .digest := by
  cases f <;> decide

end EnvelopeField

namespace RecordClass

/-- The envelope fields the class carries, in the table's order for the class.
A positional list carries none. NAMED_GAP writes PFS before INHERITS, as its
table lines do; a class's own fields stand between these and DIGEST. -/
def envelopeFields : RecordClass → List EnvelopeField
  | result | assumption | corroboration | verification =>
    [.recordId, .recordClass, .grade, .status, .block, .author, .landedBy, .landed,
      .vettedIn, .cites, .assumptions, .literature, .supersedes, .inherits, .pfsVersion,
      .instructionSetDigest, .digest]
  | entryStatus =>
    [.recordId, .recordClass, .grade, .status, .block, .author, .landedBy, .landed,
      .vettedIn, .cites, .assumptions, .literature, .inherits, .pfsVersion,
      .instructionSetDigest, .digest]
  | namedGap =>
    [.recordId, .recordClass, .grade, .landedBy, .landed, .pfsVersion, .inherits, .digest]
  | master =>
    [.recordId, .recordClass, .grade, .landedBy, .landed, .pfsVersion, .digest]
  | withdrawal | promotion | hold | release => []

/-- Whether the class carries the envelope field. -/
def carries (c : RecordClass) (f : EnvelopeField) : Bool :=
  c.envelopeFields.contains f

/-- Who writes the envelope field on a record of the class: on a class Custos
writes alone, Custos writes every field. -/
def writer (c : RecordClass) (f : EnvelopeField) : FieldWriter :=
  if c.pushed then f.pushWriter else .custos

/-- The fields every keyed record carries. -/
def commonFields : List EnvelopeField :=
  [.recordId, .recordClass, .grade, .landedBy, .landed, .pfsVersion, .digest]

/-- A class is keyed exactly when it carries an ID; the positional lists carry
no envelope. -/
theorem layout_keyed_iff (c : RecordClass) :
    c.layout = .keyed ↔ c.carries .recordId = true := by
  cases c <;> decide

/-- Every keyed class carries the common fields. -/
theorem carries_of_mem_commonFields (c : RecordClass) (h : c.layout = .keyed)
    (f : EnvelopeField) (hf : f ∈ commonFields) : c.carries f = true := by
  cases c <;> cases f <;> simp_all [layout, commonFields] <;> decide

/-- The envelope's STATUS row agrees with the STATUSES lines: a class carries
STATUS exactly when it has statuses. -/
theorem carries_status_iff (c : RecordClass) :
    c.carries .status = true ↔ c.statuses ≠ [] := by
  cases c <;> decide

/-- SUPERSEDES is carried by RESULT, ASSUMPTION, CORROBORATION and VERIFICATION;
the newest ENTRY_STATUS of an entry stands for it and names no SUPERSEDES. -/
theorem carries_supersedes_iff (c : RecordClass) :
    c.carries .supersedes = true ↔
      c = .result ∨ c = .assumption ∨ c = .corroboration ∨ c = .verification := by
  cases c <;> decide

/-- No class lists an envelope field twice. -/
theorem envelopeFields_nodup (c : RecordClass) : c.envelopeFields.Nodup := by
  cases c <;> decide

/-- On every keyed class DIGEST is the envelope's last field. -/
theorem envelopeFields_getLast (c : RecordClass) (h : c.layout = .keyed) :
    c.envelopeFields.getLast? = some .digest := by
  cases c <;> simp_all [layout] <;> decide

/-- Custos writes GRADE and STATUS on every class: no pushing account writes a
grade or a status (TPS 3.2.10, 3.2.17). -/
theorem writer_grade_status (c : RecordClass) :
    c.writer .grade = .custos ∧ c.writer .status = .custos := by
  cases c <;> decide

/-- On a class Custos writes alone, Custos writes every field. -/
theorem writer_of_not_pushed (c : RecordClass) (h : c.pushed = false)
    (f : EnvelopeField) : c.writer f = .custos := by
  simp [writer, h]

/-- The digest a record carries is Custos's, written at landing. -/
theorem writer_digest (c : RecordClass) : c.writer .digest = .custos := by
  cases c <;> decide

end RecordClass

end Principia.Record
