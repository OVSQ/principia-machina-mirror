import Principia.Record.Answer
import Principia.Units
import Principia.Form
import Principia.StartingSet.Tests
import Principia.Zone
import Principia.Zone.Preimage
import Principia.Record.StructuredWire
import Principia.Record.DerivationText
import Principia.Record.PmaTable
import Principia.Calculator.Derivation

/-!
# The table's functions: the record check, the preimage, the views

v1's `tpc_record` 0.1.0, the functions the table specifies (tpm_record_schema 0.4.0,
sections 8 to 11; tpm_record_functions 0.3.0, section 3):

* `recordCheck` (v1 `record_check`, schema 8): S1 the class, S2 every field's type and
  form, S3 the table's rules, the checks across fields, S4 T2 on an ASSUMPTION's
  PROPOSITION, S5 the fields against the Research Assembly (v1's TFK) when one is given,
  S6 the DIGEST at landing. Problems REC-01 to REC-40, version 1's; REC-41, the
  DERIVATION's three forms (below); REC-43, the PMA row DERIVATION_CLASS (below); and
  REC-44, a RESULT whose DERIVATION is a bare KERNEL (below). Problem number 42 stays retired and is not reused.
* `recordPreimage` and `recordDigest` (schema 9): the `TPC-RECORD` form 1 field list and
  its digest.
* `recordView` (schema 10): the shapes other functions read a record through.
* `schemaJson` (schema 11): the JSON Schema document generated from the table,
  non-normative, as v1 wrote it.

Digests are SHA-256 (`Principia.Digest`, `Principia.Sha256`): S6, the
record's DIGEST (REC-29); a MASTER's D_TFK, the combination of its D_TPK, D_TRM and D_TMS
(REC-33); and, with a Research Assembly, its zones' digests by the zones' own serializer
(`Principia.Zone.Preimage`, REC-34). Owed (`Principia.Record.Answer`): a number the
Calculator's exact values cannot settle (the Calculator's numbers are exact). Text is read with Unicode 15.1.0's
NFC and general category, as v1 read it, and T2's findings on a
PROPOSITION are the fundamental tests' (`StartingSet.Tests.t2Findings`).

**The DERIVATION's three forms.** The table's DERIVATION sub-table is version 1's
PROSE row `{STEPS: integer, TEXT}`. The check reads the object's shape as
`derivationOfValue` does (`Principia.Record.StructuredWire`): an object with a list `STEPS`,
or a `START`, `PROOF` or `ATTACHMENT` member (`formsShape`), is read by `derivationOfValue`,
a refusal one problem REC-41 at `DERIVATION` with the reader's word; a PROSE derivation so
read (one carrying an attachment) has its `STEPS` and `TEXT` checked by the sub-table as
well. Each text inside a derivation so read is read as the derivation command reads it, a
failure one problem REC-41 at the text's own path (`derivationTextProblems`); a STRUCTURED
or KERNEL DERIVATION passes only when every text in it passes that reading
(`recordCheck_structured_texts`). Any other DERIVATION takes version 1's path unchanged (`recordCheck_prose_unchanged`),
and a STRUCTURED or KERNEL DERIVATION passes only when the reader reads it
(`recordCheck_structured_reads`). TPC-RECORD form 1's preimage writes a
DERIVATION of `formsShape` as one text field, the canonical JSON of `derivationToValue`
applied to the derivation the reader read (`encodeDerivation`), where version 1's PROSE
fields stood; version 1's PROSE DERIVATION is encoded as before, so no version 1 digest
changes. Two derivations with one such field are one derivation
(`encodeDerivation_injective`, by `derivationOfValue_derivationToValue` and the canonical
text's injectivity, `Principia.Record.DerivationText`): a record's steps or PROOF are in its
digest.

**The PMA rows.** DERIVATION_CLASS, which Custos writes at landing, is a row of
the PMA table read beside version 1's (`Principia.Record.PmaTable`), never a line of version
1's text. The check takes a record's PMA rows out before version 1's checks read it
(`eraseRows`): present at the push, a row is REC-07 (written by Custos); at LANDED, a value
outside INSPECTION, MECHANICAL and PROVED is REC-43, and `record_check` refuses a RESULT
without the row REC-43 (`absentProblems`, after S6). The preimage carries the row after
version 1's fields, counted with them (`encodeRecord`), so the digest covers it; a record
without the row has version 1's preimage and digest. Version 1's corpus is run against
`recordCheckV1M`, and `record_check` against it with `Checked.withAbsence`.
**The bare KERNEL.** No check yet credits a KERNEL proof, so `record_check` refuses, at PUSH
and at LANDED, a RESULT whose DERIVATION reads as a bare KERNEL `{PROOF}` with one problem
REC-44 at `DERIVATION` (`kernelProblems`, after the PMA rows' REC-43): the pusher sends PROSE
`{STEPS, TEXT, ATTACHMENT: {PROOF}}`, which lands INSPECTION on its text
(`recordCheckM_bare_kernel_refused`, `kernelProblems_prose`). The rule is `record_check`'s
alone (`RowMode.land`): version 1's check and the preimage's never add it, so no digest
changes. The KERNEL checker lifts it when it credits PROVED.

`schemaJson` is unchanged: the table's text is version 1's ratified text, and the three-form
reading is the check's own rule.

v1's checks of a value nest one level: a sub-object's fields are never objects (the table
has none, which the vector runner checks), so `checkValue` reads an object's fields with
`checkScalar` and needs no recursion.
-/

namespace Principia.Record

open Principia.Canonical (Value)
open Principia.Record.Table
open Principia.Record.PmaTable

/-! ## Reading the Research Assembly argument -/

/-- A JSON value as the zone checks read it (`Principia.Zone.Value`): a number with a
fraction is one v1 read as a float. -/
partial def toZone : Value → Zone.Value
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .num _ => .real
  | .str s => .str s
  | .arr xs => .arr (xs.map toZone)
  | .obj ms => .obj (ms.map fun (k, v) => (k, toZone v))

/-- The list member `k` of an object, `[]` when absent (v1's `tpk.get(kind, [])`); `none`
when present and not a list. -/
def listOr (v : Value) (k : String) : Option (List Value) :=
  match V.get? v k with
  | none => some []
  | some (.arr xs) => some xs
  | some _ => none

/-- A DIMENSION that `normalize_dimension` reads. -/
def dimOk : Option Value → Bool
  | some (.str d) => (Dimension.normalize d).isSome
  | _ => false

/-- v1's `_tfk_ok` (schema 8.2): null, or an object whose TPK and TrM are objects; the
TPK's DOF and CONSTANT lists (absent meaning empty) of objects with a string NAME, a DOF
also with a DIMENSION that reads; the TrM's ENTRIES a list of objects with a string NAME and
a DIMENSION that reads. -/
def assemblyOk : Value → Bool
  | .null => true
  | tfk =>
    match V.get? tfk "TPK", V.get? tfk "TrM" with
    | some tpk@(.obj _), some trm@(.obj _) =>
      let entryOk (needDim : Bool) (e : Value) : Bool :=
        V.isObj e && (V.getStr? e "NAME").isSome && (!needDim || dimOk (V.get? e "DIMENSION"))
      (match listOr tpk "DOF" with
        | some es => es.all (entryOk true)
        | none => false) &&
      (match listOr tpk "CONSTANT" with
        | some es => es.all (entryOk false)
        | none => false) &&
      (match V.get? trm "ENTRIES" with
        | some (.arr es) => es.all (entryOk true)
        | _ => false)
    | _, _ => false

/-- The value under the last occurrence of a key (v1's `dict(...)` keeps the last). -/
def lookupLast {α : Type} (l : List (String × α)) (k : String) : Option α := l.reverse.lookup k

/-- `(NAME, DIMENSION)` of each entry of a list member (`DIMENSION` as given). -/
def namedDims (part : Value) (k : String) : List (String × Option Value) :=
  ((listOr part k).getD []).filterMap fun e =>
    (V.getStr? e "NAME").map fun n => (n, V.get? e "DIMENSION")

/-! ## The precision form of a decimal (v1 `prec_decimal`, functions 7.3) -/

/-- A decimal read as its sign, integer digits I, fraction digits F and exponent
X; D the digits of I then F, leading zeros removed; `0` when D is empty, else the sign, D
(trailing zeros kept) and `e` X - len(F) when that is not 0: the value `canon_decimal`
names, at the decimal's last written digit. `none` when it does not read. -/
def precForm (s : String) : Option String :=
  (Decimal.readParts s.toList).map fun p =>
    let d := (p.ip ++ p.fp).dropWhile (· == '0')
    if d.isEmpty then "0"
    else
      let x : Int := p.ex - p.fp.length
      (if p.neg then "-" else "") ++ String.ofList d ++ (if x != 0 then "e" ++ toString x else "")

/-- A decimal's precision form exists exactly when its canonical form does: one grammar. -/
theorem precForm_isNone (s : String) : (precForm s).isNone = (Decimal.canon s).isNone := by
  unfold precForm Decimal.canon
  cases Decimal.readParts s.toList <;> rfl

/-! ## v1's canonical form of a scalar (schema 9.3) -/

/-- v1's `_canon_scalar`: a field's value in its canonical form. -/
def canonScalar (f : FieldRow) (v : Value) : M Value := do
  match f.type, v with
  | "TEXT", .str s => return .str (← text s)
  | "DECIMAL", .str s =>
    if f.cons.contains "PREC" then return ((precForm s).map Value.str).getD .null
    else return ((Decimal.canon s).map Value.str).getD .null
  | "UNIT", .str s =>
    match Units.unitParse s with
    | .ok p => return .str p.spelling
    | .error r => return .str r
  | "FORM", .str s => formSpelling s .equation
  | "PREDICATE", .str s => formSpelling s .predicate
  | "DIMENSION", .str s => return ((Dimension.normalize s).map Value.str).getD .null
  | "BOOL", .bool b => return .str (if b then "true" else "false")
  | _, _ => return v
where
  /-- `parse_form(v, mode)[1]`: the canonical spelling (or the refusal's text). -/
  formSpelling (s : String) (mode : Form.Mode) : M Value :=
    match Form.parseForm s mode with
    | .ok t => pure (.str t)
    | .refused r => pure (.str r)
    | .owed (.exact w) => throw (.number w)

/-! ## S2: one value -/

/-- v1's `TYPE_PHRASE`. -/
def typePhrase (t card : String) : String :=
  match t, card with
  | "RID", _ => "a record identifier"
  | "IDSET", _ => "a set of record identifiers"
  | "IDENT", "SET" => "a set of identifiers"
  | "IDENT", _ => "an identifier"
  | "TEXT", "SET" => "a set of texts"
  | "TEXT", _ => "a text"
  | "DECIMAL", _ => "a decimal string"
  | "UNIT", _ => "a unit string"
  | "DIMENSION", _ => "a dimension string"
  | "FORM", _ => "a form string"
  | "PREDICATE", _ => "a predicate string"
  | "ENUM", _ => "a string"
  | "INT", _ => "an integer"
  | "BOOL", _ => "a boolean"
  | "OBJECT", "LIST" => "a list of objects"
  | "OBJECT", _ => "an object"
  | _, _ => ""

/-- v1's `FORM_PHRASE`. -/
def formPhrase : String → String
  | "RID" => "a record identifier"
  | "BIBID" => "a BIB ID"
  | "IDENT" => "an identifier"
  | "HEX64" => "64 lowercase hexadecimal characters"
  | "UUID4" => "a version-4 UUID"
  | "VERSION" => "a version n.n.n"
  | "UTC" => "a UTC time YYYY-MM-DDTHH:MM:SSZ"
  | "STEPS" => "an integer from 1 to 1000000"
  | "TPXONLY" => "TPX"
  | "STATELINE" => "a STATE line"
  | "ROLE" => "EOM(<DOF>), CONSTRAINT, CONSTITUTIVE, INVARIANT or DEFINITION"
  | "DIMENSION" => "a dimension"
  | _ => ""

/-- v1's `TEXT_FORMS`, in its order. -/
def textForms : List (String × (String → Bool)) :=
  [("HEX64", isHex64), ("UUID4", isUuid4), ("VERSION", isVersion), ("UTC", utcOk),
   ("STATELINE", statelineOk), ("TPXONLY", (· == "TPX"))]

/-- A record check's state: the class, the problems found, and the paths whose value passed
S2 (v1's `ctx.ok`). -/
structure Ctx where
  cls : String
  problems : List Problem := []
  ok : List String := []

/-- A step of the record check. -/
abbrev CM := StateT Ctx M

/-- Lift an owed computation. -/
def lift {α : Type} (m : M α) : CM α := StateT.lift m

/-- Add a problem. -/
def add (code field msg : String) : CM Unit :=
  modify fun c => { c with problems := c.problems ++ [(code, field, msg)] }

/-- The value at `p` passed S2. -/
def pass (p : String) : CM Unit := modify fun c => { c with ok := c.ok ++ [p] }

/-- Whether the value at `p` passed S2. -/
def passed (p : String) : CM Bool := return (← get).ok.contains p

/-- Drop `p` from the passed paths (v1's `ok.discard`). -/
def unpass (p : String) : CM Unit := modify fun c => { c with ok := c.ok.filter (· != p) }

/-- v1's `_check_value`, S2 (c) and (d), for a value of the right type's kind: the type,
then the form. A wrong type is REC-09. -/
def wrongType (f : FieldRow) (v : Value) : Bool :=
  if f.card == "SET" then
    !(match v with | .arr xs => xs.all V.isStr | _ => false)
  else if f.type == "OBJECT" && f.card == "LIST" then
    !(match v with | .arr xs => xs.all V.isObj | _ => false)
  else if f.type == "OBJECT" then !V.isObj v
  else if f.type == "INT" then !(match v with | .int _ => true | _ => false)
  else if f.type == "BOOL" then !(match v with | .bool _ => true | _ => false)
  else !V.isStr v

/-- v1's `_check_value` for every type but OBJECT: true when the value passed. -/
def checkScalar (f : FieldRow) (v : Value) (path : String) : CM Bool := do
  if wrongType f v then
    add "REC-09" path s!"{path} is not {typePhrase f.type f.card}"
    return false
  let cons := f.cons
  if f.card == "SET" then
    let mut seen : List String := []
    for x in V.members (some v) do
      let c ← (do
        if f.type == "IDSET" then
          let form := if cons.contains "BIBID" then "BIBID" else "RID"
          if !(if form == "BIBID" then isBib x else isRid x) then
            add "REC-19" path s!"{path} member {← lift (showSlot x)} is not {formPhrase form}"
            return none
          return some x
        else if f.type == "IDENT" then
          if !Zone.isIdent x then
            add "REC-19" path s!"{path} member {← lift (showSlot x)} is not {formPhrase "IDENT"}"
            return none
          return some x
        else
          if let some b ← lift (firstBad x) then
            add "REC-10" path s!"{path} holds the disallowed code point {b}"
            return none
          if cons.contains "NOTBLANK" && Zone.blank x then
            add "REC-11" path s!"{path} is blank"
            return none
          return some (← lift (text x)) : CM (Option String))
      match c with
      | none => return false
      | some c =>
        if seen.contains c then
          add "REC-13" path s!"{path} repeats {← lift (showSlot c)}"
          return false
        seen := seen ++ [c]
    return true
  match f.type, v with
  | "RID", .str s | "IDENT", .str s =>
    if !(if f.type == "RID" then isRid s else Zone.isIdent s) then
      add "REC-19" path s!"{path} {← lift (showSlot s)} is not {formPhrase f.type}"
      return false
    return true
  | "TEXT", .str s =>
    if let some b ← lift (firstBad s) then
      add "REC-10" path s!"{path} holds the disallowed code point {b}"
      return false
    if cons.contains "NOTBLANK" && Zone.blank s then
      add "REC-11" path s!"{path} is blank"
      return false
    for (form, test) in textForms do
      if cons.contains form && !test s then
        add "REC-19" path s!"{path} {← lift (showSlot s)} is not {formPhrase form}"
        return false
    return true
  | "ENUM", .str s =>
    if cons.contains "ROLE" then
      if (enumValues "ROLE_WORDS").contains s || (eomName? s).isSome then return true
      add "REC-19" path s!"{path} {← lift (showSlot s)} is not {formPhrase "ROLE"}"
      return false
    if cons.contains "GRADE" then
      if !gradeValues.contains s then
        add "REC-12" path s!"{path} {← lift (showSlot s)} is not one of {orList gradeValues}"
        return false
      let cls := (← get).cls
      let lg := landgradeOf cls
      if s != lg then
        add "REC-32" path s!"GRADE {← lift (showSlot s)} is not {lg}, the landing grade of {cls}"
        return false
      return true
    let cls := (← get).cls
    let vals := if cons.contains "STATUS" then statusesOf cls
      else enumValues ((f.consValue "ENUM=").getD "")
    if !vals.contains s then
      add "REC-12" path s!"{path} {← lift (showSlot s)} is not one of {orList vals}"
      return false
    return true
  | "DECIMAL", .str s =>
    match Decimal.canon s with
    | none =>
      add "REC-14" path s!"{path} {← lift (showSlot s)} is not a decimal"
      return false
    | some c =>
      if cons.contains "POSITIVE" && (c == "0" || c.startsWith "-") then
        add "REC-15" path s!"{path} {← lift (showSlot s)} is not positive"
        return false
      if cons.contains "NONNEG" && c.startsWith "-" then
        add "REC-16" path s!"{path} {← lift (showSlot s)} is negative"
        return false
      return true
  | "UNIT", .str s =>
    match Units.tokens s with
    | .error r =>
      add "REC-17" path s!"{path}: {Zone.escape r}"
      return false
    | .ok _ => return true
  | "FORM", .str s | "PREDICATE", .str s =>
    match Form.parseForm s (if f.type == "FORM" then .equation else .predicate) with
    | .ok _ => return true
    | .refused r =>
      add "REC-18" path s!"{path}: {r}"
      return false
    | .owed (.exact w) => lift (throw (.number w))
  | "DIMENSION", .str s =>
    if (Dimension.normalize s).isNone then
      add "REC-19" path s!"{path} {← lift (showSlot s)} is not {formPhrase "DIMENSION"}"
      return false
    return true
  | "INT", .int n =>
    if cons.contains "STEPS" && !(1 ≤ n && n ≤ 1000000) then
      add "REC-19" path s!"{path} {n} is not {formPhrase "STEPS"}"
      return false
    return true
  | _, _ => return true

/-- v1's `_check_object`: unknown fields (REC-06), then each field of the sub-object,
missing (REC-08) or checked. -/
def checkObject (fields : List FieldRow) (obj : Value) (path : String) : CM Unit := do
  let names := fields.map (·.name)
  for k in V.keys obj do
    if !names.contains k then
      let k' ← lift (showSlot k)
      add "REC-06" s!"{path}.{k'}" s!"unknown field {path}.{k'}"
  for f in fields do
    let p := s!"{path}.{f.name}"
    match V.get? obj f.name with
    | some x => if ← checkScalar f x p then pass p
    | none => if f.req == "R" then add "REC-08" p s!"{p} is missing"

/-- The sub-object's fields of an OBJECT field. -/
def subFields (f : FieldRow) : List FieldRow := fieldsOf ("SUB:" ++ (f.consValue "SUB=").getD "")

/-- The key of a list member, in its canonical form, as text. -/
def keyText (kf : Option FieldRow) (v : Option Value) : M String := do
  match kf, v with
  | some kf, some v =>
    match ← canonScalar kf v with
    | .str s => pure s
    | w => pure (cj w)
  | _, _ => pure ""

/-- v1's `_check_value`: an OBJECT field's sub-objects, or any other field's value. -/
def checkValue (f : FieldRow) (v : Value) (path : String) : CM Bool := do
  if f.type != "OBJECT" then return ← checkScalar f v path
  if wrongType f v then
    add "REC-09" path s!"{path} is not {typePhrase f.type f.card}"
    return false
  let sub := (f.consValue "SUB=").getD ""
  let sfields := subFields f
  if f.card == "ONE" then
    checkObject sfields v path
    return true
  let os := match v with | .arr os => os | _ => []
  if f.cons.contains "NONEMPTY" && os.isEmpty then
    add "REC-35" path s!"{path} is empty"
    return false
  let key := subkeyOf sub
  let mut keys : List String := []
  for (o, i) in os.zipIdx 1 do
    checkObject sfields o s!"{path}[{i}]"
    if let some k := key then
      if ← passed s!"{path}[{i}].{k}" then
        keys := keys ++ [← lift (keyText (fieldNamed sfields k) (V.get? o k))]
  let mut seen : List String := []
  for kv in keys do
    if seen.contains kv then
      add "REC-13" path s!"{path} repeats {← lift (showSlot kv)}"
      return false
    seen := seen ++ [kv]
  return true

/-! ## The DERIVATION's three forms -/

/-- Whether a DERIVATION value is in a shape version 1's sub-table does not read: an object
with a list `STEPS`, or a `START`, `PROOF` or `ATTACHMENT` member. -/
def formsShape (v : Value) : Bool :=
  (match V.get? v "STEPS" with | some (.arr _) => true | _ => false) ||
    V.has v "START" || V.has v "PROOF" || V.has v "ATTACHMENT"

/-- Whether a record's DERIVATION is of `formsShape`. -/
def derivationForms (record : Value) : Bool :=
  match V.get? record "DERIVATION" with
  | some v => formsShape v
  | none => false

/-! ## The texts inside a derivation

Each text inside a DERIVATION of `formsShape` is read as the derivation command reads it
before it credits: the steps counted against `maxSteps`; a step's EQUATION and a START's
EXPRESSION within `maxEquation` code points (`textWithin`) and read by the declared-form
grammar (`Equation.parse`, `parseExpr`); a SITE read as the checker reads it (`readSite`);
an identity's name on the checker's list (`Identity.ofName?`). A name a step or a START
cites holds no disallowed code point and is not blank. A PROOF, the KERNEL's or an
attachment's, meets the record table's TEXT rules: no disallowed code point, line ends LF,
NFC, not blank, within the bound. Each text that fails is one problem at its own path. -/

open Principia.Calculator.Derivation (maxSteps maxEquation textWithin)
open Principia.StructuredCheck (readSite parseExpr)

/-- A bound's refusal as its word, `none` within the bound. -/
def boundWord : Except Calculator.Refusal Unit → Option String
  | .error r => some r.detail
  | .ok () => none

/-- Why a name a step or a START cites does not read: a disallowed code point, or blank. -/
def nameWord (s : String) : Option String :=
  match Zone.firstBad s with
  | some b => some s!"holds the disallowed code point {b}"
  | none => if Zone.blank s then some "is blank" else none

/-- Why a step's EQUATION does not read: past the bound, or not an equation of the
declared-form grammar (the checker's `equation-unreadable`). -/
def equationWord (s : String) : Option String :=
  match boundWord (textWithin "a step's EQUATION" s) with
  | some w => some w
  | none =>
    match StructuredCheck.Equation.parse s with
    | .ok _ => none
    | .error r => some s!"equation-unreadable: {r}"

/-- Why a START's EXPRESSION does not read: past the bound, or not an expression of the
declared-form grammar (the checker's `start-unreadable`). -/
def expressionWord (s : String) : Option String :=
  match boundWord (textWithin "the START's EXPRESSION" s) with
  | some w => some w
  | none =>
    match parseExpr s with
    | .ok _ => none
    | .error r => some s!"start-unreadable: {r}"

/-- Why a SITE does not read: the checker's word. -/
def siteWord (s : String) : Option String :=
  match readSite s with
  | .ok _ => none
  | .error w => some w

/-- Why an identity's name does not read: not on the checker's list. -/
def identityWord (s : String) : Option String :=
  match StructuredCheck.Identity.ofName? s with
  | some _ => none
  | none => some "unknown-identity"

/-- Why a PROOF does not meet the TEXT rules: a disallowed code point, a CR, not NFC,
blank, or past the bound. -/
def proofWord (s : String) : Option String :=
  match Zone.firstBad s with
  | some b => some s!"holds the disallowed code point {b}"
  | none =>
    if s.toList.contains '\r' then some "holds a CR: its line ends are not LF"
    else if Zone.text s != s then some "is not in NFC"
    else if Zone.blank s then some "is blank"
    else boundWord (textWithin "the PROOF" s)

/-- A problem at `p` when the word is there. -/
def atPath (p : String) : Option String → List (String × String)
  | some w => [(p, w)]
  | none => []

/-- The problems of a citation's name at a step or START path `p`. -/
def citationProblems (p : String) : StepCitation → List (String × String)
  | .law n => atPath (p ++ ".LAW") (nameWord n)
  | .assumption r => atPath (p ++ ".ASSUMPTION") (nameWord r)
  | .identity n => atPath (p ++ ".IDENTITY") (identityWord n)

/-- The problems of one step at `p`: its EQUATION, its citation, its SITE. -/
def stepProblems (p : String) (st : StructuredStep) : List (String × String) :=
  atPath (p ++ ".EQUATION") (equationWord st.equation) ++ citationProblems p st.cites ++
    atPath (p ++ ".SITE") (siteWord st.site)

/-- The problems of the steps, numbered from `i`, under `path`. -/
def stepsProblems (path : String) : List StructuredStep → Nat → List (String × String)
  | [], _ => []
  | st :: sts, i => stepProblems s!"{path}.STEPS[{i}]" st ++ stepsProblems path sts (i + 1)

/-- The problems of a START under `path`. -/
def startProblems (path : String) : StructuredStart → List (String × String)
  | .lhs => []
  | .law n => atPath (path ++ ".START.LAW") (nameWord n)
  | .assumption r => atPath (path ++ ".START.ASSUMPTION") (nameWord r)
  | .refl e => atPath (path ++ ".START.EXPRESSION") (expressionWord e)

/-- The problems of a STRUCTURED payload under `path`: more steps than the bound, else its
START's and its steps' texts. -/
def payloadProblems (path : String) (steps : List StructuredStep) (start : StructuredStart) :
    List (String × String) :=
  if maxSteps < steps.length then
    [(path ++ ".STEPS", s!"the derivation's STEPS holds more than {maxSteps} entries (the Calculator's bound)")]
  else startProblems path start ++ stepsProblems path steps 1

/-- The problems of every text inside a derivation read at `path`, each with its own path:
a STRUCTURED payload's, a KERNEL PROOF, an attachment's. -/
def derivationTextProblems (path : String) : Derivation → List (String × String)
  | .structured steps start => payloadProblems path steps start
  | .kernelProof p => atPath (path ++ ".PROOF") (proofWord p)
  | .prose _ _ (some (.structured steps start)) => payloadProblems (path ++ ".ATTACHMENT") steps start
  | .prose _ _ (some (.kernelProof p)) => atPath (path ++ ".ATTACHMENT.PROOF") (proofWord p)
  | .prose _ _ none => []

/-- Add one REC-41 for each text problem. -/
def addTextProblems : List (String × String) → CM Unit
  | [] => pure ()
  | (p, w) :: ps => do
    add "REC-41" p s!"{p} does not read as the derivation command reads it: {Zone.escape w}"
    addTextProblems ps

/-- The check of a DERIVATION of `formsShape`: read by `derivationOfValue`, a refusal
REC-41; each text inside it read as the derivation command reads it, each failure REC-41 at
the text's path (`derivationTextProblems`); a PROSE derivation's `STEPS` and `TEXT` by the
sub-table. True when the value passed. At LANDED the preimage encodes the derivation read
(`encodeDerivation`). -/
def checkDerivationForms (f : FieldRow) (v : Value) (path : String) : CM Bool := do
  match derivationOfValue v with
  | .error w =>
    add "REC-41" path s!"{path} does not read as a derivation: {Zone.escape w}"
    return false
  | .ok d =>
    let ps := derivationTextProblems path d
    addTextProblems ps
    match d with
    | .prose .. =>
      checkObject (subFields f) (V.erase v "ATTACHMENT") path
      return ps.isEmpty
    | _ => return ps.isEmpty

/-- What `checkDerivationForms` answers: the reader's refusal, or the derivation read and
the text problems found in it. -/
theorem checkDerivationForms_true (f : FieldRow) (v : Value) (path : String)
    (c c' : Ctx) (h : (checkDerivationForms f v path).run c = .ok (true, c')) :
    ∃ d, derivationOfValue v = .ok d ∧ derivationTextProblems path d = [] := by
  unfold checkDerivationForms at h
  cases hd : derivationOfValue v with
  | error w =>
    simp [hd, add, StateT.run, bind, StateT.bind, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure,
      Except.bind] at h
  | ok d =>
    refine ⟨d, rfl, ?_⟩
    rw [hd] at h
    simp only [StateT.run, bind, StateT.bind] at h
    cases ha : (addTextProblems (derivationTextProblems path d)) c with
    | error e => rw [ha] at h; cases h
    | ok r =>
      rw [ha] at h
      obtain ⟨u, c1⟩ := r
      cases d with
      | prose n t a =>
        simp only [Except.bind, StateT.bind] at h
        cases hc : checkObject (subFields f) (V.erase v "ATTACHMENT") path c1 with
        | error e => rw [hc] at h; cases h
        | ok r2 =>
          rw [hc] at h
          simp [pure, StateT.pure, Except.pure, bind, Except.bind] at h
          exact h.1
      | structured s st =>
        simp [Except.bind, pure, StateT.pure, Except.pure] at h
        exact h.1
      | kernelProof p =>
        simp [Except.bind, pure, StateT.pure, Except.pure] at h
        exact h.1

/-- **A STRUCTURED or KERNEL DERIVATION passes only when the reader reads it**: when the
field check of a DERIVATION of `formsShape` passes, `derivationOfValue` reads the value. -/
theorem recordCheck_structured_reads (f : FieldRow) (v : Value) (path : String)
    (c c' : Ctx) (h : (checkDerivationForms f v path).run c = .ok (true, c')) :
    ∃ d, derivationOfValue v = .ok d :=
  let ⟨d, hd, _⟩ := checkDerivationForms_true f v path c c' h
  ⟨d, hd⟩

theorem atPath_nil (p : String) (w : Option String) : atPath p w = [] ↔ w = none := by
  cases w <;> simp [atPath]

theorem siteWord_none {s : String} (h : siteWord s = none) : ∃ x, readSite s = .ok x := by
  unfold siteWord at h
  cases hr : readSite s with
  | ok x => exact ⟨x, rfl⟩
  | error w => rw [hr] at h; cases h

theorem identityWord_none {s : String} (h : identityWord s = none) :
    ∃ i, StructuredCheck.Identity.ofName? s = some i := by
  unfold identityWord at h
  cases hr : StructuredCheck.Identity.ofName? s with
  | some i => exact ⟨i, rfl⟩
  | none => rw [hr] at h; cases h

theorem equationWord_none {s : String} (h : equationWord s = none) :
    textWithin "a step's EQUATION" s = .ok () ∧
      ∃ e, StructuredCheck.Equation.parse s = .ok e := by
  unfold equationWord boundWord at h
  cases ht : textWithin "a step's EQUATION" s with
  | error r => rw [ht] at h; cases h
  | ok u =>
    rw [ht] at h
    cases hp : StructuredCheck.Equation.parse s with
    | error r => rw [hp] at h; cases h
    | ok e => exact ⟨rfl, e, rfl⟩

theorem expressionWord_none {s : String} (h : expressionWord s = none) :
    textWithin "the START's EXPRESSION" s = .ok () ∧ ∃ e, parseExpr s = .ok e := by
  unfold expressionWord boundWord at h
  cases ht : textWithin "the START's EXPRESSION" s with
  | error r => rw [ht] at h; cases h
  | ok u =>
    rw [ht] at h
    cases hp : parseExpr s with
    | error r => rw [hp] at h; cases h
    | ok e => exact ⟨rfl, e, rfl⟩

/-- A step without problems is read by the checker, and its EQUATION is within the bound. -/
theorem readStep_of_stepProblems {p : String} {st : StructuredStep} (h : stepProblems p st = []) :
    textWithin "a step's EQUATION" st.equation = .ok () ∧
      ∃ s, StructuredCheck.readStep st = .ok s := by
  simp only [stepProblems, List.append_eq_nil_iff, atPath_nil] at h
  obtain ⟨⟨he, hc⟩, hsite⟩ := h
  obtain ⟨hw, e, hpe⟩ := equationWord_none he
  obtain ⟨⟨side, path⟩, hx⟩ := siteWord_none hsite
  refine ⟨hw, ?_⟩
  obtain ⟨eq, cites, site, fwd⟩ := st
  simp only at hpe hx hw
  cases cites with
  | law n =>
    exact ⟨⟨side, path, .cite (.law n) fwd, e⟩, by
      simp [StructuredCheck.readStep, hx, hpe, bind, Except.bind, pure, Except.pure]⟩
  | assumption r =>
    exact ⟨⟨side, path, .cite (.assumption r) fwd, e⟩, by
      simp [StructuredCheck.readStep, hx, hpe, bind, Except.bind, pure, Except.pure]⟩
  | identity n =>
    simp only [citationProblems, atPath_nil] at hc
    obtain ⟨i, hi⟩ := identityWord_none hc
    exact ⟨⟨side, path, .identity i fwd, e⟩, by
      simp [StructuredCheck.readStep, hx, hpe, hi, bind, Except.bind, pure, Except.pure]⟩

/-- Steps without problems are read by the checker, each EQUATION within the bound. -/
theorem readSteps_of_stepsProblems (path : String) :
    ∀ (steps : List StructuredStep) (i : Nat), stepsProblems path steps i = [] →
      (∀ st ∈ steps, textWithin "a step's EQUATION" st.equation = .ok ()) ∧
      ∃ ss, StructuredCheck.readSteps steps i = .ok ss
  | [], _, _ => ⟨by simp, [], rfl⟩
  | st :: sts, i, h => by
    simp only [stepsProblems, List.append_eq_nil_iff] at h
    obtain ⟨hs, hr⟩ := h
    obtain ⟨hall, ss, hss⟩ := readSteps_of_stepsProblems path sts (i + 1) hr
    obtain ⟨hw, s, hs'⟩ := readStep_of_stepProblems hs
    refine ⟨?_, s :: ss, by simp [StructuredCheck.readSteps, hs', hss]⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact hall x hx

/-- A START without problems is read by the checker, whatever the RESULT's EQUATION, and its
EXPRESSION is within the bound. -/
theorem readStart_of_startProblems (path : String) (st : StructuredStart)
    (h : startProblems path st = []) :
    (match st with
      | .refl e => textWithin "the START's EXPRESSION" e
      | _ => pure ()) = .ok () ∧
    ∀ goal, ∃ s, StructuredCheck.readStart goal st = .ok s := by
  cases st with
  | lhs => exact ⟨rfl, fun _ => ⟨_, rfl⟩⟩
  | law n => exact ⟨rfl, fun _ => ⟨_, rfl⟩⟩
  | assumption r => exact ⟨rfl, fun _ => ⟨_, rfl⟩⟩
  | refl e =>
    simp only [startProblems, atPath_nil] at h
    obtain ⟨hw, x, hx⟩ := expressionWord_none h
    exact ⟨hw, fun _ => ⟨.refl x, by simp [StructuredCheck.readStart, hx]⟩⟩

theorem forM_textWithin_ok (steps : List StructuredStep)
    (h : ∀ st ∈ steps, textWithin "a step's EQUATION" st.equation = .ok ()) :
    steps.forM (fun st => textWithin "a step's EQUATION" st.equation) = .ok () := by
  induction steps with
  | nil => rfl
  | cons s ss ih =>
    have h1 := h s (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    show (do textWithin "a step's EQUATION" s.equation; ss.forM _) = _
    rw [h1]
    exact h2

/-- A STRUCTURED payload without problems is within the command's bounds and read by the
checker: at most `maxSteps` steps, its texts within `maxEquation`, its steps and its START
read. -/
theorem payload_of_payloadProblems (path : String) (steps : List StructuredStep)
    (start : StructuredStart) (h : payloadProblems path steps start = []) :
    steps.length ≤ maxSteps ∧
      Calculator.Derivation.payloadWithin steps start = .ok () ∧
      (∃ ss, StructuredCheck.readSteps steps 1 = .ok ss) ∧
      ∀ goal, ∃ s, StructuredCheck.readStart goal start = .ok s := by
  unfold payloadProblems at h
  split at h
  · cases h
  · rename_i hlen
    rw [List.append_eq_nil_iff] at h
    obtain ⟨hst, hss⟩ := h
    obtain ⟨hall, hread⟩ := readSteps_of_stepsProblems path steps 1 hss
    obtain ⟨hsw, hstart⟩ := readStart_of_startProblems path start hst
    refine ⟨by omega, ?_, hread, hstart⟩
    unfold Calculator.Derivation.payloadWithin
    simp only [bind, Except.bind, forM_textWithin_ok steps hall]
    cases start <;> simp_all <;> rfl

/-- **A STRUCTURED or KERNEL DERIVATION passes only when every text in it passes the
command's reading**: when the field check of a DERIVATION of `formsShape` passes, the reader
reads it, no text in it has a problem, the derivation command's bounds hold of it
(`derivationWithin`), and each STRUCTURED payload in it, its own or an attachment's, has at
most `maxSteps` steps whose texts the checker reads, and a START the checker reads. -/
theorem recordCheck_structured_texts (f : FieldRow) (v : Value) (path : String)
    (c c' : Ctx) (h : (checkDerivationForms f v path).run c = .ok (true, c')) :
    ∃ d, derivationOfValue v = .ok d ∧ derivationTextProblems path d = [] ∧
      Calculator.Derivation.derivationWithin d = .ok () ∧
      ∀ steps start, (d = .structured steps start ∨
          ∃ n t, d = .prose n t (some (.structured steps start))) →
        steps.length ≤ maxSteps ∧ (∃ ss, StructuredCheck.readSteps steps 1 = .ok ss) ∧
          ∀ goal, ∃ s, StructuredCheck.readStart goal start = .ok s := by
  obtain ⟨d, hd, hp⟩ := checkDerivationForms_true f v path c c' h
  refine ⟨d, hd, hp, ?_, ?_⟩
  · cases d with
    | structured steps start =>
      exact (payload_of_payloadProblems path steps start hp).2.1
    | _ => rfl
  · intro steps start hs
    rcases hs with rfl | ⟨n, t, rfl⟩
    · obtain ⟨h1, -, h3, h4⟩ := payload_of_payloadProblems path steps start hp
      exact ⟨h1, h3, h4⟩
    · obtain ⟨h1, -, h3, h4⟩ := payload_of_payloadProblems (path ++ ".ATTACHMENT") steps start hp
      exact ⟨h1, h3, h4⟩

/-! ## S3: the table's rules -/

/-- v1's `_cond_true`. -/
def condTrue (c : Option Cond) (rec : Value) : Bool :=
  match c with
  | none => true
  | some c =>
    if c.op == "PRESENT" then V.has rec c.field
    else if c.op == "ABSENT" then !V.has rec c.field
    else V.get? rec c.field == some (.str c.value)

/-- v1's `_cond_text`. -/
def condText : Option Cond → String
  | some c =>
    if c.op == "PRESENT" then s!"{c.field} is present"
    else if c.op == "ABSENT" then s!"{c.field} is absent"
    else s!"{c.field} is {c.value}"
  | none => ""

/-! ## S5: the fields against the Research Assembly -/

/-- v1's `_tfk_checks` over the fields of one object that passed S2: the names a field
must find in the TPK or the TrM (REC-25), then the dimension a unit must have (REC-26). -/
def assemblyFields (tfk obj : Value) (fields : List FieldRow) (pre : String) : CM Unit := do
  let tpk := (V.get? tfk "TPK").getD .null
  let trm := (V.get? tfk "TrM").getD .null
  let dofs := namedDims tpk "DOF"
  let consts := (namedDims tpk "CONSTANT").map Prod.fst
  let ents := namedDims trm "ENTRIES"
  let mut resolved : List (String × Option Value) := []
  for f in fields do
    let n := f.name
    let p := pre ++ n
    unless ← passed p do continue
    let v := (V.get? obj n).getD .null
    let cons := f.cons
    if cons.contains "TPKNAME" then
      let xs := if f.card == "SET" then V.members (some v) else (match v with | .str s => [s] | _ => [])
      for x in xs do
        if (lookupLast dofs x).isNone && !consts.contains x then
          add "REC-25" p s!"{p} {if f.card == "SET" then "member " else ""}{← lift (showSlot x)} is not a DOF or CONSTANT of the TPK"
          break
    if cons.contains "TPKDOF" then
      match v with
      | .str s =>
        match lookupLast dofs s with
        | some d => resolved := resolved ++ [(n, d)]
        | none => add "REC-25" p s!"{p} {← lift (showSlot s)} is not a DOF of the TPK"
      | _ => pure ()
    if cons.contains "TRMENTRY" then
      if f.card == "SET" then
        for x in V.members (some v) do
          if (lookupLast ents x).isNone then
            add "REC-25" p s!"{p} member {← lift (showSlot x)} is not an entry of the TrM"
            break
      else
        match v with
        | .str s =>
          match lookupLast ents s with
          | some d => resolved := resolved ++ [(n, d)]
          | none => add "REC-25" p s!"{p} {← lift (showSlot s)} is not an entry of the TrM"
        | _ => pure ()
  for f in fields do
    let n := f.name
    let p := pre ++ n
    unless ← passed p do continue
    for c in f.cons do
      if c == "DIM=QUANTITY" || c == "DIM=DOF" then
        let target := String.ofList (c.toList.drop 4)
        if let some d := lookupLast resolved target then
          let want := match d with
            | some (.str s) => (Dimension.normalize s).getD ""
            | _ => ""
          match V.get? obj n with
          | some (.str u) =>
            match Units.unitParse u with
            | .ok pu =>
              if pu.dimension != want then
                add "REC-26" p s!"{p} {← lift (showSlot u)} has dimension {pu.dimension}, not {want}"
            | .error _ => pure ()
          | _ => pure ()

/-- v1's `_tfk_checks` over a record: its own fields, then each sub-object's. -/
def assemblyChecks (tfk record : Value) (fields : List FieldRow) : CM Unit := do
  assemblyFields tfk record fields ""
  for f in fields do
    if f.type == "OBJECT" then
      unless ← passed f.name do continue
      let v := (V.get? record f.name).getD .null
      if f.card == "ONE" then
        assemblyFields tfk v (subFields f) (f.name ++ ".")
      else
        let os := match v with | .arr os => os | _ => []
        for (o, i) in os.zipIdx 1 do
          assemblyFields tfk o (subFields f) s!"{f.name}[{i}]."

/-- A member, or null. -/
def getOrNull (v : Value) (k : String) : Value := (V.get? v k).getD .null

/-- Whether the zone checks pass a zone of the Research Assembly (v1's `_zone_digest`
reads only that before digesting it): `none` when the zone check owes its verdict (the
Calculator's numbers are exact). -/
def zoneGood (tfk : Value) (zn : String) : M (Option Bool) := do
  match V.get? tfk zn with
  | some zone@(.obj _) =>
    let z := toZone zone
    let units := Zone.UnitHook.calculator
    let verdict : Option Zone.Verdict :=
      if zn == "TPK" then some (StartingSet.wellFormed units z)
      else if zn == "TrM" then
        match V.get? tfk "TPK" with
        | some tpk@(.obj _) => some (Correspondence.wellFormed units z (toZone tpk))
        | _ => none
      else some (Criteria.wellFormed units z)
    -- A zone the zone check owes to the declared forms is still refused by the problems
    -- found without them, which v1's check finds as well.
    let without : List String :=
      if zn == "TPK" then StartingSet.problems units z
      else if zn == "TrM" then Correspondence.problems units z (toZone (getOrNull tfk "TPK"))
      else Criteria.problems units z
    match verdict with
    | none => pure (some false)
    | some (.checked ps) => pure (some ps.isEmpty)
    | some (.owed _) => pure (if without.isEmpty then none else some false)
  | _ => pure (some false)

/-- v1's `_zone_digest` of a zone the zone check passed: D(TPK), D(TrM) or D(TMS) by the
zones' serializer (`Principia.Zone.Preimage`), or the serializer's refusal. -/
def zoneDigestOf (tfk : Value) (zn : String) : Except Zone.Fault String :=
  match Zone.ZoneName.ofString? zn, V.get? tfk zn with
  | some name, some zone => Zone.zoneDigest name (toZone zone)
  | _, _ => .error ("the TFK has no zone " ++ zn)

/-! ## The canonical form and the preimage (schema 9) -/

/-- v1's `_forbidden`: the fields a FORBID rule that holds names. -/
def forbidden (cls : String) (rec : Value) : List String :=
  (rulesOf cls).flatMap fun r => if r.action == "FORBID" && condTrue r.cond rec then r.fields else []

/-- Strings sorted in code point order. -/
def sortStrings (xs : List String) : List String := xs.mergeSort fun a b => decide (a ≤ b)

/-- v1's `_encode_obj`: a sub-object's present fields, counted, each name then value. -/
def encodeObj (sf : List FieldRow) (o : Value) : M (List Value) := do
  let pres := sf.filter fun f => V.has o f.name
  let mut out : List Value := [.int pres.length]
  for f in pres do
    out := out ++ [.str f.name, ← canonScalar f ((V.get? o f.name).getD .null)]
  return out

/-- v1's `_encode`: one field's value as preimage fields. -/
def encode (f : FieldRow) (v : Value) : M (List Value) := do
  if f.card == "SET" then
    let xs := V.members (some v)
    let mem ← if f.type == "TEXT" then xs.mapM text else pure xs
    let mem := sortStrings mem
    return .int mem.length :: mem.map Value.str
  if f.type == "OBJECT" then
    let sf := subFields f
    if f.card == "ONE" then return ← encodeObj sf v
    let os := match v with | .arr os => os | _ => []
    let kf := (subkeyOf ((f.consValue "SUB=").getD "")).bind (fieldNamed sf)
    let keyed ← os.mapM fun o => do
      return (← keyText kf (kf.bind fun k => V.get? o k.name), o)
    let sorted := keyed.mergeSort fun a b => decide (a.1 ≤ b.1)
    let mut out : List Value := [.int sorted.length]
    for (_, o) in sorted do
      out := out ++ (← encodeObj sf o)
    return out
  if f.type == "INT" then return [v]
  return [← canonScalar f v]

/-- The `TPC-RECORD` form 1 encoding of a DERIVATION of `formsShape`: one
text field, the canonical JSON of the derivation read, where version 1's PROSE fields
stood. -/
def encodeDerivation (d : Derivation) : List Value := [.str (cj (derivationToValue d))]

/-- The derivation a field's value is read as when it is the DERIVATION and of
`formsShape`; `none` for every other field and for version 1's PROSE DERIVATION. -/
def derivationRead (f : FieldRow) (v : Value) : Option Derivation :=
  if f.name == "DERIVATION" && formsShape v then
    match derivationOfValue v with
    | .ok d => some d
    | .error _ => none
  else none

/-- **The DERIVATION's steps and PROOF are in the preimage**: two derivations of
`formsShape` whose `TPC-RECORD` form 1 fields are one are one derivation, its form, its
steps, its START and its PROOF included. -/
theorem encodeDerivation_injective {d d' : Derivation}
    (h : encodeDerivation d = encodeDerivation d') : d = d' := by
  simp only [encodeDerivation, List.cons.injEq, Value.str.injEq, and_true] at h
  exact cj_derivationToValue_injective h

/-- The `TPC-RECORD` form 1 encoding of the PMA rows a record carries: each
row's name, then its value, after version 1's fields. -/
def encodeRows (rows : List (FieldRow × Value)) : List Value :=
  rows.flatMap fun (f, v) => [.str f.name, v]

/-- The `TPC-RECORD` form 1 field list of a record that passed the check, its DIGEST
removed (v1's `record_preimage` after its check); a DERIVATION of `formsShape` by
`encodeDerivation`; the PMA rows `rows` (taken out of `rec`) after version 1's fields, counted
with them. With no PMA row it is version 1's field list. -/
def encodeRecord (rec : Value) (rows : List (FieldRow × Value) := []) : M (List Value) := do
  let cls := (V.getStr? rec "CLASS").getD ""
  let forb := forbidden cls rec
  let mut body : List Value := []
  let mut n := 0
  for f in fieldsOf cls do
    if f.dig != "D" then continue
    let v? : Option Value :=
      match V.get? rec f.name with
      | some v => some v
      | none =>
        if f.default == "EMPTY" && !forb.contains f.name then some (.arr [])
        else if f.default == "FALSE" && !forb.contains f.name then some (.bool false)
        else none
    match v? with
    | none => pure ()
    | some v =>
      n := n + 1
      let enc ← match derivationRead f v with
        | some d => pure (encodeDerivation d)
        | none => encode f v
      body := body ++ [.str f.name] ++ enc
  return [.str "TPC-RECORD", .str "1", .int (n + rows.length)] ++ body ++ encodeRows rows

/-- A preimage's values as digest fields. -/
def digestFields (vs : List Value) : List Digest.Field :=
  vs.map fun
    | .int n => .int n
    | .str s => .text s
    | v => .text (cj v)

/-! ## record_check (schema 8) -/

/-- The record check's outcome: its problems. -/
structure Checked where
  problems : List Problem
  /-- S2 to S6 ran: the record passed the checks of stage, setting, Research Assembly and
  class that answer one problem alone. -/
  ran : Bool := false

/-- One problem, and nothing else checked. -/
def Checked.one (code field msg : String) : Checked := { problems := [(code, field, msg)] }

/-- S2 to S6 over a keyed record of class `cv`; `forms` true reads the DERIVATION by its
shape (`checkDerivationForms`), false is version 1's check. -/
def checkRecordCore (forms : Bool) (rows : List (FieldRow × Value)) (record tfk setting : Value)
    (stage cv : String) : CM Unit := do
  let fields := fieldsOf cv
  let names := fields.map (·.name)
  -- S2
  for k in V.keys record do
    if !names.contains k then
      let k' ← lift (showSlot k)
      add "REC-06" k' s!"unknown field {k'}"
  for f in fields do
    let n := f.name
    match V.get? record n with
    | some x =>
      if stage == "PUSH" && f.writer == "TPX" then
        add "REC-07" n s!"{n} is written by TPX"
        continue
      if ← (if forms && n == "DERIVATION" && f.type == "OBJECT" then
          checkDerivationForms f x n else checkValue f x n) then pass n
    | none =>
      if f.req == "R" && (stage == "LANDED" || f.writer != "TPX") then
        add "REC-08" n s!"{n} is missing"
  -- S3, the rules
  for r in rulesOf cv do
    if !condTrue r.cond record then continue
    let fl := r.fields
    if r.action == "REQUIRE" then
      for x in fl do
        if stage == "PUSH" && ((fieldNamed fields x).map (·.writer)) == some "TPX" then continue
        if !V.has record x then add "REC-20" x s!"{x} is required when {condText r.cond}"
    else if r.action == "FORBID" then
      for x in fl do
        if V.has record x then add "REC-21" x s!"{x} is not allowed when {condText r.cond}"
    else if r.action == "ALL OR NONE" then
      let pres := fl.filter (V.has record)
      if 0 < pres.length && pres.length < fl.length then
        let first := (fl.filter fun x => !V.has record x).headD ""
        add "REC-22" first s!"{andList fl} are given together or not at all"
    else if r.action == "AT LEAST ONE" then
      if !fl.any (V.has record) then add "REC-23" "-" s!"one of {orList fl} is required"
  -- the checks across fields
  let str (k : String) : String := (V.getStr? record k).getD ""
  if cv == "RESULT" && (← passed "REGIME") && (← passed "QUANTITY") && (← passed "ENTRIES") &&
      str "REGIME" == "M" then
    if !(V.members (V.get? record "ENTRIES")).contains (str "QUANTITY") then
      add "REC-27" "ENTRIES" s!"ENTRIES does not name QUANTITY {← lift (showSlot (str "QUANTITY"))}"
  if cv == "MASTER" then
    if (← passed "ID") && (← passed "PREFIX") && str "ID" != str "PREFIX" ++ "-1" then
      add "REC-28" "ID" s!"ID {← lift (showSlot (str "ID"))} is not {str "PREFIX"}-1"
    if (← passed "D_TFK") && (← passed "D_TPK") && (← passed "D_TRM") && (← passed "D_TMS") then
      -- the three passed as 64 lowercase hexadecimal characters, so the combination is taken
      match Digest.digestResearchAssembly (str "D_TPK") (str "D_TRM") (str "D_TMS") with
      | none => pure ()
      | some d =>
        if d != str "D_TFK" then
          add "REC-33" "D_TFK" s!"D_TFK {str "D_TFK"} is not the combination of D_TPK, D_TRM and D_TMS"
  if setting == .str "OFF" && (← passed "LITERATURE") then
    add "REC-30" "LITERATURE" "LITERATURE is not kept under BIBLIOGRAPHY SETTING OFF"
  if (setting == .str "ON" || setting == .str "CLOSED") && (← passed "SOURCE") &&
      cv == "VERIFICATION" && ((← passed "LITERATURE") || !V.has record "LITERATURE") then
    let s := str "SOURCE"
    if !(isBib s && (V.members (V.get? record "LITERATURE")).contains s) then
      add "REC-31" "SOURCE" s!"SOURCE {← lift (showSlot s)} is not a BIB ID in LITERATURE"
  if cv == "NAMED_GAP" && (← passed "SOURCE") then
    let src := str "SOURCE"
    if ← passed "AGAINST" then
      let ag := V.members (V.get? record "AGAINST")
      if src == "SR7_DOMAIN" then
        if ag != ["TFK DOMAIN"] then
          add "REC-19" "AGAINST" "AGAINST is not the one member TFK DOMAIN"
          unpass "AGAINST"
      else
        let (test, form) : (String → Bool) × String :=
          if src == "IC2" || src == "UNDER" then (Zone.isIdent, "IDENT") else (isRid, "RID")
        for x in ag do
          if !test x then
            add "REC-19" "AGAINST" s!"AGAINST member {← lift (showSlot x)} is not {formPhrase form}"
            unpass "AGAINST"
            break
    if (← passed "TRIGGER") && (src == "SR5_LOCUS" || src == "SR7_ASSUMPTIONS" || src == "SR7_DOMAIN") then
      if !isRid (str "TRIGGER") then
        add "REC-19" "TRIGGER" s!"TRIGGER {← lift (showSlot (str "TRIGGER"))} is not {formPhrase "RID"}"
  -- S4, T2
  if cv == "ASSUMPTION" && (← passed "PROPOSITION") then
    for fnd in StartingSet.Tests.t2Findings (str "PROPOSITION") do
      add "REC-24" "PROPOSITION" ("PROPOSITION " ++ fnd)
  -- S5, the Research Assembly
  if tfk != .null then
    assemblyChecks tfk record fields
    if cv == "NAMED_GAP" && (← passed "SOURCE") && (← passed "AGAINST") &&
        (str "SOURCE" == "IC2" || str "SOURCE" == "UNDER") then
      let dofs := (namedDims ((V.get? tfk "TPK").getD .null) "DOF").map Prod.fst
      for x in V.members (V.get? record "AGAINST") do
        if !dofs.contains x then
          add "REC-25" "AGAINST" s!"AGAINST member {← lift (showSlot x)} is not a DOF of the TPK"
          break
    if cv == "MASTER" then
      for (fld, zn) in [("D_TPK", "TPK"), ("D_TRM", "TrM"), ("D_TMS", "TMS")] do
        unless ← passed fld do continue
        match ← lift (zoneGood tfk zn) with
        | some true =>
          match zoneDigestOf tfk zn with
          | .ok d =>
            if d != str fld then add "REC-34" fld s!"{fld} {str fld} is not the TFK's D({zn})"
          -- v1's serializer raised here; the zone check has passed every zone that reaches it
          | .error _ => add "REC-39" "-" "the TFK is not readable"
        | some false => add "REC-39" "-" "the TFK is not readable"
        | none => lift (throw (.number s!"the zone check of the TFK's {zn} owes its verdict"))
  -- S6, the digest
  if stage == "LANDED" && (← passed "DIGEST") && (← get).problems.isEmpty then
    let pre ← lift (encodeRecord (V.erase record "DIGEST") rows)
    let d := Digest.digestFields (digestFields pre)
    if d != str "DIGEST" then
      add "REC-29" "DIGEST" s!"DIGEST {str "DIGEST"} is not the record's digest {d}"

/-! ## The PMA rows (`Principia.Record.PmaTable`) -/

/-- How a check reads the PMA rows: `v1` not at all (version 1's check); `read` each row
present checked, none required (the preimage's check); `land` as `read`, and each required
row of a record at LANDED required (`record_check`). -/
inductive RowMode where
  | v1
  | read
  | land
  deriving DecidableEq, Repr

/-- The PMA rows a record of class `cv` carries, each with its value. -/
def presentRows (cv : String) (record : Value) : List (FieldRow × Value) :=
  (pmaFieldsOf cv).filterMap fun f => (V.get? record f.name).map (f, ·)

/-- The record with its PMA rows taken out: what version 1's check reads. -/
def eraseRows (record : Value) (rows : List (FieldRow × Value)) : Value :=
  rows.foldl (fun r fv => V.erase r fv.1.name) record

/-- The problems of the PMA rows present: at the push each is written by Custos (REC-07, as
version 1's TPX fields); at landing a value outside the row's enumeration is REC-43. -/
def rowProblems (stage : String) (rows : List (FieldRow × Value)) : M (List Problem) :=
  rows.flatMapM fun (f, v) => do
    if stage == "PUSH" then return [("REC-07", f.name, s!"{f.name} is written by TPX")]
    if rowValueOk f v then return []
    let shown ← match v with
      | .str s => showSlot s
      | _ => showJson v
    return [("REC-43", f.name,
      s!"{f.name} {shown} is not one of {orList (pmaEnumValues f.name)}")]

/-- REC-43 for each required PMA row a record of class `cv` lacks at LANDED, under `land`. -/
def absentProblems (mode : RowMode) (stage cv : String) (record : Value) : List Problem :=
  if mode == .land && stage == "LANDED" then
    (pmaFieldsOf cv).filterMap fun f =>
      if f.req == "R" && !V.has record f.name then some ("REC-43", f.name, s!"{f.name} is missing")
      else none
  else []

/-- Whether a record's DERIVATION reads as a bare KERNEL `{PROOF}`. -/
def bareKernel (record : Value) : Bool :=
  match V.get? record "DERIVATION" with
  | some v =>
    match derivationOfValue v with
    | .ok (.kernelProof _) => true
    | _ => false
  | none => false

/-- REC-44, the problem of a bare KERNEL. -/
def kernelProblem : Problem :=
  ("REC-44", "DERIVATION",
    "DERIVATION is a bare KERNEL, which no check credits yet: push PROSE {STEPS, TEXT} " ++
      "with the PROOF as its ATTACHMENT")

/-- REC-44 for a RESULT of class `cv` whose DERIVATION is a bare KERNEL, at PUSH and at
LANDED, under `land`. -/
def kernelProblems (mode : RowMode) (stage cv : String) (record : Value) : List Problem :=
  if mode == .land && cv == "RESULT" && (stage == "PUSH" || stage == "LANDED") &&
      bareKernel record then [kernelProblem]
  else []

/-- The checks of `record_check` that answer one problem alone (stage, setting, Research
Assembly, the record's shape and class): the problem, or the class and the stage's text. -/
def headCheck (record tfk setting stage : Value) : M (Problem ⊕ (String × String)) := do
  unless stage == .str "PUSH" || stage == .str "LANDED" do
    return .inl ("REC-36", "-", s!"stage {← showJson stage} is not PUSH or LANDED")
  unless setting == .str "OFF" || setting == .str "ON" || setting == .str "CLOSED" ||
      setting == .null do
    return .inl ("REC-36", "-", s!"setting {← showJson setting} is not OFF, ON, CLOSED or null")
  unless assemblyOk tfk do return .inl ("REC-39", "-", "the TFK is not readable")
  unless V.isObj record do return .inl ("REC-01", "-", "the record is not an object")
  let some cvv := V.get? record "CLASS" | return .inl ("REC-02", "CLASS", "CLASS is missing")
  let .str cv := cvv | return .inl ("REC-09", "CLASS", "CLASS is not a string")
  unless classes.contains cv do
    return .inl ("REC-03", "CLASS", s!"CLASS {← showSlot cv} is not a record class")
  if formOf cv == "LIST" then
    return .inl ("REC-04", "CLASS", s!"CLASS {cv} is written by TPX in its own form")
  let stageText := match stage with | .str s => s | _ => ""
  if stageText == "PUSH" && writerOf cv == "TPX" then
    return .inl ("REC-05", "CLASS", s!"CLASS {cv} is written by TPX and never pushed")
  return .inr (cv, stageText)

/-- REC-43 for each required PMA row the record lacks at LANDED, then REC-44 for a bare
KERNEL at PUSH or LANDED, under `land`, its class and stage read from the record and the
stage. -/
def absentOf (mode : RowMode) (record stage : Value) : List Problem :=
  let st := match stage with | .str s => s | _ => ""
  let cv := (V.getStr? record "CLASS").getD ""
  absentProblems mode st cv record ++ kernelProblems mode st cv record

/-- S2 to S6 over a record of class `cv` that passed `headCheck`, the PMA rows read as `mode`
says. -/
def coreCheck (forms : Bool) (mode : RowMode) (record tfk setting stage : Value)
    (cv stageText : String) : M Checked := do
  let rows := if mode == .v1 then [] else presentRows cv record
  let init ← rowProblems stageText rows
  let ((), ctx) ← (checkRecordCore forms rows (eraseRows record rows) tfk setting stageText cv).run
    { cls := cv, problems := init }
  return { problems := ctx.problems ++ absentOf mode record stage, ran := true }

/-- v1's `record_check(record, tfk, setting, stage)`, schema 8; `forms` as
`checkRecordCore`'s; the PMA rows read as `mode` says, taken out of the record before version
1's checks read it, so a PMA row is never an unknown field (REC-06) of its class, and carried
into S6's preimage. -/
def recordCheckMCore (forms : Bool) (mode : RowMode) (record tfk setting stage : Value) :
    M Checked := do
  match ← headCheck record tfk setting stage with
  | .inl p => return { problems := [p] }
  | .inr (cv, stageText) => coreCheck forms mode record tfk setting stage cv stageText

/-- The record check: version 1's, the DERIVATION read by its shape when it is of
`formsShape`, the PMA rows read and required at landing. -/
def recordCheckM (record tfk setting stage : Value) : M Checked :=
  recordCheckMCore (derivationForms record) .land record tfk setting stage

/-- Version 1's record check with the DERIVATION read by its shape, no PMA row read: what
version 1's corpus is run against. -/
def recordCheckV1M (record tfk setting stage : Value) : M Checked :=
  recordCheckMCore (derivationForms record) .v1 record tfk setting stage

/-- What `record_check` adds to version 1's check on a record without the PMA rows: REC-43
for each required row, when the checks ran at LANDED, and REC-44 for a bare KERNEL. -/
def Checked.withAbsence (record stage : Value) (c : Checked) : Checked :=
  if c.ran then { c with problems := c.problems ++ absentOf .land record stage } else c

/-- The result list of a check. -/
def Checked.result (c : Checked) : Value := if c.problems.isEmpty then okV else refused c.problems

/-- v1's `record_check`, as the Calculator answers it: its digests SHA-256, owed only for a
number its exact values cannot settle (the Calculator's numbers are exact). -/
def recordCheck (record tfk setting stage : Value) : Answer :=
  Answer.ofM (Checked.result <$> recordCheckM record tfk setting stage)

/-- The Calculator answers a record check with the check's result, unless the check itself is
owed (a number): no digest is ever owed. -/
theorem recordCheck_eq (r t s st : Value) :
    recordCheck r t s st = match recordCheckM r t s st with
      | .ok c => .done c.result
      | .error w => .owed w := by
  unfold recordCheck Answer.ofM
  cases recordCheckM r t s st <;> rfl

/-- **Version 1's PROSE check is unchanged**: a record whose DERIVATION is absent, or has
no list `STEPS` and no `START`, `PROOF` or `ATTACHMENT`, is checked exactly as version 1's
check (`recordCheckMCore false`) checks it. -/
theorem recordCheck_prose_unchanged (r t s st : Value) (h : derivationForms r = false) :
    recordCheck r t s st = Answer.ofM (Checked.result <$> recordCheckMCore false .land r t s st) := by
  simp [recordCheck, recordCheckM, h]

/-- A record without DERIVATION_CLASS carries no PMA row. -/
theorem presentRows_nil (cv : String) (r : Value) (h : V.get? r "DERIVATION_CLASS" = none) :
    presentRows cv r = [] := by
  unfold presentRows
  rw [List.filterMap_eq_nil_iff]
  intro f hf
  simp [pmaFieldsOf_name cv f hf, h]

/-- **`record_check` is version 1's check on a record without the PMA rows, with REC-43 at
LANDED**: for a record without DERIVATION_CLASS, its answer is version 1's (the DERIVATION read by
its shape included), REC-43 added for each required row when the checks ran at LANDED
(`Checked.withAbsence`). -/
theorem recordCheckM_without_rows (r t s st : Value) (h : V.get? r "DERIVATION_CLASS" = none) :
    recordCheckM r t s st = Checked.withAbsence r st <$> recordCheckV1M r t s st := by
  simp only [recordCheckM, recordCheckV1M, recordCheckMCore]
  cases headCheck r t s st with
  | error e => rfl
  | ok x =>
    cases x with
    | inl p => rfl
    | inr cs =>
      obtain ⟨cv, stageText⟩ := cs
      have e1 : (RowMode.land == RowMode.v1) = false := by decide
      have e2 : absentOf RowMode.v1 r st = [] := by simp [absentOf, absentProblems, kernelProblems]
      have e3 : ∀ x, rowProblems x [] = pure [] := fun _ => rfl
      simp only [coreCheck, bind, Except.bind]
      simp only [e1, e2, presentRows_nil cv r h, Bool.false_eq_true, ite_false,
        beq_self_eq_true, ite_true, e3, List.append_nil, pure, Except.pure]
      cases StateT.run (checkRecordCore (derivationForms r) [] (eraseRows r []) t s stageText cv)
          { cls := cv, problems := [] } <;> rfl

/-- **A PROSE derivation is never REC-44**: a record whose DERIVATION reads as PROSE, an
attachment or none, takes no problem of the bare-KERNEL rule. -/
theorem kernelProblems_prose (m : RowMode) (st cv : String) (r v : Value) (n : Nat)
    (t : String) (a : Option Attachment) (hv : V.get? r "DERIVATION" = some v)
    (hd : derivationOfValue v = .ok (.prose n t a)) : kernelProblems m st cv r = [] := by
  simp [kernelProblems, bareKernel, hv, hd]

/-- A bare KERNEL RESULT at PUSH or LANDED takes REC-44 under `land`. -/
theorem kernelProblems_bare (st : String) (r v : Value) (p : String)
    (hs : st = "PUSH" ∨ st = "LANDED") (hv : V.get? r "DERIVATION" = some v)
    (hd : derivationOfValue v = .ok (.kernelProof p)) :
    kernelProblems .land st "RESULT" r = [kernelProblem] := by
  rcases hs with rfl | rfl <;> simp [kernelProblems, bareKernel, hv, hd]

/-- **A bare KERNEL is refused**: when `record_check`'s checks run on a RESULT at PUSH or at
LANDED whose DERIVATION reads as a bare KERNEL, its problems hold REC-44. -/
theorem recordCheckM_bare_kernel_refused (r t s : Value) (st : String) (v : Value) (p : String)
    (c : Checked) (hs : st = "PUSH" ∨ st = "LANDED") (hc : V.getStr? r "CLASS" = some "RESULT")
    (hv : V.get? r "DERIVATION" = some v) (hd : derivationOfValue v = .ok (.kernelProof p))
    (h : recordCheckM r t s (.str st) = .ok c) (hran : c.ran = true) :
    kernelProblem ∈ c.problems := by
  have hk : kernelProblem ∈ absentOf .land r (.str st) := by
    simp only [absentOf, hc, Option.getD_some, kernelProblems_bare st r v p hs hv hd]
    simp
  simp only [recordCheckM, recordCheckMCore] at h
  cases hh : headCheck r t s (.str st) with
  | error e => rw [hh] at h; cases h
  | ok x =>
    rw [hh] at h
    cases x with
    | inl q =>
      simp [bind, Except.bind, pure, Except.pure] at h
      subst h; simp at hran
    | inr cs =>
      obtain ⟨cv, stageText⟩ := cs
      simp only [bind, Except.bind] at h
      simp only [coreCheck, bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact List.mem_append_right _ hk

/-! ## record_preimage and record_digest (schema 9) -/

/-- v1's `record_preimage`: the record checked at LANDED without a Research Assembly, its
DIGEST removed first; then the `TPC-RECORD` form 1 field list. The check's outcome is
returned with it. The check reads the PMA rows present (`RowMode.read`) and requires none, so
a record without them has version 1's preimage; a row present is carried after version 1's
fields. -/
def recordPreimageM (record : Value) : M (Checked × Value) := do
  let r := if V.has record "DIGEST" then V.erase record "DIGEST" else record
  let c ← recordCheckMCore (derivationForms r) .read r .null .null (.str "LANDED")
  if !c.problems.isEmpty then return (c, c.result)
  let rows := presentRows ((V.getStr? r "CLASS").getD "") r
  return (c, okWith [.arr (← encodeRecord (eraseRows r rows) rows)])

/-- v1's `record_preimage`, as the Calculator answers it. -/
def recordPreimage (record : Value) : Answer := Answer.ofM ((·.2) <$> recordPreimageM record)

/-- v1's `record_digest`: SHA-256 of the preimage's fields, or the preimage's refusal. -/
def recordDigestM (record : Value) : M Value := do
  let (_, r) ← recordPreimageM record
  match r with
  | .arr [.str "OK", .arr fields] =>
    return okWith [.str (Digest.digestFields (digestFields fields))]
  | _ => return r

/-- v1's `record_digest`, as the Calculator answers it. -/
def recordDigest (record : Value) : Answer := Answer.ofM (recordDigestM record)

/-! ## record_view (schema 10) -/

/-- v1's `VIEWS`. -/
def views : List String := ["HOLD", "STRIKE", "SUITE", "PROBE_L", "PROBE_M", "PROBE_LOAD", "LITERATURE", "EOM"]

/-- v1's `record_view(record, view, grade)`: a view maps, it does not check (10.2); the
status word of 10.3. The view SUITE also shows the PMA row DERIVATION_CLASS, as
`derivation_class`, when the record carries it; a record without it is viewed as
version 1 viewed it. A STRUCTURED derivation's `steps`, in STRIKE and SUITE, is the count of
its steps, as version 1's `steps` is a count. -/
def recordViewM (r view grade : Value) : M Value := do
  unless V.isObj r do return one "REC-01" "-" "the record is not an object"
  unless (match view with | .str v => views.contains v | _ => false) do
    return one "REC-37" "-" s!"view {← showJson view} is not a view"
  unless grade == .null || (match grade with | .str g => gradeValues.contains g | _ => false) do
    return one "REC-38" "-" s!"grade {← showJson grade} is not a grade"
  let w : Option Value :=
    match V.get? r "STATUS" with
    | some (.str "HELD") => some (.str "HELD")
    | some (.str "REFUTED") => some (.str "REFUTED")
    | _ => if grade != .null then some grade else V.get? r "GRADE"
  let put (k src : String) : List (String × Value) :=
    match V.get? r src with
    | some x => [(k, x)]
    | none => []
  let steps : List (String × Value) :=
    match V.get? r "DERIVATION" with
    | some d@(.obj _) =>
      match V.get? d "STEPS" with
      | some (.arr xs) => [("steps", .int xs.length)]
      | some s => [("steps", s)]
      | none => []
    | _ => []
  let whenW (k : String) : List (String × Value) := (w.map fun x => [(k, x)]).getD []
  let tpxCorr := V.get? r "CLASS" == some (.str "CORROBORATION") && V.get? r "LANDED_BY" == some (.str "TPX")
  let v := match view with | .str v => v | _ => ""
  let o : List (String × Value) :=
    if v == "HOLD" then
      put "id" "ID" ++ put "block_id" "BLOCK" ++
      (if tpxCorr then [("author", .str "TPX")] else put "author" "AUTHOR") ++
      put "cites" "CITES" ++ put "assumptions" "ASSUMPTIONS" ++ put "kind" "CLASS" ++
      whenW "status" ++
      (if tpxCorr then put "supplied_by" "AUTHOR" else []) ++
      (match V.get? r "LANDED_BY" with
        | some lb =>
          if lb != .str "TPX" && (match V.get? r "AUTHOR" with | some a => lb != a | none => true)
          then [("vetted_by", lb)] else []
        | none => []) ++
      put "vetted_in" "VETTED_IN"
    else if v == "STRIKE" then put "assumptions" "ASSUMPTIONS" ++ put "cites" "CITES" ++ steps
    else if v == "SUITE" then
      put "regime" "REGIME" ++ put "assumptions" "ASSUMPTIONS" ++ put "cites" "CITES" ++ steps ++
        put "domain" "DOMAIN" ++ put "derivation_class" "DERIVATION_CLASS"
    else if v == "PROBE_L" then
      match V.get? r "EQUATION", V.get? r "VALUE", V.get? r "STATEMENT" with
      | some e, _, _ => [("finding", .obj [("type", .str "EQUATION"), ("value", e)])]
      | none, some x, _ => [("finding", .obj [("type", .str "DECIMAL"), ("value", x)])]
      | none, none, some s => [("finding", .obj [("type", .str "TEXT"), ("value", s)])]
      | none, none, none => []
    else if v == "PROBE_M" then put "x" "VALUE" ++ put "u" "U_C" ++ put "unit" "UNIT"
    else if v == "PROBE_LOAD" then
      put "cites" "CITES" ++ put "assumptions" "ASSUMPTIONS" ++
        (w.map fun x => [("standing", .bool (x == .str "PROVISIONAL" || x == .str "ESTABLISHED"))]).getD []
    else if v == "LITERATURE" then
      put "id" "ID" ++ whenW "status" ++ [("literature", (V.get? r "LITERATURE").getD (.arr []))]
    else
      put "ID" "ID" ++ whenW "STATUS" ++ put "ROLE" "ROLE" ++ put "EQUATION" "EQUATION"
  return okWith [.obj o]

/-- v1's `record_view`, as the Calculator answers it. -/
def recordView (r view grade : Value) : Answer := Answer.ofM (recordViewM r view grade)

/-! ## schema_json (schema 11; non-normative) -/

/-- v1's `SCHEMA_TEXT_VERSION`. -/
def schemaTextVersion : String := "0.4.0"

/-- v1's `_DESC`. -/
def schemaDescription : String :=
  "Generated by TPC tpc_record schema_json from tpm_record_schema " ++ schemaTextVersion ++
    ". Non-normative: the table governs and TPC record_check decides; a validator run on " ++
    "this document can pass a record TPX refuses."

/-- v1's `_QUIET`. -/
def quietCons : List String :=
  ["NOTBLANK", "KEY", "NONEMPTY", "SETTING", "TPKNAME", "TPKDOF", "TRMENTRY", "DTFK",
   "DIGEST", "T2", "GRADE", "STATUS"]

/-- v1's `_TYPE_FN`. -/
def typeChecker : String → Option String
  | "FORM" | "PREDICATE" => some "tpc_form parse_form"
  | "DECIMAL" => some "tpc_zone canon_decimal"
  | "UNIT" => some "tpc_units unit_parse"
  | "DIMENSION" => some "tpc_zone normalize_dimension"
  | _ => none

/-- v1's `_desc`. -/
def fieldDescription (f : FieldRow) : String :=
  let d := s!"{f.type} ({f.card}), written by {f.writer}"
  let fn := match typeChecker f.type with
    | some fn => some fn
    | none =>
      let other := f.cons.filter fun c => !quietCons.contains c && !c.startsWith "ENUM=" &&
        !c.startsWith "SUB=" && !c.startsWith "DIM=" && !c.startsWith "ZONE="
      if !other.isEmpty || f.type == "RID" || f.type == "IDSET" || f.cons.contains "ROLE" then
        some "tpc_record record_check" else none
  (match fn with | some fn => d ++ "; checked by TPC " ++ fn | none => d) ++ "."

/-- v1's `_fs`: one field's JSON Schema. -/
def fieldSchema (cls : Option String) (f : FieldRow) : Value :=
  let d : String × Value := ("description", .str (fieldDescription f))
  if f.card == "SET" then
    .obj [("type", .str "array"), ("items", .obj [("type", .str "string")]),
          ("uniqueItems", .bool true), d]
  else if f.type == "OBJECT" then
    let ref := .str ("#/$defs/" ++ (f.consValue "SUB=").getD "")
    if f.card == "ONE" then .obj [("$ref", ref), d]
    else .obj [("type", .str "array"), ("items", .obj [("$ref", ref)]), d]
  else if f.type == "ENUM" && !f.cons.contains "ROLE" then
    if f.cons.contains "GRADE" then .obj [("enum", V.strs [landgradeOf (cls.getD "")]), d]
    else if f.cons.contains "STATUS" then .obj [("enum", V.strs (statusesOf (cls.getD ""))), d]
    else .obj [("enum", V.strs (enumValues ((f.consValue "ENUM=").getD ""))), d]
  else if f.type == "INT" then
    .obj [("type", .str "integer"), ("minimum", .int 1), ("maximum", .int 1000000), d]
  else if f.type == "BOOL" then .obj [("type", .str "boolean"), d]
  else .obj [("type", .str "string"), d]

/-- v1's `schema_json()`: `["OK", text]`, the JSON Schema 2020-12 document generated from
the table, in canonical JSON. -/
def schemaJson : Value :=
  let branches := keyed.map fun c =>
    let fl := fieldsOf c
    .obj [("if", .obj [("properties", .obj [("CLASS", .obj [("const", .str c)])]),
                       ("required", V.strs ["CLASS"])]),
          ("then", .obj [("type", .str "object"),
                         ("properties", .obj (fl.map fun f => (f.name, fieldSchema (some c) f))),
                         ("required", V.strs ((fl.filter fun f => f.req == "R" &&
                            (f.writer == "AUTHOR" || f.writer == "LEAD")).map (·.name))),
                         ("additionalProperties", .bool false)])]
  let defs := table.subs.map fun s =>
    let fl := fieldsOf ("SUB:" ++ s)
    (s, Value.obj [("type", .str "object"),
                   ("properties", .obj (fl.map fun f => (f.name, fieldSchema none f))),
                   ("required", V.strs ((fl.filter (·.req == "R")).map (·.name))),
                   ("additionalProperties", .bool false)])
  let doc : Value := .obj [
    ("$schema", .str "https://json-schema.org/draft/2020-12/schema"),
    ("title", .str "TPM register record"), ("description", .str schemaDescription),
    ("type", .str "object"), ("required", V.strs ["CLASS"]),
    ("properties", .obj [("CLASS", .obj [("enum", V.strs keyed)])]),
    ("allOf", .arr branches), ("$defs", .obj defs)]
  okWith [.str (cj doc)]

end Principia.Record
