import Principia
import Lean.Data.Json

/-!
The runner of v1's `vectors/record_corpus.json` (932 cases, 37 functions) and
`vectors/record_view_corpus.json` (213 cases of `record_view`) against the register
functions (`Principia.Record`), and the check of the record table v1 carried as text.

A case is `{"name", "fn", "args", "expected"}`. Its arguments are read into
`Principia.Canonical.Value` (`Lean.Json` reads inputs only: an integer stays an integer, a
number with a fraction keeps its exact decimal value); `expected` is v1's result in TPM's
canonical JSON. An answer passes when its canonical JSON is `expected`, byte for byte.

Every digest is SHA-256 (`Principia.Sha256`; decision D2, option 1): the digests a function
writes and those a check compares (REC-29, REC-33, REC-34) are computed, and their answers
compared with v1's byte for byte as every other answer is. Owed, each listed with its reason
in `vectors/record_corpus.owed.json` (the list must be exactly the owed cases, each for its
reason): `number`, v1's floating-point arithmetic, with no exact counterpart yet (decision
D6).

The table check: `Principia.Record.Table.tableText` is v1's `TABLE_TEXT` in
`docs/v1/tpc_py/tpc_record.py`, byte for byte; it reads; its class part agrees with
Phase 1's typed table (`RecordClass`: form, writer, landing grade, grades, statuses) and its
envelope fields with `EnvelopeField` (type, cardinality, requirement, writer, digest), v1's
words read as PMA's (LEAD the Holder, TPX Custos, TPS the PFS); and no sub-object field is an
object, the nesting `Principia.Record.checkValue` reads.
-/

namespace Tests.Record

open Lean
open Principia
open Principia.Record
open Principia.Canonical (Value)

/-- A JSON value as v1's reader gives it, exactly. -/
partial def toValue : Json → Value
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent == 0 then .int n.mantissa else .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr a => .arr (a.toList.map toValue)
  | .obj kvs => .obj (kvs.foldl (fun acc k v => acc ++ [(k, toValue v)]) [])

/-- An argument (v1's `_a`: absent is null). -/
def arg (a : Value) (k : String) : Value := (V.get? a k).getD .null

/-- One case's answer, or `none` for a function the runner does not know. -/
def answerOf (fn : String) (a : Value) : Option Answer :=
  let x := arg a
  match fn with
  | "record_check" => some (recordCheck (x "record") (x "tfk") (x "setting") (x "stage"))
  | "record_preimage" => some (recordPreimage (x "record"))
  | "record_digest" => some (recordDigest (x "record"))
  | "record_view" => some (recordView (x "record") (x "view") (x "grade"))
  | "schema_json" => some (.done schemaJson)
  | "grade_values" => some (.ofM (gradeValuesOf (x "class")))
  | "status_values" => some (.ofM (statusValuesOf (x "class")))
  | "grade_now" => some (.ofM (gradeNow (x "register") (x "id")))
  | "status_words" => some (.ofM (statusWords (x "register")))
  | "is_standing" => some (.ofM (isStanding (x "word")))
  | "status_word" => some (.ofM (statusWord (x "grade") (x "status")))
  | "grade_next" => some (.ofM (gradeNext (x "class") (x "grade") (x "event")))
  | "status_next" => some (.ofM (statusNext (x "class") (x "status") (x "event")))
  | "inherit_grade" => some (.ofM (inheritGrade (x "class") (x "grade")))
  | "citation_check" =>
    some (.ofM (citationCheck (x "record") (x "register") (x "entries") (x "supersede_decided")))
  | "withdrawal_scope" => some (.ofM (withdrawalScope (x "register") (x "root") (x "still_stands")))
  | "withdrawal_preimage" => some (.ofM (withdrawalPreimage (x "act")))
  | "withdrawal_record" => some (.ofM (withdrawalRecord (x "withdrawal_id") (x "act")))
  | "budget_check" => some (.ofM (budgetCheck (x "record")))
  | "field_values" => some (.ofM (fieldValues (x "record")))
  | "prec_decimal" => some (.ofM (precDecimal (x "s")))
  | "l_finding_pair" => some (.ofM (lFindingPair (x "original") (x "reproduction")))
  | "record_form_check" => some (.ofM (recordFormCheck (x "record") (x "tfk")))
  | "domain_check" => some (.ofM (domainCheck (x "record") (x "tfk")))
  | "gap_records" => some (.ofM
      (gapRecords (x "prefix") (x "ic2") (x "under") (x "trigger") (x "landed") (x "tps")))
  | "gap_record" => some (.ofM
      (gapRecord (x "id") (x "source") (x "against") (x "trigger") (x "landed") (x "tps")))
  | "gap_view" => some (.ofM (gapView (x "gap") (x "records") (x "tfk")))
  | "gap_state" => some (.ofM (gapState (x "state") (x "date") (x "what")))
  | "eom0_open" => some (.ofM (eom0Open (x "records")))
  | "verification_order" =>
    some (.ofM (verificationOrder (x "target_push") (x "verification_push") (x "source_push")))
  | "verification_difference" =>
    some (.ofM (verificationDifference (x "target") (x "verification") (x "k")))
  | "promotion_eligible" =>
    some (.ofM (promotionEligible (x "records") (x "words") (x "tfk") (x "open_audits") (x "id")))
  | "promotion_pass" => some (.ofM (promotionPass (x "records") (x "words") (x "tfk") (x "open_audits")))
  | "promotion_record" => some (.ofM
      (promotionRecord (x "promotion_id") (x "landing_block") (x "promoted")))
  | "entry_view" => some (.ofM (entryView (x "records") (x "words") (x "tfk") (x "entry")))
  | "reaudit_scope" => some (.ofM (reauditScope (x "src") (x "dst")))
  | "repromote_batch" => some (.ofM (repromoteBatch (x "src_records") (x "src_words")
      (x "dst_records") (x "dst_words") (x "tfk") (x "open_audits")))
  | "reaudit_batch" => some (.ofM (reauditBatch (x "src") (x "dst") (x "src_records")
      (x "src_words") (x "dst_records") (x "dst_words") (x "tfk") (x "setting")
      (x "promotion_id") (x "landing_block") (x "prefix") (x "ic2") (x "under") (x "trigger")
      (x "landed") (x "tps")))
  | _ => none

/-! ## Running a corpus -/

/-- One case's verdict. -/
inductive Verdict where
  | pass
  | fail (why : String)
  | owed (reason : String)

/-- An answer's canonical JSON, or its owed word. -/
def answerText : Answer → String
  | .done v => cj v
  | .owed why => "owed " ++ why.word

/-- Judge one case. In version 1's corpus (`v1`), a `record_check` case is judged against
version 1's check (`recordCheckV1M`), and `record_check`'s own answer must be that check's
with the PMA row's REC-43 added (`Checked.withAbsence`; theorem `recordCheckM_without_rows`). -/
def judge (v1 : Bool) (fn : String) (args : Value) (expected : String) : IO Verdict := do
  let some a := answerOf fn args | throw (IO.userError s!"unknown function {fn}")
  let a ← if v1 && fn == "record_check" then do
      let x := arg args
      let base := recordCheckV1M (x "record") (x "tfk") (x "setting") (x "stage")
      let adjusted : Answer := .ofM ((·.result) <$> (Checked.withAbsence (x "record") (x "stage") <$> base))
      if answerText a != answerText adjusted then
        return .fail s!"record_check {answerText a} is not version 1's with REC-43 {answerText adjusted}"
      pure (Answer.ofM (Checked.result <$> base))
    else pure a
  match a with
  | .done v =>
    let got := cj v
    return if got == expected then .pass else .fail s!"got {got}"
  | .owed why => return .owed why.word

/-- The cases of a corpus file. -/
def casesOf (path : System.FilePath) : IO (Array Json) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)

/-- Run a corpus: passes and failures; owed cases are counted, printed, and checked against
the owed list. -/
def runCorpus (label : String) (path owedPath : System.FilePath) (v1 : Bool := false) :
    IO (Nat × Nat) := do
  let cases ← casesOf path
  let listed ← if ← owedPath.pathExists then do
      let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile owedPath))
      let owedList ← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)
      owedList.toList.mapM fun o => do
        pure ((← IO.ofExcept (o.getObjValAs? String "name")),
              (← IO.ofExcept (o.getObjValAs? String "reason")))
    else pure []
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String × String) := []
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let e ← IO.ofExcept (c.getObjValAs? String "expected")
    let args := toValue (← IO.ofExcept (c.getObjVal? "args"))
    match ← judge v1 fn args e with
    | .pass => pass := pass + 1
    | .fail why =>
      IO.eprintln s!"FAIL {label} {name} ({fn}):\n  expected {e}\n  {why}"
      fail := fail + 1
    | .owed reason => owed := owed ++ [(name, fn, reason)]
  for (name, _, why) in owed do
    unless listed.contains (name, why) do
      IO.eprintln s!"FAIL {label} {name}: owed ({why}) but not listed so in {owedPath}"
      fail := fail + 1
  for (name, why) in listed do
    unless owed.any (fun (n, _, w) => n == name && w == why) do
      IO.eprintln s!"FAIL {label} {name}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  let per (r : String) := (owed.filter fun o => o.2.2 == r).length
  IO.println s!"{label}: {owed.length} owed (number {per "number"}); every digest SHA-256, as v1's"
  return (pass, fail)

/-- `vectors/record_corpus.json`. -/
def runRecord : IO (Nat × Nat) :=
  runCorpus "record" "vectors/record_corpus.json" "vectors/record_corpus.owed.json" (v1 := true)

/-- `vectors/record_view_corpus.json`. -/
def runRecordView : IO (Nat × Nat) :=
  runCorpus "record_view" "vectors/record_view_corpus.json" "vectors/record_view_corpus.owed.json"

/-- `vectors/record_forms.json`: the record check's reading of a DERIVATION by its shape,
hand-written; no case is owed. -/
def runRecordForms : IO (Nat × Nat) :=
  runCorpus "record_forms" "vectors/record_forms.json" "vectors/record_forms.owed.json"

/-- `vectors/reaudit_corpus.json`: `reaudit_batch`, hand-written; no case is owed. -/
def runReaudit : IO (Nat × Nat) :=
  runCorpus "reaudit" "vectors/reaudit_corpus.json" "vectors/reaudit_corpus.owed.json"

/-! ## The table -/

/-- v1's `TABLE_TEXT` literal in `tpc_record.py`. -/
def v1TableText (src : String) : Option String :=
  match (Table.split src "TABLE_TEXT = \"\"\"") with
  | [_, rest] => (Table.split rest "\"\"\"").head?
  | _ => none

/-- PMA's wire word for v1's word in the table's WRITER column. -/
def writerWord : String → String
  | "LEAD" => "HOLDER"
  | "TPX" => "CUSTOS"
  | w => w

/-- PMA's wire word for v1's field name. -/
def fieldWord : String → String
  | "TPS" => "PFS"
  | n => n

/-- The table's checks. -/
def runRecordTable : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let check (ok : Bool) (what : String) (p f : Nat) : IO (Nat × Nat) := do
    if ok then return (p + 1, f)
    IO.eprintln s!"FAIL record_table {what}"
    return (p, f + 1)
  let src ← IO.FS.readFile "docs/v1/tpc_py/tpc_record.py"
  (pass, fail) ← check (v1TableText src == some Table.tableText)
    "tableText is not v1's TABLE_TEXT byte for byte" pass fail
  (pass, fail) ← check (Table.parseTable Table.tableText).isSome "the table does not read" pass fail
  let w {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a
  let cs : List RecordClass := WireWord.members
  (pass, fail) ← check (Table.classes == cs.map w) "the classes are not RecordClass's" pass fail
  for c in cs do
    let n := w c
    (pass, fail) ← check (Table.formOf n == w c.layout) s!"{n}: form" pass fail
    (pass, fail) ← check ((Table.writerOf n == "PUSH") == c.pushed) s!"{n}: writer" pass fail
    (pass, fail) ← check (Table.landgradeOf n == w c.landingGrade) s!"{n}: landing grade" pass fail
    (pass, fail) ← check (Table.gradesOf n == c.grades.map w) s!"{n}: grades" pass fail
    (pass, fail) ← check (Table.statusesOf n == c.statuses.map w) s!"{n}: statuses" pass fail
    let envelope := c.envelopeFields.map w
    let rows := (Table.fieldsOf n).filter fun r => envelope.contains (fieldWord r.name)
    (pass, fail) ← check (rows.map (fieldWord ·.name) == envelope) s!"{n}: envelope fields" pass fail
    for f in c.envelopeFields do
      match rows.find? (fieldWord ·.name == w f) with
      | none => pure ()
      | some r =>
        let at_ := s!"{n}.{w f}"
        (pass, fail) ← check (r.type == w f.valueType) s!"{at_}: type" pass fail
        (pass, fail) ← check (r.card == w f.cardinality) s!"{at_}: cardinality" pass fail
        (pass, fail) ← check ((r.req == "R") == f.required) s!"{at_}: requirement" pass fail
        (pass, fail) ← check (writerWord r.writer == w (c.writer f)) s!"{at_}: writer" pass fail
        (pass, fail) ← check ((r.dig == "D") == f.inDigest) s!"{at_}: digest" pass fail
  for s in Table.table.subs do
    (pass, fail) ← check ((Table.fieldsOf ("SUB:" ++ s)).all (·.type != "OBJECT"))
      s!"SUB {s}: a field is an object" pass fail
  return (pass, fail)

end Tests.Record
