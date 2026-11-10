import Principia.Calculator.Interface
import Principia.Record.Classes
import Principia.Record.Derivation
import Principia.Record.Envelope
import Principia.Record.Measured
import Principia.Record.Reaudit

/-!
# Family `record`: the record table and the register functions

The record table, in the shapes of the record types' corpora:

* `class_row {"class": c}`: the class's layout, whether it is pushed, its landing grade,
  grades and statuses.
* `envelope {"class": c}`: the envelope fields the class carries, in order, each with
  its type, cardinality, whether it is required, its writer and its digest membership.
* `check_class {"form": f}`: the check class a derivation form earns when verified.
* `form_credit {"form": f, "verified": b}`: the form credited.

The register functions, version 1's `tpc_record` (`Principia.Record`), one function each
under version 1's name, its arguments named as version 1 named them. Version 1 read every
argument with `args.get`, so each may be absent, read as `null`; a member the function does
not read is refused. The answer is version 1's value, `["OK", ...]`, `["REFUSED",
problems]`, `["INSPECT", reason]`, `["CONVENTION", reason]`, `["NOT", reasons]` or
`["ELIGIBLE", ...]`, written as canonical JSON at exit code 0: a refusal version 1 wrote as
a value stays a value.

* the record: `record_check {"record", "tfk", "setting", "stage"}`, `record_preimage
  {"record"}`, `record_digest {"record"}`, `record_view {"record", "view", "grade"}`,
  `schema_json {}`;
* grade and status: `grade_values {"class"}`, `status_values {"class"}`, `grade_now
  {"register", "id"}`, `status_words {"register"}`, `is_standing {"word"}`, `status_word
  {"grade", "status"}`, `grade_next {"class", "grade", "event"}`, `status_next {"class",
  "status", "event"}`, `inherit_grade {"class", "grade"}`;
* citations and the withdrawal: `citation_check {"record", "register", "entries",
  "supersede_decided"}`, `withdrawal_scope {"register", "root", "still_stands"}`,
  `withdrawal_preimage {"act"}`, `withdrawal_record {"withdrawal_id", "act"}`;
* the measured fields and the declared form: `budget_check {"record"}`, `field_values
  {"record"}`, `prec_decimal {"s"}`, `l_finding_pair {"original", "reproduction"}`,
  `record_form_check {"record", "tfk"}`, `domain_check {"record", "tfk"}`;
* named gaps: `gap_records {"prefix", "ic2", "under", "trigger", "landed", "tps"}`,
  `gap_record {"id", "source", "against", "trigger", "landed", "tps"}`, `gap_view {"gap",
  "records", "tfk"}`, `gap_state {"state", "date", "what"}`, `eom0_open {"records"}`;
* verification: `verification_order {"target_push", "verification_push", "source_push"}`,
  `verification_difference {"target", "verification", "k"}`;
* promotion and successors: `promotion_eligible {"records", "words", "tfk", "open_audits",
  "id"}`, `promotion_pass {"records", "words", "tfk", "open_audits"}`, `promotion_record
  {"promotion_id", "landing_block", "promoted"}`, `entry_view {"records", "words", "tfk",
  "entry"}`, `reaudit_scope {"src", "dst"}`, `repromote_batch {"src_records", "src_words",
  "dst_records", "dst_words", "tfk", "open_audits"}`;
* the successor's re-audit in one call: `reaudit_batch {"src", "dst", "src_records",
  "src_words", "dst_records", "dst_words", "tfk", "setting", "promotion_id", "landing_block",
  "prefix", "ic2", "under", "trigger", "landed", "tps"}` (`Principia.Record.reauditBatch`):
  the scope, the re-check of the inherited records, `status_next` on `HOLD` for a record that
  fails it with the gap records `gap_records` opens, the re-promotion and its PROMOTION record;
  a successor above `maxRecords` is refused whole.

Every digest is SHA-256, as version 1's. Every number a function forms from its arguments,
a measurement normalized or a budget's sums, is formed within the bound on an exact value's
size and refused past it, "exact value too large" (`Principia.Record.Bounded`). The
verification's difference, its uncertainty and its zeta, which version 1 computed in
floating point with a square root, are computed exactly and written to twelve digits
(`Principia.Record.Verification`). An answer the Calculator does not compute is refused
`OWED`, its detail saying what it waits on: a value in a unit that carries π whose twelve
digits the Calculator's bounds on π do not settle.

Bounds, measured on the Calculator's command line (CPU time, on a machine shared with
other work): a register function's request holds at most `maxEntries` entries in any list
or object, strings of at most `maxText` code points each and `maxTextTotal` in all; a
register at most `maxRecords` records, whose CITES, ASSUMPTIONS and ENTRIES number at most
`maxListed` in all; a promotion at most `maxAudits` open audits. Membership is tested
along lists, so a check's work grows with the square of a list's length: a set of 64,000
members took 27 s, one of 1024 a few milliseconds. The promotion's fixed point tests every
candidate over its closure in every round, as version 1's does: 256 records in a chain took
9.2 s (version 1 itself 4.0 s), 64 records with 1024 assumptions 1.5 s, and with 250
entries each 3.0 s. The slowest requests found at the bounds: a promotion over 64 records
in a chain, one holding 385 assumptions, with 64 open audits, 0.70 s; the digest of a
result whose 1024 budget components hold 130,000 code points of combining marks to
reorder, 0.49 s; a MASTER checked against a Starting Set of 28 laws of 4,000 code points,
0.44 s; a citation check over 63 withdrawals naming 6,300 records, 0.29 s; 2,048 named
gaps written, 0.27 s. A request of a mebibyte past the bounds is refused in at most 0.43 s.
-/

namespace Principia.Calculator.Record

open Principia.Canonical Principia.Record

/-- A wire word as a JSON string. -/
def word {α : Type} [WireWord α] (a : α) : Value := .str (WireWord.toWire a)

/-! ## The family's bounds, measured -/

/-- The most entries a list or an object of a register function's request holds, at any
depth. -/
def maxEntries : Nat := 1024

/-- The most code points a string of a request holds, a member's name included. -/
def maxText : Nat := 16384

/-- The most code points the strings of a request hold in all, members' names included:
each text is read in NFC, whose cost grows with its length. -/
def maxTextTotal : Nat := 131072

/-- The most records a register holds (`register`, `records`, `src_records`,
`dst_records`), keyed and positional: the promotion's rounds each test every candidate
over its closure. -/
def maxRecords : Nat := 64

/-- The most CITES, ASSUMPTIONS and ENTRIES a register's records hold in all: the closures
walk the first two, and the promotion looks each of the third up in the Correspondence
Table, in every round. -/
def maxListed : Nat := 512

/-- The most open audits a promotion is given: each is looked for in every candidate's
closure. -/
def maxAudits : Nat := 64

/-- The size of a request: the most entries of one list or object, the most code points of
one string, and the code points of all its strings. -/
structure Size where
  entries : Nat := 0
  longest : Nat := 0
  text : Nat := 0

/-- Two sizes together. -/
def Size.join (a b : Size) : Size :=
  ⟨max a.entries b.entries, max a.longest b.longest, a.text + b.text⟩

/-- The size of a string. -/
def Size.ofText (s : String) : Size := ⟨0, s.length, s.length⟩

mutual
/-- The size of a value. -/
def valueSize : Value → Size
  | .str s => Size.ofText s
  | .arr xs => (listSize xs).join ⟨xs.length, 0, 0⟩
  | .obj ms => (membersSize ms).join ⟨ms.length, 0, 0⟩
  | _ => {}

/-- The size of a list's values. -/
def listSize : List Value → Size
  | [] => {}
  | x :: xs => (valueSize x).join (listSize xs)

/-- The size of an object's members, their names included. -/
def membersSize : List (String × Value) → Size
  | [] => {}
  | (k, v) :: ms => ((Size.ofText k).join (valueSize v)).join (membersSize ms)
end

/-- A request within `maxEntries`, `maxText` and `maxTextTotal`. -/
def sizeWithin (v : Value) : Except Refusal Unit := do
  let s := valueSize v
  if maxEntries < s.entries then
    badArgument s!"a list or an object of the request holds more than {maxEntries} entries (the Calculator's bound)"
  if maxText < s.longest then
    badArgument s!"a string of the request holds more than {maxText} code points (the Calculator's bound)"
  if maxTextTotal < s.text then
    badArgument s!"the strings of the request hold more than {maxTextTotal} code points in all (the Calculator's bound)"

/-- The entries of a list member `k` of an object, `0` when it is not a list. -/
def listLength (r : Value) (k : String) : Nat :=
  match V.get? r k with
  | some (.arr xs) => xs.length
  | _ => 0

/-- A register within `maxRecords`, its CITES, ASSUMPTIONS and ENTRIES within `maxListed`. -/
def registerWithin (what : String) : Value → Except Refusal Unit
  | .arr rs => do
    atMost what maxRecords rs
    let n := (rs.map fun r =>
      listLength r "CITES" + listLength r "ASSUMPTIONS" + listLength r "ENTRIES").sum
    if maxListed < n then
      badArgument s!"the records of {what} hold more than {maxListed} CITES, ASSUMPTIONS and ENTRIES in all (the Calculator's bound)"
  | _ => pure ()

/-- A request's registers and open audits within their bounds. -/
def registersWithin (a : String → Value) : Except Refusal Unit := do
  for k in ["register", "records", "src_records", "dst_records"] do
    registerWithin k (a k)
  match a "open_audits" with
  | .arr xs => atMost "open_audits" maxAudits xs
  | _ => pure ()

/-! ## The register functions -/

/-- A request's arguments as version 1 read them: each of `names`, `null` when absent; a
member not among them is refused. -/
def readArgs (names : List String) (v : Value) : Except Refusal (String → Value) := do
  let ms ← membersOf names v
  pure fun k => (ms.lookup k).getD .null

/-- An owed answer's detail, in plain words: what it waits on. -/
def owedDetail : Owed → String
  | .number what =>
    if what == "twelve digits" then
      "a value's twelve digits wait on the numeric meaning's application to a unit that " ++
        "carries pi: the Calculator's bounds on pi do not settle them"
    else "a number waits on the numeric meaning's application to the record functions: " ++ what
  | .tooLarge => Principia.ValueBound.tooLarge

/-- An answer as `pcalc` gives it: version 1's value; a value past the bound on an exact
value's size refused, "exact value too large"; or the refusal `OWED`. -/
def answer : Principia.Record.Answer → Except Refusal Value
  | .done v => .ok v
  | .owed .tooLarge => badArgument Principia.ValueBound.tooLarge
  | .owed why => .error ⟨.owed, owedDetail why⟩

/-- The register functions: version 1's name, its arguments, and the function. -/
def registerFunctions : List (String × List String × ((String → Value) → Principia.Record.Answer)) := [
  ("budget_check", ["record"], fun a => .ofM (budgetCheck (a "record"))),
  ("citation_check", ["record", "register", "entries", "supersede_decided"], fun a =>
    .ofM (citationCheck (a "record") (a "register") (a "entries") (a "supersede_decided"))),
  ("domain_check", ["record", "tfk"], fun a => .ofM (domainCheck (a "record") (a "tfk"))),
  ("entry_view", ["records", "words", "tfk", "entry"], fun a =>
    .ofM (entryView (a "records") (a "words") (a "tfk") (a "entry"))),
  ("eom0_open", ["records"], fun a => .ofM (eom0Open (a "records"))),
  ("field_values", ["record"], fun a => .ofM (fieldValues (a "record"))),
  ("gap_record", ["id", "source", "against", "trigger", "landed", "tps"], fun a =>
    .ofM (gapRecord (a "id") (a "source") (a "against") (a "trigger") (a "landed") (a "tps"))),
  ("gap_records", ["prefix", "ic2", "under", "trigger", "landed", "tps"], fun a =>
    .ofM (gapRecords (a "prefix") (a "ic2") (a "under") (a "trigger") (a "landed") (a "tps"))),
  ("gap_state", ["state", "date", "what"], fun a =>
    .ofM (gapState (a "state") (a "date") (a "what"))),
  ("gap_view", ["gap", "records", "tfk"], fun a =>
    .ofM (gapView (a "gap") (a "records") (a "tfk"))),
  ("grade_next", ["class", "grade", "event"], fun a =>
    .ofM (gradeNext (a "class") (a "grade") (a "event"))),
  ("grade_now", ["register", "id"], fun a => .ofM (gradeNow (a "register") (a "id"))),
  ("grade_values", ["class"], fun a => .ofM (gradeValuesOf (a "class"))),
  ("inherit_grade", ["class", "grade"], fun a => .ofM (inheritGrade (a "class") (a "grade"))),
  ("is_standing", ["word"], fun a => .ofM (isStanding (a "word"))),
  ("l_finding_pair", ["original", "reproduction"], fun a =>
    .ofM (lFindingPair (a "original") (a "reproduction"))),
  ("prec_decimal", ["s"], fun a => .ofM (precDecimal (a "s"))),
  ("promotion_eligible", ["records", "words", "tfk", "open_audits", "id"], fun a =>
    .ofM (promotionEligible (a "records") (a "words") (a "tfk") (a "open_audits") (a "id"))),
  ("promotion_pass", ["records", "words", "tfk", "open_audits"], fun a =>
    .ofM (promotionPass (a "records") (a "words") (a "tfk") (a "open_audits"))),
  ("promotion_record", ["promotion_id", "landing_block", "promoted"], fun a =>
    .ofM (promotionRecord (a "promotion_id") (a "landing_block") (a "promoted"))),
  ("reaudit_scope", ["src", "dst"], fun a => .ofM (reauditScope (a "src") (a "dst"))),
  ("reaudit_batch", ["src", "dst", "src_records", "src_words", "dst_records", "dst_words",
      "tfk", "setting", "promotion_id", "landing_block", "prefix", "ic2", "under", "trigger",
      "landed", "tps"], fun a =>
    .ofM (reauditBatch (a "src") (a "dst") (a "src_records") (a "src_words") (a "dst_records")
      (a "dst_words") (a "tfk") (a "setting") (a "promotion_id") (a "landing_block") (a "prefix")
      (a "ic2") (a "under") (a "trigger") (a "landed") (a "tps"))),
  ("record_check", ["record", "tfk", "setting", "stage"], fun a =>
    recordCheck (a "record") (a "tfk") (a "setting") (a "stage")),
  ("record_digest", ["record"], fun a => recordDigest (a "record")),
  ("record_form_check", ["record", "tfk"], fun a => .ofM (recordFormCheck (a "record") (a "tfk"))),
  ("record_preimage", ["record"], fun a => recordPreimage (a "record")),
  ("record_view", ["record", "view", "grade"], fun a =>
    recordView (a "record") (a "view") (a "grade")),
  ("repromote_batch", ["src_records", "src_words", "dst_records", "dst_words", "tfk",
      "open_audits"], fun a =>
    .ofM (repromoteBatch (a "src_records") (a "src_words") (a "dst_records") (a "dst_words")
      (a "tfk") (a "open_audits"))),
  ("schema_json", [], fun _ => .done schemaJson),
  ("status_next", ["class", "status", "event"], fun a =>
    .ofM (statusNext (a "class") (a "status") (a "event"))),
  ("status_values", ["class"], fun a => .ofM (statusValuesOf (a "class"))),
  ("status_word", ["grade", "status"], fun a => .ofM (statusWord (a "grade") (a "status"))),
  ("status_words", ["register"], fun a => .ofM (statusWords (a "register"))),
  ("verification_difference", ["target", "verification", "k"], fun a =>
    .ofM (verificationDifference (a "target") (a "verification") (a "k"))),
  ("verification_order", ["target_push", "verification_push", "source_push"], fun a =>
    .ofM (verificationOrder (a "target_push") (a "verification_push") (a "source_push"))),
  ("withdrawal_preimage", ["act"], fun a => .ofM (withdrawalPreimage (a "act"))),
  ("withdrawal_record", ["withdrawal_id", "act"], fun a =>
    .ofM (withdrawalRecord (a "withdrawal_id") (a "act"))),
  ("withdrawal_scope", ["register", "root", "still_stands"], fun a =>
    .ofM (withdrawalScope (a "register") (a "root") (a "still_stands"))),
]

/-- A register function as a call: its arguments read, then version 1's answer. -/
def registerCall (names : List String) (f : (String → Value) → Principia.Record.Answer) : Call :=
  fun v => do
    let a ← readArgs names v
    sizeWithin v
    registersWithin a
    answer (f a)

/-- The family's functions. -/
def calls : Family := [
  ("class_row", fun v => do
    let c ← asWord RecordClass "a record class" (← argument1 "class" v)
    pure (.obj [("layout", word c.layout), ("pushed", .bool c.pushed),
      ("landing_grade", word c.landingGrade), ("grades", .arr (c.grades.map word)),
      ("statuses", .arr (c.statuses.map word))])),
  ("envelope", fun v => do
    let c ← asWord RecordClass "a record class" (← argument1 "class" v)
    pure (.arr (c.envelopeFields.map fun f =>
      .obj [("field", word f), ("type", word f.valueType), ("card", word f.cardinality),
        ("required", .bool f.required), ("writer", word (c.writer f)),
        ("digest", .bool f.inDigest)]))),
  ("check_class", fun v => do
    let f ← asWord DerivationForm "a derivation form" (← argument1 "form" v)
    pure (word f.checkClass)),
  ("form_credit", fun v => do
    let (f, b) ← argument2 "form" "verified" v
    let f ← asWord DerivationForm "a derivation form" f
    pure (word (f.credit (← asBool "verified" b))))] ++
  registerFunctions.map fun (n, names, f) => (n, registerCall names f)

end Principia.Calculator.Record
