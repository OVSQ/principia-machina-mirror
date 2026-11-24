import Tests.Calculator.Common

/-!
The Calculator's runners of the family `record`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The record family

v1's record corpora through `pcalc record`, and the family's bounds. -/

/-- A record corpus's owed list: `(name, reason)` for each case the Calculator does not
answer yet; empty when the corpus has none. -/
def recordOwed (path : System.FilePath) : IO (List (String × String)) := do
  unless ← path.pathExists do return []
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => do pure (← memberStr o "name", ← memberStr o "reason")
    | _ => throw (IO.userError s!"{path}: no owed list")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- `record_corpus.json`, `record_view_corpus.json` and `record_forms.json`: every case's `args` through
`record <fn>`, its answer's canonical JSON v1's `expected`. A case the corpus's owed list
names must be refused `OWED` for a number, and no other case may be; both lists are empty
since the verification's difference is computed exactly. -/
def runRecordCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for corpus in ["record_corpus", "record_view_corpus", "record_forms"] do
    let owed ← recordOwed s!"vectors/{corpus}.owed.json"
    for c in ← v1Cases s!"vectors/{corpus}.json" do
      let name ← memberStr c "name"
      let fn ← memberStr c "fn"
      let expected ← memberStr c "expected"
      let some args := member c "args" | throw (IO.userError s!"{name}: no args")
      let got := respondTo "record" fn args
      -- version 1's corpus: `record_check` answers version 1's check with the PMA row's REC-43
      -- (`Checked.withAbsence`), version 1's own answer being `expected` (Tests.Record)
      let expected := if corpus == "record_corpus" && fn == "record_check" then
          let x (k : String) : Value := (Principia.Record.V.get? args k).getD .null
          match Principia.Record.recordCheckV1M (x "record") (x "tfk") (x "setting") (x "stage") with
          | .ok c =>
            if Principia.Record.cj c.result == expected then
              Principia.Record.cj (Principia.Record.Checked.withAbsence (x "record") (x "stage") c).result
            else expected
          | .error _ => expected
        else expected
      match owed.lookup name with
      | some why =>
        let ok := match got with
          | .error r => r.code == .owed && why == "number"
          | .ok _ => false
        t ← t.check ok s!"record {fn} {name}: listed as owed ({why}), got {repr (got.toOption.map (·.canonicalJson))}"
      | none =>
        let ok := match got with
          | .ok v => v.canonicalJson == some expected
          | .error _ => false
        t ← t.check ok
          s!"record {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- How a request at or past a bound must come out. -/
inductive BoundOutcome where
  /-- Answered, not refused by a bound. -/
  | answered
  /-- Refused by one of the family's bounds. -/
  | bound
  /-- Refused by the bound on an exact value's size. -/
  | tooLarge
  /-- Answered, with exactly this canonical JSON. -/
  | exactly (json : String)

/-- Whether an answer came out so. -/
def BoundOutcome.holds : BoundOutcome → Except Refusal Value → Bool
  | .answered, got => !boundRefusal got && match got with
    | .error r => r.detail != Principia.ValueBound.tooLarge
    | .ok _ => true
  | .bound, got => boundRefusal got
  | .tooLarge, got => match got with
    | .error r => r.code == .badArgument && r.detail == Principia.ValueBound.tooLarge
    | .ok _ => false
  | .exactly j, got => match got with
    | .ok v => v.canonicalJson == some j
    | .error _ => false

/-- A RESULT of the record corpora's own form, its members `extra` added or replaced. -/
def recordResult (id : String) (extra : List (String × Value)) : Value :=
  let base : List (String × Value) := [("ASSUMPTIONS", strs []), ("AUTHOR", .str "agent-a"),
    ("BLOCK", .str "B-1"), ("CITES", strs []), ("CLASS", .str "RESULT"),
    ("DERIVATION", .obj [("STEPS", .int 2), ("TEXT", .str "t")]), ("D_IS", .str hex64a),
    ("FALSIFIER", .str "f"), ("FALSIFIER_CLASS", .str "F3"), ("GRADE", .str "PROVISIONAL"),
    ("ID", .str id), ("LANDED", .str "2026-09-28T12:00:00Z"), ("LANDED_BY", .str "agent-a"),
    ("REGIME", .str "L"), ("STATEMENT", .str "n"), ("STATUS", .str "UNMARKED"),
    ("TPS", .str "0.4.0")]
  .obj ((base.filter fun m => !(extra.any (·.1 == m.1))) ++ extra)

/-- An M RESULT of uncertainty `uc` in seconds, with one BUDGET component of `u`. -/
def mResult (uc u : String) : Value :=
  recordResult "RR-10" [("REGIME", .str "M"), ("QUANTITY", .str "period"),
    ("ENTRIES", strs ["period"]), ("VALUE", .str "2"), ("U_C", .str uc), ("UNIT", .str "s"),
    ("BUDGET", .arr [.obj [("BASIS", .str "b"), ("EVALUATION", .str "A"), ("NAME", .str "c"),
      ("U", .str u), ("UNIT", .str "s")]])]

/-- A register of `n` RESULTs, record `i` citing `cites` times the one before. -/
def recordRegister (n cites : Nat) : Value :=
  .arr ((List.range n).map fun i => recordResult s!"RR-{i + 1}"
    [("CITES", strs (if i = 0 then [] else (List.range cites).map fun _ => s!"RR-{i}"))])

/-- A register of 64 RESULTs, the first holding `n` ASSUMPTIONS, the others none. -/
def listedRegister (n : Nat) : Value :=
  .arr ((List.range 64).map fun i => recordResult s!"RR-{i + 1}"
    [("ASSUMPTIONS", strs (if i = 0 then (List.range n).map (fun j => s!"AA-{j + 1}") else []))])

/-- A decimal string `0.` and `z` zeros, then `1e-9999`: `10^-(z + 10000)`, whose
denominator holds 65,536 bits for `z = 9728` and 65,539 for `z = 9729`. -/
def tinyDecimal (z : Nat) : String := "0." ++ String.ofList (List.replicate z '0') ++ "1e-9999"

/-- A verification of an L RESULT of `7 × 10^-n` seconds against 0 s with an uncertainty of
3 s, its DIFFERENCE presented as `value`, 3 and `zeta`: ZETA's square is `49 / (9 × 10^(2n))`,
whose denominator holds 65,532 bits for `n = 9863` and 65,538 for `n = 9864`. -/
def verificationAt (n : Nat) (value zeta : String) : Value :=
  .obj [("target", recordResult "RR-10" [("QUANTITY", .str "period"),
      ("VALUE", .str s!"7e-{n}"), ("UNIT", .str "s")]),
    ("verification", .obj [("CLASS", .str "VERIFICATION"), ("TARGET", .str "RR-10"),
      ("DIFFERENCE", .obj [("U", .str "3"), ("VALUE", .str value), ("ZETA", .str zeta)]),
      ("EXTERNAL", .obj [("QUANTITY", .str "period"), ("VALUE", .str "0"),
        ("U_C", .str "3"), ("UNIT", .str "s")])]), ("k", .str "2")]

/-- A request of `reaudit_batch`, its successor's register padded with `n` RESULTs no
re-check reads (none carries INHERITS). -/
def reauditPadded (request : Value) (n : Nat) : Value :=
  let pad : List Value := (List.range n).map fun i => recordResult s!"PP-{i + 1}" []
  match request with
  | .obj ms => .obj (ms.map fun m =>
      match m with
      | ("dst_records", .arr rs) => ("dst_records", .arr (rs ++ pad))
      | m => m)
  | v => v

/-- The length of the register a request of `reaudit_batch` answers, `none` for a refusal. -/
def reauditRegister (got : Except Refusal Value) : Option Nat :=
  match got with
  | .ok (.arr [.str "OK", o]) =>
    match member o "REGISTER" with
    | some (.arr xs) => some xs.length
    | _ => none
  | _ => none

/-- The register after the re-audit within `maxRecords`: RX17 of
`vectors/reaudit_corpus.json` (a failed re-check opening an IC2 and a UNDER gap) with its
successor's register padded so that the register it answers holds 64 records is answered;
padded with one record more, it is refused whole by the bound, never written past it. -/
def runReauditRegisterBound : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let some rx17 := (← v1Cases "vectors/reaudit_corpus.json").find? fun c =>
      match member c "name" with
      | some (.str s) => s.startsWith "RX17"
      | _ => false
    | throw (IO.userError "reaudit_corpus.json: no RX17")
  let some request := member rx17 "args" | throw (IO.userError "RX17: no args")
  -- RX17 answers its 3 records and 2 gap records, and promotes nothing. Padded with `n`
  -- RESULTs it answers the 3 + n records and the 2 gap records, the padding not promoted.
  let at64 := respondTo "record" "reaudit_batch" (reauditPadded request 59)
  t ← t.check (reauditRegister at64 == some 64)
    s!"record reaudit_batch, the register after the re-audit at 64: got {repr (at64.toOption.map (·.canonicalJson))} or {repr (match at64 with | .error r => some r.detail | _ => none)}"
  let past := respondTo "record" "reaudit_batch" (reauditPadded request 60)
  t ← t.check (boundRefusal past)
    s!"record reaudit_batch, the register after the re-audit past 64: got {repr (past.toOption.map (·.canonicalJson))} or {repr (match past with | .error r => some r.detail | _ => none)}"
  return t.pair

def runRecordBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let tfk := .obj [("TPK", .obj []), ("TrM", .obj [("ENTRIES", .arr [])]),
    ("TMS", .obj [("PARAMETERS", .obj [])])]
  let promotion (n audits : Nat) : Value := .obj [("records", recordRegister n 1),
    ("words", .obj []), ("tfk", tfk),
    ("open_audits", strs ((List.range audits).map fun i => s!"AA-{i + 1}"))]
  -- `{"record": {"T": texts}}`: the names "record" and "T" hold 7 code points.
  let texts (total : Nat) : Value := .obj [("record", .obj [("T", .arr (textsOf (total - 7)))])]
  let cases : List (String × String × Value × BoundOutcome) := [
    ("entries at 1024", "record_check",
      .obj [("record", recordResult "RR-1" [("ASSUMPTIONS",
        strs ((List.range 1024).map fun i => s!"RR-{i + 2}"))]), ("stage", .str "PUSH")], .answered),
    ("entries past 1024", "record_check",
      .obj [("record", recordResult "RR-1" [("ASSUMPTIONS",
        strs ((List.range 1025).map fun i => s!"RR-{i + 2}"))]), ("stage", .str "PUSH")], .bound),
    ("a string at 16384 code points", "prec_decimal",
      .obj [("s", .str (String.ofList (List.replicate 16384 '7')))], .answered),
    ("a string past 16384 code points", "prec_decimal",
      .obj [("s", .str (String.ofList (List.replicate 16385 '7')))], .bound),
    ("a member's name past 16384 code points", "record_view",
      .obj [("record", .obj [(codePoints 16385, .int 1)]), ("view", .str "HOLD")], .bound),
    ("text at 131072 code points in all", "record_check", texts 131072, .answered),
    ("text past 131072 code points in all", "record_check", texts 131073, .bound),
    ("register records at 64", "status_words", .obj [("register", recordRegister 64 1)], .answered),
    ("register records past 64", "status_words", .obj [("register", recordRegister 65 1)], .bound),
    ("register lists at 512", "withdrawal_scope",
      .obj [("register", listedRegister 512), ("root", .str "RR-1"), ("still_stands", strs [])],
      .answered),
    ("register lists past 512", "withdrawal_scope",
      .obj [("register", listedRegister 513), ("root", .str "RR-1"), ("still_stands", strs [])],
      .bound),
    ("source records past 64", "repromote_batch",
      .obj [("src_records", recordRegister 65 0), ("src_words", .obj []),
        ("dst_records", recordRegister 1 0), ("dst_words", .obj []), ("tfk", tfk),
        ("open_audits", strs [])], .bound),
    ("successor records past 64", "reaudit_batch",
      .obj [("dst_records", recordRegister 65 0), ("dst_tfk", tfk)], .bound),
    ("predecessor records past 64", "reaudit_batch",
      .obj [("src_records", recordRegister 65 0), ("dst_records", recordRegister 1 0),
        ("dst_tfk", tfk)], .bound),
    ("open audits at 64", "promotion_pass", promotion 64 64, .answered),
    ("open audits past 64", "promotion_pass", promotion 64 65, .bound),
    ("an uncertainty of 10^-19728", "field_values",
      .obj [("record", mResult (tinyDecimal 9728) "1")], .answered),
    ("an uncertainty of 10^-19729, past the bound on an exact value", "field_values",
      .obj [("record", mResult (tinyDecimal 9729) "1")], .tooLarge),
    ("a point past the bound on an exact value", "verification_difference",
      .obj [("target", recordResult "RR-10" [("QUANTITY", .str "period"), ("VALUE", .str "2"),
          ("UNIT", .str "s"), ("AT", .arr [.obj [("DOF", .str "t"), ("UNIT", .str "s"),
            ("VALUE", .str (tinyDecimal 12000))]])]),
        ("verification", .obj [("CLASS", .str "VERIFICATION"), ("TARGET", .str "RR-10"),
          ("EXTERNAL", .obj [("QUANTITY", .str "period"), ("VALUE", .str "2"),
            ("U_C", .str "0.1"), ("UNIT", .str "s")])]), ("k", .str "2")], .tooLarge),
    -- ZETA's square within the bound and formed; the twelve digits from Python's decimal at
    -- 60 digits, independently.
    ("a verification's zeta squared within the bound on an exact value", "verification_difference",
      verificationAt 9863 "7e-9863" "233333333333e-9874",
      .exactly "[\"OK\",{\"U\":\"3\",\"VALUE\":\"7e-9863\",\"ZETA\":\"233333333333e-9874\"},false]"),
    ("a verification's zeta squared past the bound on an exact value", "verification_difference",
      verificationAt 9864 "7e-9864" "233333333333e-9875", .tooLarge),
    ("a budget's square within the bound", "budget_check",
      .obj [("record", mResult "1" ("0." ++ String.ofList (List.replicate 9000 '1')))], .answered),
    ("a budget's square past the bound on an exact value", "budget_check",
      .obj [("record", mResult "1" ("0." ++ String.ofList (List.replicate 10000 '1')))], .tooLarge)]
  for (what, fn, request, outcome) in cases do
    let got := respondTo "record" fn request
    t ← t.check (outcome.holds got)
      s!"record {fn}, {what}: got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Record

open Tests.Calculator

/-- The family `record`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc record (record, record_view, record_forms)", runRecordCalls),
  ("pcalc record bounds", runRecordBounds),
  ("pcalc record reaudit register bound", runReauditRegisterBound),
]

end Tests.Calculator.Record
