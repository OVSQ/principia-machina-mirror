import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/lint_corpus.json` (v1's `tpc_lint` 0.1.0, 231 cases: lint 209,
counts 3, counts_of 7, norm 4, tokens 7, tables 1) against `Principia.Lint`.

Each case's arguments are read as v1's corpus gives them: a zone or tools argument as a
text, as bytes from `<name>_hex`, or as a text built from `<name>_parts`, and anything
else as neither; the cap and the findings as v1's JSON reader gives them. The function is
run and its typed outcome compared with the case's `expected` text read back into the same
types: a finding list into `Finding`s (each code, item and locator read into its type: an
entry's id must be one of its table's, a code point must be written as v1 writes it, a
path's names must be in `KNOWN_KEYS`), the counts into numbers per code, the tokens into a
list; a refusal `ERROR:<word>` into `Refusal`. The finding list and the counts are also
compared as v1's text, which the Calculator writes.

Nothing is owed: with Unicode's tables (decision D3) the lint answers every case, and
`vectors/lint_corpus.owed.json` must list none. Fault checks run first: the comparisons
must refuse mutated expectations, the order must sort and merge, and the owed list's check
must refuse a list missing or adding a case.

`runTables` checks the tables: `Principia.Lint.tablesJson` equals v1's `LINT_TABLES_JSON`
in `docs/v1/tpc_py/tpc_lint.py`, character for character, and reads whole.
-/

open Lean
open Principia
open Principia.Lint
open Principia.Zone (Value)

namespace Tests.Lint

/-- Passing and failing checks. -/
structure Count where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr. -/
def Count.check (t : Count) (ok : Bool) (what : String) : IO Count := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL lint: {what}"
    return { t with fail := t.fail + 1 }

/-! ## Reading the arguments -/

/-- A hexadecimal digit's value. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- v1's `bytes.fromhex`. -/
def hexBytes (s : String) : Option ByteArray :=
  let rec go : List Char → Array UInt8 → Option (Array UInt8)
    | [], acc => some acc
    | a :: b :: rest, acc => do go rest (acc.push (((← hexDigit? a) * 16 + (← hexDigit? b)).toUInt8))
    | [_], _ => none
  (go s.toList #[]).map ByteArray.mk

/-- v1's `_arg_text`: `<name>_hex` as bytes, `<name>_parts` joined as a text, else the
argument itself, a text or anything else. -/
def argInput (args : Json) (name : String) : IO Input := do
  if let .ok (.str h) := args.getObjVal? (name ++ "_hex") then
    match hexBytes h with
    | some b => return .bytes b
    | none => throw (IO.userError s!"lint: {name}_hex is not hexadecimal")
  if let .ok parts := args.getObjVal? (name ++ "_parts") then
    let mut s := ""
    for p in ← IO.ofExcept parts.getArr? do
      let piece ← IO.ofExcept ((← IO.ofExcept (p.getArrVal? 0)).getStr?)
      let times ← IO.ofExcept ((← IO.ofExcept (p.getArrVal? 1)).getNat?)
      for _ in [0:times] do
        s := s ++ piece
    return .text s
  match args.getObjVal? name with
  | .ok (.str s) => return .text s
  | _ => return .other

/-- An argument as v1's JSON reader gives it; a missing one is `None`, v1's `null`. -/
def argValue (args : Json) (name : String) : Value :=
  match args.getObjVal? name with
  | .ok v => Tests.Zone.toValue v
  | .error _ => .null

/-! ## Reading v1's texts back into the types -/

/-- A code's word. -/
def readCode? (s : String) : Option Code := Code.all.find? (·.text == s)

/-- The ids of a code's table. -/
def tableIds : Code → List String
  | .pl2 => tables.pl2.map (·.id)
  | .pl3 => tables.pl3.map (·.id)
  | .pl4 => tables.pl4.map (·.id)
  | .pl5 => tables.pl5.map (·.id)
  | .pl6 => tables.pl6.map (·.id)
  | .pl7 => tables.pl7.map (·.id)
  | .pl9 => tables.pl9.map (·.id)
  | _ => []

/-- `U+XXXX` read into its code point, only as v1 writes it. -/
def readCodePoint? (s : String) : Option Char := do
  guard (s.startsWith "U+")
  let n ← ((s.drop 2).toString.toList.mapM hexDigit?).map fun ds => ds.foldl (fun a d => a * 16 + d) 0
  let c := Char.ofNat n
  guard (Principia.Zone.codePoint c == s)
  pure c

/-- An item read for its code. -/
def readItem? (code : Code) (s : String) : Option Item :=
  match code with
  | .pl0 => (Fault.all.find? (·.text == s)).map .fault
  | .pl1 => (readCodePoint? s).map .codePoint
  | .pl8 => if s == "-" then some .dash else none
  | c => if (tableIds c).contains s then some (.entry s) else none

/-- A path step: `@<rank>`, an index, or a name in `KNOWN_KEYS`. -/
def readSeg? (s : String) : Option Seg :=
  if s.startsWith "@" then
    let r := (s.drop 1).toString
    if !r.isEmpty && r.all Char.isDigit then r.toNat?.map .rank else none
  else if !s.isEmpty && s.all Char.isDigit then s.toNat?.map .index
  else if tables.knownKeys.contains s then some (.name s) else none

/-- A number written as v1 writes one: digits, no sign, no leading zero. -/
def readNat? (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit && (s == "0" || !s.startsWith "0") then s.toNat? else none

/-- A locator read back. -/
def readLocator? (s : String) : Option Locator :=
  if s == "-" then some .none
  else match s.splitOn ":" with
    | ["Z", l, c] => do pure (.zone (← readNat? l) (← readNat? c))
    | ["T", i, path] => do pure (.tool (← readNat? i) (← (path.splitOn "/").mapM readSeg?) false)
    | ["T", i, path, "key"] => do pure (.tool (← readNat? i) (← (path.splitOn "/").mapM readSeg?) true)
    | _ => none

/-- A finding list's text read back into findings. -/
def readFindings? (expected : String) : Option (List Finding) := do
  let j ← (Json.parse expected).toOption
  let items ← j.getArr?.toOption
  items.toList.mapM fun o => do
    let code ← readCode? (← (o.getObjValAs? String "code").toOption)
    let item ← readItem? code (← (o.getObjValAs? String "item").toOption)
    let loc ← readLocator? (← (o.getObjValAs? String "locator").toOption)
    pure ⟨code, item, loc⟩

/-- The counts' text read back: each code's number, in `CODES` order. -/
def readCounts? (expected : String) : Option (List Nat) := do
  let j ← (Json.parse expected).toOption
  Code.all.mapM fun c => (j.getObjValAs? Nat c.text).toOption

/-- The tokens' text read back. -/
def readTokens? (expected : String) : Option (List String) := do
  let j ← (Json.parse expected).toOption
  (← j.getArr?.toOption).toList.mapM fun t => t.getStr?.toOption

/-- v1's `json.dumps` of the tokens (each is `a-z0-9`, nothing to escape). -/
def tokensJson (ts : List String) : String := "[" ++ ",".intercalate (ts.map fun t => "\"" ++ t ++ "\"") ++ "]"

/-- A refusal text, `ERROR:<word>`. -/
def refusalOf? (expected : String) : Option Refusal :=
  if expected.startsWith "ERROR:" then
    [Refusal.findings, .text, .name].find? (·.message == (expected.drop 6).toString)
  else none

/-! ## Running a case -/

/-- What a case gives, typed. -/
inductive Got where
  | findings (o : Outcome (List Finding))
  | counts (o : Outcome (List Nat))
  | text (o : Outcome String)
  | tokens (o : Outcome (List String))
  | tables (s : String)

def runCase (fn : String) (args : Json) : IO Got := do
  match fn with
  | "lint" => pure (.findings (lint (← argInput args "zone") (← argInput args "tools") (argValue args "cap")))
  | "counts" =>
    pure (.counts ((lint (← argInput args "zone") (← argInput args "tools") (argValue args "cap")).map counts))
  | "counts_of" => pure (.counts (countsOf (argValue args "findings")))
  | "norm" => pure (.text (lintNorm (argValue args "text")))
  | "tokens" => pure (.tokens (nameTokens (argValue args "name")))
  | "tables" => pure (.tables tablesAnswer)
  | other => throw (IO.userError s!"lint: unknown fn {other}")

/-- A judged outcome against the expected text, typed and as text: `true` when they agree. -/
def agrees (expected : String) : Got → Bool
  | .findings (.ok fs) => readFindings? expected == some fs && findingsJson fs == expected
  | .counts (.ok ns) => readCounts? expected == some ns && countsJson ns == expected
  | .text (.ok s) => s == expected
  | .tokens (.ok ts) => readTokens? expected == some ts && tokensJson ts == expected
  | .tables s => s == expected
  | .findings (.error (.refused r)) | .counts (.error (.refused r)) | .text (.error (.refused r))
  | .tokens (.error (.refused r)) => refusalOf? expected == some r

/-- The owed list's check, both ways. -/
def owedComplaints (owed listed : List (String × String)) : List String :=
  (owed.filter (!listed.contains ·)).map (fun (n, r) => s!"{n}: owed ({r}) but not listed so") ++
  (listed.filter (!owed.contains ·)).map (fun (n, r) => s!"{n}: listed as owed ({r}) but not owed for that reason")

/-! ## Fault checks -/

/-- Each is `true` when the check refuses a fault, or accepts what it must. -/
def faultChecks : List (String × Bool) :=
  let f1 : Finding := ⟨.pl1, .codePoint '​', .zone 2 25⟩
  let f2 : Finding := ⟨.pl1, .codePoint '​', .tool 0 [.name "description"] false⟩
  let f3 : Finding := ⟨.pl4, .entry "PL4-01", .zone 1 1⟩
  let fs := [f1, f2, f3]
  let text := "[{\"code\":\"PL1\",\"item\":\"U+200B\",\"locator\":\"Z:2:25\"},{\"code\":\"PL1\",\"item\":\"U+200B\",\"locator\":\"T:0:description\"},{\"code\":\"PL4\",\"item\":\"PL4-01\",\"locator\":\"Z:1:1\"}]"
  let keyLoc := "T:0:inputSchema/properties/@0:key"
  let tag : Finding := ⟨.pl1, .codePoint (Char.ofNat 0xE0041), .zone 1 1⟩
  let bom : Finding := ⟨.pl1, .codePoint '﻿', .zone 1 1⟩
  [("findings as printed are accepted", agrees text (.findings (.ok fs))),
   ("two findings swapped", !agrees text (.findings (.ok [f2, f1, f3]))),
   ("a column changed", !agrees (text.replace "Z:2:25" "Z:2:24") (.findings (.ok fs))),
   ("an item changed", !agrees (text.replace "PL4-01" "PL4-02") (.findings (.ok fs))),
   ("a finding missing", !agrees text (.findings (.ok [f1, f2]))),
   ("a code point in lower case is not v1's", readItem? .pl1 "U+200b" == none),
   ("an entry outside its table is not read", readItem? .pl4 "PL4-99" == none),
   ("a key locator reads into its steps",
     readLocator? keyLoc == some (.tool 0 [.name "inputSchema", .name "properties", .rank 0] true) &&
       (Locator.tool 0 [.name "inputSchema", .name "properties", .rank 0] true).text == keyLoc),
   ("a rank is not an index", readSeg? "@0" != readSeg? "0"),
   ("a name outside KNOWN_KEYS is never read", readSeg? "token" == none),
   ("a leading zero is not v1's number", readLocator? "Z:01:1" == none),
   ("a refusal's word changed", !agrees "ERROR:text" (.text (.error (.refused .name)))),
   ("the order sorts and merges",
     ordered [f3, f2, f1, f3, f1] == [f1, f2, f3]),
   ("items in code point order of their text: U+E0041 before U+FEFF",
     ordered [bom, tag] == [tag, bom]),
   ("counts count every finding once", counts [f1, f2, f3, f3] == [0, 2, 0, 0, 2, 0, 0, 0, 0, 0]),
   ("counts as printed are accepted",
     agrees "{\"PL0\":0,\"PL1\":2,\"PL2\":0,\"PL3\":0,\"PL4\":1,\"PL5\":0,\"PL6\":0,\"PL7\":0,\"PL8\":0,\"PL9\":0}"
       (.counts (.ok [0, 2, 0, 0, 1, 0, 0, 0, 0, 0]))),
   ("a count changed", !agrees
       "{\"PL0\":0,\"PL1\":2,\"PL2\":0,\"PL3\":0,\"PL4\":1,\"PL5\":0,\"PL6\":0,\"PL7\":0,\"PL8\":0,\"PL9\":0}"
       (.counts (.ok [0, 1, 0, 0, 1, 0, 0, 0, 0, 0]))),
   ("an owed case missing from the list", !(owedComplaints [("x", "unicode U+0301")] []).isEmpty),
   ("a listed case not owed", !(owedComplaints [] [("x", "unicode U+0301")]).isEmpty),
   ("a case owed for another reason",
     !(owedComplaints [("x", "unicode U+0301")] [("x", "unicode U+2019")]).isEmpty)]

/-! ## The run -/

/-- Run the corpus: passes and failures; owed cases are counted and printed. -/
def run : IO (Nat × Nat) := do
  let mut t : Count := {}
  for (what, ok) in faultChecks do
    t ← t.check ok s!"fault check: {what}"
  let faults := t
  t := {}
  let corpus ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/lint_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (corpus.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/lint_corpus.owed.json"))
  let listed ← (← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let args ← IO.ofExcept (c.getObjVal? "args")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let got ← runCase fn args
    t ← t.check (agrees expected got) s!"{name}: expected {repr expected}"
  -- The lint owes nothing, so the owed list must be empty.
  for complaint in owedComplaints [] listed do
    t ← t.check false complaint
  IO.println s!"lint: none owed; {faults.pass} of {faultChecks.length} fault checks refused or accepted as they must"
  return (t.pass, t.fail + faults.fail)

/-! ## The tables against v1's text -/

/-- A Python literal's body in single quotes, its `\\` and `\'` undone; `none` for any
other escape. -/
def unescapePy : List Char → Option (List Char)
  | [] => some []
  | '\\' :: '\\' :: rest => ('\\' :: ·) <$> unescapePy rest
  | '\\' :: '\'' :: rest => ('\'' :: ·) <$> unescapePy rest
  | '\\' :: _ => none
  | c :: rest => (c :: ·) <$> unescapePy rest

/-- `LINT_TABLES_JSON`'s literal in v1's source: its quoted pieces between
`LINT_TABLES_JSON = (` and `)`, joined. -/
def v1Tables (src : String) : Option String := do
  let after ← (src.splitOn "LINT_TABLES_JSON = (\n")[1]?
  let block ← (after.splitOn "\n)\n")[0]?
  let pieces ← (block.splitOn "\n").mapM fun l =>
    let t := l.trimAscii.toString
    if t.startsWith "'" && t.endsWith "'" && t.length ≥ 2 then
      (unescapePy ((t.toList.drop 1).dropLast)).map String.ofList
    else none
  return String.join pieces

/-- The entries' ids are `<code>-01`, `<code>-02` ..., in order. -/
def idsInOrder (code : String) (ids : List String) : Bool :=
  ids == (List.range ids.length).map fun k =>
    code ++ "-" ++ (if k + 1 < 10 then "0" else "") ++ toString (k + 1)

def runTables : IO (Nat × Nat) := do
  let src ← IO.FS.readFile "docs/v1/tpc_py/tpc_lint.py"
  let phraseTables := [tables.pl3, tables.pl4, tables.pl5, tables.pl6, tables.pl9]
  let checks : List (Bool × String) := [
    (v1Tables src == some tablesJson, "tablesJson equals v1's LINT_TABLES_JSON, character for character"),
    ((readTables tablesJson).isSome, "the tables read whole"),
    (tables.version == tablesVersion && src.contains ("LINT_TABLES_VERSION = \"" ++ tablesVersion ++ "\""),
      "the tables' version is v1's"),
    (src.contains tablesSha256, "the recorded SHA-256 is v1's"),
    (Sha256.digestText tablesJson == tablesSha256,
      "SHA-256 of tablesJson is the SHA-256 v1 records for it, as v1 checked it on loading"),
    (src.contains ("VERSION = \"" ++ Principia.Lint.version ++ "\"") && src.contains ("LINT_MAX_BYTES = " ++ toString maxBytes) &&
      src.contains ("LINT_CAP_MAX = " ++ toString capMax), "the version and the two bounds are v1's"),
    (tables.knownKeys.length == 53 && tables.neg.length == 23 && tables.negWindow == 4 &&
      tables.pl2.length == 30 && (tables.pl2.map (·.rules.length)).sum == 46 &&
      tables.pl3.length == 12 && tables.pl4.length == 11 && tables.pl5.length == 9 &&
      tables.pl6.length == 16 && tables.pl7.length == 3 && tables.pl9.length == 6,
      "every table has v1's number of entries"),
    (idsInOrder "PL2" (tables.pl2.map (·.id)) && idsInOrder "PL3" (tables.pl3.map (·.id)) &&
      idsInOrder "PL4" (tables.pl4.map (·.id)) && idsInOrder "PL5" (tables.pl5.map (·.id)) &&
      idsInOrder "PL6" (tables.pl6.map (·.id)) && idsInOrder "PL7" (tables.pl7.map (·.id)) &&
      idsInOrder "PL9" (tables.pl9.map (·.id)), "the entries' ids are in order"),
    (tables.pl2.all (·.rules.all fun els => match els with | .lit (_ :: _) :: _ => true | _ => false),
      "every credential shape starts with a literal (v1 finds its candidates by it)"),
    (phraseTables.all (·.all (·.rules.all fun parts =>
        match parts with | alts :: _ => alts.all (!·.isEmpty) | [] => false)) &&
      tables.pl7.all (·.templates.all fun parts =>
        match parts with | alts :: _ => alts.all (!·.isEmpty) | [] => false),
      "every phrase starts with a character (v1 finds its candidates by its first part)"),
    (["function", "name", "description", "title"].all tables.knownKeys.contains,
      "the members PL6 and PL7 read are in KNOWN_KEYS")]
  let mut pass := 0
  let mut fail := 0
  for (ok, what) in checks do
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL lint_tables: {what}"
      fail := fail + 1
  return (pass, fail)

end Tests.Lint
