import Principia
import Tests.Canonical
import Tests.Form
import Tests.Governor
import Tests.Sha256
import Tests.Strike
import Tests.Unicode

/-!
The vectors of the Calculator's interface: the JSON reader (`vectors/json_text.json`,
`Canonical.readText`) and the dispatch of `pcalc <family> <function>`
(`vectors/pcalc.json`, `Calculator.answer`), both run in-process: a case's stdin is
given to `answer` as bytes, and its stdout and exit code compared byte for byte.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- Bytes from lowercase hexadecimal. -/
def hexBytes (s : String) : IO ByteArray := do
  let digit (c : Char) : IO UInt8 :=
    match hexValue c with
    | some n => pure n.toUInt8
    | none => throw (IO.userError s!"not hexadecimal: {s}")
  let rec go : List Char → ByteArray → IO ByteArray
    | a :: b :: rest, acc => do go rest (acc.push ((← digit a) * 16 + (← digit b)))
    | [], acc => pure acc
    | _, _ => throw (IO.userError s!"odd hexadecimal: {s}")
  go s.toList ByteArray.empty

/-- A case's input: `text` as UTF-8, or `bytes` / `stdin_hex` in hexadecimal. -/
def input (c : Json) (textKey hexKey : String) : IO ByteArray := do
  match c.getObjValAs? String textKey with
  | .ok t => pure t.toUTF8
  | .error _ => hexBytes (← str c hexKey)

/-- A reading refused with exactly `f`. -/
def refusedWith (r : Except ReadFailure Value) (f : ReadFailure) : Bool :=
  match r with
  | .error g => g == f
  | .ok _ => false

/-- A value read back from its own canonical JSON writes the same text. -/
def rereads (v : Value) : Bool :=
  match v.canonicalJson with
  | none => false
  | some t =>
    match readString t with
    | .ok w => w.canonicalJson == some t
    | .error _ => false

/-! ## json_text.json: the reader -/

def runJsonText : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/json_text.json") do
    let what := c.compress
    let got := readText (← input c "text" "bytes")
    match c.getObjValAs? String "refused" with
    | .ok code =>
      let pos : Option Nat ← match c.getObjVal? "position" with
        | .ok .null => pure none
        | .ok (.num ⟨p, 0⟩) => pure (some p.toNat)
        | _ => throw (IO.userError s!"{what}: no position")
      let ok := match got with
        | .error f => WireWord.toWire f.error == code && f.position == pos
        | .ok _ => false
      t ← t.check ok s!"{what}: got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error f => some f | _ => none)}"
    | .error _ =>
      match got with
      | .error f => t ← t.check false s!"{what}: refused {repr f}"
      | .ok v =>
        match c.getObjValAs? String "canonical" with
        | .ok text =>
          t ← t.check (v.canonicalJson == some text) s!"{what}: got {repr v.canonicalJson}"
        | .error _ =>
          let expected ← value (← field c "value")
          t ← t.check (v == expected) s!"{what}: got {repr v}"
        t ← t.check (rereads v) s!"{what}: its canonical JSON does not read back alike"
  -- Built here, too long for a corpus line: the size bound, and numbers in a text.
  let spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
  let atLimit := (spaces (maxTextBytes - 1) ++ "1").toUTF8
  t ← t.check ((readText atLimit).toOption.isSome) s!"a text of exactly {maxTextBytes} bytes is read"
  let overLimit := (spaces maxTextBytes ++ "1").toUTF8
  t ← t.check (refusedWith (readText overLimit) ⟨.tooLarge, none⟩)
    s!"a text of {maxTextBytes + 1} bytes is refused TOO_LARGE"
  let digits (n : Nat) : String := String.ofList (List.replicate n '7')
  t ← t.check ((readString ("[" ++ digits maxNumberDigits ++ "]")).toOption.isSome)
    s!"a number of {maxNumberDigits} digits in a text is read"
  t ← t.check (refusedWith (readString ("[" ++ digits (maxNumberDigits + 1) ++ "]"))
      ⟨.numberTooLong, some 1⟩)
    s!"a number of {maxNumberDigits + 1} digits in a text is refused NUMBER_TOO_LONG"
  return t.pair

/-! ## v1's corpora through the dispatch

Each case of a v1 corpus is read with the Calculator's own reader, which keeps a number's
kind and the members' order (`Lean.Json` would turn `2.0` into `2`), and its input given
to the family's function as a request, through `Calculator.respondTo`; the text path is
`pcalc.json`'s. -/

/-- A v1 corpus's cases, read by the Calculator's reader. -/
def v1Cases (path : System.FilePath) : IO (List Value) := do
  let text ← IO.FS.readFile path
  match readString text with
  | .error f => throw (IO.userError s!"{path}: refused {repr f}")
  | .ok (.obj ms) =>
    match ms.lookup "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError s!"{path}: no cases")
  | .ok _ => throw (IO.userError s!"{path}: not an object")

def member (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

def memberStr (v : Value) (k : String) : IO String :=
  match member v k with
  | some (.str s) => pure s
  | _ => throw (IO.userError s!"no string {k}")

/-- Whether v1's `canon` text of an answer reads back as that answer: every string in it
non-empty and free of `,`, `[` and `]` (v1 wrote strings unquoted). -/
partial def plainStrings : Value → Bool
  | .str s => !s.isEmpty && !s.any fun c => c == ',' || c == '[' || c == ']'
  | .arr xs => xs.all plainStrings
  | _ => true

/-- `cluster_corpus.json`: every case's request through `cluster cluster` or
`cluster resolving_step`; v1's text, or v1's word as a refusal's detail. -/
def runClusterCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/cluster_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let fn := match member c "fn" with
      | some (.str "resolving") => "resolving_step"
      | _ => "cluster"
    let params := match member c "params" with
      | some (.obj ps) => ps
      | _ => []
    let keys := if fn == "cluster" then ["rows", "paired"] else ["spacing", "ses", "paired"]
    let request : Value := .obj (params ++ keys.filterMap fun k => (member c k).map (k, ·))
    let got := respondTo "cluster" fn request
    let ok := match got, expected.startsWith "ERROR:" with
      | .ok (.str text), false => text == expected
      | .error r, true => r.code == .badArgument && "ERROR:" ++ r.detail == expected
      | _, _ => false
    t ← t.check ok s!"cluster {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `digest_corpus.json`: every case's request through the digest family, v1's names
mapped to the Calculator's (`d_tfk` is `digest_research_assembly`, its zones' digests named
by their zones; `hex_digests` is `digests`); the answer is v1's digest. -/
def runDigestCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/digest_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let arg (k : String) : IO Value := match member input k with
      | some v => pure v
      | none => throw (IO.userError s!"{id}: no {k}")
    let (fn, request) ← match ← memberStr c "fn" with
      | "digest_fields" => pure ("digest_fields", Value.obj [("fields", ← arg "fields")])
      | "combine_digests" => pure ("combine_digests", Value.obj [("digests", ← arg "hex_digests")])
      | "d_tfk" => pure ("digest_research_assembly", Value.obj [("starting_set", ← arg "d_tpk"),
          ("correspondence", ← arg "d_trm"), ("criteria", ← arg "d_tms")])
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    let got := respondTo "digest" fn request
    let ok := match got with
      | .ok (.str d) => d == expect
      | _ => false
    t ← t.check ok s!"digest {fn} {id}: expected {expect}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `dis_corpus.json`: every case's request through the digest family, v1's names mapped to
the Calculator's (`d_tps` is `digest_specification`, `d_is` is `digest_instruction_set` with
its `d_tps` named `specification`, `tps_pages` is `specification_pages`); the answer's v1
`canon` text is `expect`, no string of it holding `,`, `[` or `]`
(`Tests.Canonical.bracketFree`); a digest case's preimage is compared too, through
`preimage_specification` and `preimage_instruction_set`. -/
def runDisCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/dis_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let arg (k : String) : IO Value := match member input k with
      | some v => pure v
      | none => throw (IO.userError s!"{id}: no {k}")
    let (fn, pre, request) ← match ← memberStr c "fn" with
      | "pre_texts" => pure ("pre_texts", none, Value.obj [("wikitext", ← arg "wikitext")])
      | "tps_pages" => pure ("specification_pages", none, Value.obj [("pages", ← arg "pages")])
      | "d_tps" => pure ("digest_specification", some "preimage_specification",
          Value.obj [("version", ← arg "version"), ("pages", ← arg "pages")])
      | "d_is" => pure ("digest_instruction_set", some "preimage_instruction_set",
          Value.obj [("version", ← arg "version"), ("specification", ← arg "d_tps"),
            ("members", ← arg "members")])
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    let got := respondTo "digest" fn request
    let ok := match got with
      | .ok v => v.canon == some expect && Tests.Canonical.bracketFree v
      | .error _ => false
    t ← t.check ok
      s!"digest {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))}"
    match member c "preimage", pre with
    | some (.str p), some preFn =>
      let ok := match respondTo "digest" preFn request with
        | .ok (.arr [.str "OK", .str q]) => q == p
        | _ => false
      t ← t.check ok s!"digest {preFn} {id}: expected {repr p}"
    | _, _ => pure ()
  return t.pair

/-- A v1 corpus of the strike family (`strike`) or SR9 (`sr9`): every case's `input`
through `<family> <fn>`; v1's `canon` text of the answer compared with `expect`. -/
def runCanonCalls (family : String) (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases path do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo family fn input
    let ok := match got with
      | .ok v => v.canon == some expect && plainStrings v
      | .error _ => false
    t ← t.check ok s!"{family} {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))}"
  return t.pair

/-- A v1 corpus's owed list: `(id, reason)` for each case the Calculator does not answer yet. -/
def owedList (path : System.FilePath) : IO (List (String × String)) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => do pure (← memberStr o "id", ← memberStr o "reason")
    | _ => throw (IO.userError s!"{path}: no owed list")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- `eom_corpus.json` and `settlement_corpus.json`: every case's request through
`eom <fn>`. The answer's v1 `canon` text is `eom_corpus.json`'s `expect` (a question's commas
are compared within the text, as v1 wrote it); its canonical JSON is
`settlement_corpus.json`'s `expected`. A case listed in the corpus's owed list must be
refused `OWED`, its detail the plain words for the listed reason, and no other case may be. -/
def runEomCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for (corpus, idKey, argsKey, expectKey, asCanon) in
      [("eom_corpus", "id", "input", "expect", true),
       ("settlement_corpus", "name", "args", "expected", false)] do
    let owed ← owedList s!"vectors/{corpus}.owed.json"
    for c in ← v1Cases s!"vectors/{corpus}.json" do
      let id ← memberStr c idKey
      let fn ← memberStr c "fn"
      let expect ← memberStr c expectKey
      let some args := member c argsKey | throw (IO.userError s!"{id}: no {argsKey}")
      let got := respondTo "eom" fn args
      let text (v : Value) : Option String := if asCanon then v.canon else v.canonicalJson
      match owed.lookup id with
      | some why =>
        let detail := Eom.owedDetail (if why == "forms" then Zone.Owed.forms.message else why)
        let ok := match got with
          | .error r => r.code == .owed && r.detail == detail
          | .ok _ => false
        t ← t.check ok s!"eom {fn} {id}: listed as owed ({why}), got {repr (got.toOption.map text)}"
      | none =>
        let ok := match got with
          | .ok v => text v == some expect
          | .error _ => false
        t ← t.check ok
          s!"eom {fn} {id}: expected {repr expect}, got {repr (got.toOption.map text)} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- Version 1's names of the zone functions whose names carry a version 1 code, and the
Calculator's PMA words for them; every other function of `zone_corpus.json` keeps its name. -/
def zoneNames : List (String × String) := [
  ("t1_well_formed", "starting_set_well_formed"),
  ("trm_well_formed", "correspondence_table_well_formed"),
  ("tms_well_formed", "criteria_set_well_formed"),
  ("d_tpk", "digest_starting_set"),
  ("d_trm", "digest_correspondence_table"),
  ("d_tms", "digest_criteria_set"),
  ("d_tfk_of", "digest_research_assembly_of")]

/-- `zone_corpus.json`: all its cases through `zone <fn>`, version 1's names mapped
(`zoneNames`); version 1's `canon` text of the answer compared with `expect`, `null` for
none. None is owed, and none refused. -/
def runZoneCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/zone_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := (zoneNames.lookup v1).getD v1
    let some expect := member c "expect" | throw (IO.userError s!"{id}: no expect")
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "zone" fn input
    let text (v : Value) : Option String := match v with
      | .null => some "null"
      | _ => v.canon
    let ok := match got, expect with
      | .ok v, .str e => text v == some e
      | .ok (.bool b), .bool e => b == e
      | _, _ => false
    t ← t.check ok s!"zone {fn} {id}: expected {repr (expect.canonicalJson)}, got {repr (got.toOption.map text)} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

def runStrikeCalls : IO (Nat × Nat) := do
  let (p1, f1) ← runCanonCalls "strike" "vectors/strike_corpus.json"
  let (p2, f2) ← runCanonCalls "strike" "vectors/sr8_order_corpus.json"
  return (p1 + p2, f1 + f2)

def runSr9Calls : IO (Nat × Nat) := runCanonCalls "sr9" "vectors/sr9_corpus.json"

/-- `sr3_scope_corpus.json`: every case's `input` through `strike sr3_scope`. v1's text of
the answer, a word or `[REFUSED,<reason>]`, is read back into its kind
(`Tests.Strike.sr3Expect`) and compared with the answer, the word as a string or v1's
refusal as the value `["REFUSED", reason]`; none is refused by `pcalc`. -/
def runSr3ScopeCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/sr3_scope_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "strike" "sr3_scope" input
    let ok := match got, Tests.Strike.sr3Expect expect with
      | .ok (.str w), .ok w' => w == w'
      | .ok (.arr [.str "REFUSED", .str r]), .error r' => r == r'
      | _, _ => false
    t ← t.check ok s!"strike sr3_scope {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `conditions_corpus.json`: every case's `args` through `strike <fn>` (`conditions_of`,
`comparison_set`, `sr8_groups`); the answer's canonical JSON is the case's `expected`, v1's
`["OK", ...]` or `["REFUSED", [[code, field, message]]]` as TPM's canonical JSON writes it,
which quotes every string; none is refused by `pcalc`, and none is owed. -/
def runConditionsCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/conditions_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "strike" fn args
    let ok := match got with
      | .ok v => v.canonicalJson == some expected
      | .error _ => false
    t ← t.check ok s!"strike {fn} {name}: expected {expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- An answer of `pcalc` as a landing case writes it: its canonical JSON, or a refusal by
`pcalc` as `refused <code>: <detail>`. -/
def landingShow : Except Refusal Value → String
  | .ok v => v.canonicalJson.getD "?"
  | .error r => s!"refused {r.code.word}: {r.detail}"

/-- `landing_screen.json`: every case's `args` through `landing strike_screen`; the answer's
canonical JSON is the case's `expected`, or, where `pcalc` refuses (owed, or a bound),
`refused <code>: <detail>`. -/
def runLandingCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/landing_screen.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := landingShow (respondTo "landing" fn args)
    t ← t.check (got == expected) s!"landing {fn} {name}: expected {expected}, got {got}"
  return t.pair

/-- v1's names of the probe functions in `probe_corpus.json` (`run_case`), and the
Calculator's. -/
def probeFunctions : List (String × String) :=
  [("compare", "compare"), ("el", "expected_loss"), ("load", "load"), ("probe", "probe_draw"),
   ("ratio", "ratio_step"), ("reset", "reset_update"), ("schedule", "schedule_step"),
   ("step", "probe_step"), ("uniform", "uniform"), ("view", "historical_view")]

/-- `probe_corpus.json`: every case's `args` through `probe <function>`, each giving v1's
text, or v1's message as a refusal's detail; none is owed. -/
def runProbeCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/probe_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := probeFunctions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "probe" fn args
    let ok := match got with
      | .ok (.str text) => text == expected
      | .error r => r.code == .badArgument && "ERROR:" ++ r.detail == expected
      | _ => false
    t ← t.check ok s!"probe {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- A corpus request's members with `text_parts`, v1's runner's packing of a long text, joined
into `text` as v1's `run_case` joins it: each part's string repeated its count of times. -/
def joinTextParts (ms : List (String × Value)) : IO (List (String × Value)) := do
  match ms.lookup "text_parts" with
  | none => pure ms
  | some (.arr parts) =>
    let pieces ← parts.mapM fun
      | .arr [.str s, .int n] => pure (String.join (List.replicate n.toNat s))
      | _ => throw (IO.userError "text_parts: not [string, count] pairs")
    pure ((ms.filter (·.1 != "text_parts")) ++ [("text", .str (String.join pieces))])
  | some _ => throw (IO.userError "text_parts: not a list")

/-- `module_corpus.owed.json`'s cases: each name with the detail its reason is refused with. -/
def provisionOwed : IO (List (String × String)) := do
  match readString (← IO.FS.readFile "vectors/module_corpus.owed.json") with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => do
      let why ← memberStr o "reason"
      let w : Principia.Provision.Owed :=
        if why == "digests" then .digest else .exact (String.ofList (why.toList.drop 7))
      pure (← memberStr o "name", Calculator.Provision.owedDetail w)
    | _ => throw (IO.userError "module_corpus.owed.json: no owed list")
  | _ => throw (IO.userError "module_corpus.owed.json: not an object")

/-- `module_corpus.json`: every case's `args` through `provision <fn>`; the answer is v1's
value, `["OK", ...]` or `["REFUSED", reason]`, compared with the case's `expected` text read
as JSON, through canonical JSON, which writes two values alike only when they are equal. A
case in `module_corpus.owed.json` must be refused `OWED`, its detail the plain words for its
reason, and no other case may be (none is listed). -/
def runProvisionCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← provisionOwed
  for c in ← v1Cases "vectors/module_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some (.obj args) := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "provision" fn (.obj (← joinTextParts args))
    match owed.lookup name with
    | some detail =>
      let ok := match got with
        | .error r => r.code == .owed && r.detail == detail
        | .ok _ => false
      t ← t.check ok s!"provision {fn} {name}: listed as owed, got {repr (got.toOption.map (·.canonicalJson))}"
    | none =>
      let want ← match readString expected with
        | .ok v => pure v.canonicalJson
        | .error _ => throw (IO.userError s!"{name}: the expected text does not read")
      let ok := match got with
        | .ok v => want.isSome && v.canonicalJson == want
        | .error _ => false
      t ← t.check ok
        s!"provision {fn} {name}: expected {expected}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The names of a v1 corpus's owed cases (`{"owed": [{"name": ...}, ...]}`). -/
def owedNames (path : System.FilePath) : IO (List String) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => memberStr o "name"
    | _ => throw (IO.userError s!"{path}: no owed list")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- A v1 corpus of `{name, fn, args, expected}` cases: every case's `args` through `call`
with the Calculator's name of v1's `run_case` function; v1's text, or v1's word as a
refusal's detail (`ERROR:<word>`); a case the owed list names answered `OWED`, and no
other. -/
def runTextCalls (family : String) (path : System.FilePath) (owed : List String)
    (functions : List (String × String)) (call : String → Value → Except Refusal Value) :
    IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases path do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := functions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := call fn args
    let ok := match got, owed.contains name with
      | .error r, true => r.code == .owed
      | .ok (.str text), false => text == expected
      | .error r, false => r.code == .badArgument && "ERROR:" ++ r.detail == expected
      | _, _ => false
    t ← t.check ok s!"{family} {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- v1's names of the identity functions in `identity_corpus.json` (`run_case`), and the
Calculator's. -/
def identityFunctions : List (String × String) :=
  [("class", "change_class"), ("compare", "identity_compare"), ("digest", "prompt_digest"),
   ("family", "family_of"), ("tools", "canonical_tools")]

/-- `identity_corpus.json`: every case through `identity <function>`; the owed list,
`identity_corpus.owed.json`, names none. -/
def runIdentityCalls : IO (Nat × Nat) := do
  runTextCalls "identity" "vectors/identity_corpus.json"
    (← owedNames "vectors/identity_corpus.owed.json") identityFunctions (respondTo "identity")

/-- v1's names of the sponsor functions in `sponsor_corpus.json` (`run_case`), and the
Calculator's. -/
def sponsorFunctions : List (String × String) :=
  [("evidence", "user_evidence"), ("resolve", "conduct_resolve"), ("whitewash", "whitewash_count")]

/-- `sponsor_corpus.json`: every case through `sponsor <function>`; none is owed. -/
def runSponsorCalls : IO (Nat × Nat) :=
  runTextCalls "sponsor" "vectors/sponsor_corpus.json" [] sponsorFunctions (respondTo "sponsor")

/-- v1's names of the lint's functions in `lint_corpus.json` (`run_case`), and the
Calculator's. -/
def lintFunctions : List (String × String) :=
  [("counts", "counts"), ("counts_of", "lint_counts"), ("lint", "lint"), ("norm", "lint_norm"),
   ("tables", "tables"), ("tokens", "name_tokens")]

/-- `lint_corpus.json`: every case through `lint <function>`; the owed list,
`lint_corpus.owed.json`, names none. -/
def runLintCalls : IO (Nat × Nat) := do
  runTextCalls "lint" "vectors/lint_corpus.json" (← owedNames "vectors/lint_corpus.owed.json")
    lintFunctions (respondTo "lint")
/-! ## The units family's corpora

v1's expectations are its `canon` text of a list: `[OK,...]`, `[REFUSED,reason]` or
`[CONVENTION,reason]`. A reason is compared whole (it may hold a comma); the items of an OK
answer by kind: text as text, a boolean or SR8's `S` as its `canon` text, and an exact
number by value, v1's digits read as a decimal against the Calculator's exact spelling (the
hand corpora write the exact spelling itself, which is compared as text). A
reason the Calculator owes (`Calculator.Units.owedReasons`) is expected refused `OWED` with
it as the detail. A case recorded in `units_corpus.divergences.json` is checked against the
recorded answer instead, and the record's v1 text against the corpus. -/

/-- The positions of exact numbers among a function's OK items. -/
def exactItems : String → List Nat
  | "unit_scale" => [0]
  | "normalize_measurement" => [0, 1]
  | _ => []

/-- The Calculator's answer agrees with v1's expectation. -/
def unitsAgrees (fn expect : String) (got : Except Refusal Value) : Bool :=
  let inner (pre : String) : Option String :=
    if expect.startsWith pre && expect.endsWith "]" then
      some (String.ofList ((expect.toList.drop pre.length).dropLast))
    else none
  match inner "[REFUSED,", inner "[CONVENTION,", inner "[OK," with
  | some r, _, _ =>
    if Principia.Calculator.Units.owedReasons.contains r then
      match got with
      | .error e => e.code == .owed && e.detail == r
      | .ok _ => false
    else got.toOption == some (.arr [.str "REFUSED", .str r])
  | _, some r, _ => got.toOption == some (.arr [.str "CONVENTION", .str r])
  | _, _, some body =>
    match got with
    | .ok (.arr (.str "OK" :: items)) =>
      let parts := body.splitOn ","
      parts.length == items.length && plainStrings (.arr items) &&
        (parts.zip (items.zip (List.range items.length))).all fun (p, item, i) =>
          match item with
          | .str s =>
            if (exactItems fn).contains i then
              s == p || (Principia.Decimal.value p).any fun q => (Exact.ofRat q).render == s
            else s == p
          | other => other.canon == some p
    | _ => false
  | _, _, _ => false

/-- The units family's cases of one corpus through `units <fn>`, those of the seven
functions; the corpus's other cases (the double range of an unevaluated product, the
enclosure of π, the helpers) test the library and are left to its runner. -/
def runUnitsCorpus (path : System.FilePath) (divs : List Value) : IO Counts := do
  let mut t : Counts := {}
  let mut seen : List String := []
  for c in ← v1Cases path do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    unless (Principia.Calculator.Units.calls.lookup fn).isSome do continue
    let got := respondTo "units" fn input
    let shown := repr (match got with
      | .ok v => v.canonicalJson
      | .error r => some s!"{r.code.word}: {r.detail}")
    match divs.find? fun d => member d "id" == some (.str id) with
    | some d =>
      seen := id :: seen
      let v1 ← memberStr d "v1"
      let v2 ← memberStr d "v2"
      t ← t.check (v1 == expect && (got.toOption.bind (·.canon)) == some v2)
        s!"units {fn} {id} (recorded divergence): v1 {expect}, recorded {v1}; recorded v2 {v2}, got {shown}"
    | none =>
      t ← t.check (unitsAgrees fn expect got) s!"units {fn} {id}: expected {expect}, got {shown}"
  -- A divergence recorded for a case the corpus does not have is a stale record.
  for d in divs do
    let id ← memberStr d "id"
    unless seen.contains id do
      t ← t.check false s!"units {id}: a recorded divergence with no case"
  return t

/-- `units_corpus.json` (with its recorded divergences), `units_range.json` and
`units_pi.json` through the units family. -/
def runUnitsCalls : IO (Nat × Nat) := do
  let divs ← match readString (← IO.FS.readFile "vectors/units_corpus.divergences.json") with
    | .ok (.obj ms) => match ms.lookup "divergences" with
      | some (.arr ds) => pure ds
      | _ => throw (IO.userError "units_corpus.divergences.json: no divergences")
    | _ => throw (IO.userError "units_corpus.divergences.json: does not read")
  let mut pass := 0
  let mut fail := 0
  for (path, ds) in [("vectors/units_corpus.json", divs), ("vectors/units_range.json", []),
      ("vectors/units_pi.json", [])] do
    let t ← runUnitsCorpus path ds
    pass := pass + t.pass
    fail := fail + t.fail
  return (pass, fail)

/-! ## The families' bounds, at each and one past it

Built here, too long for a line of `pcalc.json`. A request at a bound must not be refused
by it; one past it must be, with the bound named. -/

/-- Whether an answer is a refusal by one of the Calculator's family bounds. -/
def boundRefusal : Except Refusal Value → Bool
  | .error r => r.code == .badArgument && (r.detail.splitOn "the Calculator's bound").length > 1
  | .ok _ => false

def strs (xs : List String) : Value := .arr (xs.map .str)

/-- `n` cluster rows of distinct models. -/
def clusterRows (n : Nat) : Value :=
  .arr ((List.range n).map fun (i : Nat) => .arr [.str s!"m{i}", .str "c", .int (i : Int), .int 1])

/-- `n` strike records, each with one assumption and `cites` citations of the next. -/
def strikeRecords (n cites : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"R{i}", .obj [("assumptions", strs [s!"a{i}"]),
    ("cites", strs ((List.range cites).map fun _ => s!"R{(i + 1) % n}")), ("steps", .int 1)]))

/-- A suite of `n` records, each with `cites` citations, and `k` contradictions. -/
def suite (n cites k : Nat) : Value :=
  .obj [("records", .obj ((List.range n).map fun i => (s!"R{i}", .obj [
      ("regime", .str (if i % 2 == 0 then "M" else "L")), ("assumptions", strs [s!"A{i}"]),
      ("cites", strs ((List.range cites).map fun _ => s!"R{(i + 1) % n}")),
      ("steps", .int 1), ("domain", .str "MAIN"), ("sr1_fail", .bool false)]))),
    ("contradictions", .arr ((List.range k).map fun i => strs [s!"R{i % n}", s!"R{(i + 1) % n}"]))]

/-- `n` standing probe records, each citing the next. -/
def probeRecords (n : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"P{i}", .obj [
    ("cites", strs (if i + 1 < n then [s!"P{i + 1}"] else [])), ("assumptions", strs []),
    ("standing", .bool true)]))

/-- An M `compare` request with `n` standing records whose values and uncertainties carry
`d` digits. -/
def standingCompare (n d : Nat) : Value :=
  let digits (lead : Nat) : Value := .num ⟨((lead * 10 ^ (d - 1) + 7 : Nat) : Int), -((d : Int) - 1)⟩
  let mrec (x : Nat) : Value := .obj [("x", .int x), ("u", .int 1),
    ("unit", .str "m")]
  .obj [("kind", .str "M"), ("original", mrec 10), ("reproduction", mrec 11),
    ("standing", .arr ((List.range n).map fun (i : Nat) =>
      .obj [("x", digits (1 + i % 9)), ("u", digits 1)])), ("k", .int 2)]

/-- `n` revisions, each allocating `per` identifiers. -/
def revisions (n per : Nat) : Value :=
  .arr ((List.range n).map fun (i : Nat) => .obj [("rev", .int (i : Int)),
    ("allocated", strs ((List.range per).map fun j => s!"a{i}_{j}"))])

/-- `n` measurements whose values carry `d` digits. -/
def measurements (n d : Nat) : Value :=
  .arr ((List.range n).map fun i =>
    .obj [("x", .num ⟨((10 ^ (d - 1) + i : Nat) : Int), -((d : Int) - 1)⟩), ("u", .num ⟨((10 ^ (d - 1) : Nat) : Int), -((d : Int) - 1)⟩)])

/-- The specification's root and `n - 1` section pages, each with one block. -/
def specPages (n : Nat) : Value :=
  .arr (.arr [.str "The Principia Machina/TPS", .str "<pre>\nroot\n</pre>"] ::
    (List.range (n - 1)).map fun i =>
      .arr [.str s!"The Principia Machina/TPS/{i / 100 + 1}.{i % 100} Section {i}",
        .str s!"<pre>\nsection {i}\n</pre>"])

/-- A digest of 64 lowercase hexadecimal characters. -/
def hex64a : String := String.ofList (List.replicate 64 'a')

/-- `n` members of the instruction set, of distinct titles. -/
def members (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .arr [.str s!"Member {i}", .str hex64a])

/-- `n` copies of a value, as a list. -/
def valueCopies (n : Nat) (v : Value) : Value := .arr (List.replicate n v)

/-- `n` code points `c`. -/
def chars (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-- A value's canonical JSON as a string: a Provision's text built as a value. -/
def jsonText (v : Value) : Value := .str (v.canonicalJson.getD "")

/-- A Starting Set of `n` empty entries in each of `kinds`. -/
def entriesTpk (kinds : List String) (n : Nat) : Value :=
  .obj (kinds.map fun k => (k, valueCopies n (.obj [])))

/-- The Starting Set's six kinds. -/
def tpkKinds : List String := ["DOF", "CONSTANT", "LAW", "ASSUMPTION", "CONSTRAINT", "BOUNDARY"]

/-- A text that writes one ASSUMPTION `{S}`, and a claim binding `S` to one name of `n` code
points: the PROPOSITION filled holds `n`. -/
def filledRequest (n : Nat) : Value :=
  .obj [("modules", .arr [jsonText (.obj [("ID", .str "FILL"),
      ("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str "{S}")]])])]),
    ("claims", .arr [.obj [("ID", .str "FILL"), ("BIND", .obj [("S", strs [chars n 'n'])])]])]

/-- A `module_check` text that writes one ASSUMPTION `{S}` with one test binding binding `S`
to one name of `n` code points. -/
def filledCheck (n : Nat) : Value :=
  .obj [("text", jsonText (.obj [("ID", .str "FILL"),
      ("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str "{S}")]]),
      ("TEST_BINDINGS", .arr [.obj [("BIND", .obj [("S", strs [chars n 'n'])])]])])),
    ("modules", .arr [])]

/-- A text of `terms` TERMs aimed at `V`, claimed with `V` bound to `names` names. -/
def placedRequest (terms names : Nat) : Value :=
  .obj [("modules", .arr [jsonText (.obj [("ID", .str "TERMS"),
      ("TERMS", valueCopies terms (.obj [("TARGET", .str "V")]))])]),
    ("claims", .arr [.obj [("ID", .str "TERMS"),
      ("BIND", .obj [("V", strs ((List.range names).map fun i => s!"v{i}"))])]])]

/-- The same, `module_check`'s text placing its terms by its own test binding. -/
def placedCheck (terms names : Nat) : Value :=
  .obj [("text", jsonText (.obj [("ID", .str "TERMS"),
      ("TERMS", valueCopies terms (.obj [("TARGET", .str "V")])),
      ("TEST_BINDINGS", .arr [.obj [("BIND", .obj [("V", strs ((List.range names).map fun i => s!"v{i}"))])]])])),
    ("modules", .arr [])]

/-- A `module_verify` request whose base and draft hold 384 entries each, and one text whose
test binding's Starting Set holds `n`. -/
def entriesInAll (n : Nat) : Value :=
  .obj [("base", .obj [("TPK", entriesTpk tpkKinds 64)]), ("draft", .obj [("TPK", entriesTpk tpkKinds 64)]),
    ("modules", .arr [jsonText (.obj [("TEST_BINDINGS", .arr [.obj [("TPK",
      .obj [("DOF", valueCopies (min n 64) (.obj [])), ("CONSTANT", valueCopies (min (n - 64) 64) (.obj [])),
        ("LAW", valueCopies (min (n - 128) 64) (.obj [])), ("ASSUMPTION", valueCopies (n - 192) (.obj []))])]])])])]

/-- A Starting Set with one entry of `kind` whose `field` holds `n` code points. -/
def fieldTpk (kind field : String) (n : Nat) : Value :=
  .obj [("tpk", .obj [(kind, .arr [.obj [(field, .str (chars n 'p'))]])])]

/-- The provision family's bounds, each at its value and one past it. -/
def provisionBounds : List (String × String × String × Value × Bool) := [
  ("lines at 256", "provision", "catalogue_state", .obj [("lines", valueCopies 256 .null)], false),
  ("lines past 256", "provision", "catalogue_state", .obj [("lines", valueCopies 257 .null)], true),
  ("claims at 8", "provision", "module_expand", .obj [("claims", valueCopies 8 .null)], false),
  ("claims past 8", "provision", "module_expand", .obj [("claims", valueCopies 9 .null)], true),
  ("rounds at 64", "provision", "interview_check", .obj [("answer", valueCopies 64 .null)], false),
  ("rounds past 64", "provision", "interview_check", .obj [("answer", valueCopies 65 .null)], true),
  ("carried at 64", "provision", "not_included_lines", .obj [("carried", valueCopies 64 .null)], false),
  ("carried past 64", "provision", "not_included_lines", .obj [("carried", valueCopies 65 .null)], true),
  ("modified at 64", "provision", "interview_check", .obj [("modified", valueCopies 64 .null)], false),
  ("modified past 64", "provision", "interview_check", .obj [("modified", valueCopies 65 .null)], true),
  ("certificates at 1024", "provision", "module_use_view", .obj [("certificates", valueCopies 1024 .null)], false),
  ("certificates past 1024", "provision", "module_use_view", .obj [("certificates", valueCopies 1025 .null)], true),
  ("Provisions used at 4096", "provision", "module_use_view",
    .obj [("certificates", .arr [.obj [("MODULES_USED", valueCopies 4096 .null)]])], false),
  ("Provisions used past 4096", "provision", "module_use_view",
    .obj [("certificates", .arr [.obj [("MODULES_USED", valueCopies 2048 .null)],
      .obj [("MODULES_USED", valueCopies 2049 .null)]])], true),
  ("texts at 8", "provision", "module_verify", .obj [("modules", valueCopies 8 (.str "x"))], false),
  ("texts past 8", "provision", "module_verify", .obj [("modules", valueCopies 9 (.str "x"))], true),
  ("texts at 65536 bytes", "provision", "draft_module_status",
    .obj [("modules", .arr [.str (chars 65536 'a')])], false),
  ("texts past 65536 bytes", "provision", "draft_module_status",
    .obj [("modules", .arr [.str (chars 65537 'a')])], true),
  ("texts with the checked text at 65536 bytes", "provision", "module_check",
    .obj [("text", .str (chars 32768 'a')), ("modules", .arr [.str (chars 32768 'a')])], false),
  ("texts with the checked text past 65536 bytes", "provision", "module_check",
    .obj [("text", .str (chars 32769 'a')), ("modules", .arr [.str (chars 32768 'a')])], true),
  ("a text alone past 65536 bytes, outside the texts' bound", "provision", "module_parse",
    .obj [("text", .str (chars 65537 'a'))], false),
  ("DOF at 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["DOF"] 64)], false),
  ("DOF past 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["DOF"] 65)], true),
  ("BOUNDARY past 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["BOUNDARY"] 65)], true),
  ("a draft's LAW past 64", "provision", "module_expand",
    .obj [("draft", .obj [("TPK", entriesTpk ["LAW"] 65)])], true),
  ("a base's CONSTRAINT past 64", "provision", "draft_module_status",
    .obj [("base", .obj [("TPK", entriesTpk ["CONSTRAINT"] 65)])], true),
  ("a test binding's ASSUMPTION past 64", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("TEST_BINDINGS", .arr [.obj [("TPK", entriesTpk ["ASSUMPTION"] 65)]])]))], true),
  ("entries in all at 1024", "provision", "module_verify", entriesInAll 256, false),
  ("entries in all past 1024", "provision", "module_verify", entriesInAll 257, true),
  ("a REFS at 128", "provision", "module_bind",
    .obj [("tpk", .obj [("LAW", .arr [.obj [("REFS", valueCopies 128 (.str "x"))]])])], false),
  ("a REFS past 128", "provision", "module_bind",
    .obj [("tpk", .obj [("LAW", .arr [.obj [("REFS", valueCopies 129 (.str "x"))]])])], true),
  ("an EQUATION at 16384", "provision", "module_bind", fieldTpk "LAW" "EQUATION" 16384, false),
  ("an EQUATION past 16384", "provision", "module_bind", fieldTpk "LAW" "EQUATION" 16385, true),
  ("a CONDITION at 16384", "provision", "module_bind", fieldTpk "BOUNDARY" "CONDITION" 16384, false),
  ("a CONDITION past 16384", "provision", "module_bind", fieldTpk "BOUNDARY" "CONDITION" 16385, true),
  ("a PROPOSITION at 256", "provision", "module_bind", fieldTpk "ASSUMPTION" "PROPOSITION" 256, false),
  ("a PROPOSITION past 256", "provision", "module_bind", fieldTpk "ASSUMPTION" "PROPOSITION" 257, true),
  ("a PREDICATE at 256", "provision", "module_bind", fieldTpk "BOUNDARY" "PREDICATE" 256, false),
  ("a PREDICATE past 256", "provision", "module_bind", fieldTpk "BOUNDARY" "PREDICATE" 257, true),
  ("a text's PROPOSITION at 256", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str (chars 256 'p'))]])]))], false),
  ("a text's PROPOSITION past 256", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str (chars 257 'p'))]])]))], true),
  ("a text's PREDICATE past 256", "provision", "module_digest",
    .obj [("text", jsonText (.obj [("BOUNDARIES", .arr [.obj [("PREDICATE", .str (chars 257 'p'))]])]))], true),
  ("a PROPOSITION filled to 256", "provision", "module_expand", filledRequest 256, false),
  ("a PROPOSITION filled past 256", "provision", "module_expand", filledRequest 257, true),
  ("a PROPOSITION filled by a test binding to 256", "provision", "module_check", filledCheck 256, false),
  ("a PROPOSITION filled by a test binding past 256", "provision", "module_check", filledCheck 257, true),
  ("placements at 64", "provision", "module_expand", placedRequest 4 16, false),
  ("placements past 64", "provision", "module_expand", placedRequest 5 13, true),
  ("a test binding's placements at 64", "provision", "module_check", placedCheck 4 16, false),
  ("a test binding's placements past 64", "provision", "module_check", placedCheck 5 13, true),
  ("a slot given more names than any slot takes places none", "provision", "module_expand",
    placedRequest 16 17, false),
  ("the interview fills nothing", "provision", "interview_check", filledRequest 257, false)]

/-- The provision family's bounds: a request at a bound is not refused by it, one past it is,
with the bound named. -/
def runProvisionBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for (what, family, fn, request, refused) in provisionBounds do
    let got := respondTo family fn request
    t ← t.check (boundRefusal got == refused)
      s!"{family} {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}: {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair
/-- A `user_evidence` request of `events` events FOR, each of weight 1, and `ages` ages of 0. -/
def evidenceRequest (events ages : Nat) : Value :=
  .obj [("events", .arr ((List.range events).map fun _ =>
      .obj [("kind", .str "AGENT"), ("resolution", .str "FOR"), ("weight", .int 1)])),
    ("ages", .arr ((List.range ages).map fun _ => .int 0)),
    ("g", .obj [("CE-F1", .int 1), ("CE-F2", .int 1)]),
    ("h", .obj [("CE-A1", .int 2), ("CE-A2", .int 3), ("CE-A3", .int 3), ("CE-A4", .int 2),
      ("CE-A5", .int 3)]),
    ("a0", .int 1), ("b0", .int 1), ("half_life", .int 500)]

/-- A `whitewash_count` request of `adm` admissions, `ret` retirements and `st` states, none
of an agent then troubled. -/
def whitewashRequest (adm ret st : Nat) : Value :=
  .obj [("admissions", .arr ((List.range adm).map fun i =>
      .obj [("agent", .str s!"A{i}"), ("time", .int 1000)])),
    ("retirements", .arr ((List.range ret).map fun i =>
      .obj [("agent", .str s!"R{i}"), ("time", .int 1000)])),
    ("states", .obj ((List.range st).map fun i =>
      (s!"R{i}", .obj [("state", .str "GREEN"), ("pending", .int 0)]))),
    ("window", .int 10)]

/-- A `lint` request of a zone of `n` zero-width spaces, one finding each. -/
def hiddenZone (n : Nat) : Value :=
  .obj [("zone_parts", .arr [.arr [.str "\u200b", .int n]]), ("tools", .str "[]"),
    ("cap", .int 1048576)]
/-- `n` letters `m`: one token, no unit symbol. -/
def letters (n : Nat) : String := String.ofList (List.replicate n 'm')

/-- The unit `m` written `n` times, one token each. -/
def metres (n : Nat) : String := " ".intercalate (List.replicate n "m")

/-- A decimal of `n` digits. -/
def digitText (n : Nat) : String := "1" ++ String.ofList (List.replicate (n - 1) '0')

/-- `n` measurements in metres whose values carry `d` digits. -/
def unitMeasurements (n d : Nat) : Value :=
  .arr ((List.range n).map fun i =>
    .obj [("x", .str ("1." ++ String.ofList (List.replicate (d - 2) '0') ++ toString (i % 10))),
      ("u", .str "1"), ("unit", .str "m")])
/-- A Starting Set of the DOF `t` and `d - 1` unknowns, `c` CONSTANTs, `l` laws (law `i`:
`D(x_i, t) = x_(i+1)`, of ROLE EOM(x_i)) and `k` FIXes; `d` at least 2. -/
def eomTfk (d c l k : Nat) : Value :=
  let x (i : Nat) : String := s!"x{i % (d - 1)}"
  .obj [("TPK", .obj [
      ("DOF", .arr (.obj [("NAME", .str "t")] ::
        (List.range (d - 1)).map fun i => .obj [("NAME", .str s!"x{i}")])),
      ("CONSTANT", .arr ((List.range c).map fun i => .obj [("NAME", .str s!"c{i}")])),
      ("LAW", .arr ((List.range l).map fun i => .obj [("NAME", .str s!"L{i}"),
        ("ROLE", .str s!"EOM({x i})"), ("EQUATION", .str s!"D({x i}, t) = {x (i + 1)}")])),
      ("CONSTRAINT", .arr ((List.range k).map fun i => .obj [("NAME", .str s!"C{i}"),
        ("TARGET", .str (x i)), ("ACTION", .str "FIX"), ("VALUE", .str "0")]))]),
    ("TMS", .obj [("PARAMETERS", .obj [])])]

/-- `n` standing records, record `i` of ROLE EOM(x_i) and the form `D(x_i, t) = x_i`, over
`d - 1` unknowns. -/
def eomRecords (n d : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("ID", .str s!"R-{i + 1}"),
    ("STATUS", .str "PROVISIONAL"), ("ROLE", .str s!"EOM(x{i % (d - 1)})"),
    ("EQUATION", .str s!"D(x{i % (d - 1)}, t) = x{i % (d - 1)}")])

/-- A Starting Set of the DOFs `t` and `x0` and one law whose EQUATION's text is `n` code
points, at least 13: `D(x0, t) = x0` and spaces. -/
def eomLongLaw (n : Nat) : Value :=
  .obj [("TPK", .obj [("DOF", .arr [.obj [("NAME", .str "t")], .obj [("NAME", .str "x0")]]),
      ("LAW", .arr [.obj [("NAME", .str "L0"), ("ROLE", .str "EOM(x0)"),
        ("EQUATION", .str ("D(x0, t) = " ++ String.ofList (List.replicate (n - 13) ' ') ++ "x0"))]])]),
    ("TMS", .obj [("PARAMETERS", .obj [])])]

/-- A settlement check over `n` OPEN UNDER gaps, `w` status words and `k` namings. -/
def eomSettlement (n w k : Nat) : Value :=
  .obj [("tfk", eomTfk 3 1 1 0),
    ("records", .arr ((List.range n).map fun i => .obj [("ID", .str s!"G-{i + 1}"),
      ("CLASS", .str "NAMED_GAP"), ("SOURCE", .str "UNDER"), ("STATE", .str "OPEN"),
      ("AGAINST", strs [s!"u{1000 + i}"])])),
    ("words", .obj ((List.range w).map fun i => (s!"G-{i + 1}", .str "NOT GRADED"))),
    ("naming", .arr ((List.range k).map fun i => strs [s!"u{1000 + i}", s!"G-{i + 1}"]))]
/-- A register of `n` standing M RESULT records of `E_x`, the first holding `entries - 1`
assumptions and citing itself, so that the register holds `entries` ASSUMPTIONS and CITES
entries in all. -/
def register (n entries : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj ([("ID", .str s!"R{i}"), ("CLASS", .str "RESULT"),
    ("QUANTITY", .str "E_x"), ("REGIME", .str "M")] ++
    if i == 0 then [("ASSUMPTIONS", strs ((List.range (entries - 1)).map fun j => s!"A{j}")),
      ("CITES", strs ["R0"])] else []))

/-- A register of one RESULT record `R0` with `n` AT points, each of `value` in `unit`. -/
def pointsRegister (n : Nat) (value unit : String) : Value :=
  .arr [.obj [("ID", .str "R0"), ("CLASS", .str "RESULT"), ("AT", .arr ((List.range n).map
    fun i => .obj [("DOF", .str s!"t{i}"), ("VALUE", .str value), ("UNIT", .str unit)]))]]

/-- A `conditions_of` request for `R0`. -/
def conditionsRequest (records : Value) : Value := .obj [("records", records), ("id", .str "R0")]

/-- A `comparison_set` or `sr8_groups` request over `E_x`, an entry of the Research
Assembly's Correspondence Table, with no status word given. -/
def scopeRequest (records : Value) : Value :=
  .obj [("records", records), ("words", .obj []), ("quantity", .str "E_x"),
    ("tfk", .obj [("TrM", .obj [("ENTRIES", .arr [.obj [("NAME", .str "E_x"),
      ("DOF", .str "x")]])]), ("TPK", .obj [])])]

/-- A `landing strike_screen` request over `records`, the batch `R0`. -/
def screenRequest (records : Value) : Value :=
  .obj [("records", records), ("incoming", strs ["R0"]),
    ("tfk", .obj [("TrM", .obj [("ENTRIES", .arr [.obj [("NAME", .str "E_x"),
      ("DOF", .str "x")]])]), ("TPK", .obj [])])]

/-- A unit of `n` metres and a square second: `2n + 2` characters. -/
def longUnit (n : Nat) : String := " ".intercalate (List.replicate n "m") ++ " s2"

def runFamilyBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × String × Value × Bool) := [
    ("DOF at 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 1 0)], false),
    ("DOF past 64", "eom", "eom_map", .obj [("tfk", eomTfk 65 1 1 0)], true),
    ("CONSTANT at 64", "eom", "eom_findings", .obj [("tfk", eomTfk 3 64 1 0)], false),
    ("CONSTANT past 64", "eom", "eom_findings", .obj [("tfk", eomTfk 3 65 1 0)], true),
    ("LAW at 64", "eom", "eom_class", .obj [("tfk", eomTfk 64 1 64 0)], false),
    ("LAW past 64", "eom", "eom_class", .obj [("tfk", eomTfk 64 1 65 0)], true),
    ("CONSTRAINT at 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 2 64)], false),
    ("CONSTRAINT past 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 2 65)], true),
    ("a LAW's EQUATION at 16384 code points", "eom", "eom_map",
      .obj [("tfk", eomLongLaw 16384)], false),
    ("a LAW's EQUATION past 16384 code points", "eom", "eom_map",
      .obj [("tfk", eomLongLaw 16385)], true),
    ("register records at 64", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 64 1 64 0), ("records", eomRecords 64 64)], false),
    ("register records past 64", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 64 1 64 0), ("records", eomRecords 65 64)], true),
    ("a record's EQUATION past 16384 code points", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 3 1 1 0), ("records", .arr [.obj [("ID", .str "R-1"),
        ("STATUS", .str "PROVISIONAL"), ("ROLE", .str "EOM(x0)"),
        ("EQUATION", .str (String.ofList (List.replicate 16385 ' ')))]])], true),
    ("settlement records, words and namings at 64", "eom", "settlement_check",
      eomSettlement 64 64 64, false),
    ("settlement records past 64", "eom", "settlement_check", eomSettlement 65 1 1, true),
    ("settlement words past 64", "eom", "settlement_check", eomSettlement 1 65 1, true),
    ("settlement namings past 64", "eom", "settlement_check", eomSettlement 1 1 65, true),
    ("probe records at 400", "probe", "load", .obj [("records", probeRecords 400), ("r", .str "P1")], false),
    ("probe records past 400", "probe", "load", .obj [("records", probeRecords 401), ("r", .str "P1")], true),
    ("probe revisions at 4000", "probe", "historical_view",
      .obj [("revisions", revisions 4000 1), ("target", .str "a0_0")], false),
    ("probe revisions past 4000", "probe", "historical_view",
      .obj [("revisions", revisions 4001 0), ("target", .str "a0_0")], true),
    ("probe allocated at 4000", "probe", "historical_view",
      .obj [("revisions", revisions 2 2000), ("target", .str "a0_0")], false),
    ("probe allocated past 4000", "probe", "historical_view",
      .obj [("revisions", revisions 2 2001), ("target", .str "a0_0")], true),
    ("probe standing at 100", "probe", "compare", standingCompare 100 30, false),
    ("probe standing past 100", "probe", "compare", standingCompare 101 1, true),
    ("probe standing digits past 30", "probe", "compare", standingCompare 1 31, true),
    ("rows at 1000", "cluster", "cluster", .obj [("rows", clusterRows 1000)], false),
    ("rows past 1000", "cluster", "cluster", .obj [("rows", clusterRows 1001)], true),
    ("paired at 5000", "cluster", "cluster",
      .obj [("rows", clusterRows 3), ("paired", .arr ((List.range 5000).map fun _ => .null))], false),
    ("paired past 5000", "cluster", "cluster",
      .obj [("rows", clusterRows 3), ("paired", .arr ((List.range 5001).map fun _ => .null))], true),
    ("ses at 1000", "cluster", "resolving_step",
      .obj [("spacing", .int 1), ("ses", .arr ((List.range 1000).map fun _ => .int 1))], false),
    ("ses past 1000", "cluster", "resolving_step",
      .obj [("spacing", .int 1), ("ses", .arr ((List.range 1001).map fun _ => .int 1))], true),
    ("records at 2000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 2000 1)], false),
    ("records past 2000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 2001 1)], true),
    ("record entries at 20000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 1000 19)], false),
    ("record entries past 20000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 1000 20)], true),
    ("register records at 2000", "strike", "conditions_of", conditionsRequest (register 2000 1), false),
    ("register records past 2000", "strike", "conditions_of", conditionsRequest (register 2001 1), true),
    ("register entries at 5000", "strike", "conditions_of", conditionsRequest (register 2 5000), false),
    ("register entries past 5000", "strike", "conditions_of", conditionsRequest (register 2 5001), true),
    ("scope records at 200", "strike", "comparison_set", scopeRequest (register 200 1), false),
    ("scope records past 200", "strike", "comparison_set", scopeRequest (register 201 1), true),
    ("scope records past 200, the groups", "strike", "sr8_groups", scopeRequest (register 201 1), true),
    ("scope entries at 500", "strike", "sr8_groups", scopeRequest (register 2 500), false),
    ("scope entries past 500", "strike", "sr8_groups", scopeRequest (register 2 501), true),
    ("scope entries past 500, the pairs", "strike", "comparison_set", scopeRequest (register 2 501), true),
    ("screen records at 225", "landing", "strike_screen", screenRequest (register 225 1), false),
    ("screen records past 225", "landing", "strike_screen", screenRequest (register 226 1), true),
    ("screen entries at 1500", "landing", "strike_screen", screenRequest (register 2 1500), false),
    ("screen entries past 1500", "landing", "strike_screen", screenRequest (register 2 1501), true),
    ("screen AT points past 1000", "landing", "strike_screen", screenRequest (.arr [.obj [("ID", .str "R0"), ("CLASS", .str "RESULT"),
      ("QUANTITY", .str "E_x"), ("AT", .arr ((List.range 1001).map fun i =>
        .obj [("DOF", .str s!"t{i}"), ("VALUE", .str "1.5"), ("UNIT", .str "m")]))]]), true),
    ("screen records past 225, no QUANTITY reached", "landing", "strike_screen",
      .obj [("records", .arr ((List.range 226).map fun i => .obj [("ID", .str s!"R{i}")])),
        ("incoming", strs ["R0"]), ("tfk", .obj [])], false),
    ("AT points at 1000", "strike", "conditions_of", conditionsRequest (pointsRegister 1000 "1.5" "m"), false),
    ("AT points past 1000", "strike", "conditions_of", conditionsRequest (pointsRegister 1001 "1.5" "m"), true),
    ("AT points past 1000, the pairs", "strike", "comparison_set", scopeRequest (pointsRegister 1001 "1.5" "m"), true),
    ("AT VALUE at 64 characters", "strike", "conditions_of",
      conditionsRequest (pointsRegister 1 ("1." ++ String.ofList (List.replicate 62 '2')) "m"), false),
    ("AT VALUE past 64 characters", "strike", "conditions_of",
      conditionsRequest (pointsRegister 1 ("1." ++ String.ofList (List.replicate 63 '2')) "m"), true),
    ("AT UNIT at 64 characters", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1" (longUnit 31)), false),
    ("AT UNIT past 64 characters", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1" (longUnit 31 ++ "0")), true),
    ("AT value at 2048 bits", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1e-616" "m"), false),
    ("AT value past 2048 bits", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1e-617" "m"), true),
    ("AT value past 2048 bits, the groups", "strike", "sr8_groups", scopeRequest (pointsRegister 1 "1e-617" "m"), true),
    ("SR6 identifiers at 128", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 16).map fun i =>
        strs ((List.range 8).map fun j => s!"p{i}_{j}")))], false),
    ("SR6 identifiers past 128", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 16).map (fun i =>
        strs ((List.range 8).map fun j => s!"p{i}_{j}")) ++ [strs ["q"]]))], true),
    ("SR6 sets at 1000", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 1000).map fun _ => strs [])),
            ("same_model", .arr ((List.range 1000).map fun _ => .bool true))], false),
    ("SR6 sets past 1000", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 1001).map fun _ => strs [])),
            ("same_model", .arr ((List.range 1001).map fun _ => .bool true))], true),
    ("SR8 measurements at 100", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 100 3)], false),
    ("SR8 measurements past 100", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 101 3)], true),
    ("SR8 digits at 30", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 2 30)], false),
    ("SR8 digits past 30", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 2 31)], true),
    ("suite records at 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 1 0)], false),
    ("suite records past 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 51 1 0)], true),
    ("suite contradictions past 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 10 1 51)], true),
    ("suite entries at 500", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 9 0)], false),
    ("suite entries past 500", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 10 0)], true),
    ("pages at 1000", "digest", "digest_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1000)], false),
    ("pages past 1000", "digest", "digest_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1001)], true),
    ("pages past 1000, the list", "digest", "specification_pages",
      .obj [("pages", specPages 1001)], true),
    ("pages past 1000, the preimage", "digest", "preimage_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1001)], true),
    ("members at 1000", "digest", "digest_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1000)],
      false),
    ("members past 1000", "digest", "digest_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1001)],
      true),
    ("members past 1000, the preimage", "digest", "preimage_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1001)],
      true),
    ("findings' text at 1048576 characters", "lint", "lint", hiddenZone 19993, false),
    ("findings' text past 1048576 characters", "lint", "lint", hiddenZone 19994, true),
    ("the counts of findings past it", "lint", "counts", hiddenZone 19994, false),
    ("events at 50", "sponsor", "user_evidence", evidenceRequest 50 50, false),
    ("events past 50", "sponsor", "user_evidence", evidenceRequest 51 51, true),
    ("ages past 50", "sponsor", "user_evidence", evidenceRequest 50 51, true),
    ("agents at 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4000 4000, false),
    ("admissions past 4000", "sponsor", "whitewash_count", whitewashRequest 4001 4000 4000, true),
    ("retirements past 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4001 4000, true),
    ("states past 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4000 4001, true),
    ("a unit of 1024 characters", "units", "unit_parse", .obj [("u", .str (letters 1024))], false),
    ("a unit past 1024 characters", "units", "unit_parse", .obj [("u", .str (letters 1025))], true),
    ("a unit of 128 tokens", "units", "unit_scale", .obj [("u", .str (metres 128))], false),
    ("a unit past 128 tokens", "units", "unit_scale", .obj [("u", .str (metres 129))], true),
    ("a dimension past 1024 characters", "units", "unit_matches",
      .obj [("u", .str "m"), ("dimension", .str (letters 1025))], true),
    ("a value of 4096 characters", "units", "normalize_measurement",
      .obj [("value", .str (digitText 4096)), ("uncertainty", .str "0"), ("u", .str "m")], false),
    ("a value past 4096 characters", "units", "normalize_measurement",
      .obj [("value", .str (digitText 4097)), ("uncertainty", .str "0"), ("u", .str "m")], true),
    ("x_m past 4096 characters", "units", "lm_contradicts_units",
      .obj [("x_l", .str "1"), ("unit_l", .str "m"), ("x_m", .str (digitText 4097)),
        ("u_m", .str "1"), ("unit_m", .str "m"), ("k", .int 2)], true),
    ("SR8 units, measurements at 100", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 100 30)], false),
    ("SR8 units, measurements past 100", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 101 1)], true),
    ("SR8 units, digits past 30", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 2 31)], true)]
  for (what, family, fn, request, refused) in cases do
    let got := respondTo family fn request
    t ← t.check (boundRefusal got == refused)
      s!"{family} {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The bound on an exact value, where a unit's scale meets it: held in lowest terms, the
  -- scale is refused exactly when its numerator or denominator passes 65,536 bits.
  let tooLarge : List (String × String × Value × Bool) := [
    ("a scale whose denominator has 65,536 bits", "unit_scale",
      .obj [("u", .str "arcsec9286 Qrad1635 hrad")], false),
    ("a scale whose denominator has 65,537 bits", "unit_scale",
      .obj [("u", .str "arcsec9286 Qrad1635 darad")], true),
    ("a value in a unit whose scale has 65,537 bits", "normalize_measurement",
      .obj [("value", .str "1"), ("uncertainty", .str "0"), ("u", .str "arcsec9286 Qrad1635 darad")],
      true),
    ("SR3 over a scale of 32,748 bits, squared", "mm_contradicts_units",
      .obj [("x1", .str "1"), ("u1", .str "1"), ("unit1", .str "arcsec4662 Qrad826"),
        ("x2", .str "2"), ("u2", .str "1"), ("unit2", .str "arcsec4662 Qrad826"), ("k", .int 2)],
      false),
    ("SR3 over a scale of 32,780 bits, squared", "mm_contradicts_units",
      .obj [("x1", .str "1"), ("u1", .str "1"), ("unit1", .str "arcsec4667 Qrad827"),
        ("x2", .str "2"), ("u2", .str "1"), ("unit2", .str "arcsec4667 Qrad827"), ("k", .int 2)],
      true)]
  for (what, fn, request, refused) in tooLarge do
    let got := respondTo "units" fn request
    let isTooLarge := match got with
      | .error r => r.code == .badArgument && r.detail == Principia.ValueBound.tooLarge
      | .ok _ => false
    t ← t.check (isTooLarge == refused && (refused || got.toOption.isSome))
      s!"units {fn}, {what}: refused as too large {isTooLarge}, expected {refused}"
  return t.pair

/-! ## The derivation family: the structured checker's corpora through `pcalc derivation`

Every record of `vectors/structured_credit.json` given to `derivation credit_record` as a
RESULT holding its DERIVATION in the wire form, and each STRUCTURED one also to
`derivation credit` as a payload, on the case's `sources` or on sources holding its `laws`:
a LAW of the Starting Set for each law, and for each ASSUMPTION record one of the register
that the record's ASSUMPTIONS name. The answer is the case's verdict and class as wire
words; a KERNEL derivation is refused `OWED`. Every case of `vectors/structured_wire.json`
given to `derivation credit` as the value its text reads to: a payload the reader refuses is
`BAD_ARGUMENT`, its detail ending with the reader's word; one it reads is credited as the
case's `credit` says, or (without one) answered. Then the family's bounds, at each and one
past it. -/

/-- A corpus of the Calculator's own reading. -/
def derivCorpus (path : System.FilePath) : IO Value := do
  match readString (← IO.FS.readFile path) with
  | .ok v => pure v
  | .error f => throw (IO.userError s!"{path}: refused {repr f}")

/-- A member the case needs. -/
def derivNeed (v : Value) (k : String) : IO Value :=
  match member v k with
  | some x => pure x
  | none => throw (IO.userError s!"derivation: no member {k}")

/-- A runner-shaped step in the wire form: its EQUATION, its citation, its SITE (empty when
the case gives none) and FORWARD (false for `"dir": "bwd"`). -/
def derivWireStep (j : Value) : IO Value := do
  let eq ← memberStr j "equation"
  let cite ← match member j "law", member j "assumption", member j "identity" with
    | some (.str n), _, _ => pure ("LAW", Value.str n)
    | _, some (.str r), _ => pure ("ASSUMPTION", Value.str r)
    | _, _, some (.str n) => pure ("IDENTITY", Value.str n)
    | _, _, _ => throw (IO.userError "derivation: a step cites nothing")
  let site := match member j "site" with
    | some (.str s) => s
    | _ => ""
  let fwd := match member j "dir" with
    | some (.str "bwd") => false
    | _ => true
  pure (.obj [("EQUATION", .str eq), cite, ("SITE", .str site), ("FORWARD", .bool fwd)])

/-- A runner-shaped list of steps in the wire form. -/
def derivWireSteps (v : Value) : IO Value := do
  match v with
  | .arr xs => pure (.arr (← xs.mapM derivWireStep))
  | _ => throw (IO.userError "derivation: the steps are not a list")

/-- A runner-shaped start as the payload's START member; none for the left side. -/
def derivWireStart (j : Value) : IO (List (String × Value)) := do
  match member j "start" with
  | none => pure []
  | some s =>
    match member s "law", member s "assumption", member s "refl" with
    | some (.str n), _, _ => pure [("START", .obj [("LAW", .str n)])]
    | _, some (.str r), _ => pure [("START", .obj [("ASSUMPTION", .str r)])]
    | _, _, some (.str e) => pure [("START", .obj [("EXPRESSION", .str e)])]
    | _, _, _ => throw (IO.userError "derivation: not a start")

/-- A runner-shaped derivation in the wire form of the DERIVATION sum. -/
def derivWire (j : Value) : IO Value := do
  match member j "structured", member j "prose", member j "kernelProof" with
  | some s, _, _ => pure (.obj ((← derivWireStart j) ++ [("STEPS", ← derivWireSteps s)]))
  | _, some p, _ =>
    let n ← match member p "steps" with
      | some (.int n) => pure n
      | _ => throw (IO.userError "derivation: PROSE without a step count")
    let att ← match member p "attachment" with
      | some a => pure [("ATTACHMENT", .obj [("STEPS", ← derivWireSteps a)])]
      | none => pure []
    pure (.obj ([("STEPS", .int n), ("TEXT", .str (← memberStr p "text"))] ++ att))
  | _, _, some (.str p) => pure (.obj [("PROOF", .str p)])
  | _, _, _ => throw (IO.userError "derivation: not a derivation")

/-- A case's sources, `(starting_set, register, assumptions)`: its `sources` as written, or
its `laws` as LAWs of the Starting Set and ASSUMPTION records the ASSUMPTIONS name. -/
def derivSources (c : Value) : IO (Value × Value × Value) := do
  match member c "sources", member c "laws" with
  | some s, _ =>
    pure ((member s "startingSet").getD (.obj []), (member s "register").getD (.arr []),
      (member s "assumptions").getD (.arr []))
  | _, some (.arr ls) =>
    let mut laws : List Value := []
    let mut records : List Value := []
    let mut ids : List Value := []
    for l in ls do
      let name ← memberStr l "name"
      let eq ← memberStr l "equation"
      if (← memberStr l "cite") == "law" then
        laws := laws ++ [.obj [("NAME", .str name), ("EQUATION", .str eq)]]
      else
        records := records ++ [.obj [("ID", .str name), ("CLASS", .str "ASSUMPTION"),
          ("EQUATION", .str eq)]]
        ids := ids ++ [.str name]
    pure (.obj [("LAW", .arr laws)], .arr records, .arr ids)
  | _, _ => throw (IO.userError "derivation: a case has neither laws nor sources")

/-- The answer a case expects: its verdict and class as wire words. -/
def derivExpected (expect : Value) (cls : String) : IO Value := do
  let c := ("CLASS", Value.str cls)
  match ← memberStr expect "verdict" with
  | "accepted" => pure (.obj [c, ("VERDICT", .str "ACCEPTED")])
  | "notStructured" => pure (.obj [c, ("VERDICT", .str "NOT_STRUCTURED")])
  | v =>
    let i ← match member expect "step" with
      | some (.int i) => pure i
      | _ => throw (IO.userError "derivation: a verdict without its step")
    let word := if v == "refused" then "REFUSED" else "UNREADABLE"
    pure (.obj [c, ("STEP", .int i), ("VERDICT", .str word), ("WHY", .str (← memberStr expect "why"))])

/-- An answer's canonical JSON, or the refusal's code and detail. -/
def derivShow (r : Except Refusal Value) : String :=
  match r with
  | .ok v => (v.canonicalJson.getD "?")
  | .error f => s!"refused {f.code.word}: {f.detail}"

/-- A `credit` request. -/
def derivCreditRequest (payload : Value) (eq : String) (sources : Value × Value × Value) :
    Value :=
  let (ss, reg, asm) := sources
  .obj [("derivation", payload), ("equation", .str eq), ("assumptions", asm),
    ("starting_set", ss), ("register", reg)]

def runDerivationCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let credit ← derivCorpus "vectors/structured_credit.json"
  let .arr records ← derivNeed credit "records" | throw (IO.userError "derivation: no records")
  for c in records do
    let id ← memberStr c "id"
    let eq ← memberStr c "equation"
    let sources@(ss, reg, asm) ← derivSources c
    let dj ← derivNeed c "derivation"
    let dv ← derivWire dj
    let want := (← derivExpected (← derivNeed c "expect") (← memberStr c "class")).canonicalJson
    let record : Value := .obj [("ASSUMPTIONS", asm), ("CLASS", .str "RESULT"),
      ("DERIVATION", dv), ("EQUATION", .str eq)]
    let gotR := respondTo "derivation" "credit_record"
      (.obj [("record", record), ("starting_set", ss), ("register", reg)])
    let okR := if (member dj "kernelProof").isSome then
        match gotR with
        | .error r => r.code == .owed && r.detail == Derivation.kernelOwed
        | .ok _ => false
      else gotR.toOption.bind (·.canonicalJson) == want
    let gotC := if (member dj "structured").isSome then
        some (respondTo "derivation" "credit" (derivCreditRequest dv eq sources))
      else none
    let okC := match gotC with
      | some g => g.toOption.bind (·.canonicalJson) == want
      | none => true
    t ← t.check (okR && okC)
      s!"derivation {id}: credit_record {derivShow gotR}, credit {(gotC.map derivShow).getD "-"}, expected {repr want}"
  let wire ← derivCorpus "vectors/structured_wire.json"
  let .arr cases ← derivNeed wire "cases" | throw (IO.userError "derivation: no cases")
  for c in cases do
    let id ← memberStr c "id"
    let payload ← match readString (← memberStr c "text") with
      | .ok v => pure v
      | .error f => throw (IO.userError s!"derivation {id}: the text does not read: {repr f}")
    match member c "refused" with
    | some (.str w) =>
      let got := respondTo "derivation" "credit"
        (derivCreditRequest payload "F = m * a" (.obj [], .arr [], .arr []))
      let ok := match got with
        | .error r => r.code == .badArgument &&
            r.detail == s!"the derivation is not a STRUCTURED payload: {w}"
        | .ok _ => false
      t ← t.check ok s!"derivation {id}: {derivShow got}, expected BAD_ARGUMENT {w}"
    | _ =>
      match member c "credit" with
      | some k =>
        let got := respondTo "derivation" "credit"
          (derivCreditRequest payload (← memberStr k "equation") (← derivSources k))
        let want := (← derivExpected (← derivNeed k "expect") (← memberStr k "class")).canonicalJson
        t ← t.check (got.toOption.bind (·.canonicalJson) == want)
          s!"derivation {id}: {derivShow got}, expected {repr want}"
      | none =>
        let got := respondTo "derivation" "credit"
          (derivCreditRequest payload "F = m * a" (.obj [], .arr [], .arr []))
        t ← t.check got.toOption.isSome s!"derivation {id}: {derivShow got}, expected an answer"
  return t.pair

/-- `n` steps from `a + b = a + b`, each commuting the right side, back to it when `n` is
even. -/
def derivCommuting (n : Nat) : Value :=
  .obj [("START", .obj [("EXPRESSION", .str "a + b")]),
    ("STEPS", .arr ((List.range n).map fun i =>
      .obj [("EQUATION", .str (if i % 2 == 0 then "a + b = b + a" else "a + b = a + b")),
        ("IDENTITY", .str "addComm"), ("SITE", .str "rhs"), ("FORWARD", .bool true)]))]

/-- An EQUATION's text of `n` code points: `x = x` and spaces. -/
def derivLongEquation (n : Nat) : String := "x = x" ++ chars (n - 5) ' '

/-- `n` ASSUMPTION records of the register, `A-1` to `A-n`. -/
def derivRegister (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("ID", .str s!"A-{i + 1}"),
    ("CLASS", .str "ASSUMPTION"), ("EQUATION", .str "q = 0")])

/-- `n` identifiers `A-1` to `A-n`. -/
def derivIds (n : Nat) : Value := strs ((List.range n).map fun i => s!"A-{i + 1}")

def runDerivationBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let none3 : Value × Value × Value := (.obj [], .arr [], .arr [])
  let credit (payload : Value) (eq : String) (s : Value × Value × Value) : Value :=
    derivCreditRequest payload eq s
  let plain := derivCommuting 2
  let lawSet (eq : String) : Value := .obj [("LAW", .arr [.obj [("NAME", .str "n"), ("EQUATION", .str eq)]])]
  let record (d : Value) : Value := .obj [("record", .obj [("EQUATION", .str "a + b = a + b"),
    ("DERIVATION", d)]), ("starting_set", .obj []), ("register", .arr [])]
  -- (what, function, request, past the bound)
  let cases : List (String × String × Value × Bool) := [
    ("steps at 1024", "credit", credit (derivCommuting 1024) "a + b = a + b" none3, false),
    ("steps past 1024", "credit", credit (derivCommuting 1025) "a + b = a + b" none3, true),
    ("a record's steps past 1024", "credit_record", record (derivCommuting 1025), true),
    ("the EQUATION at 16384 code points", "credit", credit plain (derivLongEquation 16384) none3, false),
    ("the EQUATION past 16384 code points", "credit", credit plain (derivLongEquation 16385) none3, true),
    ("a step's EQUATION past 16384 code points", "credit",
      credit (.obj [("STEPS", .arr [.obj [("EQUATION", .str (derivLongEquation 16385)),
        ("IDENTITY", .str "addComm"), ("SITE", .str "rhs"), ("FORWARD", .bool true)]])])
        "x = x" none3, true),
    ("a LAW's EQUATION at 16384 code points", "credit",
      credit plain "a + b = a + b" (lawSet (derivLongEquation 16384), .arr [], .arr []), false),
    ("a LAW's EQUATION past 16384 code points", "credit",
      credit plain "a + b = a + b" (lawSet (derivLongEquation 16385), .arr [], .arr []), true),
    ("a Starting Set kind at 64", "credit",
      credit plain "a + b = a + b" (.obj [("DOF", valueCopies 64 (.obj []))], .arr [], .arr []), false),
    ("a Starting Set kind past 64", "credit",
      credit plain "a + b = a + b" (.obj [("DOF", valueCopies 65 (.obj []))], .arr [], .arr []), true),
    ("the register at 1024 records", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 1024, derivIds 1), false),
    ("the register past 1024 records", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 1025, derivIds 1), true),
    ("ASSUMPTIONS at 512", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 512, derivIds 512), false),
    ("ASSUMPTIONS past 512", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 513, derivIds 513), true),
    ("ASSUMPTIONS past 512, the law table", "laws",
      .obj [("assumptions", derivIds 513), ("starting_set", .obj []), ("register", .arr [])], true)]
  for (what, fn, request, past) in cases do
    let got := respondTo "derivation" fn request
    let ok := if past then boundRefusal got else got.toOption.isSome
    t ← t.check ok s!"derivation {fn}, {what}: {derivShow got}"
  return t.pair

/-! ## The falcons through `pcalc falcon` -/

/-- v1's names of the falcon functions in `falcon_corpus.json` and `falcon_hand.json`
(`run_case`), and the Calculator's: v1's names of the functions themselves. -/
def falconFunctions : List (String × String) :=
  [("canon", "falcon_canon"), ("draw", "falcon_draw"), ("hop", "source_hop"),
   ("qcheck", "quote_check"), ("qmatch", "falcon_quote_match"),
   ("reconcile", "falcon_reconcile"), ("schema_canon", "falcon_schema_canon"),
   ("schema_digest", "falcon_schema_digest"), ("source", "source_match"),
   ("stage", "sponsor_stage"), ("stop", "falcon_stop")]

/-- `falcon_corpus.json` (949 cases) and `falcon_hand.json`: every case's `args` through
`falcon <function>`, each giving v1's text, or v1's word as a refusal's detail; a case of the
corpus that `falcon_corpus.owed.json` lists is answered `OWED` (it lists none). -/
def runFalconCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← (← arr (← field (← readJson "vectors/falcon_corpus.owed.json") "owed")).mapM
    (str · "name")
  for path in ["vectors/falcon_corpus.json", "vectors/falcon_hand.json"] do
    for c in ← v1Cases path do
      let name ← memberStr c "name"
      let expected ← memberStr c "expected"
      let some fn := falconFunctions.lookup (← memberStr c "fn")
        | throw (IO.userError s!"{path} {name}: unknown function")
      let some args := member c "args" | throw (IO.userError s!"{path} {name}: no args")
      let got := respondTo "falcon" fn args
      let ok := if path == "vectors/falcon_corpus.json" && owed.contains name then
          match got with
          | .error r => r.code == .owed
          | .ok _ => false
        else
          match got with
          | .ok (.str text) => text == expected
          | .error r => r.code == .badArgument && "ERROR:" ++ r.detail == expected
          | _ => false
      t ← t.check ok s!"falcon {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `n` copies of a character. -/
def copies (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-- A text field's spec. -/
def textSpec : Value :=
  .obj [("name", .str "a"), ("type", .str "text"), ("class", .str "MECHANICAL")]

/-- A `falcon_canon` request of a text value, its strings holding `n` characters in all. -/
def canonOfTexts (n : Nat) : Value :=
  let base := Falcon.textChars (.obj [("value", .str ""), ("spec", textSpec)])
  .obj [("value", .str (copies (n - base) 'a')), ("spec", textSpec)]

/-- A draw's candidate. -/
def falconCandidate (i : Nat) : Value :=
  .obj [("account", .str s!"a{i}"), ("sponsor", .str s!"s{i}"), ("family", .str "f"),
    ("snapshot", .str "x"), ("tier", .bool false), ("good_standing", .bool true),
    ("sandbox", .bool false), ("over_cap", .bool false), ("window", .int 0),
    ("ontime", .int 0), ("assigned", .int 0)]

/-- A draw of two from `m` candidates, `kept` of them kept and `prior` other accounts. -/
def falconDraw (m kept prior : Nat) : Value :=
  .obj [("candidates", .arr ((List.range m).map falconCandidate)), ("n", .int 2),
    ("state", .obj [("kept", strs ((List.range kept).map fun i => s!"a{i}")),
      ("prior", strs ((List.range prior).map fun i => s!"p{i}")), ("drafted", .int 0),
      ("now", .int 0), ("falcon_wait", .int 1)]),
    ("r", .str "0123456789abcdef0123456789abcdef")]

/-- A text field, MECHANICAL. -/
def textField (name : String) : Value :=
  .obj [("name", .str name), ("type", .str "text"), ("class", .str "MECHANICAL")]

/-- A schema of the fields given. -/
def falconSchema (fields : List Value) : Value :=
  .obj [("class", .str "SURVEY"), ("narrow", .bool false), ("fields", .arr fields)]

/-- A schema of one rows field `r`, keyed by its column `k`, with the other columns
named. -/
def rowsSchema (columns : List String) : Value :=
  falconSchema [.obj [("name", .str "r"), ("type", .str "rows"), ("class", .str "MECHANICAL"),
    ("key", strs ["k"]), ("columns", .arr (textField "k" :: columns.map textField))]]

/-- An enum field of `n` values. -/
def enumField (name : String) (n : Nat) : Value :=
  .obj [("name", .str name), ("type", .str "enum"), ("class", .str "MECHANICAL"),
    ("values", strs ((List.range n).map fun i => s!"v{i}"))]

/-- `n` outputs of a one-text-field schema `f`. -/
def flatOutputs (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("account", .str s!"a{i}"),
    ("status", .str "RETURNED"), ("result", .obj [("f", .str "x")])])

/-- A reconciliation of `n` outputs and `q` quotes entries over the schema of one text
field `f`. -/
def flatReconcile (n q : Nat) : Value :=
  .obj [("outputs", flatOutputs n), ("quotes", .arr ((List.range q).map fun _ => .obj [])),
    ("schema", falconSchema [textField "f"])]

/-- A reconciliation of two outputs over `rowsSchema ["c"]`, each holding `rows` rows of
distinct keys, and `outcomes` quote outcomes in each quotes entry. -/
def rowsReconcile (rows outcomes : Nat) : Value :=
  let out (o : Nat) : Value := .obj [("account", .str s!"a{o}"), ("status", .str "RETURNED"),
    ("result", .obj [("r", .arr ((List.range rows).map fun i =>
      .obj [("k", .str s!"{i}"), ("c", .str "x")]))])]
  .obj [("outputs", .arr [out 0, out 1]),
    ("quotes", .arr ((List.range 2).map fun _ =>
      .obj ((List.range outcomes).map fun i => (s!"q{i}", .str "PASS")))),
    ("schema", rowsSchema ["c"])]

/-- Two outputs of one row each, keyed by 3354 characters, over 99 columns whose votes
split: the item lines' identifiers and values hold 999,900 characters and `extra` more,
the first column's second value holding them. -/
def itemsReconcile (extra : Nat) : Value :=
  let names := (List.range 99).map fun j => s!"c{j / 10}{j % 10}"
  let out (o : Nat) : Value := .obj [("account", .str s!"a{o}"), ("status", .str "RETURNED"),
    ("result", .obj [("r", .arr [.obj (("k", .str (copies 3354 'k')) ::
      names.map fun c => (c, .str (if o == 1 && c == "c00" then "1" ++ copies extra 'x'
        else toString o)))])])]
  .obj [("outputs", .arr [out 0, out 1]), ("quotes", .arr [.obj [], .obj []]),
    ("schema", rowsSchema names)]

/-- A source list of `marks` CODE HOST marks holding `templates` templates in all, then
`entries` EXACT entries. -/
def falconSources (marks templates entries : Nat) : Value :=
  .arr ((List.range marks).map (fun i => .arr (.str "CODE HOST" :: .str s!"h{i}.org" ::
      if i == 0 then (List.range templates).map fun j => .str s!"/o{j}/*/" else [])) ++
    (List.range entries).map fun i => .arr [.str "EXACT", .str s!"https://a.org/{i}"])

/-- `n` events of a sponsor's stage. -/
def stageEvents (n : Nat) : Value :=
  .obj [("events", .arr ((List.range n).map fun i =>
      .arr [.str "LANDED", .int ((i * 86400 : Nat) : Int), .str "a"])),
    ("as_of", .int 253402300799),
    ("thresholds", .obj [("blocks", .int 1000000), ("dates", .int 1), ("span_days", .int 0),
      ("dormant_days", .int 1)])]

/-- `n` records of a stop: falcons issued and finished in turn. -/
def stopCounts (n : Nat) : Value :=
  .obj [("counts", .arr ((List.range n).map fun i =>
      if i % 2 == 0 then .arr [.str "ISSUED", .str s!"f{i / 2}"]
      else .arr [.str "FINISHED", .str s!"f{i / 2}", .int 1, .int 0, .int 0])),
    ("limits", .obj [("breaker", .str "1"), ("window", .int 1000)])]

/-- The falcons' bounds, each at the bound and one past it, and the item lines' count of the
case built at that bound. -/
def runFalconBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let ones (n : Nat) : Value := .str (copies n '1')
  let quoteMatch (v q : Nat) : Value := .obj [("value", ones v), ("quote", ones q)]
  let quoteCheck (p q v : Nat) : Value := .obj [("page", ones p), ("quote", ones q), ("value", ones v)]
  let maxS := Falcon.maxSearch
  let fieldsOf (n : Nat) : List Value := (List.range n).map fun i => textField s!"f{i}"
  let columnsOf (n : Nat) : List String := (List.range n).map fun i => s!"c{i}"
  let cases : List (String × String × Value × Bool) := [
    ("strings at 200,000 characters", "falcon_canon", canonOfTexts Falcon.maxTexts, false),
    ("strings past 200,000 characters", "falcon_canon", canonOfTexts (Falcon.maxTexts + 1), true),
    ("a value sought at the search bound", "falcon_quote_match", quoteMatch 20 (maxS / 20), false),
    ("a value sought past the search bound", "falcon_quote_match", quoteMatch 20 (maxS / 20 + 1), true),
    ("a quote sought in a page at the search bound", "quote_check", quoteCheck (maxS / 20) 20 1, false),
    ("a quote sought in a page past the search bound", "quote_check", quoteCheck (maxS / 20 + 1) 20 1, true),
    ("a value sought in a quote at the search bound", "quote_check", quoteCheck 1000 1000 (maxS / 1000), false),
    ("a value sought in a quote past the search bound", "quote_check", quoteCheck 1000 1000 (maxS / 1000 + 1), true),
    ("candidates at 100", "falcon_draw", falconDraw 100 0 0, false),
    ("candidates past 100", "falcon_draw", falconDraw 101 0 0, true),
    ("kept accounts at 100", "falcon_draw", falconDraw 100 100 0, false),
    ("kept accounts past 100", "falcon_draw", falconDraw 100 101 0, true),
    ("prior assignees at 1000", "falcon_draw", falconDraw 100 0 1000, false),
    ("prior assignees past 1000", "falcon_draw", falconDraw 100 0 1001, true),
    ("fields at 100", "falcon_schema_canon", .obj [("schema", falconSchema (fieldsOf 100))], false),
    ("fields past 100", "falcon_schema_digest", .obj [("schema", falconSchema (fieldsOf 101))], true),
    ("columns at 100", "falcon_schema_canon", .obj [("schema", rowsSchema (columnsOf 99))], false),
    ("columns past 100", "falcon_schema_canon", .obj [("schema", rowsSchema (columnsOf 100))], true),
    ("enum values at 1000", "falcon_schema_canon",
      .obj [("schema", falconSchema [enumField "e" 600, enumField "g" 400])], false),
    ("enum values past 1000", "falcon_schema_canon",
      .obj [("schema", falconSchema [enumField "e" 600, enumField "g" 401])], true),
    ("a spec's enum values past 1000", "falcon_canon",
      .obj [("value", .str "v0"), ("spec", enumField "e" 1001)], true),
    ("a schema's string at 100 characters", "falcon_schema_canon",
      .obj [("schema", falconSchema [textField (copies 100 'f')])], false),
    ("a schema's string past 100 characters", "falcon_reconcile",
      .obj [("outputs", flatOutputs 2), ("quotes", .arr [.obj [], .obj []]),
        ("schema", falconSchema [textField (copies 101 'f')])], true),
    ("outputs at 10", "falcon_reconcile", flatReconcile 10 10, false),
    ("outputs past 10", "falcon_reconcile", flatReconcile 11 11, true),
    ("quotes entries past 10", "falcon_reconcile", flatReconcile 10 11, true),
    ("rows at 1000", "falcon_reconcile", rowsReconcile 500 0, false),
    ("rows past 1000", "falcon_reconcile", rowsReconcile 501 0, true),
    ("quote outcomes at 1000", "falcon_reconcile", rowsReconcile 2 500, false),
    ("quote outcomes past 1000", "falcon_reconcile", rowsReconcile 2 501, true),
    ("item lines at 1,000,000 characters", "falcon_reconcile", itemsReconcile 100, false),
    ("item lines past 1,000,000 characters", "falcon_reconcile", itemsReconcile 101, true),
    ("events at 10,000", "sponsor_stage", stageEvents 10000, false),
    ("events past 10,000", "sponsor_stage", stageEvents 10001, true),
    ("count records at 10,000", "falcon_stop", stopCounts 10000, false),
    ("count records past 10,000", "falcon_stop", stopCounts 10001, true),
    ("source entries at 1000", "source_match",
      .obj [("cited", .str "https://a.org/1"), ("sources", falconSources 1 0 999)], false),
    ("source entries past 1000", "source_match",
      .obj [("cited", .str "https://a.org/1"), ("sources", falconSources 1 0 1000)], true),
    ("templates at 1000", "source_hop",
      .obj [("hop", .str "https://a.org/1"), ("matched", .int 1),
        ("sources", falconSources 2 1000 1)], false),
    ("templates past 1000", "source_hop",
      .obj [("hop", .str "https://a.org/1"), ("matched", .int 1),
        ("sources", falconSources 2 1001 1)], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "falcon" fn request
    t ← t.check (boundRefusal got == refused)
      s!"falcon {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The item lines' case is built at the bound exactly, and answered there.
  let atBound := match itemsReconcile 100 with
    | .obj [("outputs", o), ("quotes", q), ("schema", s)] =>
      match Principia.Falcon.Reconcile.falconReconcile o q s with
      | .ok d => Falcon.itemChars d
      | .error _ => 0
    | _ => 0
  t ← t.check (atBound == Falcon.maxItemText)
    s!"falcon_reconcile: the item lines' case holds {atBound} characters, not {Falcon.maxItemText}"
  return t.pair

/-! ## The score family: v1's corpora and its bounds -/

/-- v1's names of the score functions in `score_corpus.json` (`run_case`), and the
Calculator's. -/
def scoreFunctions : List (String × String) :=
  [("activity", "peer_activity"), ("aggregate", "user_aggregate"), ("cut", "violation_cut"),
   ("effective", "override_effective"), ("evidence", "evidence"), ("gate", "tier_gate_release"),
   ("inherit", "inherit"), ("inquire", "inquire"), ("interval", "score_interval"),
   ("level", "pending_level"), ("mark", "override_mark"), ("override", "override_check"),
   ("pad", "pad_check"), ("pad_weight", "pad_weight"), ("prime", "prime_select"),
   ("quota", "diversity_quota"), ("rank", "rank"), ("sponsor_cut", "sponsor_cut"),
   ("standing", "standing"), ("state", "state_step"), ("trip", "trip"),
   ("update", "score_update"), ("user_evidence", "user_score_evidence")]

/-- v1's names of the Beta layer's functions in `beta_corpus.json`, and the Calculator's. -/
def betaFunctions : List (String × String) :=
  [("betainc", "betainc"), ("betainc_inv", "betainc_inv"), ("canon", "canon"),
   ("interval", "beta_interval"), ("lgamma", "lgamma"), ("mean", "beta_mean")]

/-- A case's answer through `score <fn>`, as v1's `run_case` text: the text, `ERROR:` and
v1's word, or `none` when it is refused otherwise (`OWED` among them). -/
def scoreText (fn : String) (args : Value) : Option String :=
  match respondTo "score" fn args with
  | .ok (.str text) => some text
  | .error r => if r.code == .badArgument then some ("ERROR:" ++ r.detail) else none
  | _ => none

/-- `score_corpus.json` and `beta_corpus.json`: every case's `args` through
`score <function>`, each giving v1's text, or v1's word as a refusal's detail. A case of
`score_corpus.owed.json` must be answered `OWED`, and no other; a case of
`beta_corpus.divergences.json` gives the Calculator's recorded text where v1's differs, and
each recorded divergence must still be one. -/
def runScoreCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← (← arr (← field (← readJson "vectors/score_corpus.owed.json") "owed")).mapM
    fun o => str o "name"
  for c in ← v1Cases "vectors/score_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := scoreFunctions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let ok := if owed.contains name then
        match respondTo "score" fn args with
        | .error r => r.code == .owed
        | .ok _ => false
      else scoreText fn args == some expected
    t ← t.check ok s!"score {fn} {name}: expected {repr expected}, got {repr (scoreText fn args)}"
  let divs ← (← arr (← field (← readJson "vectors/beta_corpus.divergences.json") "divergences")).mapM
    fun o => do pure ((← str o "name"), (← str o "v1"), (← str o "v2"))
  let mut diverged : List String := []
  for c in ← v1Cases "vectors/beta_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := betaFunctions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := scoreText fn args
    let ok ← match divs.find? (·.1 == name) with
      | some (_, v1, v2) =>
        if v1 == expected && got == some v2 then
          diverged := diverged ++ [name]
          pure true
        else pure false
      | none => pure (got == some expected)
    t ← t.check ok s!"score {fn} {name}: expected {repr expected}, got {repr got}"
  for (name, _, _) in divs do
    t ← t.check (diverged.contains name) s!"score {name}: listed as a divergence but not one"
  return t.pair

/-- A decimal `m × 10^e`. -/
def dec (m e : Int) : Value := .num ⟨m, e⟩

/-- `n` events of `evidence`, their ages giving `terms` distinct powers of 2 under a
HALF-LIFE of 500, FOR and AGAINST in turn. -/
def evidenceEvents (n terms : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("kind", .str (if i % 2 == 0 then "FOR" else "AGAINST")),
    ("weight", .int 1), ("age", .int ((i % terms : Nat) : Int))])

/-- The parameters `evidence` reads. -/
def evidenceParams : Value :=
  .obj [("a0", .int 1), ("b0", .int 1), ("HALF-LIFE", .int 500), ("T_idle", .int 90)]

/-- One agent holding `n` AGAINST events. -/
def agentWith (n : Nat) : Value :=
  .arr [.obj [("account", .str "a"), ("certified", .bool true), ("removed", .bool false),
    ("events", valueCopies n (.obj [("kind", .str "AGAINST"), ("base", .int 1), ("age", .int 0),
      ("counterpart", .null), ("counterpart_sponsor", .null)]))]]

/-- An account of RANK. -/
def account : Value :=
  .obj [("account", .str "a"), ("S", dec 5 (-1)), ("S_lo", dec 4 (-1)), ("S_hi", dec 6 (-1)),
    ("n", .int 0), ("active", .bool true)]

/-- An override's facts, `n` entries in each list. -/
def factsOf (n : Nat) : Value :=
  .obj [("certified", valueCopies n (.str hex64a)), ("suspended", .arr []),
    ("nonces", valueCopies n (.str "0123456789abcdef0123456789abcdef")), ("prime", .null)]

/-- The score family's bounds, at each and one past it: a request at a bound is not refused
by it (it may be answered, or refused by v1's checks), one past it is, with the bound
named. Built here, too long for a line of `pcalc.json`. -/
def runScoreBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let quota (n : Nat) : Value := .obj [("window", valueCopies n (.obj [("counterpart", .null),
    ("weight", .int 1)])), ("counterpart", .str "c"), ("g", .int 1), ("c_max", dec 25 (-2))]
  let cases : List (String × String × Value × Bool) := [
    ("window at 10000", "diversity_quota", quota 10000, false),
    ("window past 10000", "diversity_quota", quota 10001, true),
    ("accounts at 2000", "rank", .obj [("accounts", valueCopies 2000 account)], false),
    ("accounts past 2000", "rank", .obj [("accounts", valueCopies 2001 account)], true),
    ("accounts past 2000, the Prime", "prime_select",
      .obj [("accounts", valueCopies 2001 account), ("override", .null)], true),
    ("items at 5000", "pending_level", .obj [("items", valueCopies 5000 .null), ("now", .int 0)], false),
    ("items past 5000", "pending_level", .obj [("items", valueCopies 5001 .null), ("now", .int 0)], true),
    ("activity at 5000", "peer_activity", .obj [("events", valueCopies 5000 .null)], false),
    ("activity past 5000", "peer_activity", .obj [("events", valueCopies 5001 .null)], true),
    ("prior ages at 100000", "trip", .obj [("S", dec 9 (-1)), ("in_tier", .bool true),
      ("prior_ages", valueCopies 100000 (.int 1))], false),
    ("prior ages past 100000", "trip", .obj [("S", dec 9 (-1)), ("in_tier", .bool true),
      ("prior_ages", valueCopies 100001 (.int 1))], true),
    ("facts at 10000", "override_check", .obj [("decl", .null), ("facts", factsOf 10000)], false),
    ("facts past 10000", "override_check", .obj [("decl", .null), ("facts", factsOf 10001)], true),
    ("facts past 10000, the pad", "pad_check",
      .obj [("decl", .null), ("facts", factsOf 10001)], true),
    ("events at 10000", "evidence", .obj [("events", valueCopies 10000 .null),
      ("idle", .obj [("days", .int 0)])], false),
    ("events past 10000", "evidence", .obj [("events", valueCopies 10001 .null),
      ("idle", .obj [("days", .int 0)])], true),
    ("powers of 2 past 64", "evidence", .obj [("events", evidenceEvents 65 65),
      ("idle", .obj [("days", .int 0)]), ("params", evidenceParams)], true),
    ("agents at 1000", "user_aggregate", .obj [("agents", valueCopies 1000 .null),
      ("sponsor", .str "s")], false),
    ("agents past 1000", "user_aggregate", .obj [("agents", valueCopies 1001 .null),
      ("sponsor", .str "s")], true),
    ("pooled events at 30", "user_aggregate", .obj [("agents", agentWith 30),
      ("sponsor", .str "s")], false),
    ("pooled events past 30", "user_aggregate", .obj [("agents", agentWith 31),
      ("sponsor", .str "s")], true),
    ("pooled events past 30, the user evidence", "user_score_evidence",
      .obj [("agents", agentWith 31), ("conduct", .arr []), ("sponsor", .str "s")], true),
    ("conduct at 10000", "user_score_evidence", .obj [("agents", agentWith 1),
      ("conduct", valueCopies 10000 .null), ("sponsor", .str "s")], false),
    ("conduct past 10000", "user_score_evidence", .obj [("agents", agentWith 1),
      ("conduct", valueCopies 10001 .null), ("sponsor", .str "s")], true),
    ("shape at 0.1", "betainc_inv",
      .obj [("a", dec 1 (-1)), ("b", .int 1), ("p", dec 5 (-1))], false),
    ("shape below 0.1", "betainc_inv",
      .obj [("a", dec 9 (-2)), ("b", .int 1), ("p", dec 5 (-1))], true),
    ("shape at 10000", "betainc", .obj [("a", .int 10000), ("b", .int 10000), ("x", dec 5 (-1))], false),
    ("shape past 10000", "betainc", .obj [("a", .int 1), ("b", .int 10001), ("x", dec 5 (-1))], true),
    ("shape past 10000, the interval", "beta_interval",
      .obj [("a", .int 10001), ("b", .int 1), ("level", dec 95 (-2))], true),
    ("tail at 0.000001", "betainc_inv", .obj [("a", .int 1), ("b", .int 1), ("p", dec 1 (-6))], false),
    ("tail below 0.000001", "betainc_inv", .obj [("a", .int 1), ("b", .int 1), ("p", dec 9 (-7))], true),
    ("upper tail at 0.000001", "betainc_inv",
      .obj [("a", .int 1), ("b", .int 1), ("p", dec 999999 (-6))], false),
    ("upper tail below 0.000001", "betainc_inv",
      .obj [("a", .int 1), ("b", .int 1), ("p", dec 9999991 (-7))], true),
    ("level at 0.999998", "beta_interval",
      .obj [("a", .int 1), ("b", .int 1), ("level", dec 999998 (-6))], false),
    ("level past 0.999998", "beta_interval",
      .obj [("a", .int 1), ("b", .int 1), ("level", dec 9999981 (-7))], true),
    ("x of 4096 bits", "betainc", .obj [("a", .int 1), ("b", .int 1), ("x", dec 1 (-1233))], false),
    ("x of more than 4096 bits", "betainc",
      .obj [("a", .int 1), ("b", .int 1), ("x", dec 1 (-1234))], true),
    ("a coefficient of more than 4096 bits", "evidence",
      .obj [("events", .arr [.obj [("kind", .str "FOR"), ("weight", .int 1), ("age", .int 5000)]]),
        ("idle", .obj [("days", .int 0)]), ("params", .obj [("a0", .int 1), ("b0", .int 1),
          ("HALF-LIFE", .int 1), ("T_idle", .int 90)])], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "score" fn request
    t ← t.check (boundRefusal got == refused)
      s!"score {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The bound on powers of 2, at 64: checked on the sums themselves, the request at it being
  -- slow to answer in full.
  let sums (n : Nat) : Principia.Score.PowSum :=
    ⟨(List.range n).map fun (i : Nat) => (((i : Int) : Rat) / 500, 1)⟩
  let atTerms := Principia.Calculator.Score.termsWithin "F and A" (sums 40) (sums 24)
  t ← t.check (atTerms matches .ok ()) "score evidence: 64 powers of 2 refused"
  let pastTerms := Principia.Calculator.Score.termsWithin "F and A" (sums 40) (sums 25)
  t ← t.check (boundRefusal (pastTerms.map fun _ => Value.null)) "score evidence: 65 powers of 2 not refused"
  return t.pair

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

/-- A string of `n` code points. -/
def codePoints (n : Nat) : String := String.ofList (List.replicate n 'a')

/-- Strings of `total` code points in all, at most `maxText` each. -/
def textsOf (total : Nat) : List Value :=
  let full := total / Record.maxText
  let rest := total % Record.maxText
  ((List.range full).map fun _ => .str (codePoints Record.maxText)) ++
    (if rest = 0 then [] else [.str (codePoints rest)])

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
      .obj [("dst_records", recordRegister 65 0), ("dst_words", .obj []), ("tfk", tfk)], .bound),
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

/-! ## pcalc.json: the dispatch -/

def runPcalc : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/pcalc.json") do
    let what := (← field c "args").compress
    let args ← (← arr (← field c "args")).mapM fun a => IO.ofExcept a.getStr?
    -- An answer too long for a line (the permissions table) is given by the file
    -- that records its digest, `stdout_sha256_file` (custos/permits.sha256), read here at test
    -- time: the SHA-256 of the answer's text equals the file's line. A change to the Lean that
    -- moves the table turns this case red, and its fix changes `custos/**`, the paths of the
    -- check that compares custos/permits.json with the built binary byte for byte.
    let digestFile := (c.getObjValAs? String "stdout_sha256_file").toOption
    let digest ← match digestFile with
      | some path => do
          let line := ((← IO.FS.readFile path).replace "\r" "").trimAsciiEnd.toString
          pure (some line)
      | none => pure none
    let stdout ← match digest with
      | some _ => pure ""
      | none => str c "stdout"
    let exit ← IO.ofExcept (c.getObjValAs? Nat "exit")
    let got := match args with
      | [family, function] => fun bytes => answer family function bytes
      | _ => fun _ => usage
    let (out, code) := got (← input c "stdin" "stdin_hex")
    let same := match digest with
      | some d => Principia.Sha256.digestText out == d
      | none => out == stdout
    t ← t.check (same && code.toNat == exit)
      s!"pcalc {what}: expected {repr (digest.getD stdout)} exit {exit}, got {repr (if digest.isSome then Principia.Sha256.digestText out else out)} exit {code}"
  return t.pair

/-- Every function of every family of `Calculator.families` has at least one pair in
`pcalc.json`, whatever its answer: a function without one fails, naming the family and the
function. The line it prints on success counts the families, so a family added to the list is
counted without this check changing. -/
def runPcalcCoverage : IO (Nat × Nat) := do
  let mut pairs : List (String × String) := []
  for c in ← arr (← readJson "vectors/pcalc.json") do
    let args ← (← arr (← field c "args")).mapM fun a => IO.ofExcept a.getStr?
    match args with
    | [family, function] => pairs := (family, function) :: pairs
    | _ => pure ()
  let mut t : Counts := {}
  for (family, calls) in families do
    for (function, _) in calls do
      t ← t.check (pairs.contains (family, function))
        s!"pcalc.json: no pair for {family} {function}"
  if t.fail == 0 then
    IO.println s!"pcalc.json: every function of the {families.length} families has a pair"
  return t.pair

/-! ## The governor, the permissions, SHA-256 and Unicode through `pcalc`

The families `governor`, `permissions`, `sha256` and `unicode`, each corpus's cases given to
the family's functions through `Calculator.respondTo`, and their bounds at and past each
bound through `Calculator.answer`, the slowest accepted request of each family timed. -/

/-- A wire word as a value. -/
def wordValue {α : Type} [WireWord α] (a : α) : Value := .str (WireWord.toWire a)

/-- The member `k` of an object, which the case needs. -/
def need (v : Value) (k : String) : IO Value :=
  match member v k with
  | some x => pure x
  | none => throw (IO.userError s!"no member {k} in {repr (v.canonicalJson)}")

/-- An object with the member `k` set to `x`, in place or added. -/
def withMember (v : Value) (k : String) (x : Value) : Value :=
  match v with
  | .obj ms => if ms.any (·.1 == k) then .obj (ms.map fun m => if m.1 == k then (k, x) else m)
    else .obj (ms ++ [(k, x)])
  | _ => v

/-- An answer's canonical JSON; `none` for a refusal. -/
def canonOf (r : Except Refusal Value) : Option String :=
  match r with
  | .ok v => v.canonicalJson
  | .error _ => none

/-- A refusal's code, `none` for an answer. -/
def refusalOf (r : Except Refusal Value) : Option RefusalCode :=
  match r with
  | .ok _ => none
  | .error f => some f.code

/-- A governed request's kind from `governor.json`'s Lean name. -/
def governorKind (name : String) : IO Principia.Parameters.GovernedRequest :=
  match Tests.Governor.allKinds.find? (Tests.Governor.kindName · == name) with
  | some k => pure k
  | none => throw (IO.userError s!"governor: unknown kind {name}")

/-- `governor.json`'s Lean names of the admission's words, by member, and their wire words. -/
def governorWords : List (String × String × Value) := [
  ("decision", "admitted", wordValue Principia.Governor.DecisionWord.admitted),
  ("decision", "refused", wordValue Principia.Governor.DecisionWord.refused),
  ("refusal", "switch", wordValue Principia.Governor.RefusalWord.switch),
  ("refusal", "rate", wordValue Principia.Governor.RefusalWord.rate),
  ("refusal", "slots", wordValue Principia.Governor.RefusalWord.slots),
  ("reason", "agentStop", wordValue Principia.Governor.Switch.agentStop),
  ("reason", "suspended", wordValue Principia.Governor.Switch.suspended),
  ("payer", "sponsor", wordValue Principia.Governor.Payer.sponsor),
  ("payer", "agent", wordValue Principia.Governor.Payer.agent),
  ("cap", "agent", wordValue Principia.Governor.SlotCap.agent),
  ("cap", "sponsor", wordValue Principia.Governor.SlotCap.sponsor),
  ("cap", "pool", wordValue Principia.Governor.SlotCap.pool),
  ("cap", "anonymous", wordValue Principia.Governor.SlotCap.anonymous),
  ("decision", "cachedOnly", wordValue Principia.Governor.DecisionWord.cachedOnly),
  ("refusal", "pressure", wordValue Principia.Governor.RefusalWord.pressure),
  ("level", "clear", wordValue Principia.Parameters.PressureLevel.clear),
  ("level", "busy", wordValue Principia.Parameters.PressureLevel.busy),
  ("level", "strained", wordValue Principia.Parameters.PressureLevel.strained),
  ("level", "overloaded", wordValue Principia.Parameters.PressureLevel.overloaded),
  ("refusal", "traffic", wordValue Principia.Governor.RefusalWord.traffic),
  ("reason", "contained", wordValue Principia.Governor.Switch.contained),
  ("stage", "normal", wordValue Principia.Governor.TrafficStage.normal),
  ("stage", "throttled", wordValue Principia.Governor.TrafficStage.throttled),
  ("stage", "penalized", wordValue Principia.Governor.TrafficStage.penalized),
  ("stage", "contained", wordValue Principia.Governor.TrafficStage.contained)]

/-- An expectation of `governor.json` with its Lean names given as wire words. -/
def governorExpectation (e : Value) : IO Value := do
  match e with
  | .obj ms =>
    let ms ← ms.mapM fun (k, x) => do
      match x with
      | .str s =>
        if governorWords.any (·.1 == k) then
          match governorWords.find? (fun w => w.1 == k && w.2.1 == s) with
          | some w => pure (k, w.2.2)
          | none => throw (IO.userError s!"governor: unknown {k} {s}")
        else pure (k, x)
      | _ => pure (k, x)
    pure (.obj ms)
  | _ => throw (IO.userError "governor: an expectation is not an object")

/-- `governor.json`: every case through `governor`, its Lean names given as wire words.
An `admit` case is one check of both calls: `admit`'s answer is the expectation and
`charge`'s its member `charge`. Every seat cost is a number: a falcon RETURN's rows round up
(inventory U4, the Declarer's choice), so a `null` expectation is a defect of the corpus. A
`level` case goes through `pressure_level`,
its expectation the answer. -/
def runGovernorCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases ← match readString (← IO.FS.readFile "vectors/governor.json") with
    | .ok (.arr cs) => pure cs
    | _ => throw (IO.userError "governor.json: not a list of cases")
  for c in cases do
    let fn ← memberStr c "function"
    let name := match member c "name" with
      | some (.str s) => s
      | _ => s!"{fn} {repr ((member c "kind").bind (·.canonicalJson))}"
    let call (f : String) (args : List (String × Value)) := respondTo "governor" f (.obj args)
    match fn with
    | "lane" =>
      let k ← governorKind (← memberStr c "kind")
      let n ← match member c "expected" with
        | some (.int n) => pure n.toNat
        | _ => throw (IO.userError s!"governor {name}: no lane number")
      let some lane := (WireWord.members : List Principia.Parameters.Lane).find? (·.number == n)
        | throw (IO.userError s!"governor {name}: no lane {n}")
      let want := (Value.obj [("lane", wordValue lane), ("number", .int n)]).canonicalJson
      let got := canonOf (call "lane" [("kind", wordValue k)])
      t ← t.check (want.isSome && got == want) s!"governor {name}: expected {repr want}, got {repr got}"
    | "seat_cost" =>
      let k ← governorKind (← memberStr c "kind")
      let table := match member c "seat_table" with
        | some st => [("seat_table", st)]
        | none => []
      let got := call "seat_cost"
        ([("kind", wordValue k), ("records", ← need c "records"), ("rows", ← need c "rows")] ++ table)
      match ← need c "expected" with
      | .null => t ← t.check false s!"governor {name}: a seat cost expected null"
      | e =>
        t ← t.check (canonOf got == e.canonicalJson) s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "jitter" =>
      let share := match member c "share" with
        | some sh => [("share", sh)]
        | none => []
      let got := call "jitter" ([("base", ← need c "base"), ("draw", ← need c "draw")] ++ share)
      let e ← need c "expected"
      t ← t.check (canonOf got == e.canonicalJson) s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "admit" =>
      let rq ← need c "request"
      let rq := withMember rq "kind" (wordValue (← governorKind (← memberStr rq "kind")))
      let args := [("state", ← need c "state"), ("request", rq)]
      let want ← governorExpectation (← need c "expected")
      let wantCharge := (← need want "charge").canonicalJson
      let got := canonOf (call "admit" args)
      let gotCharge := canonOf (call "charge" args)
      t ← t.check (want.canonicalJson.isSome && got == want.canonicalJson && gotCharge == wantCharge)
        s!"governor {name}: expected {repr want.canonicalJson}, got {repr got}, charge {repr gotCharge}"
    | "level" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let got := call "pressure_level" ([("use", ← need c "use"), ("prev", ← need c "prev"),
        ("external_until", ← need c "external_until"), ("now", ← need c "now")] ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "traffic_step" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let which ← match member c "event", member c "end" with
        | some e, none => pure [("event", e)]
        | none, some q =>
          pure [("end", withMember q "kind" (wordValue (← governorKind (← memberStr q "kind"))))]
        | _, _ => throw (IO.userError s!"governor {name}: one of event and end")
      let got := call "traffic_step" ([("traffic", ← need c "traffic"), ("now", ← need c "now")] ++
        which ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "traffic_stage" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let got := call "traffic_stage" ([("traffic", ← need c "traffic"), ("now", ← need c "now"),
        ("kind", wordValue (← governorKind (← memberStr c "kind")))] ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | f => throw (IO.userError s!"governor: unknown function {f}")
  IO.println s!"pcalc governor: {cases.length} cases of governor.json"
  return t.pair

/-- A `permits` request of the family. -/
def permitsRequest (asker pageClass op : String) (context : List String) : Value :=
  .obj [("asker", .str asker), ("class", .str pageClass), ("op", .str op),
    ("context", .arr (context.map .str))]

/-- A case's context, an object of `permissions.json`, as the word arm's context words. -/
def contextWordsOf (j : Json) : IO (List String) := do
  match j.getObjVal? "context" with
  | .error _ => pure []
  | .ok ctx =>
    let some kvs := (match ctx with | .obj kvs => some kvs | _ => none)
      | throw (IO.userError "permissions: a context is not an object")
    let mut out : List String := []
    for (k, _) in kvs.toArray do
      match k, ctx.getObjValD k with
      | "policy", .str w => out := out ++ [w]
      | "listed", .bool b => if b then out := out ++ ["LISTED"]
      | "named", .str w => out := out ++ ["NAMED", w]
      | "queue_head", .bool b => if b then out := out ++ ["QUEUE HEAD"]
      | "reauthenticated", .bool b => if b then out := out ++ ["REAUTHENTICATED"]
      | _, _ => throw (IO.userError s!"permissions: a context member {k} that does not read")
    pure out

/-- The request a word of an enumeration of `permissions.json` is given in: an asker's,
a page class's, an operation's, a policy's or a DOSSIER READ's place. -/
def wordRequest (enum w : String) : Option Value :=
  match enum with
  | "Actor" | "Role" | "LockState" | "AccountClass" => some (permitsRequest w "SPECIFICATION" "READ" [])
  | "PageClass" => some (permitsRequest "PUBLIC" w "READ" [])
  | "Op" => some (permitsRequest "PUBLIC" "SPECIFICATION" w [])
  | "AccessPolicy" => some (permitsRequest "PUBLIC" "SPECIFICATION" "READ" [w])
  | "DossierRead" => some (permitsRequest "PUBLIC" "SPECIFICATION" "READ" ["NAMED", w])
  | _ => none

/-- The answer `permits` gives for a verdict. -/
def verdictWord (b : Bool) : Option String :=
  (Value.str (if b then "PERMITTED" else "REFUSED")).canonicalJson

/-- `permissions.json`: every case through `permissions`. A cell is one check per operation;
a word must read exactly when the corpus says so, in its place in a `permits` request; an
enumeration's members are the domain's lists for the asker, the page class and the operation,
and each reads in its place for the others; a request of the word arm is the same words in a
`permits` request, refused `BAD_ARGUMENT` where the word arm reads none. The cases not
given to the family are `AccountClass`'s members (`USER` is the class of an account that asks
in a role, and no asker's word) and the `group` cases (a role's MediaWiki group is the wiki's
name for it, no word of a request). Then the domain's 96 contexts read as 96 distinct contexts,
every one Custos can know. -/
def runPermissionsCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases ← arr (← readJson "vectors/permissions.json")
  let call := respondTo "permissions" "permits"
  let domain ← match respondTo "permissions" "domain" (.obj []) with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"permissions domain: refused {r.detail}")
  let listOf (k : String) : List String := match member domain k with
    | some (.arr xs) => xs.filterMap fun | .str s => some s | _ => none
    | _ => []
  let mut given := 0
  for c in cases do
    let fn ← str c "function"
    match fn with
    | "wire" =>
      let e ← str c "enum"
      match c.getObjValAs? (Array String) "members" with
      | .ok ms =>
        let ms := ms.toList
        match e with
        | "Actor" => t ← t.check (listOf "askers" == ms) s!"permissions domain askers: {listOf "askers"}"
        | "PageClass" => t ← t.check (listOf "classes" == ms) s!"permissions domain classes: {listOf "classes"}"
        | "Op" => t ← t.check (listOf "ops" == ms) s!"permissions domain ops: {listOf "ops"}"
        | "AccountClass" => continue
        | _ =>
          let ok := ms.all fun w => match wordRequest e w with
            | some r => (call r).toOption.isSome
            | none => false
          t ← t.check ok s!"permissions {e} members {ms}: a member does not read in its place"
        given := given + 1
      | .error _ =>
        let w ← str c "word"
        let reads ← IO.ofExcept (c.getObjValAs? Bool "reads")
        let some r := wordRequest e w | throw (IO.userError s!"permissions: unknown enumeration {e}")
        let got := call r
        t ← t.check ((got.toOption.isSome == reads) && (reads || refusalOf got == some .badArgument))
          s!"permissions {e} {repr w}: expected reads {reads}, got {repr (canonOf got)}"
        given := given + 1
    | "permits" =>
      let a ← str c "actor"
      let k ← str c "class"
      let ctx ← contextWordsOf c
      match c.getObjValAs? (Array String) "permitted" with
      | .ok listed =>
        for op in (WireWord.members : List Principia.Permissions.Op) do
          let o := WireWord.toWire op
          let got := canonOf (call (permitsRequest a k o ctx))
          t ← t.check (got == verdictWord (listed.contains o))
            s!"permissions {a} on {k} {o} in {ctx}: got {repr got}"
      | .error _ =>
        let o ← str c "op"
        let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
        let got := canonOf (call (permitsRequest a k o ctx))
        t ← t.check (got == verdictWord want) s!"permissions {a} on {k} {o} in {ctx}: got {repr got}"
      given := given + 1
    | "request" =>
      let args := (← IO.ofExcept (c.getObjValAs? (Array String) "args")).toList
      let named : List (String × Value) :=
        (["asker", "class", "op"].zip args).map fun (k, w) => (k, Value.str w)
      let context : List (String × Value) :=
        if args.length < 3 then [] else [("context", .arr ((args.drop 3).map .str))]
      let r := Value.obj (named ++ context)
      let got := call r
      match c.getObjVal? "request" with
      | .ok .null =>
        t ← t.check (refusalOf got == some .badArgument)
          s!"permissions request {args}: expected BAD_ARGUMENT, got {repr (canonOf got)}"
      | _ =>
        let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
        t ← t.check (canonOf got == verdictWord want) s!"permissions request {args}: got {repr (canonOf got)}"
      given := given + 1
    | "group" => continue
    | f => throw (IO.userError s!"permissions: unknown function {f}")
  -- The domain's contexts: 96, distinct, every context Custos can know.
  let contexts : List (List String) := match member domain "contexts" with
    | some (.arr xs) => xs.map fun
      | .arr ws => ws.filterMap fun | .str s => some s | _ => none
      | _ => []
    | _ => []
  let read := contexts.filterMap (Principia.Permissions.readContext · {})
  let mut every : List Principia.Permissions.PageContext := []
  for policy in [none, some Principia.Permissions.AccessPolicy.openAccess,
      some Principia.Permissions.AccessPolicy.closedAccess] do
    for listed in [false, true] do
      for named in [none, some Principia.Parameters.DossierRead.userOnly,
          some Principia.Parameters.DossierRead.userAndAgent,
          some Principia.Parameters.DossierRead.neither] do
        for head in [false, true] do
          for reauth in [false, true] do
            let ctx : Principia.Permissions.PageContext :=
              { policy := policy, onAccessList := listed, namedAccount := named,
                atQueueHead := head, reauthenticated := reauth }
            every := ctx :: every
  t ← t.check (contexts.length == 96 && read.length == 96 && read.eraseDups.length == 96 &&
      every.all read.contains)
    s!"permissions domain: {contexts.length} contexts, {read.length} read, {read.eraseDups.length} distinct"
  -- The table (`table {}`): its contexts the domain's; every cell of
  -- permissions.json's `permits` cases read from it; and a sample of 2,000 of its 207,360
  -- cells against `permits`, spread over the whole table by a stride coprime with its size.
  let table ← match respondTo "permissions" "table" (.obj []) with
    | .ok v => pure v
    | .error r => throw (IO.userError s!"permissions table: refused {r.detail}")
  let tableContexts : List (List String) := match member table "contexts" with
    | some (.arr xs) => xs.map fun
      | .arr ws => ws.filterMap fun | .str s => some s | _ => none
      | _ => []
    | _ => []
  t ← t.check (tableContexts == contexts) "permissions table: its contexts are not the domain's"
  let tableCells := (member table "cells").getD .null
  let readTable := tableContexts.map (Principia.Permissions.readContext · {})
  let cellAt (a k o : String) (ix : Nat) : Option String := do
    let byClass ← member tableCells a
    let byOp ← member byClass k
    match ← member byOp o with
    | .arr vs => match vs[ix]? with
      | some (.str w) => some w
      | _ => none
    | _ => none
  let cellOf (a k o : String) (ws : List String) : Option String := do
    let ctx ← Principia.Permissions.readContext ws {}
    let ix ← readTable.findIdx? (· == some ctx)
    cellAt a k o ix
  let word (b : Bool) : String := if b then "PERMITTED" else "REFUSED"
  let mut tableCases := 0
  for c in cases do
    if (← str c "function") != "permits" then continue
    let a ← str c "actor"
    let k ← str c "class"
    let ctx ← contextWordsOf c
    match c.getObjValAs? (Array String) "permitted" with
    | .ok listed =>
      for op in (WireWord.members : List Principia.Permissions.Op) do
        let o := WireWord.toWire op
        t ← t.check (cellOf a k o ctx == some (word (listed.contains o)))
          s!"permissions table: {a} on {k} {o} in {ctx}: got {repr (cellOf a k o ctx)}"
    | .error _ =>
      let o ← str c "op"
      let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
      t ← t.check (cellOf a k o ctx == some (word want))
        s!"permissions table: {a} on {k} {o} in {ctx}: got {repr (cellOf a k o ctx)}"
    tableCases := tableCases + 1
  let askers := listOf "askers"
  let classes := listOf "classes"
  let ops := listOf "ops"
  let size := askers.length * classes.length * ops.length * contexts.length
  t ← t.check (size == 207360) s!"permissions table: {size} cells, not 207,360"
  for n in List.range 2000 do
    let i := (n * 9221) % size
    let ix := i % contexts.length
    let io := (i / contexts.length) % ops.length
    let ic := (i / (contexts.length * ops.length)) % classes.length
    let ia := i / (contexts.length * ops.length * classes.length)
    match askers[ia]?, classes[ic]?, ops[io]?, contexts[ix]? with
    | some a, some k, some o, some ws =>
      let want := (call (permitsRequest a k o ws)).toOption
      t ← t.check (want.isSome && (cellAt a k o ix).map Value.str == want)
        s!"permissions table: cell {i} ({a} on {k} {o} in {ws}): got {repr (cellAt a k o ix)}"
    | _, _, _, _ => t ← t.check false s!"permissions table: cell {i} out of the domain"
  IO.println s!"pcalc permissions: {given} of {cases.length} cases of permissions.json through the family (AccountClass's members and the groups aside), and the domain's 96 contexts; the table: {tableCases} cases of permissions.json and 2000 of its {size} cells against permits"
  return t.pair

/-- The CAVP response files through `sha256 digest`, the message as hexadecimal; FIPS's
examples through `sha256 digest_text`. -/
def runSha256Calls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let j ← readJson "vectors/sha256.json"
  let mut messages := 0
  for e in ← arr (← field j "cavp") do
    let file ← str e "file"
    let bytes ← IO.FS.readBinFile ("vectors" / file)
    let some text := String.fromUTF8? bytes | throw (IO.userError s!"{file}: not UTF-8")
    let ms ← IO.ofExcept ((Tests.Sha256.readResponse text).mapError fun e => IO.userError s!"{file}: {e}")
    for m in ms do
      let got := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str (Principia.Sha256.hex m.msg))]))
      t ← t.check (got == (Value.str m.md).canonicalJson) s!"sha256 digest {file} Len = {m.bits}: got {repr got}"
      messages := messages + 1
  let examples ← arr (← field j "examples")
  for c in examples do
    let n ← IO.ofExcept (c.getObjValAs? Nat "repeat")
    let text := String.join (List.replicate n (← str c "text"))
    let got := canonOf (respondTo "sha256" "digest_text" (.obj [("text", .str text)]))
    t ← t.check (got == (Value.str (← str c "expect")).canonicalJson) s!"sha256 digest_text {← str c "id"}: got {repr got}"
  IO.println s!"pcalc sha256: {messages} CAVP messages through digest, {examples.length} FIPS examples through digest_text"
  return t.pair

/-- Unicode's NormalizationTest.txt through `unicode`: one check a line, of the file's ten
conformance equalities through `nfc` and `nfd` and of the general category of each code point
of its first column through `general_category`, against UnicodeData.txt as `Tests.Unicode`
reads it. -/
def runUnicodeCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let u ← IO.ofExcept ((Tests.Unicode.readUnicodeData (← IO.FS.readFile "vectors/unicode/UnicodeData.txt")).mapError IO.userError)
  let call (f s : String) : Option String := canonOf (respondTo "unicode" f (.obj [("text", .str s)]))
  let canonStr (s : String) : Option String := (Value.str s).canonicalJson
  let mut lines := 0
  for raw in (← IO.FS.readFile "vectors/unicode/NormalizationTest.txt").splitOn "\n" do
    let line := ((raw.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty || line.startsWith "@Part" then continue
    let cols := line.splitOn ";"
    unless cols.length == 6 do throw (IO.userError s!"unicode: not five columns: {line}")
    let some cs := (cols.take 5).mapM Tests.Unicode.codes?
      | throw (IO.userError s!"unicode: a column that does not read: {line}")
    let col := (cs.map String.ofList).toArray
    let f (k : Nat) : String := col[k]!
    let nfcOk := [0, 1, 2].all (fun k => call "nfc" (f k) == canonStr (f 1)) &&
      [3, 4].all (fun k => call "nfc" (f k) == canonStr (f 3))
    let nfdOk := [0, 1, 2].all (fun k => call "nfd" (f k) == canonStr (f 2)) &&
      [3, 4].all (fun k => call "nfd" (f k) == canonStr (f 4))
    let cats := (Value.arr ((cs.headD []).map fun c => .str (u.category[c.toNat]!).code)).canonicalJson
    let gcOk := call "general_category" (f 0) == cats
    t ← t.check (nfcOk && nfdOk && gcOk) s!"unicode {line}: nfc {nfcOk}, nfd {nfdOk}, general_category {gcOk}"
    lines := lines + 1
  IO.println s!"pcalc unicode: {lines} lines of NormalizationTest.txt through nfc, nfd and general_category"
  return t.pair

/-- `n` combining marks of falling class, 230, 220, 202 and 1, over and over: each run is
sorted by canonical ordering. -/
def fallingMarks (n : Nat) : String :=
  String.ofList ((List.range n).map fun i => match i % 4 with
    | 0 => '́' | 1 => '̖' | 2 => '̧' | _ => '̴')

/-- A request's text of exactly `size` bytes: `{"<name>":"` and `"}` around `fill` repeated. -/
def requestOfSize (name : String) (fill : Char) (size : Nat) : ByteArray :=
  let head := "{\"" ++ name ++ "\":\""
  (head ++ String.ofList (List.replicate (size - head.utf8ByteSize - 2) fill) ++ "\"}").toUTF8

/-- A number of 308 digits, near the reader's bound below 2^1024. -/
def nearBound : Value := .int (10 ^ 307 + 7)

/-- The new families' bounds, each at and past it, through `Calculator.answer` (the reader
included); the slowest accepted request of each family is timed and printed. -/
def runRequestBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let text (s : String) : ByteArray :=
    ((Value.obj [("text", .str s)]).canonicalJson.getD "").toUTF8
  let at_ := String.singleton 'a' ++ fallingMarks (Principia.Calculator.Unicode.maxText - 1)
  let past := at_ ++ "́"
  let big := Value.obj [("state", .obj [("now", nearBound), ("agent_stop", .bool false),
      ("suspended", .bool false), ("governor_off", .bool false),
      ("agent_seats", .arr [nearBound, .int 0]), ("sponsor_seats", .arr [nearBound, .int 0]),
      ("agent_in_flight", .int 0), ("sponsor_in_flight", .int 0), ("finishing_in_flight", .int 0),
      ("starting_in_flight", .int 0), ("tuning", .obj [("agent_seat_rate", nearBound),
        ("sponsor_seat_rate", .int 1), ("sponsor_seat_burst", nearBound),
        ("agent_seat_burst", .int 1), ("retry_after_jitter", .arr [nearBound, nearBound])])]),
    ("request", .obj [("kind", .str "PUSH"), ("seats", nearBound), ("draw", .arr [nearBound, nearBound])])]
  let words := Value.arr ((List.replicate 100000 "LISTED").map .str)
  let bigUse := Value.obj [("hour", nearBound), ("day", nearBound), ("thirty_days", nearBound)]
  let bigLevel := Value.obj [("use", bigUse), ("prev", .str "OVERLOADED"),
    ("external_until", nearBound), ("now", nearBound),
    ("tuning", .obj [("kappa_m", .arr [nearBound, nearBound]), ("descent", .str "BANDS")])]
  let bigPressure := match big with
    | .obj ms => Value.obj (ms.map fun ((k : String), (v : Value)) => match k, v with
      | "state", Value.obj st => (k, Value.obj (st ++ [("use", bigUse), ("pressure", .str "OVERLOADED"),
          ("external_until", nearBound), ("anonymous_in_flight", nearBound)]))
      | _, _ => (k, v))
    | v => v
  let bigRecord := Value.obj [("stage", .str "PENALIZED"), ("breaker_until", nearBound),
    ("trial_pending", .bool true), ("retry_after", nearBound), ("backoff_until", nearBound),
    ("streak", nearBound), ("te3_times", .arr (List.replicate 10 nearBound)),
    ("throttled_times", .arr [nearBound, nearBound]), ("penalized_times", .arr [nearBound, nearBound]),
    ("last_event", nearBound), ("flood_inquire", nearBound), ("flood_release", nearBound)]
  let bigTuning := Value.obj [("retry_after_cap", nearBound), ("penalty_hour", nearBound),
    ("flood_interval", nearBound), ("error_streak", nearBound), ("doubling", .str "PER EVENT")]
  let bigTraffic := Value.obj [("traffic", bigRecord), ("now", nearBound),
    ("end", .obj [("kind", .str "PETITION"), ("ending", .str "RATE"), ("retry_after", nearBound)]),
    ("tuning", bigTuning)]
  let bigStage := Value.obj [("traffic", bigRecord), ("now", nearBound), ("kind", .str "INQUIRE"),
    ("tuning", bigTuning)]
  let cases : List (String × String × String × ByteArray × Bool) := [
    ("governor", "admit", "admit with every number near 2^1024",
      ((big.canonicalJson.getD "").toUTF8), true),
    ("governor", "pressure_level", "pressure_level with every number near 2^1024",
      ((bigLevel.canonicalJson.getD "").toUTF8), true),
    ("governor", "admit", "admit from the uses, every number near 2^1024",
      ((bigPressure.canonicalJson.getD "").toUTF8), true),
    ("governor", "traffic_step", "traffic_step with every number near 2^1024",
      ((bigTraffic.canonicalJson.getD "").toUTF8), true),
    ("governor", "traffic_stage", "traffic_stage with every number near 2^1024",
      ((bigStage.canonicalJson.getD "").toUTF8), true),
    ("permissions", "permits", "permits with 100,000 context words",
      (((Value.obj [("asker", .str "HOLDER"), ("class", .str "REGISTER OPEN"),
        ("op", .str "WRITE"), ("context", words)]).canonicalJson.getD "").toUTF8), true),
    ("sha256", "digest_text", "digest_text of a request of 1 MiB",
      requestOfSize "text" 'a' Principia.Canonical.maxTextBytes, true),
    ("sha256", "digest_text", "digest_text of a request of 1 MiB and a byte",
      requestOfSize "text" 'a' (Principia.Canonical.maxTextBytes + 1), false),
    ("sha256", "digest", "digest of a request of 1 MiB",
      requestOfSize "hex" 'a' Principia.Canonical.maxTextBytes, true),
    ("sha256", "digest", "digest of a request of 1 MiB and a byte",
      requestOfSize "hex" 'a' (Principia.Canonical.maxTextBytes + 1), false),
    ("unicode", "nfc", "nfc at 131,072 code points, a run of falling marks", text at_, true),
    ("unicode", "nfc", "nfc past 131,072 code points", text past, false),
    ("unicode", "nfd", "nfd at 131,072 code points, a run of falling marks", text at_, true),
    ("unicode", "nfd", "nfd past 131,072 code points", text past, false),
    ("unicode", "general_category", "general_category at 131,072 code points", text at_, true),
    ("unicode", "general_category", "general_category past 131,072 code points", text past, false)]
  let mut slowest : List (String × Nat) := []
  for (family, fn, what, bytes, accepted) in cases do
    let start ← IO.monoMsNow
    let (out, code) := answer family fn bytes
    t ← t.check ((code == 0) == accepted && (accepted || out.startsWith "{\"detail\":"))
      s!"{family} {fn}, {what}: exit {code}, {(out.take 200).toString}"
    let ms := (← IO.monoMsNow) - start
    if accepted then
      slowest := match slowest.lookup family with
        | some m => if m < ms then (family, ms) :: slowest.filter (·.1 != family) else slowest
        | none => (family, ms) :: slowest
  -- The answers at the bounds agree with the library, and a digest reads upper case alike.
  let lower := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str "616263")]))
  let upper := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str "616263".toUpper)]))
  t ← t.check (lower == upper && lower == (Value.str (Principia.Sha256.digestText "abc")).canonicalJson)
    s!"sha256 digest of 616263: {repr lower}, upper case {repr upper}"
  t ← t.check (refusalOf (respondTo "sha256" "digest" (.obj [("hex", .str "abc")])) == some .badArgument)
    "sha256 digest of an odd count of digits is not refused BAD_ARGUMENT"
  t ← t.check (canonOf (respondTo "unicode" "nfc" (.obj [("text", .str at_)])) ==
      (Value.str (Principia.Unicode.nfc at_)).canonicalJson) "unicode nfc at the bound"
  let shown := ", ".intercalate ((slowest.reverse).map fun (f, m) => s!"{f} {m} ms")
  IO.println s!"pcalc request bounds: the slowest accepted request of each family, reading included: {shown}"
  return t.pair

/-! ## The zones through `pcalc` -/

/-- A Starting Set of `n` DOF, each `{"NAME": "x<i>", "DIMENSION": "L1"}`. -/
def dofTpk (n : Nat) : Value :=
  .obj [("DOF", .arr ((List.range n).map fun i =>
    .obj [("NAME", .str s!"x{i}"), ("DIMENSION", .str "L1")]))]

/-- A Criteria Set term of `n` `NEG:` around `A`. -/
def negTerm (n : Nat) : String := String.join (List.replicate n "NEG:") ++ "A"

/-- The zone family's bounds (`Calculator.Zone`), each at its value and one past it. -/
def runZoneBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("DOF at 1024", "starting_set_well_formed", .obj [("tpk", dofTpk 1024)], false),
    ("DOF past 1024", "starting_set_well_formed", .obj [("tpk", dofTpk 1025)], true),
    ("DOF at 1024, the digest", "digest_starting_set", .obj [("tpk", dofTpk 1024)], false),
    ("DOF past 1024, the digest", "digest_starting_set", .obj [("tpk", dofTpk 1025)], true),
    ("a term at 32768 code points", "canonical_term", .obj [("t", .str (negTerm 8191))], false),
    ("a term past 32768 code points", "canonical_term",
      .obj [("t", .str (negTerm 8191 ++ "1234"))], true),
    -- "zone", "value" and "TMS" hold 12 code points.
    ("text at 131072 code points in all", "zone_preimage",
      .obj [("zone", .str "TMS"), ("value", .arr (textsOf (131072 - 12)))], false),
    ("text past 131072 code points in all", "zone_preimage",
      .obj [("zone", .str "TMS"), ("value", .arr (textsOf (131073 - 12)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "zone" fn request
    t ← t.check (boundRefusal got == refused)
      s!"zone {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## The fundamental tests through `pcalc` -/

/-- `tests_corpus.json`: all its cases through `fundamental <fn>`, version 1's
`kernel_tests` spelled `fundamental_tests`; version 1's `canon` text of the answer
compared with `expect`. None is owed, and none refused. -/
def runFundamentalCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/tests_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := if v1 == "kernel_tests" then "fundamental_tests" else v1
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "fundamental" fn input
    let ok := match got with
      | .ok v => v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"fundamental {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The fundamental family's bounds (`Calculator.Fundamental`), each at its value and one
past it. -/
def runFundamentalBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("DOF at 64", "fundamental_tests", .obj [("tpk", dofTpk 64)], false),
    ("DOF past 64", "fundamental_tests", .obj [("tpk", dofTpk 65)], true),
    ("DOF past 64, T5", "t5_dof_yield", .obj [("tpk", dofTpk 65)], true),
    ("a PROPOSITION at 16384 code points", "t2_findings", .obj [("prop", .str (codePoints 16384))], false),
    ("a PROPOSITION past 16384 code points", "t2_findings", .obj [("prop", .str (codePoints 16385))], true),
    -- "tfk" holds 3 code points; eight strings of 16,384 and one of 1 reach 131,075.
    ("text at 131072 code points in all", "final_checks",
      .obj [("tfk", .arr (textsOf (131072 - 3)))], false),
    ("text past 131072 code points in all", "final_checks",
      .obj [("tfk", .arr (textsOf (131073 - 3)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "fundamental" fn request
    t ← t.check (boundRefusal got == refused)
      s!"fundamental {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## The bibliography through `pcalc` -/

/-- v1's `_esc`: `|` and `\` behind a backslash; a C0 control or DEL as `\xHH`. -/
def biblioEsc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '|' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      let h := Nat.toDigits 16 c.toNat
      "\\x" ++ (if h.length < 2 then "0" else "") ++ String.ofList h
    else c.toString)

/-- A member of an answer object as a string, "" when absent or not a string. -/
def sOf (v : Value) (k : String) : String :=
  match member v k with
  | some (.str s) => s
  | _ => ""

/-- A text or `null` as v1 rendered None in `render_compare`: `-`. -/
def orDash : Option Value → String
  | some (.str s) => s
  | _ => "-"

/-- v1's render (`render_*` in tpc_biblio.py) of the family's JSON answer. -/
def biblioRender (fn : String) (v : Value) : Option String :=
  match fn, v with
  | "doi", _ => some s!"doi|{sOf v "kind"}|{biblioEsc (sOf v "doi")}|{biblioEsc (sOf v "id")}"
  | "shape", .bool b => some ("shape|" ++ toString b)
  | "withdrawn", .bool b => some ("withdrawn|" ++ toString b)
  | "arxiv", _ => match member v "version" with
    | some (.int n) => some s!"arxiv|{sOf v "id"}|{n}|{sOf v "key"}|{sOf v "scheme"}"
    | _ => none
  | "isbn", _ => some s!"isbn|{sOf v "isbn13"}|{sOf v "given"}"
  | "issn", .str s => some ("issn|" ++ s)
  | "pmid", .str s => some ("pmid|" ++ s)
  | "pmcid", .str s => some ("pmcid|" ++ s)
  | "key", .str s => some ("key|" ++ biblioEsc s)
  | "url", .str s => some ("url|" ++ biblioEsc s)
  | "preimage", .str s => some ("preimage|" ++ biblioEsc s)
  | "dupe", _ => some s!"dupe|{sOf v "kind"}|{biblioEsc (sOf v "key")}"
  | "canon", _ => some ("canon|" ++ sOf v "digest" ++ "\n" ++ biblioEsc (sOf v "text"))
  | "check", _ => do
    let d ← member v "dupe"
    let .obj ids ← member v "identifiers" | none
    -- v1's order of kinds (the answer's keys are sorted once written as canonical JSON).
    let idLines := ["DOI", "ARXIV", "ISBN", "ISSN", "PMID", "PMCID"].filterMap fun k =>
      match ids.lookup k with
      | some (.str s) => some s!"id|{k}|{biblioEsc s}"
      | _ => none
    some ("\n".intercalate (s!"check|OK|{sOf d "kind"}|{biblioEsc (sOf d "key")}" :: idLines))
  | "compare", _ => do
    let .arr rs ← member v "results" | none
    let .arr ns ← member v "notices" | none
    let rLines ← rs.mapM fun r => match r with
      | .arr [.str k, .str i, .str res, .arr fs] =>
        some s!"{k}|{biblioEsc i}|{res}|{",".intercalate (fs.filterMap fun | .str f => some f | _ => none)}"
      | _ => none
    let nLines := ns.map fun n =>
      s!"notice|{biblioEsc (sOf n "source")}|{biblioEsc (orDash (member n "identifier"))}|{orDash (member n "date")}|{biblioEsc (sOf n "type")}"
    let nl := sOf v "notices_line"
    some ("\n".intercalate ((("compare|" ++ sOf v "check") :: rLines) ++ nLines ++
      ["line|" ++ biblioEsc (sOf v "check_line"), "line|" ++ (if nl.isEmpty then "-" else biblioEsc nl)]))
  | "view", _ => do
    let .arr rs ← member v "records" | none
    let .arr hs ← member v "for_hdecl" | none
    let rLines ← rs.mapM fun r => match r with
      | .arr [.str rid, .arr fl] => do
        let parts ← fl.mapM fun p => match p with
          | .arr [.str b, .str reason] => some (biblioEsc b ++ ":" ++ reason)
          | _ => none
        some ("record|" ++ biblioEsc rid ++ "|" ++ "|".intercalate parts)
      | _ => none
    let hd := ",".intercalate (hs.filterMap fun | .str b => some (biblioEsc b) | _ => none)
    some ("\n".intercalate ((s!"view|{rs.length}" :: rLines) ++ ["hdecl|" ++ hd]))
  | "holdlist", .arr ps => do
    let ls ← ps.mapM fun p => match p with
      | .arr [.str b, .str c] => some (biblioEsc b ++ "|" ++ c)
      | _ => none
    some ("\n".intercalate (s!"holdlist|{ps.length}" :: ls))
  | _, _ => none

/-- `biblio_corpus.json`: all 405 cases through `biblio <fn>`, each case's `args` the request;
the answer rendered as v1 rendered it (`biblioRender`) and compared with `expected` byte for
byte; `ERROR:<m>` expects the refusal `BAD_ARGUMENT` with detail `m`. -/
def runBiblioCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/biblio_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "biblio" fn args
    let ok := match got with
      | .ok v => biblioRender fn v == some expected
      | .error r => r.code == .badArgument && "ERROR:" ++ r.detail == expected
    t ← t.check ok s!"biblio {fn} {name}: expected {repr expected}, got {repr (got.toOption.bind (biblioRender fn))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The biblio family's bounds (`Calculator.Biblio`), each at its value and one past it. -/
def runBiblioBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("a text at 16384 code points", "pmid", .obj [("text", .str (codePoints 16384))], false),
    ("a text past 16384 code points", "pmid", .obj [("text", .str (codePoints 16385))], true),
    ("identifiers at 64", "dupe",
      .obj [("identifiers", .obj ((List.range 64).map fun i => (s!"K{i}", .str "x")))], false),
    ("identifiers past 64", "dupe",
      .obj [("identifiers", .obj ((List.range 65).map fun i => (s!"K{i}", .str "x")))], true),
    ("existing at 1024", "check",
      .obj [("entry", .obj []), ("existing", .arr ((List.range 1024).map fun _ => .arr [])), ("caps", .obj [])], false),
    ("existing past 1024", "check",
      .obj [("entry", .obj []), ("existing", .arr ((List.range 1025).map fun _ => .arr [])), ("caps", .obj [])], true),
    -- "comment" holds 7 code points.
    ("text at 131072 code points in all", "withdrawn",
      .obj [("comment", .arr (textsOf (131072 - 7)))], false),
    ("text past 131072 code points in all", "withdrawn",
      .obj [("comment", .arr (textsOf (131073 - 7)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "biblio" fn request
    t ← t.check (boundRefusal got == refused)
      s!"biblio {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## Hold scope through `pcalc` -/

/-- `hold_corpus.json`: all 140 cases through `hold <fn>`, version 1's `tpx_allocate` spelled
`allocate_identifiers`; version 1's `canon` text of the answer compared with `expect`. -/
def runHoldCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/hold_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := if v1 == "tpx_allocate" then "allocate_identifiers" else v1
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "hold" fn input
    let ok := match got with
      | .ok v => v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"hold {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The hold family's bounds (`Calculator.Hold`), each at its value and one past it. -/
def runHoldBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let blocks (n : Nat) : Value := .obj [("account", .str "acct"), ("admission_block", .str "B0"),
    ("blocks", .arr ((List.range n).map fun i => .obj [("block_id", .str s!"B{i}"), ("canary", .null)]))]
  let cases : List (String × String × Value × Bool) := [
    ("history at 4000 blocks", "hold_scope",
      .obj [("history", blocks 4000), ("lookback_passes", .int 2)], false),
    ("history past 4000 blocks", "hold_scope",
      .obj [("history", blocks 4001), ("lookback_passes", .int 2)], true),
    ("records at 1000", "held_closure",
      .obj [("records", .arr ((List.range 1000).map fun i => .obj [("id", .str s!"RR-{i}")])),
        ("seeds", .obj [])], false),
    ("records past 1000", "held_closure",
      .obj [("records", .arr ((List.range 1001).map fun i => .obj [("id", .str s!"RR-{i}")])),
        ("seeds", .obj [])], true),
    ("a name at 16384 code points", "allocate_identifiers",
      .obj [("range", .obj [("prefix", .str (codePoints 16384))])], false),
    ("a name past 16384 code points", "allocate_identifiers",
      .obj [("range", .obj [("prefix", .str (codePoints 16385))])], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "hold" fn request
    t ← t.check (boundRefusal got == refused)
      s!"hold {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## The yardsticks through `pcalc` -/

/-- A value of `yardstick_corpus.json`'s expectation, or of the answer: a decimal, or
`numerator/denominator`, read exactly. -/
def exactOf (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [a, b] => do
    let n ← a.toInt?
    let d ← b.toNat?
    if d = 0 then none else some ((n : Rat) / (d : Rat))
  | _ => Decimal.value s

/-- `yardstick_corpus.json`: all 46 cases through `yardstick <fn>`. -/
def runYardstickCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/yardstick_corpus.json" do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let keys := if fn == "yardstick_key" then ["tms", "name", "rid", "records", "fields"]
      else ["tms", "name", "suite"]
    let request : Value := .obj (keys.filterMap fun k => (member input k).map (k, ·))
    let got := respondTo "yardstick" fn request
    let ok := match got with
      | .ok (.arr [.str "REFUSED", .str r]) => expect == "[REFUSED," ++ r ++ "]"
      | .ok (.arr [.str "OK", .arr vs]) =>
        if fn == "yardstick_key" then
          let want := (String.ofList ((expect.toList.drop 5).dropLast.dropLast)).splitOn "," |>.map exactOf
          let have_ := vs.map fun | .str s => exactOf s | _ => none
          want == have_ && want.all Option.isSome
        else false
      | .ok v => fn != "yardstick_key" && v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"yardstick {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## The declared forms through `pcalc` -/

/-- eval_form's text against version 1's, as the forms' runner compares them
(`Tests.Form.compareEval`): an `OK` answer's numbers by value, its KIND and every other
answer as text. -/
def evalAgrees (expect mine : String) : Bool :=
  match Tests.Form.splitTwo expect, Tests.Form.splitTwo mine with
  | some ("OK", v1), some ("OK", m) =>
    let a := v1.splitOn ","
    let b := m.splitOn ","
    a.length == b.length && ((List.range a.length).zip (a.zip b)).all fun (i, x, y) =>
      if i + 1 == a.length then Tests.Form.separable y && x == y
      else match Decimal.value x, Decimal.value y with
        | some p, some q => p == q
        | _, _ => false
  | _, _ => expect == mine

/-- What the command gave: version 1's text of its answer (the bound on an exact value's
refusal written as version 1's `[REFUSED,exact value too large]`), or the detail of an `OWED`
refusal. -/
inductive FormGot where
  | text (t : String)
  | owed (detail : String)
  | other (what : String)

def formGot : Except Refusal Value → FormGot
  | .ok v => match v.canon with
    | some t => .text t
    | none => .other "an answer with no canon text"
  | .error r =>
    if r.code == .owed then .owed r.detail
    else if r.code == .badArgument && r.detail == ValueBound.tooLarge then
      .text ("[REFUSED," ++ ValueBound.tooLarge ++ "]")
    else .other s!"refused {r.code.word}: {r.detail}"

def FormGot.show : FormGot → String
  | .text t => t
  | .owed d => "OWED: " ++ d
  | .other w => w

/-- `form_corpus.json` and `form_numbers.json`: every case through `form <fn>`, the forms'
runner the reference (`Tests.Form.run`, `runFormNumbers`). A case the runner agrees on must
agree, compared as the runner compares; a case it finds owed must be refused `OWED` with the
plain words for what it met; a recorded divergence must give the divergence's own text. -/
def runFormCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let divJson ← readJson "vectors/form_corpus.divergences.json"
  let divs ← (← arr (← field divJson "divergences")).mapM fun o => do
    pure ((← str o "id"), (← str o "v1"), (← str o "v2"))
  let jsonCases ← arr (← field (← readJson "vectors/form_corpus.json") "cases")
  let valueCases ← v1Cases "vectors/form_corpus.json"
  for (j, c) in jsonCases.zip valueCases do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := formGot (respondTo "form" fn input)
    let reference ← Tests.Form.run fn (← field j "input") expect
    let agrees (mine : String) := if fn == "eval_form" then evalAgrees expect mine else expect == mine
    let ok := match reference, got with
      | .agrees, .text m => agrees m
      | .differs mine, .text m => m == mine && divs.contains (id, expect, mine)
      | .owed w, .owed d => d == Principia.Calculator.Form.owedDetail w
      | _, _ => false
    t ← t.check ok s!"form {fn} {id}: expected {repr expect}, got {repr got.show}"
  let numberCases ← arr (← field (← readJson "vectors/form_numbers.json") "cases")
  for (c, v) in numberCases.zip (← v1Cases "vectors/form_numbers.json") do
    let id ← str c "id"
    let j ← field c "input"
    let expect ← str c "expect"
    let some input := member v "input" | throw (IO.userError s!"{id}: no input")
    let got := formGot (respondTo "form" "eval_form" input)
    let b := Tests.Form.bindingsArg j
    let reference := Principia.Form.withArgs (Tests.Form.strArg j "text")
      ((Tests.Form.strArg j "mode").getD "") fun s m => Principia.Form.evalForm (some Principia.Calculator.Form.stepBudget) s m b
    let ok := match reference, got with
      | .owed w, .owed d => expect == "OWED" && d == Principia.Calculator.Form.owedDetail w
      | .owed _, _ => false
      | _, .text m => expect != "OWED" && evalAgrees expect m
      | _, _ => false
    t ← t.check ok s!"form_numbers {id}: expected {repr expect}, got {repr got.show}"
  return t.pair

/-- A `dimensions` object of `n` names, each `L1`. -/
def formDims (n : Nat) : Value := .obj ((List.range n).map fun i => (s!"d{i}", .str "L1"))

/-- A `bindings` object of `n` names, each one metre. -/
def formBindings (n : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"b{i}", .obj [("VALUE", .str "1"), ("UNIT", .str "m")]))

/-- A `dimensions` object of four strings holding `n` code points in all, beside a form `x`:
the names `text`, `mode`, `dimensions`, `x`, `expression` and the four keys hold 37. -/
def formText (n : Nat) : Value :=
  let rest := n - 37 - 3 * 32768
  .obj [("text", .str "x"), ("mode", .str "expression"),
    ("dimensions", .obj [("a0", .str (codePoints 32768)), ("a1", .str (codePoints 32768)),
      ("a2", .str (codePoints 32768)), ("a3", .str (codePoints rest))])]

/-- The sum `ln(x0)+...+ln(x{k-1})`, its names bound to 2, 3, ... -/
def lnSum (k : Nat) : String := "+".intercalate ((List.range k).map fun i => s!"ln(x{i})")

/-- `eval_form` of a sum of `k` ln less itself, a value exactly zero but not known so: every
precision up to 4096 bits is tried before it is owed (`vectors/pcalc.json` holds `k` = 64). -/
def lnZero (k : Nat) : Value :=
  .obj [("text", .str s!"({lnSum k})-({lnSum k})"), ("mode", .str "expression"),
    ("bindings", .obj ((List.range k).map fun i =>
      (s!"x{i}", .obj [("VALUE", .str (toString (i + 2))), ("UNIT", .str "1")])))]

/-- `t3_laws` over `laws` LAWs, each a sum of `k` ln of CONSTANTs equated to itself. -/
def lnLaws (laws k : Nat) : Value :=
  .obj [("tpk", .obj [("DOF", .arr []),
    ("CONSTANT", .arr ((List.range k).map fun i => .obj [("NAME", .str s!"x{i}"),
      ("DIMENSION", .str "1"), ("VALUE", .str (toString (i + 2))), ("UNIT", .str "1")])),
    ("LAW", .arr ((List.range laws).map fun j => .obj [("NAME", .str s!"L{j}"),
      ("STATEMENT", .str "a sum of ln"), ("REFS", .arr []), ("ROLE", .str "DEFINITION"),
      ("EQUATION", .str s!"{lnSum k} = {lnSum k}")])),
    ("CONSTRAINT", .arr [])])]

/-- The form family's bounds (`Calculator.Form`), each at its value and one past it; the
precision-step budget (`Calculator.Form.stepBudget`) by requests on either side of it. -/
def runFormBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let tm (s : String) : List (String × Value) := [("text", .str s), ("mode", .str "expression")]
  let cases : List (String × String × Value × Bool) := [
    ("a form at 32768 code points", "parse_form", .obj (tm (codePoints 32768)), false),
    ("a form past 32768 code points", "parse_form", .obj (tm (codePoints 32769)), true),
    ("text at 131072 code points in all", "form_dimension", formText 131072, false),
    ("text past 131072 code points in all", "form_dimension", formText 131073, true),
    ("bindings at 64", "eval_form", .obj (tm "b0" ++ [("bindings", formBindings 64)]), false),
    ("bindings past 64", "eval_form", .obj (tm "b0" ++ [("bindings", formBindings 65)]), true),
    ("DOF at 64", "names_check", .obj [("tpk", dofTpk 64)], false),
    ("DOF past 64", "names_check", .obj [("tpk", dofTpk 65)], true),
    ("DOF past 64, T3", "t3_laws", .obj [("tpk", dofTpk 65)], true),
    ("dimensions at 1024", "form_dimension", .obj (tm "d0" ++ [("dimensions", formDims 1024)]), false),
    ("dimensions past 1024", "form_dimension", .obj (tm "d0" ++ [("dimensions", formDims 1025)]), true),
    ("dimensions past 1024, totality", "form_totality",
      .obj [("text", .str "d0<1"), ("dimensions", formDims 1025)], true),
    ("one ln less itself, owed within the step budget", "eval_form", lnZero 1, false),
    ("two ln less themselves, past the step budget", "eval_form", lnZero 2, true),
    ("64 ln less themselves, past the step budget", "eval_form", lnZero 64, true),
    ("4 LAWs of 4 ln, within the step budget", "t3_laws", lnLaws 4 4, false),
    ("64 LAWs of 40 ln, past the step budget", "t3_laws", lnLaws 64 40, true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "form" fn request
    t ← t.check (boundRefusal got == refused)
      s!"form {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator
