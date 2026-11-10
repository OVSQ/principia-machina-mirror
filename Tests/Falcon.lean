import Principia
import Lean.Data.Json

/-!
The runner of v1's `vectors/falcon_corpus.json` (949 cases) against `Principia.Falcon`, and
the check of the character class table against v1's text.

A case is `{"name", "fn", "args", "hand_checked", "expected"}`. Its arguments are read into
`Principia.Canonical.Value` as v1's JSON reader gives them: a number with a fraction or an
exponent is v1's float (`num`), any other an integer. Its `expected` is v1's render of the
result (`render_*` in `tpc_falcon.py`), or `ERROR:` and the refusal's word. The Calculator
writes the same render (each `render*` function is v1's, ported), and the two texts must be
equal character for character.

Nothing is owed: the draw's `h` and the output schema's digest are SHA-256
(`Principia.Sha256`, decision D2), and text is put in NFC with Unicode 15.1.0's tables, as
v1 put it (decision D3); `vectors/falcon_corpus.owed.json` must list none.

`vectors/falcon_hand.json` holds hand vectors in the same form: inputs chosen to reach paths
the corpus leaves out, each expectation computed by v1's own `run_case`; all must pass.

The table check reads `_UTABLE`'s literal from `docs/v1/tpc_py/tpc_falcon.py` and requires
`Principia.Falcon.tableText` to equal it character for character, every item to read, the
1247 ranges to increase without overlap, v1's binary search (`classIn`) to agree with
a scan (`classByScan`) at every range's ends and beside them, and the table's SHA-256 to be
the one v1 records for it and checked on first use.
-/

namespace Tests.Falcon

open Lean
open Principia
open Principia.Falcon
open Principia.Canonical (Value)

/-- A JSON value as v1's reader gives it: a number with a fraction or an exponent is a
float (`num`), any other an integer. -/
partial def toValue : Json → Value
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent == 0 then .int n.mantissa else .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr a => .arr (a.toList.map toValue)
  | .obj kvs => .obj (kvs.foldl (fun acc k v => acc ++ [(k, toValue v)]) [])

/-- A case's result. -/
inductive Judged where
  | pass
  | fail (why : String)

/-- A render against v1's expectation, as text; a refusal as `ERROR:` and its word. -/
def judge (expected : String) : Result String → Judged
  | .ok s => if s == expected then .pass else .fail s!"got {repr s}"
  | .error (.refused w) =>
    if expected == "ERROR:" ++ w then .pass else .fail s!"refused {w}"

/-- An argument, `null` when absent (v1's `args.get(k)`). -/
def arg (args : Json) (k : String) : Value :=
  match args.getObjVal? k with
  | .ok j => toValue j
  | .error _ => .null

/-- An argument with a default when absent (v1's `args.get(k, default)`). -/
def argOr (args : Json) (k : String) (d : Value) : Value :=
  match args.getObjVal? k with
  | .ok j => toValue j
  | .error _ => d

/-- Run one case: v1's `run_case`. -/
def runCase (fn : String) (args : Json) : Option (Result String) :=
  let a := arg args
  let flags := (a "affix", a "scale", argOr args "accounting" (.bool false))
  match fn with
  | "canon" => some (canonCase (a "value") (a "spec"))
  | "qmatch" =>
    some ((Quote.quoteMatch (a "value") (a "quote") flags.1 flags.2.1 flags.2.2).map
      Quote.renderQuote)
  | "qcheck" =>
    some ((Quote.quoteCheck (a "page") (a "quote") (a "value") flags.1 flags.2.1
      flags.2.2).map Quote.renderQuote)
  | "source" => some ((Source.sourceMatch (a "cited") (a "sources")).map Source.renderSource)
  | "hop" =>
    some ((Source.sourceHop (a "hop") (a "matched") (a "sources")).map Source.renderHop)
  | "draw" =>
    some ((Draw.falconDraw (a "candidates") (a "n") (a "state") (a "r")).map Draw.renderDraw)
  | "reconcile" =>
    some ((Reconcile.falconReconcile (a "outputs") (a "quotes") (a "schema")).map
      Reconcile.renderReconcile)
  | "stage" =>
    some ((Stage.sponsorStage (a "events") (a "as_of") (a "thresholds")).map Stage.renderStage)
  | "stop" => some ((Stop.falconStop (a "counts") (a "limits")).map Stop.renderStop)
  | "schema_canon" => some ((Schema.schemaCanon (a "schema")).map Schema.renderCanonText)
  | "schema_digest" => some ((Schema.schemaDigest (a "schema")).map Schema.renderDigest)
  | _ => none

/-! ## The class table against v1's text -/

/-- `_UTABLE`'s literal in v1's source: its quoted pieces between `_UTABLE = (` and `)`. -/
def v1Table (src : String) : Option String := do
  let after ← (src.splitOn "_UTABLE = (\n")[1]?
  let block ← (after.splitOn "\n)\n")[0]?
  let pieces := (block.splitOn "\n").filterMap fun l =>
    let t := l.trimAscii.toString
    if t.startsWith "\"" && t.endsWith "\"" && t.length ≥ 2 then
      some (String.ofList ((t.toList.drop 1).dropLast))
    else none
  return String.join pieces

/-- The code points at and beside every range's ends. -/
def probes (t : Array ClassRange) : List Nat :=
  t.toList.flatMap fun r => [r.first - 1, r.first, r.first + 1, r.last - 1, r.last, r.last + 1]

def runTable : IO (Nat × Nat) := do
  let src ← IO.FS.readFile "docs/v1/tpc_py/tpc_falcon.py"
  let mut pass := 0
  let mut fail := 0
  let read := readTable tableText
  let scanAgrees := (probes table).all fun n =>
    if n.isValidChar then classIn table (Char.ofNat n) == classByScan table (Char.ofNat n)
    else true
  let checks : List (Bool × String) := [
    (v1Table src == some tableText, "tableText equals v1's _UTABLE, character for character"),
    (read.isSome, "every item of the table reads"),
    (table.size == 1247, "the table reads into 1247 ranges"),
    (increasing table.toList, "the ranges increase without overlap"),
    (scanAgrees, "classIn agrees with classByScan at and beside every range's ends"),
    (src.contains tableSha256 && src.contains s!"UNICODE_VERSION = \"{tableVersion}\"",
      "the recorded SHA-256 and Unicode version are v1's"),
    (Sha256.digestText tableText == tableSha256,
      "the table's SHA-256 is the one v1 records (UNICODE_TABLE_SHA256)")]
  for (ok, what) in checks do
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL falcon_table: {what}"
      fail := fail + 1
  return (pass, fail)

/-! ## The corpus -/

/-- Run the corpus: passes and failures. Nothing is owed, so the owed list must be empty. -/
def runFalcon : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/falcon_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/falcon_corpus.owed.json"))
  let owedList ← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)
  let listed ← owedList.toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")),
          (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let e ← IO.ofExcept (c.getObjValAs? String "expected")
    let some got := runCase fn (← IO.ofExcept (c.getObjVal? "args"))
      | throw (IO.userError s!"falcon {name}: unknown function {fn}")
    match judge e got with
    | .pass => pass := pass + 1
    | .fail why =>
      IO.eprintln s!"FAIL falcon {name}:\n  expected {repr e}\n  {why}"
      fail := fail + 1
  for (name, why) in listed do
    IO.eprintln s!"FAIL falcon {name}: listed as owed ({why}) but nothing is owed"
    fail := fail + 1
  IO.println s!"falcon: none owed"
  return (pass, fail)

/-- Run the hand vectors (`vectors/falcon_hand.json`): inputs chosen by hand, each
expectation v1's own answer; every case must pass. -/
def runHand : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/falcon_hand.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let e ← IO.ofExcept (c.getObjValAs? String "expected")
    let some got := runCase fn (← IO.ofExcept (c.getObjVal? "args"))
      | throw (IO.userError s!"falcon_hand {name}: unknown function {fn}")
    match judge e got with
    | .pass => pass := pass + 1
    | .fail why =>
      IO.eprintln s!"FAIL falcon_hand {name}:\n  expected {repr e}\n  {why}"
      fail := fail + 1
  return (pass, fail)

end Tests.Falcon
