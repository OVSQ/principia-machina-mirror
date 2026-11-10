import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of v1's `vectors/biblio_corpus.json` (405 cases) against `Principia.Biblio`, and
the check of the key form's class table against v1's text.

A case is `{"name", "fn", "args", "hand_checked", "expected"}`. Its arguments are read into
`Principia.Zone.Value` as v1's JSON reader gives them (`Tests.Zone.toValue`). Its `expected`
is v1's render of the result (`render_*` in `tpc_biblio.py`), or `ERROR:` and the refusal's
message. A refusal is compared by its message. A render is read back into the function's
typed result (v1's `_esc` undone: `\|`, `\\` and `\xHH`) and the typed values are compared.
Where a render joins words with commas, a word holding a comma fails the case rather than
passes it.

A canonical entry's digest is SHA-256 (`Principia.Sha256`; decision D2, option 1), compared
with v1's as its text is. An owed case would be listed with its reason in
`vectors/biblio_corpus.owed.json` (the list must be exactly the owed cases); none is. NFD and
NFC are Unicode 15.1.0's, v1's (decision D3).

The table check reads `_UTABLE`'s literal from `docs/v1/tpc_py/tpc_biblio.py` and requires
`Principia.Biblio.utable` to equal it character for character, every item to read, and the
ranges to increase without overlap.
-/

namespace Tests.Biblio

open Lean
open Principia
open Principia.Biblio
open Principia.Zone (Value codePoint)

/-! ## v1's render, read back -/

/-- v1 `_esc` undone over one field. -/
def unesc : List Char → List Char
  | '\\' :: 'x' :: h1 :: h2 :: rest =>
    match hexValue? (String.ofList [h1, h2]).toUpper with
    | some n => Char.ofNat n :: unesc rest
    | none => '\\' :: 'x' :: unesc (h1 :: h2 :: rest)
  | '\\' :: c :: rest => c :: unesc rest
  | c :: rest => c :: unesc rest
  | [] => []

/-- A render line's fields, split at the bars `_esc` left unescaped, each unescaped. -/
def fields (line : String) : List String :=
  let rec go : List Char → List Char → List (List Char) → List (List Char)
    | [], cur, acc => (acc ++ [cur])
    | '\\' :: c :: rest, cur, acc => go rest (cur ++ ['\\', c]) acc
    | '|' :: rest, cur, acc => go rest [] (acc ++ [cur])
    | c :: rest, cur, acc => go rest (cur ++ [c]) acc
  (go line.toList [] []).map fun f => String.ofList (unesc f)

/-- A comma-joined list, empty for the empty text. -/
def commaList (s : String) : List String := if s.isEmpty then [] else s.splitOn ","

def bool? : String → Option Bool
  | "true" => some true
  | "false" => some false
  | _ => none

def doiOf : List String → Option DoiNorm
  | ["doi", k, d, i] => do
    let kind ← if k == "DOI" then some DoiKind.doi else if k == "ARXIV" then some .arxiv else none
    return { doi := d, kind, id := i }
  | _ => none

def arxivOf : List String → Option ArxivId
  | ["arxiv", i, v, k, s] => do
    let scheme ← if s == "NEW" then some Scheme.new else if s == "OLD" then some .old else none
    return { id := i, version := ← v.toNat?, key := k, scheme }
  | _ => none

def isbnOf : List String → Option Isbn
  | ["isbn", n, g] => if g == "10" then some ⟨n, true⟩ else if g == "13" then some ⟨n, false⟩ else none
  | _ => none

def oneOf (tag : String) : List String → Option String
  | [t, v] => if t == tag then some v else none
  | _ => none

/-- `check|OK|<dupe kind>|<dupe key>`, then `id|<KIND>|<value>` per identifier. -/
def checkOf (lines : List (List String)) : Option CheckResult := do
  let (first, rest) ← match lines with
    | f :: r => some (f, r)
    | [] => none
  let dupe ← match first with
    | ["check", "OK", k, key] => some ({ kind := k, key } : Dupe)
    | _ => none
  let mut ids : Identifiers := {}
  for l in rest do
    match l with
    | ["id", "DOI", v] => ids := { ids with doi := some v }
    | ["id", "ARXIV", v] => ids := { ids with arxiv := some v }
    | ["id", "ISBN", v] => ids := { ids with isbn := some v }
    | ["id", "ISSN", v] => ids := { ids with issn := some v }
    | ["id", "PMID", v] => ids := { ids with pmid := some v }
    | ["id", "PMCID", v] => ids := { ids with pmcid := some v }
    | _ => none
  return { identifiers := ids, dupe }

/-- `compare|<check>`, the result lines, the notice lines, then the two status lines. -/
def compareOf (lines : List (List String)) : Option (Comparison × String × String) := do
  let mut check := none
  let mut res : List IdentResult := []
  let mut notices : List Notice := []
  let mut ls : List String := []
  for l in lines do
    match l with
    | ["compare", c] => check := some c
    | ["notice", src, i, d, t] =>
      notices := notices ++ [{ type := t, identifier := if i == "-" then none else some i,
                               date := if d == "-" then none else some d, source := src }]
    | ["line", x] => ls := ls ++ [x]
    | [k, i, r, fs] => res := res ++ [{ kind := k, identifier := i, result := r, fields := commaList fs }]
    | _ => none
  match ls with
  | [cl, nl] => return ({ check := ← check, results := res, notices }, cl, if nl == "-" then "" else nl)
  | _ => none

/-- `view|<n>`, `record|<id>|<bib>:<reason>|...` per record, `hdecl|<bibs>`. -/
def viewOf (lines : List (List String)) : Option LiteratureView := do
  let mut recs : List (String × List (String × String)) := []
  let mut hd := none
  let mut n := none
  for l in lines do
    match l with
    | ["view", c] => n := c.toNat?
    | ["hdecl", bs] => hd := some (commaList bs)
    | "record" :: rid :: flags =>
      let pairs ← flags.mapM fun f => do
        let parts := f.splitOn ":"
        let reason ← parts.getLast?
        some (":".intercalate parts.dropLast, reason)
      recs := recs ++ [(rid, pairs)]
    | _ => none
  guard (n == some recs.length)
  return { records := recs, forHdecl := ← hd }

/-- `holdlist|<n>`, then `<bib_id>|<check>` per entry. -/
def holdListOf (lines : List (List String)) : Option (List (String × String)) := do
  match lines with
  | ["holdlist", c] :: rest =>
    let pairs ← rest.mapM fun
      | [b, k] => some (b, k)
      | _ => none
    guard (c.toNat? == some pairs.length)
    return pairs
  | _ => none

/-! ## Judging a case -/

/-- A case's result. -/
inductive Judged where
  | pass
  | fail (why : String)
  | owed (reason : String)

/-- A result against v1's expectation: a refusal by its message, an answer by its typed value
read from the render; `words` must carry no comma where the render joins with commas. -/
def judge {α : Type} [DecidableEq α] [Repr α] (expected : String) (read : String → Option α)
    (got : Check α) (words : α → List String := fun _ => []) : Judged :=
  match got with
  | .error (.refused m) =>
    if expected == "ERROR:" ++ m then .pass else .fail s!"refused {m}"
  | .ok a =>
    match read expected with
    | none => .fail s!"answered {repr a}; the expectation does not read as this answer"
    | some b =>
      if (words a).any (fun w => w.toList.contains ',') then .fail s!"answered {repr a}, ambiguous"
      else if a == b then .pass else .fail s!"answered {repr a}"

/-- The render's lines, each split into fields. -/
def lines (e : String) : List (List String) := (e.splitOn "\n").map fields

def single {α : Type} (f : List String → Option α) (e : String) : Option α :=
  match lines e with
  | [l] => f l
  | _ => none

def arg (args : Json) (k : String) : IO Value := do
  match args.getObjVal? k with
  | .ok j => return Tests.Zone.toValue j
  | .error e => throw (IO.userError s!"{e} in {args.compress}")

/-- Run one case. -/
def runCase (fn : String) (args : Json) (e : String) : IO Judged := do
  let a := arg args
  match fn with
  | "doi" => return judge e (single doiOf) (doiNorm (← a "text"))
  | "shape" => return judge e (single fun l => (oneOf "shape" l).bind bool?) (doiShape (← a "text"))
  | "arxiv" => return judge e (single arxivOf) (arxivParse (← a "text"))
  | "isbn" => return judge e (single isbnOf) (isbnCheck (← a "text"))
  | "issn" => return judge e (single (oneOf "issn")) (issnCheck (← a "text"))
  | "pmid" => return judge e (single (oneOf "pmid")) (pmidCheck (← a "text"))
  | "pmcid" => return judge e (single (oneOf "pmcid")) (pmcidCheck (← a "text"))
  | "key" => return judge e (single (oneOf "key")) (keyForm (← a "text") (← a "kind"))
  | "dupe" =>
    return judge e (single fun
      | ["dupe", k, key] => some ({ kind := k, key } : Dupe)
      | _ => none) (dupeKey (← a "identifiers"))
  | "check" =>
    return judge e (fun t => checkOf (lines t)) (biblioCheck (← a "entry") (← a "existing") (← a "caps"))
  | "preimage" =>
    return judge e (single (oneOf "preimage")) (biblioPreimage (← a "bib_id") (← a "proposed_by")
      (← a "landed_by") (← a "landed") (← a "supersedes") (← a "identifiers") (← a "item"))
  | "canon" =>
    let got := biblioCanon (← a "bib_id") (← a "proposed_by") (← a "landed_by")
      (← a "landed") (← a "supersedes") (← a "identifiers") (← a "item")
    let readCanon (t : String) : Option CanonEntry := match lines t with
      | [["canon", digest], [text]] => some { text, digest }
      | _ => none
    return judge e readCanon got
  | "url" => return judge e (single (oneOf "url")) (registryUrl (← a "declaration") (← a "identifier"))
  | "compare" =>
    let (entry, records, date) := (← a "entry", ← a "records", ← a "date")
    let got : Check (Comparison × String × String) := do
      let c ← biblioCompare entry records
      return (c, ← checkLine c date, ← noticesLine c date)
    return judge e (fun t => compareOf (lines t)) got (fun (c, _, _) => c.results.flatMap (·.fields))
  | "withdrawn" =>
    return judge e (single fun l => (oneOf "withdrawn" l).bind bool?) (arxivWithdrawn (← a "comment"))
  | "view" =>
    return judge e (fun t => viewOf (lines t))
      (literatureView (← a "records") (← a "entries") (← a "findings")) (fun v => v.forHdecl)
  | "holdlist" =>
    return judge e (fun t => holdListOf (lines t))
      (biblioHoldList (← a "entries") (← a "account") (← a "blocks") (← a "checks"))
  | other => throw (IO.userError s!"unknown function {other}")

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

def runTable : IO (Nat × Nat) := do
  let src ← IO.FS.readFile "docs/v1/tpc_py/tpc_biblio.py"
  let mut pass := 0
  let mut fail := 0
  let checks : List (Bool × String) := [
    (v1Table src == some utable, "utable equals v1's _UTABLE, character for character"),
    (table.length == (utable.splitOn ";").length, "every item of the table reads"),
    ((table.zip table.tail).all (fun ((_, b, _), (c, _, _)) => b < c) &&
      table.all (fun (a, b, _) => a ≤ b), "the ranges increase without overlap"),
    (src.contains tableSha256 && src.contains tableUnicodeVersion,
      "the recorded SHA-256 and Unicode version are v1's")]
  for (ok, what) in checks do
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL biblio_table: {what}"
      fail := fail + 1
  return (pass, fail)

/-! ## The corpus -/

/-- Run the corpus: passes and failures; owed cases are counted, printed, and checked against
the owed list. -/
def runBiblio : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/biblio_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/biblio_corpus.owed.json"))
  let owedList ← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)
  let listed ← owedList.toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")),
          (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String × String) := []
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let e ← IO.ofExcept (c.getObjValAs? String "expected")
    match ← runCase fn (← IO.ofExcept (c.getObjVal? "args")) e with
    | .pass => pass := pass + 1
    | .fail why =>
      IO.eprintln s!"FAIL biblio {name}:\n  expected {e}\n  {why}"
      fail := fail + 1
    | .owed reason => owed := owed ++ [(name, fn, reason)]
  for (name, _, why) in owed do
    unless listed.contains (name, why) do
      IO.eprintln s!"FAIL biblio {name}: owed ({why}) but not listed so in vectors/biblio_corpus.owed.json"
      fail := fail + 1
  for (name, why) in listed do
    unless owed.any (fun (n, _, w) => n == name && w == why) do
      IO.eprintln s!"FAIL biblio {name}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  IO.println s!"biblio: {owed.length} owed; the canonical entries' digests SHA-256, compared with v1's"
  return (pass, fail)

/-! ## `vectors/biblio_recheck_urls.json`: the recheck's first call

Each case's `request` goes through `biblio recheck_urls`, read with the Calculator's own reader.
An `expected` answer is compared as canonical JSON; a `refused` case must be refused with that
code and that detail. No case is owed. -/

/-- A member of a value read by the Calculator's reader. -/
def member (v : Principia.Canonical.Value) (k : String) : Option Principia.Canonical.Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

/-- Run `biblio_recheck_urls.json`: the counts of cases passed and failed. -/
def runRecheckUrls : IO (Nat × Nat) := do
  let file ← match Principia.Canonical.readString (← IO.FS.readFile "vectors/biblio_recheck_urls.json") with
    | .ok v => pure v
    | .error _ => throw (IO.userError "biblio_recheck_urls.json: refused by the reader")
  let cases ← match member file "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError "biblio_recheck_urls.json: no cases")
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let some (.str name) := member c "name" | throw (IO.userError "a case without a name")
    let some request := member c "request" | throw (IO.userError s!"{name}: no request")
    let got := Principia.Calculator.respondTo "biblio" "recheck_urls" request
    let ok : Bool := match got, member c "expected", member c "refused" with
      | .ok v, some e, none => v.canonicalJson.isSome && v.canonicalJson == e.canonicalJson
      | .error r, none, some (.str w) =>
        r.code.word == w && (match member c "detail" with | some (.str d) => d == r.detail | _ => false)
      | _, _, _ => false
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL biblio_recheck_urls {name}: got {repr (match got with | .ok v => v.canonicalJson | .error r => some r.detail)}"
      fail := fail + 1
  if cases.isEmpty then
    IO.eprintln "FAIL biblio_recheck_urls: the corpus checked nothing"
    fail := fail + 1
  return (pass, fail)

end Tests.Biblio
