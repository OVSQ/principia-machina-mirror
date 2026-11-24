import Tests.Calculator.Common

/-!
The Calculator's runners of the family `units`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

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

end Tests.Calculator

namespace Tests.Calculator.Units

open Tests.Calculator

/-- The family `units`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc units (units_corpus, units_range, units_pi)", runUnitsCalls),
]

end Tests.Calculator.Units
