import Tests.Calculator.Common

/-!
The Calculator's runners of the family `eom`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

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

/-- `register_structure_test.json`: every case's request through `eom register_structure_test`,
its answer's canonical JSON equal to the case's `expected`, which version 1's reference functions
computed (`scripts/register_structure_vectors.py`). No case is owed. -/
def runRegisterStructureCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/register_structure_test.json" do
    let name ← memberStr c "name"
    let expect ← memberStr c "expected"
    let some args := member c "input" | throw (IO.userError s!"{name}: no input")
    let got := respondTo "eom" "register_structure_test" args
    let ok := match got with
      | .ok v => v.canonicalJson == some expect
      | .error _ => false
    t ← t.check ok
      s!"eom register_structure_test {name}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Eom

open Tests.Calculator

/-- The family `eom`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc eom (eom, settlement)", runEomCalls),
  ("pcalc eom (register structure test)", runRegisterStructureCalls),
]

end Tests.Calculator.Eom
