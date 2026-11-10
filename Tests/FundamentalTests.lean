import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/tests_corpus.json` (v1's `tpc_tests` 0.2.1, 120 cases): the
fundamental tests T2, T3, T5 and their run, the isomorphism checks and the final pass.
Each input is read into `Principia.Zone.Value` as v1's JSON reader gives it, each result
written as v1's `canon` writes it (`Principia.Canonical.Value.canon`) and compared with
the case's `expect`: its first item (a pass flag or a verdict word) as a value, and the
whole as v1's text. An owed case is neither a pass nor a failure: it must be listed with
its reason in `vectors/tests_corpus.owed.json`, and every case listed there must come
out owed for it.
-/

open Lean
open Principia
open Principia.Zone
open Principia.StartingSet.Tests

namespace Tests.FundamentalTests

abbrev CV := Principia.Canonical.Value

def strs (l : List String) : CV := .arr (l.map .str)

/-- A `[pass, problems]` result. -/
def passProblems (ps : List String) : CV := .arr [.bool ps.isEmpty, strs ps]

def stateValue : TestState → CV
  | .ran b => .bool b
  | .notRun => .str "NOT_RUN"
  | .noForm => .str "NO FORM"

def runValue (r : Run) : CV :=
  .arr [.bool r.pass, .arr (r.rows.map fun row => .arr [.str row.test, stateValue row.state, strs row.problems]),
    strs r.inspections]

def icValue (r : Correspondence.IcResult) : CV :=
  .arr [.str r.verdict.word, strs r.problems, strs r.gaps]

/-- The owed reason as the owed list spells it. -/
def owingWord : Owing → String
  | .zone o => Tests.Zone.owedWord o
  | .digits => "digits"
  | .exact what => "exact: " ++ what

def input (c : Json) (k : String) : IO Value := do
  pure (Tests.Zone.toValue (← IO.ofExcept ((← IO.ofExcept (c.getObjVal? "input")).getObjVal? k)))

/-- One case: the result as a canon value, or why it is owed. -/
def run (fn : String) (c : Json) : IO (Except Owing CV) := do
  match fn with
  | "t2_findings" =>
    let p ← IO.ofExcept ((← IO.ofExcept (c.getObjVal? "input")).getObjValAs? String "prop")
    pure (.ok (strs (t2Findings p)))
  | "t2_atomicity" => pure (.ok (passProblems (t2Atomicity (← input c "tpk"))))
  | "t3_consistency" => pure ((t3Consistency (← input c "tpk") (← input c "tms")).map passProblems)
  | "t5_dof_yield" => pure (.ok (passProblems (t5DofYield (← input c "tpk"))))
  | "kernel_tests" => pure ((fundamentalTests (← input c "tpk")).map runValue)
  | "ic_checks" => pure ((Correspondence.isomorphismChecks (← input c "trm") (← input c "tpk")).map icValue)
  | "final_checks" => pure ((ResearchAssembly.finalChecks (← input c "tfk")).map icValue)
  | _ => throw (IO.userError s!"unknown function {fn}")

/-- The first item of a canon list's text: a pass flag or a verdict word. -/
def headOf (t : String) : String := ((t.drop 1).toString.splitOn ",").headD ""

def runTests : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/tests_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/tests_corpus.owed.json"))
  let listed ← (← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String) := []
  for c in cases do
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let id ← IO.ofExcept (c.getObjValAs? String "id")
    let expect ← IO.ofExcept (c.getObjValAs? String "expect")
    match ← run fn c with
    | .error why => owed := owed ++ [(id, owingWord why)]
    | .ok v =>
      let got := v.canon.getD "(refused by canon)"
      -- t2_findings returns a bare list; every other function a list headed by a flag or a word.
      let headOk := fn == "t2_findings" || match v with
        | .arr (h :: _) => (Principia.Canonical.Value.canon h).getD "" == headOf expect
        | _ => false
      if got == expect && headOk then pass := pass + 1
      else
        IO.eprintln s!"FAIL tests {id}:\n  expected {repr expect}\n  got      {repr got}"
        fail := fail + 1
  for (id, why) in owed do
    unless listed.contains (id, why) do
      IO.eprintln s!"FAIL tests {id}: owed ({why}) but not listed so in vectors/tests_corpus.owed.json"
      fail := fail + 1
  for (id, why) in listed do
    unless owed.contains (id, why) do
      IO.eprintln s!"FAIL tests {id}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  let count (w : String) := (owed.filter (·.2.startsWith w)).length
  IO.println s!"tests: {owed.length} owed (declared forms {count "forms"}, digits {count "digits"})"
  return (pass, fail)

end Tests.FundamentalTests
