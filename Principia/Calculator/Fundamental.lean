import Principia.Calculator.Interface
import Principia.Calculator.Record
import Principia.StartingSet.Tests
import Principia.Correspondence.Isomorphism
import Principia.ResearchAssembly
import Principia.Strike.Conditions

/-!
# Family `fundamental`: the fundamental tests and the isomorphism checks

Version 1's `tpc_tests` 0.2.1 on the command line, its arguments named as version 1's corpus
(the fundamental tests' corpus) names them, the run spelled `fundamental_tests` (version 1's
`kernel_tests`):

* `t2_findings {"prop"}`: T2's findings on one PROPOSITION, a list of texts.
* `t2_atomicity {"tpk"}`, `t5_dof_yield {"tpk"}`, `t3_consistency {"tpk", "tms"}`:
  `[pass, problems]`.
* `fundamental_tests {"tpk"}`: `[pass, rows, inspections]`, each row `[test, state,
  problems]`, the state `true`, `false`, `NOT_RUN` or `NO FORM`.
* `ic_checks {"trm", "tpk"}`, `final_checks {"tfk"}`: `[verdict, problems, gaps]`.

Each zone is read as the zones read JSON (`Strike.toZoneValue`). An answer the Calculator owes
(a zone check owed, a value's twelve digits not decided, an exact value past the bounds) is
refused `OWED`, its detail saying what it waits on; version 1's corpus has none.

Bounds, as the `eom` family's: at most `maxEntries` entries in each of the Starting Set's
kinds (and in each list of the request), and every string, a form included, at most
`maxText` code points; 131,072 code points in all.
-/

namespace Principia.Calculator.Fundamental

open Principia.Canonical
open Principia.StartingSet.Tests

/-- The most entries a list or an object of a request holds, at any depth: the `eom`
family's 64 entries per kind of the Starting Set. T3 compares the FIX values pair by pair. -/
def maxEntries : Nat := 64

/-- The most code points a string of a request holds: a form of 4096 code points after NFC
is the declared forms' bound, read here before NFC, as `eom`'s `maxEquation`. -/
def maxText : Nat := 16384

/-- The most code points the strings of a request hold in all. -/
def maxTextTotal : Nat := 131072

/-- A request within `maxEntries`, `maxText` and `maxTextTotal`. -/
def within (v : Value) : Except Refusal Unit := do
  let s := Record.valueSize v
  if maxEntries < s.entries then
    badArgument s!"a list or an object of the request holds more than {maxEntries} entries (the Calculator's bound)"
  if maxText < s.longest then
    badArgument s!"a string of the request holds more than {maxText} code points (the Calculator's bound)"
  if maxTextTotal < s.text then
    badArgument s!"the strings of the request hold more than {maxTextTotal} code points in all (the Calculator's bound)"

/-- An argument as the zones read it. -/
def zoneOf (v : Value) : Principia.Zone.Value := Principia.Strike.toZoneValue v

/-- A list of texts. -/
def strs (xs : List String) : Value := .arr (xs.map .str)

/-- `[pass, problems]`. -/
def passProblems (ps : List String) : Value := .arr [.bool ps.isEmpty, strs ps]

/-- A row's state as version 1 wrote it. -/
def stateValue : TestState → Value
  | .ran b => .bool b
  | .notRun => .str "NOT_RUN"
  | .noForm => .str "NO FORM"

/-- The run's answer: `[pass, rows, inspections]`. -/
def runValue (r : Run) : Value :=
  .arr [.bool r.pass,
    .arr (r.rows.map fun row => .arr [.str row.test, stateValue row.state, strs row.problems]),
    strs r.inspections]

/-- An isomorphism check's answer: `[verdict, problems, gaps]`. -/
def icValue (r : Correspondence.IcResult) : Value :=
  .arr [.str r.verdict.word, strs r.problems, strs r.gaps]

/-- An owed answer's detail, in plain words. -/
def owedDetail (o : Owing) : String :=
  "the fundamental tests do not compute this answer yet: " ++ o.message

/-- An answer as `pcalc` gives it, or the refusal `OWED`. -/
def answer {α : Type} (f : α → Value) : Except Owing α → Except Refusal Value
  | .ok a => .ok (f a)
  | .error o => .error ⟨.owed, owedDetail o⟩

/-- The family's functions. -/
def calls : Family := [
  ("final_checks", fun v => do
    within v
    answer icValue (ResearchAssembly.finalChecks (zoneOf (← argument1 "tfk" v)))),
  ("fundamental_tests", fun v => do
    within v
    answer runValue (fundamentalTests (zoneOf (← argument1 "tpk" v)))),
  ("ic_checks", fun v => do
    within v
    let (trm, tpk) ← argument2 "trm" "tpk" v
    answer icValue (Correspondence.isomorphismChecks (zoneOf trm) (zoneOf tpk))),
  ("t2_atomicity", fun v => do
    within v
    pure (passProblems (t2Atomicity (zoneOf (← argument1 "tpk" v))))),
  ("t2_findings", fun v => do
    within v
    pure (strs (t2Findings (← asString "prop" (← argument1 "prop" v))))),
  ("t3_consistency", fun v => do
    within v
    let (tpk, tms) ← argument2 "tpk" "tms" v
    answer passProblems (t3Consistency (zoneOf tpk) (zoneOf tms))),
  ("t5_dof_yield", fun v => do
    within v
    pure (passProblems (t5DofYield (zoneOf (← argument1 "tpk" v))))),
]

end Principia.Calculator.Fundamental
