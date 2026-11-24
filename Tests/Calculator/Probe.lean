import Tests.Calculator.Common

/-!
The Calculator's runners of the family `probe`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

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

end Tests.Calculator

namespace Tests.Calculator.Probe

open Tests.Calculator

/-- The family `probe`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc probe (probe_corpus)", runProbeCalls),
]

end Tests.Calculator.Probe
