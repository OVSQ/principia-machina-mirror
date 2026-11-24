import Tests.Calculator.Common

/-!
The Calculator's runners of the family `landing`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

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

end Tests.Calculator

namespace Tests.Calculator.Landing

open Tests.Calculator

/-- The family `landing`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc landing (landing_screen)", runLandingCalls),
]

end Tests.Calculator.Landing
