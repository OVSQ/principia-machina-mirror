import Tests.Calculator.Common

/-!
The Calculator's runners of the family `sr9`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

def runSr9Calls : IO (Nat × Nat) := runCanonCalls "sr9" "vectors/sr9_corpus.json"

end Tests.Calculator

namespace Tests.Calculator.Sr9

open Tests.Calculator

/-- The family `sr9`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc sr9 (sr9_corpus)", runSr9Calls),
]

end Tests.Calculator.Sr9
