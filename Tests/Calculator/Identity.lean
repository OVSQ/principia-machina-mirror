import Tests.Calculator.Common

/-!
The Calculator's runners of the family `identity`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

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

end Tests.Calculator

namespace Tests.Calculator.Identity

open Tests.Calculator

/-- The family `identity`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc identity (identity_corpus)", runIdentityCalls),
]

end Tests.Calculator.Identity
