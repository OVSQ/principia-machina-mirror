import Tests.Calculator.Common

/-!
The Calculator's runners of the family `lint`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- v1's names of the lint's functions in `lint_corpus.json` (`run_case`), and the
Calculator's. -/
def lintFunctions : List (String × String) :=
  [("counts", "counts"), ("counts_of", "lint_counts"), ("lint", "lint"), ("norm", "lint_norm"),
   ("tables", "tables"), ("tokens", "name_tokens")]

/-- `lint_corpus.json`: every case through `lint <function>`; the owed list,
`lint_corpus.owed.json`, names none. -/
def runLintCalls : IO (Nat × Nat) := do
  runTextCalls "lint" "vectors/lint_corpus.json" (← owedNames "vectors/lint_corpus.owed.json")
    lintFunctions (respondTo "lint")

end Tests.Calculator

namespace Tests.Calculator.Lint

open Tests.Calculator

/-- The family `lint`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc lint (lint_corpus)", runLintCalls),
]

end Tests.Calculator.Lint
