import Tests.Calculator.Common

/-!
The Calculator's runners of the family `sponsor`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- v1's names of the sponsor functions in `sponsor_corpus.json` (`run_case`), and the
Calculator's. -/
def sponsorFunctions : List (String × String) :=
  [("evidence", "user_evidence"), ("resolve", "conduct_resolve"), ("whitewash", "whitewash_count")]

/-- `sponsor_corpus.json`: every case through `sponsor <function>`; none is owed. -/
def runSponsorCalls : IO (Nat × Nat) :=
  runTextCalls "sponsor" "vectors/sponsor_corpus.json" [] sponsorFunctions (respondTo "sponsor")

end Tests.Calculator

namespace Tests.Calculator.Sponsor

open Tests.Calculator

/-- The family `sponsor`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc sponsor (sponsor_corpus)", runSponsorCalls),
]

end Tests.Calculator.Sponsor
