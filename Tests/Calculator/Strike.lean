import Tests.Calculator.Common

/-!
The Calculator's runners of the family `strike`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

def runStrikeCalls : IO (Nat × Nat) := do
  let (p1, f1) ← runCanonCalls "strike" "vectors/strike_corpus.json"
  let (p2, f2) ← runCanonCalls "strike" "vectors/sr8_order_corpus.json"
  return (p1 + p2, f1 + f2)

/-- `sr3_scope_corpus.json`: every case's `input` through `strike sr3_scope`. v1's text of
the answer, a word or `[REFUSED,<reason>]`, is read back into its kind
(`Tests.Strike.sr3Expect`) and compared with the answer, the word as a string or v1's
refusal as the value `["REFUSED", reason]`; none is refused by `pcalc`. -/
def runSr3ScopeCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/sr3_scope_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "strike" "sr3_scope" input
    let ok := match got, Tests.Strike.sr3Expect expect with
      | .ok (.str w), .ok w' => w == w'
      | .ok (.arr [.str "REFUSED", .str r]), .error r' => r == r'
      | _, _ => false
    t ← t.check ok s!"strike sr3_scope {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `conditions_corpus.json`: every case's `args` through `strike <fn>` (`conditions_of`,
`comparison_set`, `sr8_groups`); the answer's canonical JSON is the case's `expected`, v1's
`["OK", ...]` or `["REFUSED", [[code, field, message]]]` as TPM's canonical JSON writes it,
which quotes every string; none is refused by `pcalc`, and none is owed. -/
def runConditionsCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/conditions_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "strike" fn args
    let ok := match got with
      | .ok v => v.canonicalJson == some expected
      | .error _ => false
    t ← t.check ok s!"strike {fn} {name}: expected {expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Strike

open Tests.Calculator

/-- The family `strike`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc strike (conditions_corpus)", runConditionsCalls),
  ("pcalc strike (sr3_scope_corpus)", runSr3ScopeCalls),
  ("pcalc strike (strike, sr8_order)", runStrikeCalls),
]

end Tests.Calculator.Strike
