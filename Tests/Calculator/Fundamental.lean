import Tests.Calculator.Common

/-!
The Calculator's runners of the family `fundamental`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The fundamental tests through `pcalc` -/

/-- `tests_corpus.json`: all its cases through `fundamental <fn>`, version 1's
`kernel_tests` spelled `fundamental_tests`; version 1's `canon` text of the answer
compared with `expect`. None is owed, and none refused. -/
def runFundamentalCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/tests_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := if v1 == "kernel_tests" then "fundamental_tests" else v1
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "fundamental" fn input
    let ok := match got with
      | .ok v => v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"fundamental {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The fundamental family's bounds (`Calculator.Fundamental`), each at its value and one
past it. -/
def runFundamentalBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("DOF at 64", "fundamental_tests", .obj [("tpk", dofTpk 64)], false),
    ("DOF past 64", "fundamental_tests", .obj [("tpk", dofTpk 65)], true),
    ("DOF past 64, T5", "t5_dof_yield", .obj [("tpk", dofTpk 65)], true),
    ("a PROPOSITION at 16384 code points", "t2_findings", .obj [("prop", .str (codePoints 16384))], false),
    ("a PROPOSITION past 16384 code points", "t2_findings", .obj [("prop", .str (codePoints 16385))], true),
    -- "tfk" holds 3 code points; eight strings of 16,384 and one of 1 reach 131,075.
    ("text at 131072 code points in all", "final_checks",
      .obj [("tfk", .arr (textsOf (131072 - 3)))], false),
    ("text past 131072 code points in all", "final_checks",
      .obj [("tfk", .arr (textsOf (131073 - 3)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "fundamental" fn request
    t ← t.check (boundRefusal got == refused)
      s!"fundamental {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Fundamental

open Tests.Calculator

/-- The family `fundamental`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc fundamental (tests_corpus)", runFundamentalCalls),
  ("pcalc fundamental bounds", runFundamentalBounds),
]

end Tests.Calculator.Fundamental
