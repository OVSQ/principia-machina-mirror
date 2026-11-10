import Principia
import Lean.Data.Json
import Tests.Beta
import Tests.Score

/-!
The runner of `vectors/sponsor_corpus.json` (v1's `tpc_sponsor` 0.1.0, corpus 0.1.0, 83
cases), against `Principia.Sponsor`.

Each case is `{name, fn, args, expected}`, `expected` being v1's `run_case` text: the
function's `render_*` line or lines, or `ERROR:<word>`. Each argument is read as the
Calculator reads a request (`Canonical.Value`). The Calculator's typed outcome is written in
v1's form and compared with v1's text line by line and field by field (`Tests.Score.agrees`):
each field a wire word read back from its typed enumeration, an integer, a number in the
twelve-digit form of the Calculator's exact value rounded once, or an agent name escaped as
v1's `_esc` escapes it, so that a name holding `|` cannot pass for two fields.

No case is owed and none diverges: an owed case (a number whose bounds do not settle) or
a difference from v1's text fails the run. On every number the corpus prints, v1's double
and the Calculator's exact value round to the same twelve digits.

The runner also measures the size of the exact values, as `Tests/Score.lean` does: the most
bits of a numerator and of a denominator among each case's arguments and every number of
its answer, printed with the case that reaches it.
-/

open Lean
open Principia
open Principia.Beta
open Principia.Score
open Principia.Sponsor
open Tests.Beta (toValue arg field)
open Tests.Score (Outcome esc written withNumbers powValues agrees fieldsOf Sizes valueRats)

namespace Tests.Sponsor

/-- A wire word. -/
def wire {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a

/-! ## The functions, written as v1's `render_*` -/

/-- v1 `render_resolve`. -/
def resolveText (r : Resolved) : String := wire r.1 ++ "|" ++ wire r.2

def runResolve (a : String → Canonical.Value) : Outcome :=
  written (conductResolve (a "event") (a "facts")) fun r => .text (resolveText r) []

/-- The exact rationals of a posterior: `F_u`, `A_u` and `E_u` when it is rational. -/
def posteriorValues (r : Posterior) : List Rat :=
  powValues r.f ++ powValues r.a ++ (match r.e with | .exact q => [q] | _ => [])

/-- v1 `render_evidence`, with a prefix (`OK|` for the score's `render_user_evidence`). -/
def posteriorText (pre : String) (r : Posterior) : Outcome :=
  withNumbers [r.f.toQuantity, r.a.toQuantity, r.e, r.lo, r.hi] (fun ts =>
    match ts with
    | [f, aa, e, lo, hi] => pre ++ "|".intercalate [f, aa, toString r.n, e, lo, hi]
    | _ => "")
    (posteriorValues r)

def runEvidence (a : String → Canonical.Value) : Outcome :=
  written (userEvidence (a "events") (a "ages") (a "g") (a "h") (a "a0") (a "b0") (a "half_life"))
    (posteriorText "")

/-- v1 `render_whitewash`. -/
def whitewashText (ms : List (String × String)) : String :=
  "\n".intercalate (s!"count|{ms.length}" :: ms.map fun (adm, ret) => s!"match|{esc adm}|{esc ret}")

def runWhitewash (a : String → Canonical.Value) : Outcome :=
  written (whitewashCount (a "admissions") (a "retirements") (a "states") (a "window")) fun ms =>
    .text (whitewashText ms) []

/-- The Calculator's outcome on a case. -/
def run (fn : String) (args : Json) : IO Outcome := do
  let a := arg args
  match fn with
  | "resolve" => return runResolve a
  | "evidence" => return runEvidence a
  | "whitewash" => return runWhitewash a
  | other => throw (IO.userError s!"sponsor: no runner for {other}")

/-- Each check is `true` when the comparison does what it must: an agent named `N|1` is one
field, an unescaped bar is refused, swapped numbers are refused, a missing match line is
refused. -/
def mutationChecks : List (String × Bool) :=
  let t := whitewashText [("N|1", "A")]
  [("the whitewash text as written is accepted", agrees t t),
   ("an escaped name is one field", (fieldsOf "match|N\\|1|A").length == 3),
   ("an unescaped bar in a name is refused", !agrees "count|1\nmatch|N|1|A" t),
   ("a missing match line is refused", !agrees "count|1" t),
   ("swapped numbers are refused", !agrees "1|0|1|0.666666666667|0.158113883008|0.987420882907"
     "0|1|1|0.666666666667|0.158113883008|0.987420882907")]

/-! ## The run -/

/-- Run the corpus: passes and failures. -/
def runSponsor : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for (what, ok) in mutationChecks do
    unless ok do
      IO.eprintln s!"FAIL sponsor runner mutation check: {what}"
      fail := fail + 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/sponsor_corpus.json"))
  let cases ← IO.ofExcept ((← field json "cases").getArr?)
  let mut sizes : Sizes := {}
  let mut perFn : List (String × Nat) := []
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let args ← field c "args"
    sizes := sizes.add name (valueRats (toValue args))
    match ← run fn args with
    | .owed why =>
      IO.eprintln s!"FAIL sponsor {name}: owed ({why}); the corpus has no owed case"
      fail := fail + 1
    | .text mine values =>
      sizes := sizes.add name values
      if agrees expected mine then
        pass := pass + 1
        perFn := match perFn.find? (·.1 == fn) with
          | some _ => perFn.map fun (k, n) => if k == fn then (k, n + 1) else (k, n)
          | none => perFn ++ [(fn, 1)]
      else
        IO.eprintln s!"FAIL sponsor {name} ({fn}):\n  expected {repr expected}\n  got      {repr mine}"
        fail := fail + 1
  let counts := perFn.map fun (k, n) => s!"{k} {n}"
  IO.println s!"sponsor_corpus: {pass} pass, no divergence, none owed; {", ".intercalate counts}"
  IO.println s!"sponsor: the largest exact value has a numerator of {sizes.num} bits ({sizes.numCase}) and a denominator of {sizes.den} bits ({sizes.denCase})"
  return (pass, fail)

end Tests.Sponsor
