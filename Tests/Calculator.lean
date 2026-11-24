import Tests.Calculator.Common
import Tests.Calculator.Biblio
import Tests.Calculator.Cluster
import Tests.Calculator.Derivation
import Tests.Calculator.Digest
import Tests.Calculator.Eom
import Tests.Calculator.Falcon
import Tests.Calculator.Form
import Tests.Calculator.Fundamental
import Tests.Calculator.Governor
import Tests.Calculator.Hold
import Tests.Calculator.Identity
import Tests.Calculator.Interface
import Tests.Calculator.Landing
import Tests.Calculator.Lint
import Tests.Calculator.Permissions
import Tests.Calculator.Probe
import Tests.Calculator.Provision
import Tests.Calculator.Record
import Tests.Calculator.Score
import Tests.Calculator.Sha256
import Tests.Calculator.Sponsor
import Tests.Calculator.Sr9
import Tests.Calculator.Strike
import Tests.Calculator.Unicode
import Tests.Calculator.Units
import Tests.Calculator.Yardstick
import Tests.Calculator.Zone

/-!
The vectors of the Calculator's interface: the JSON reader (`vectors/json_text.json`,
`Canonical.readText`) and the dispatch of `pcalc <family> <function>`
(`vectors/pcalc.json`, `Calculator.answer`), both run in-process: a case's stdin is
given to `answer` as bytes, and its stdout and exit code compared byte for byte.
The runners live one file per family under `Tests/Calculator/`; `runners` below gathers them
for `Tests/Main.lean`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## pcalc.json: the dispatch -/

def runPcalc : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/pcalc.json") do
    let what := (← field c "args").compress
    let args ← (← arr (← field c "args")).mapM fun a => IO.ofExcept a.getStr?
    -- An answer too long for a line (the permissions table) is given by the file
    -- that records its digest, `stdout_sha256_file` (custos/permits.sha256), read here at test
    -- time: the SHA-256 of the answer's text equals the file's line. A change to the Lean that
    -- moves the table turns this case red, and its fix changes `custos/**`, the paths of the
    -- check that compares custos/permits.json with the built binary byte for byte.
    let digestFile := (c.getObjValAs? String "stdout_sha256_file").toOption
    let digest ← match digestFile with
      | some path => do
          let line := ((← IO.FS.readFile path).replace "\r" "").trimAsciiEnd.toString
          pure (some line)
      | none => pure none
    let stdout ← match digest with
      | some _ => pure ""
      | none => str c "stdout"
    let exit ← IO.ofExcept (c.getObjValAs? Nat "exit")
    let got := match args with
      | [family, function] => fun bytes => answer family function bytes
      | _ => fun _ => usage
    let (out, code) := got (← input c "stdin" "stdin_hex")
    let same := match digest with
      | some d => Principia.Sha256.digestText out == d
      | none => out == stdout
    t ← t.check (same && code.toNat == exit)
      s!"pcalc {what}: expected {repr (digest.getD stdout)} exit {exit}, got {repr (if digest.isSome then Principia.Sha256.digestText out else out)} exit {code}"
  return t.pair

/-- Every function of every family of `Calculator.families` has at least one pair in
`pcalc.json`, whatever its answer: a function without one fails, naming the family and the
function. The line it prints on success counts the families, so a family added to the list is
counted without this check changing. -/
def runPcalcCoverage : IO (Nat × Nat) := do
  let mut pairs : List (String × String) := []
  for c in ← arr (← readJson "vectors/pcalc.json") do
    let args ← (← arr (← field c "args")).mapM fun a => IO.ofExcept a.getStr?
    match args with
    | [family, function] => pairs := (family, function) :: pairs
    | _ => pure ()
  let mut t : Counts := {}
  for (family, calls) in families do
    for (function, _) in calls do
      t ← t.check (pairs.contains (family, function))
        s!"pcalc.json: no pair for {family} {function}"
  if t.fail == 0 then
    IO.println s!"pcalc.json: every function of the {families.length} families has a pair"
  return t.pair

/-- The dispatch's own runners, over `vectors/pcalc.json`. -/
def own : List (String × IO (Nat × Nat)) := [
  ("pcalc", runPcalc),
  ("pcalc coverage (pcalc.json)", runPcalcCoverage),
]

/-- Every runner of the Calculator's tests, the families' and the dispatch's, sorted by name in
code point order. -/
def runners : List (String × IO (Nat × Nat)) :=
  (Tests.Calculator.Biblio.runners ++
    Tests.Calculator.Cluster.runners ++
    Tests.Calculator.Derivation.runners ++
    Tests.Calculator.Digest.runners ++
    Tests.Calculator.Eom.runners ++
    Tests.Calculator.Falcon.runners ++
    Tests.Calculator.Form.runners ++
    Tests.Calculator.Fundamental.runners ++
    Tests.Calculator.Governor.runners ++
    Tests.Calculator.Hold.runners ++
    Tests.Calculator.Identity.runners ++
    Tests.Calculator.Interface.runners ++
    Tests.Calculator.Landing.runners ++
    Tests.Calculator.Lint.runners ++
    Tests.Calculator.Permissions.runners ++
    Tests.Calculator.Probe.runners ++
    Tests.Calculator.Provision.runners ++
    Tests.Calculator.Record.runners ++
    Tests.Calculator.Score.runners ++
    Tests.Calculator.Sha256.runners ++
    Tests.Calculator.Sponsor.runners ++
    Tests.Calculator.Sr9.runners ++
    Tests.Calculator.Strike.runners ++
    Tests.Calculator.Unicode.runners ++
    Tests.Calculator.Units.runners ++
    Tests.Calculator.Yardstick.runners ++
    Tests.Calculator.Zone.runners ++
    own).mergeSort fun a b => a.1 ≤ b.1

end Tests.Calculator
