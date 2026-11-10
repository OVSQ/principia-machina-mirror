import Principia
import Lean.Data.Json
import Tests.Zone
import Tests.Strike

/-!
The structure check's runner: v1's `eom_corpus.json` (421 cases: `eom_findings`,
`eom_class`, `eom_map`, `eom_register_test`) against `Principia.Eom`, and
`settlement_corpus.json` (17 cases, `settlement_check`).

`eom_corpus.json`'s `expect` is v1's `canon` text of the answer, written here by the
canonical serialization (`Canonical.Value.canon`). Its structure is the answer's type; its
strings are compared within the text, and a question's commas are its own (v1's `canon`
writes a string unquoted, so this comparison is as strong as v1's text allows).
`settlement_corpus.json`'s `expected` is TPM's canonical JSON, which quotes every string.

Forms are read by the declared forms' parser (`FormHook.calculator`). A case the
Calculator owes (a form the declared forms owe) is neither a pass nor a failure; it must be
listed, with its reason, in `vectors/<corpus>.owed.json`, and every case listed there must
come out owed for that reason.
-/

namespace Tests.Eom

open Lean
open Principia
open Principia.Eom

/-- The declared forms' parser the check runs with. -/
def forms : FormHook := FormHook.calculator

/-- An owed reason as the owed lists spell it, the zones' words. -/
def owedWord (msg : String) : String :=
  if msg == Zone.Owed.forms.message then "forms" else msg

/-- An owed list: `(id, reason)`. -/
def loadOwed (path : System.FilePath) : IO (List (String × String)) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let owed ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "owed")).getArr?)
  owed.toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")), (← IO.ofExcept (o.getObjValAs? String "reason")))

/-- The owed cases are exactly the listed ones, each for its listed reason: the failures. -/
def checkOwed (corpus : String) (owed listed : List (String × String)) : IO Nat := do
  let mut fail := 0
  for (id, why) in owed do
    unless listed.contains (id, why) do
      IO.eprintln s!"FAIL {corpus} {id}: owed ({why}) but not listed so in vectors/{corpus}.owed.json"
      fail := fail + 1
  for (id, why) in listed do
    unless owed.contains (id, why) do
      IO.eprintln s!"FAIL {corpus} {id}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  return fail

def runEom : IO (Nat × Nat) := do
  let listed ← loadOwed "vectors/eom_corpus.owed.json"
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String) := []
  for c in ← Tests.Strike.loadV1Cases "vectors/eom_corpus.json" do
    let id ← Tests.Strike.str (← Tests.Strike.field c "id")
    let fn ← Tests.Strike.str (← Tests.Strike.field c "fn")
    let input ← Tests.Strike.field c "input"
    let get (k : String) : Zone.Value :=
      ((input.getObjVal? k).toOption.map Tests.Zone.toValue).getD .null
    let r : Result ← match fn with
      | "eom_map" => pure (eomMap forms (get "tfk"))
      | "eom_findings" => pure (eomFindings forms (get "tfk"))
      | "eom_class" => pure (eomClass forms (get "tfk"))
      | "eom_register_test" => pure (eomRegisterTest forms (get "tfk") (get "records"))
      | other => throw (IO.userError s!"unknown function {other}")
    let exp ← Tests.Strike.str (← Tests.Strike.field c "expect")
    match r with
    | .error why => owed := owed ++ [(id, owedWord why)]
    | .ok v =>
      if v.canon == some exp then pass := pass + 1
      else
        IO.eprintln s!"FAIL eom {id}:\n  expected {exp}\n  got      {(v.canon).getD "(no text)"}"
        fail := fail + 1
  fail := fail + (← checkOwed "eom_corpus" owed listed)
  IO.println s!"eom: {owed.length} owed (declared forms {(owed.filter (·.2 == "forms")).length})"
  return (pass, fail)

def runSettlement : IO (Nat × Nat) := do
  let listed ← loadOwed "vectors/settlement_corpus.owed.json"
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String) := []
  for c in ← Tests.Strike.loadV1Cases "vectors/settlement_corpus.json" do
    let name ← Tests.Strike.str (← Tests.Strike.field c "name")
    let args ← Tests.Strike.field c "args"
    let arg (k : String) : Canonical.Value :=
      ((args.getObjVal? k).toOption.map Tests.Strike.toCanonical).getD .null
    let fn ← Tests.Strike.str (← Tests.Strike.field c "fn")
    unless fn == "settlement_check" do throw (IO.userError s!"unknown function {fn}")
    let exp ← Tests.Strike.str (← Tests.Strike.field c "expected")
    match settlementCheck forms (arg "tfk") (arg "records") (arg "words") (arg "naming") with
    | .error why => owed := owed ++ [(name, owedWord why)]
    | .ok v =>
      let text := v.canonicalJson
      if text == some exp then pass := pass + 1
      else
        IO.eprintln s!"FAIL settlement {name}:\n  expected {exp}\n  got      {text.getD "(no text)"}"
        fail := fail + 1
  fail := fail + (← checkOwed "settlement_corpus" owed listed)
  IO.println s!"settlement: {owed.length} owed (declared forms {(owed.filter (·.2 == "forms")).length})"
  return (pass, fail)

end Tests.Eom
