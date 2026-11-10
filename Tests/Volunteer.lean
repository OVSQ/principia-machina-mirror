import Principia

/-!
The volunteer family's runner: v1's `volunteer_corpus.json` (202 cases), through
`Calculator.respondTo "volunteer"`.

A case is `{"name", "fn", "args", "hand_checked", "expected"}`, `expected` v1's text of the
answer: its render (`render_standing`, `render_bucket`, ..., `render_draw`), or `ERROR:` and
v1's message. The request is read by the Calculator's own reader, which keeps a number's kind
(`2.0` a float, `2` an int), and the answer's text, or `ERROR:` and a `BAD_ARGUMENT`
refusal's detail, is compared byte for byte; numbers that v1 printed with `%.12g` are the
exact values correctly rounded to twelve significant digits.

A case whose double fell otherwise than the exact value is listed in
`vectors/volunteer_corpus.divergences.json` (`{"divergences": [{"name", "got", "reason"}]}`),
when that file is present: a listed case must answer exactly the listed text and differ from
v1's, and every case not listed must agree with v1's.
-/

namespace Tests.Volunteer

open Principia Principia.Canonical

def member (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

def memberStr (v : Value) (k : String) : IO String :=
  match member v k with
  | some (.str s) => pure s
  | _ => throw (IO.userError s!"no string {k}")

/-- A JSON file read by the Calculator's reader: the list under `key`. -/
def listIn (path : System.FilePath) (key : String) : IO (List Value) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup key with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError s!"{path}: no list {key}")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- The recorded divergences: name, the Calculator's text, the reason. -/
def divergences : IO (List (String × String × String)) := do
  let path : System.FilePath := "vectors/volunteer_corpus.divergences.json"
  unless ← path.pathExists do return []
  (← listIn path "divergences").mapM fun d => do
    pure (← memberStr d "name", ← memberStr d "got", ← memberStr d "reason")

/-- An answer's text as v1 wrote it, or none for an answer of another form. -/
def text : Except Calculator.Refusal Value → Option String
  | .ok (.str s) => some s
  | .error r => if r.code == .badArgument then some ("ERROR:" ++ r.detail) else none
  | _ => none

def runVolunteer : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let mut agree := 0
  let mut diverged := 0
  let listed ← divergences
  let cases ← listIn "vectors/volunteer_corpus.json" "cases"
  let names ← cases.mapM fun c => memberStr c "name"
  for (n, _, _) in listed do
    unless names.contains n do
      IO.eprintln s!"FAIL volunteer divergence {n}: no such case"
      fail := fail + 1
  for c in cases do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := text (Calculator.respondTo "volunteer" fn args)
    match listed.find? (·.1 == name) with
    | some (_, want, _) =>
      if got == some want && want != expected then
        pass := pass + 1
        diverged := diverged + 1
      else
        IO.eprintln s!"FAIL volunteer {fn} {name}: listed as diverging with {repr want}, got {repr got}, v1 {repr expected}"
        fail := fail + 1
    | none =>
      if got == some expected then
        pass := pass + 1
        agree := agree + 1
      else
        IO.eprintln s!"FAIL volunteer {fn} {name}: expected {repr expected}, got {repr got}"
        fail := fail + 1
  IO.println s!"volunteer_corpus: {cases.length} cases, {agree} agree with v1, {diverged} recorded divergences, {fail} fail"
  return (pass, fail)

end Tests.Volunteer
