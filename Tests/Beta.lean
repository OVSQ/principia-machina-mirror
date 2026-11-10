import Principia
import Lean.Data.Json

/-!
The runner of `vectors/beta_corpus.json` (v1's `tpc_beta` 0.1.0, corpus 0.1.0, 99 cases),
against `Principia.Beta`.

Each case is `{name, fn, args, expected}`, `expected` being v1's `run_case` text: a number
in canon's twelve-digit form, two numbers joined by `|` for an interval, or `ERROR:<word>`.
Each argument is read as the Calculator reads a request (`Canonical.Value`: a JSON number
with a fraction or an exponent is a number, any other an integer). The outcome is compared
typed: a refusal by its word; each number as the twelve-digit form of the Calculator's
exact value, rounded once (`Principia.Beta.Quantity.twelve?`), against v1's field.

A case whose number the Calculator's bounds do not settle is owed (none here). A case where
the Calculator's answer departs from v1's is a recorded v2 divergence, listed in
`vectors/beta_corpus.divergences.json` with v1's text and the Calculator's, both checked;
an entry that stops applying fails.
-/

open Lean
open Principia
open Principia.Beta

namespace Tests.Beta

/-- A JSON value as the Calculator's reader gives it: a number with a fraction or an
exponent is a number (v1's float), any other an integer. -/
partial def toValue : Json → Canonical.Value
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent == 0 then .int n.mantissa else .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr a => .arr (a.toList.map toValue)
  | .obj kvs => .obj (kvs.foldl (fun acc k v => acc ++ [(k, toValue v)]) [])

/-- An argument, `null` when absent (v1 indexed the args object). -/
def arg (args : Json) (k : String) : Canonical.Value :=
  ((args.getObjVal? k).toOption.map toValue).getD .null

/-- What a case came to: the Calculator's text in v1's form, or owed. -/
inductive Outcome where
  | text (t : String)
  | owed (why : String)

/-- The reason an unsettled number is owed. -/
def unsettled : String :=
  "a number whose bounds up to 4096 bits do not settle its twelve digits"

/-- A refusal or a value, written as v1's `run_case` writes it. -/
def written {α : Type} (r : Except String α) (f : α → Outcome) : Outcome :=
  match r with
  | .error w => .text ("ERROR:" ++ w)
  | .ok a => f a

/-- One number. -/
def number (q : Quantity) : Outcome :=
  match q.twelve? with
  | some t => .text t
  | none => .owed unsettled

/-- The Calculator's outcome on a case. -/
def run (fn : String) (args : Json) : IO Outcome := do
  let a := arg args
  match fn with
  | "mean" => return written (betaMean (a "a") (a "b")) fun q => .text (Quantity.ratText q)
  | "interval" =>
    return written (betaInterval (a "a") (a "b") (a "level")) fun (lo, hi) =>
      match lo.twelve?, hi.twelve? with
      | some l, some h => .text (l ++ "|" ++ h)
      | _, _ => .owed unsettled
  | "betainc" => return written (betaincOf (a "a") (a "b") (a "x")) number
  | "betainc_inv" => return written (betaincInv (a "a") (a "b") (a "p")) number
  | "lgamma" => return written (lgammaOf (a "x")) number
  | "canon" => return written (canonOf (a "x")) fun q => .text (Quantity.ratText q)
  | other => throw (IO.userError s!"beta: no runner for {other}")

/-- v1's text against the Calculator's, field by field: the refusal word, or each `|` field,
which is a number's twelve-digit form and holds no `|`. -/
def agrees (expected mine : String) : Bool :=
  let a := expected.splitOn "|"
  let b := mine.splitOn "|"
  a.length == b.length && (a.zip b).all fun (x, y) => x == y

def field (j : Json) (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)

/-- Run the corpus: passes (recorded divergences among them) and failures. -/
def runBeta : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/beta_corpus.json"))
  let cases ← IO.ofExcept ((← field json "cases").getArr?)
  let divJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/beta_corpus.divergences.json"))
  let divs ← (← IO.ofExcept ((← field divJson "divergences").getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")), (← IO.ofExcept (o.getObjValAs? String "v1")),
      (← IO.ofExcept (o.getObjValAs? String "v2")))
  let mut pass := 0
  let mut fail := 0
  let mut diverged : List String := []
  let mut owed := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    match ← run fn (← field c "args") with
    | .owed why =>
      IO.eprintln s!"FAIL beta {name}: owed ({why}); the corpus has no owed case"
      owed := owed + 1
      fail := fail + 1
    | .text mine =>
      if agrees expected mine then pass := pass + 1
      else match divs.find? (·.1 == name) with
        | some (_, v1, v2) =>
          if v1 == expected && v2 == mine then
            diverged := diverged ++ [name]
            pass := pass + 1
          else
            IO.eprintln s!"FAIL beta {name}: the divergence listed no longer applies:\n  expected {repr expected}\n  got      {repr mine}"
            fail := fail + 1
        | none =>
          IO.eprintln s!"FAIL beta {name} ({fn}):\n  expected {repr expected}\n  got      {repr mine}"
          fail := fail + 1
  for (name, _, _) in divs do
    unless diverged.contains name do
      IO.eprintln s!"FAIL beta {name}: listed as a divergence but not one"
      fail := fail + 1
  IO.println s!"beta_corpus: {pass} pass ({diverged.length} as recorded v2 divergences), {owed} owed"
  return (pass, fail)

end Tests.Beta
