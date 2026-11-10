import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/form_corpus.json` (v1's `tpc_form` 0.2.1 corpus 0.5.1, 555 cases),
against `Principia.Form`.

Each case is `{"id", "fn", "input", "expect"}`, `expect` being v1's `canon` text of the
result. That text writes a string unquoted, so it is not one to one; the runner reads it
against the result's known shape and compares typed values:

* a two-item answer `[OK, s]` or `[REFUSED, r]`: the word before the first comma (neither
  word holds one) and the rest, so a canonical spelling holding a comma (`D(x,t,2)`) is
  still compared whole;
* a list of names, a tree or a DIMENSION: item by item, every item the
  Calculator gives first checked to hold no comma and no bracket, so the text determines
  the items (a case whose items could not be told apart fails rather than compares);
* a number: by value, v1's twelve digits read as an exact decimal against the
  Calculator's exact value rounded once to twelve digits;
* a validator's `[pass, problems]`: the pass flag as a value; the problems, which may hold
  commas, by v1's text, as the zones' runner compares them; `form_totality`'s problems so
  too.

An owed case is neither a pass nor a failure: it must be listed with its reason in
`vectors/form_corpus.owed.json`, and every case listed there must come out owed for that
reason. A v2 divergence is listed in `vectors/form_corpus.divergences.json` with v1's
text and the Calculator's, both checked.
-/

open Lean
open Principia
open Principia.Form

namespace Tests.Form

/-! ## Reading the input -/

def field (j : Json) (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)

/-- A string argument, or `none` for any other JSON value. -/
def strArg (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

/-- An object's members, in key order. -/
def members (j : Json) : List (String × Json) :=
  match j with
  | .obj kvs => kvs.foldl (fun acc k v => acc ++ [(k, v)]) []
  | _ => []

/-- `{name: DIMENSION}`: a value that is not a string has none; a non-object is empty. -/
def dimsArg (input : Json) : DimTable :=
  match input.getObjVal? "dimensions" with
  | .ok j => DimTable.ofStrings ((members j).map fun (k, v) => (k, match v with | .str s => some s | _ => none))
  | .error _ => []

/-- `{name: {VALUE, UNIT}}`: an entry that is not an object binds nothing; a non-object is
empty. -/
def bindingsArg (input : Json) : List (String × BindingArg) :=
  match input.getObjVal? "bindings" with
  | .ok j => (members j).map fun (k, v) =>
      (k, match v with
        | .obj _ => some (strArg v "VALUE", strArg v "UNIT")
        | _ => none)
  | .error _ => []

/-- A zone argument as v1's JSON reader gives it. -/
def zoneArg (input : Json) (k : String) : IO Zone.Value := do
  return Tests.Zone.toValue (← field input k)

/-! ## v1's text -/

/-- A text item that cannot be told apart from its neighbours in v1's text. -/
def separable (s : String) : Bool := !s.any fun c => c == ',' || c == '[' || c == ']'

/-- A list as v1's `canon` writes it. -/
def listText (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

/-- v1's two-item answer: the word and the rest. -/
def splitTwo (expect : String) : Option (String × String) :=
  if expect.startsWith "[" && expect.endsWith "]" then
    let inner := (expect.toList.drop 1).dropLast
    let word := inner.takeWhile (· != ',')
    if word.length < inner.length then some (String.ofList word, String.ofList (inner.drop (word.length + 1)))
    else none
  else none

/-- Every string of a value. -/
partial def valueStrings : Canonical.Value → List String
  | .str s => [s]
  | .arr xs => xs.flatMap valueStrings
  | _ => []

/-- What a case came to. -/
inductive Outcome where
  | agrees
  | differs (mine : String)
  | owed (why : Owed)

/-- A two-item answer compared with v1's: the word, then the payload. -/
def compareAnswer {α : Type} (expect : String) (payload : α → Option String) : Answer α → Outcome
  | .owed w => .owed w
  | .refused r =>
    if splitTwo expect == some ("REFUSED", r) then .agrees else .differs ("[REFUSED," ++ r ++ "]")
  | .ok a =>
    match payload a with
    | some p => if splitTwo expect == some ("OK", p) then .agrees else .differs ("[OK," ++ p ++ "]")
    | none => .differs "(an item holding a comma or a bracket)"

/-- A list payload, when every item is separable. -/
def listPayload (xs : List String) : Option String :=
  if xs.all separable then some (listText xs) else none

/-- A validator's verdict: the pass flag as a value, the problems as v1's text. -/
def compareVerdict (expect : String) (r : Except Owed (List String)) : Outcome :=
  match r with
  | .error w => .owed w
  | .ok ps =>
    let text := if ps.isEmpty then "[true,[]]" else "[false," ++ listText ps ++ "]"
    if expect.startsWith "[true," == ps.isEmpty && expect == text then .agrees else .differs text

/-- eval_form's answer: numbers by value, the rest as text. -/
def compareEval (expect : String) : Answer Evaluation → Outcome
  | .owed w => .owed w
  | .refused r => if expect == "[REFUSED," ++ r ++ "]" then .agrees else .differs ("[REFUSED," ++ r ++ "]")
  | .ok e =>
    let mine := e.text
    match e with
    | .unbound n | .convention n =>
      if separable n && expect == mine then .agrees else .differs mine
    | .value _ _ | .sides _ _ _ =>
      match splitTwo expect, splitTwo mine with
      | some ("OK", v1), some ("OK", m) =>
        let a := v1.splitOn ","
        let b := m.splitOn ","
        let same := a.length == b.length && ((List.range a.length).zip (a.zip b)).all fun (i, x, y) =>
          if i + 1 == a.length then separable y && x == y
          else match Decimal.value x, Decimal.value y with
            | some p, some q => p == q
            | _, _ => false
        if same then .agrees else .differs mine
      | _, _ => .differs mine

/-! ## One case -/

/-- The Calculator's outcome on a case. -/
def run (fn : String) (input : Json) (expect : String) : IO Outcome := do
  match fn with
  | "parse_form" =>
    return compareAnswer expect some (withArgs (strArg input "text") ((strArg input "mode").getD "") parseForm)
  | "form_tree" =>
    return compareAnswer expect (fun t =>
        let v := t.toValue
        if (valueStrings v).all separable then v.canon else none)
      (withArgs (strArg input "text") ((strArg input "mode").getD "") formTree)
  | "form_names" =>
    return compareAnswer expect listPayload (withArgs (strArg input "text") ((strArg input "mode").getD "") formNames)
  | "form_dimension" =>
    let t := dimsArg input
    return compareAnswer expect (fun d => if separable d then some d else none)
      (withArgs (strArg input "text") ((strArg input "mode").getD "") fun s m => formDimension s m t)
  | "form_totality" =>
    let t := dimsArg input
    -- Problems, which may hold commas (", which is not total"), are compared by v1's text.
    return compareAnswer expect (fun ps => some (listText ps))
      (withArgs (strArg input "text") "predicate" fun s _ => formTotality s t)
  | "eval_form" =>
    let b := bindingsArg input
    return compareEval expect (withArgs (strArg input "text") ((strArg input "mode").getD "") fun s m => evalForm (some Principia.Calculator.Form.stepBudget) s m b)
  | "grammar_witness_count" =>
    let ok := grammarWitnesses.all witnessHolds && grammarWitnesses.length == grammarWitnessCount
    return if ok && expect == toString grammarWitnessCount then .agrees else .differs (toString grammarWitnesses.length)
  | "names_check" => return compareVerdict expect (namesCheck (← zoneArg input "tpk"))
  | "d_variable_check" => return compareVerdict expect (dVariableCheck (← zoneArg input "tpk"))
  | "t4_homogeneity" => return compareVerdict expect (t4Homogeneity (← zoneArg input "tpk"))
  | "t6_totality" => return compareVerdict expect (t6Totality (← zoneArg input "tpk"))
  | "t3_laws" =>
    let laws := (t3LawsIn (some Principia.Calculator.Form.stepBudget) (← zoneArg input "tpk")).mapError
      fun | .owed w => w | _ => .exact budgetExceeded
    return compareVerdict expect laws
  | "d_variables" =>
    match dVariables (← zoneArg input "tpk") with
    | .error w => return .owed w
    | .ok vs =>
      return match listPayload vs with
        | some t => if t == expect then .agrees else .differs t
        | none => .differs "(an item holding a comma or a bracket)"
  | "form_coverage" =>
    let (laws, bnds) := formCoverage (← zoneArg input "tpk")
    return match listPayload laws, listPayload bnds with
      | some a, some b => let t := "[" ++ a ++ "," ++ b ++ "]"; if t == expect then .agrees else .differs t
      | _, _ => .differs "(an item holding a comma or a bracket)"
  | "ic4a_signature" =>
    match ic4aSignature (← zoneArg input "trm") with
    | .error w => return .owed w
    | .ok (ps, und) =>
      let t := "[" ++ (if ps.isEmpty then "true" else "false") ++ "," ++ listText ps ++ "," ++ listText und ++ "]"
      return if expect.startsWith "[true," == ps.isEmpty && expect == t then .agrees else .differs t
  | _ => throw (IO.userError s!"form: no runner for {fn}")

/-! ## The corpus -/

/-- Run the corpus: passes (divergences among them) and failures; owed cases are counted. -/
def runForm : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/form_corpus.json"))
  let cases ← IO.ofExcept ((← field json "cases").getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/form_corpus.owed.json"))
  let listed ← (← IO.ofExcept ((← field owedJson "owed").getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  let divJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/form_corpus.divergences.json"))
  let divs ← (← IO.ofExcept ((← field divJson "divergences").getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")), (← IO.ofExcept (o.getObjValAs? String "v1")),
      (← IO.ofExcept (o.getObjValAs? String "v2")))
  let mut pass := 0
  let mut fail := 0
  let mut diverged : List String := []
  let mut owed : List (String × String) := []
  let mut perFn : List (String × Nat × Nat × Nat) := []
  for c in cases do
    let id ← IO.ofExcept (c.getObjValAs? String "id")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let input ← field c "input"
    let expect ← IO.ofExcept ((← field c "expect").getStr?)
    let outcome ← run fn input expect
    let (p, o) ← match outcome with
      | .agrees => pure (1, 0)
      | .owed w =>
        owed := owed ++ [(id, w.word)]
        pure (0, 1)
      | .differs mine =>
        match divs.find? (·.1 == id) with
        | some (_, v1, v2) =>
          if v1 == expect && v2 == mine then
            diverged := diverged ++ [id]
            pure (1, 0)
          else
            IO.eprintln s!"FAIL form {id} ({fn}): the divergence listed no longer applies:\n  expected {repr expect}\n  got      {repr mine}"
            pure (0, 0)
        | none =>
          IO.eprintln s!"FAIL form {id} ({fn}):\n  expected {repr expect}\n  got      {repr mine}"
          pure (0, 0)
    if p == 0 && o == 0 then fail := fail + 1
    pass := pass + p
    perFn := match perFn.find? (·.1 == fn) with
      | some _ => perFn.map fun (k, a, b, d) => if k == fn then (k, a + p, b + o, d + (1 - p - o)) else (k, a, b, d)
      | none => perFn ++ [(fn, p, o, 1 - p - o)]
  for (id, why) in owed do
    unless listed.contains (id, why) do
      IO.eprintln s!"FAIL form {id}: owed ({why}) but not listed so in vectors/form_corpus.owed.json"
      fail := fail + 1
  for (id, why) in listed do
    unless owed.contains (id, why) do
      IO.eprintln s!"FAIL form {id}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  for (id, _, _) in divs do
    unless diverged.contains id do
      IO.eprintln s!"FAIL form {id}: listed as a divergence but not one"
      fail := fail + 1
  let counts := perFn.map fun (k, a, b, d) => s!"{k} {a}" ++ (if b > 0 then s!" ({b} owed)" else "") ++ (if d > 0 then s!" ({d} FAIL)" else "")
  IO.println s!"form_corpus: {pass} pass ({diverged.length} as recorded v2 divergences), {owed.length} owed; {", ".intercalate counts}"
  return (pass, fail)

/-- `vectors/form_numbers.json`, written by hand: values with no exact form, enclosed. Each
case is run as eval_form's; an expectation `OWED` passes only when the Calculator does not
answer. -/
def runFormNumbers : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/form_numbers.json"))
  let cases ← IO.ofExcept ((← field json "cases").getArr?)
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let id ← IO.ofExcept (c.getObjValAs? String "id")
    let input ← field c "input"
    let expect ← IO.ofExcept ((← field c "expect").getStr?)
    let b := bindingsArg input
    let answer := withArgs (strArg input "text") ((strArg input "mode").getD "") fun s m => evalForm (some Principia.Calculator.Form.stepBudget) s m b
    let ok := match answer, expect with
      | .owed _, "OWED" => true
      | .owed _, _ => false
      | _, "OWED" => false
      | a, _ => match compareEval expect a with
        | .agrees => true
        | _ => false
    if ok then pass := pass + 1
    else
      let got := match answer with
        | .ok e => e.text
        | .refused r => "[REFUSED," ++ r ++ "]"
        | .owed w => "owed: " ++ w.word
      IO.eprintln s!"FAIL form_numbers {id}:\n  expected {repr expect}\n  got      {repr got}"
      fail := fail + 1
  return (pass, fail)

end Tests.Form
