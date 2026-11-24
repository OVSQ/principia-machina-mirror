import Tests.Calculator.Common

/-!
The Calculator's runners of the family `form`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The declared forms through `pcalc` -/

/-- eval_form's text against version 1's, as the forms' runner compares them
(`Tests.Form.compareEval`): an `OK` answer's numbers by value, its KIND and every other
answer as text. -/
def evalAgrees (expect mine : String) : Bool :=
  match Tests.Form.splitTwo expect, Tests.Form.splitTwo mine with
  | some ("OK", v1), some ("OK", m) =>
    let a := v1.splitOn ","
    let b := m.splitOn ","
    a.length == b.length && ((List.range a.length).zip (a.zip b)).all fun (i, x, y) =>
      if i + 1 == a.length then Tests.Form.separable y && x == y
      else match Decimal.value x, Decimal.value y with
        | some p, some q => p == q
        | _, _ => false
  | _, _ => expect == mine

/-- What the command gave: version 1's text of its answer (the bound on an exact value's
refusal written as version 1's `[REFUSED,exact value too large]`), or the detail of an `OWED`
refusal. -/
inductive FormGot where
  | text (t : String)
  | owed (detail : String)
  | other (what : String)

def formGot : Except Refusal Value → FormGot
  | .ok v => match v.canon with
    | some t => .text t
    | none => .other "an answer with no canon text"
  | .error r =>
    if r.code == .owed then .owed r.detail
    else if r.code == .badArgument && r.detail == ValueBound.tooLarge then
      .text ("[REFUSED," ++ ValueBound.tooLarge ++ "]")
    else .other s!"refused {r.code.word}: {r.detail}"

def FormGot.show : FormGot → String
  | .text t => t
  | .owed d => "OWED: " ++ d
  | .other w => w

/-- `form_corpus.json` and `form_numbers.json`: every case through `form <fn>`, the forms'
runner the reference (`Tests.Form.run`, `runFormNumbers`). A case the runner agrees on must
agree, compared as the runner compares; a case it finds owed must be refused `OWED` with the
plain words for what it met; a recorded divergence must give the divergence's own text. -/
def runFormCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let divJson ← readJson "vectors/form_corpus.divergences.json"
  let divs ← (← arr (← field divJson "divergences")).mapM fun o => do
    pure ((← str o "id"), (← str o "v1"), (← str o "v2"))
  let jsonCases ← arr (← field (← readJson "vectors/form_corpus.json") "cases")
  let valueCases ← v1Cases "vectors/form_corpus.json"
  for (j, c) in jsonCases.zip valueCases do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := formGot (respondTo "form" fn input)
    let reference ← Tests.Form.run fn (← field j "input") expect
    let agrees (mine : String) := if fn == "eval_form" then evalAgrees expect mine else expect == mine
    let ok := match reference, got with
      | .agrees, .text m => agrees m
      | .differs mine, .text m => m == mine && divs.contains (id, expect, mine)
      | .owed w, .owed d => d == Principia.Calculator.Form.owedDetail w
      | _, _ => false
    t ← t.check ok s!"form {fn} {id}: expected {repr expect}, got {repr got.show}"
  let numberCases ← arr (← field (← readJson "vectors/form_numbers.json") "cases")
  for (c, v) in numberCases.zip (← v1Cases "vectors/form_numbers.json") do
    let id ← str c "id"
    let j ← field c "input"
    let expect ← str c "expect"
    let some input := member v "input" | throw (IO.userError s!"{id}: no input")
    let got := formGot (respondTo "form" "eval_form" input)
    let b := Tests.Form.bindingsArg j
    let reference := Principia.Form.withArgs (Tests.Form.strArg j "text")
      ((Tests.Form.strArg j "mode").getD "") fun s m => Principia.Form.evalForm (some Principia.Calculator.Form.stepBudget) s m b
    let ok := match reference, got with
      | .owed w, .owed d => expect == "OWED" && d == Principia.Calculator.Form.owedDetail w
      | .owed _, _ => false
      | _, .text m => expect != "OWED" && evalAgrees expect m
      | _, _ => false
    t ← t.check ok s!"form_numbers {id}: expected {repr expect}, got {repr got.show}"
  return t.pair

/-- A `dimensions` object of `n` names, each `L1`. -/
def formDims (n : Nat) : Value := .obj ((List.range n).map fun i => (s!"d{i}", .str "L1"))

/-- A `bindings` object of `n` names, each one metre. -/
def formBindings (n : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"b{i}", .obj [("VALUE", .str "1"), ("UNIT", .str "m")]))

/-- A `dimensions` object of four strings holding `n` code points in all, beside a form `x`:
the names `text`, `mode`, `dimensions`, `x`, `expression` and the four keys hold 37. -/
def formText (n : Nat) : Value :=
  let rest := n - 37 - 3 * 32768
  .obj [("text", .str "x"), ("mode", .str "expression"),
    ("dimensions", .obj [("a0", .str (codePoints 32768)), ("a1", .str (codePoints 32768)),
      ("a2", .str (codePoints 32768)), ("a3", .str (codePoints rest))])]

/-- The sum `ln(x0)+...+ln(x{k-1})`, its names bound to 2, 3, ... -/
def lnSum (k : Nat) : String := "+".intercalate ((List.range k).map fun i => s!"ln(x{i})")

/-- `eval_form` of a sum of `k` ln less itself, a value exactly zero but not known so: every
precision up to 4096 bits is tried before it is owed (`vectors/pcalc.json` holds `k` = 64). -/
def lnZero (k : Nat) : Value :=
  .obj [("text", .str s!"({lnSum k})-({lnSum k})"), ("mode", .str "expression"),
    ("bindings", .obj ((List.range k).map fun i =>
      (s!"x{i}", .obj [("VALUE", .str (toString (i + 2))), ("UNIT", .str "1")])))]

/-- `t3_laws` over `laws` LAWs, each a sum of `k` ln of CONSTANTs equated to itself. -/
def lnLaws (laws k : Nat) : Value :=
  .obj [("tpk", .obj [("DOF", .arr []),
    ("CONSTANT", .arr ((List.range k).map fun i => .obj [("NAME", .str s!"x{i}"),
      ("DIMENSION", .str "1"), ("VALUE", .str (toString (i + 2))), ("UNIT", .str "1")])),
    ("LAW", .arr ((List.range laws).map fun j => .obj [("NAME", .str s!"L{j}"),
      ("STATEMENT", .str "a sum of ln"), ("REFS", .arr []), ("ROLE", .str "DEFINITION"),
      ("EQUATION", .str s!"{lnSum k} = {lnSum k}")])),
    ("CONSTRAINT", .arr [])])]

/-- The form family's bounds (`Calculator.Form`), each at its value and one past it; the
precision-step budget (`Calculator.Form.stepBudget`) by requests on either side of it. -/
def runFormBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let tm (s : String) : List (String × Value) := [("text", .str s), ("mode", .str "expression")]
  let cases : List (String × String × Value × Bool) := [
    ("a form at 32768 code points", "parse_form", .obj (tm (codePoints 32768)), false),
    ("a form past 32768 code points", "parse_form", .obj (tm (codePoints 32769)), true),
    ("text at 131072 code points in all", "form_dimension", formText 131072, false),
    ("text past 131072 code points in all", "form_dimension", formText 131073, true),
    ("bindings at 64", "eval_form", .obj (tm "b0" ++ [("bindings", formBindings 64)]), false),
    ("bindings past 64", "eval_form", .obj (tm "b0" ++ [("bindings", formBindings 65)]), true),
    ("DOF at 64", "names_check", .obj [("tpk", dofTpk 64)], false),
    ("DOF past 64", "names_check", .obj [("tpk", dofTpk 65)], true),
    ("DOF past 64, T3", "t3_laws", .obj [("tpk", dofTpk 65)], true),
    ("dimensions at 1024", "form_dimension", .obj (tm "d0" ++ [("dimensions", formDims 1024)]), false),
    ("dimensions past 1024", "form_dimension", .obj (tm "d0" ++ [("dimensions", formDims 1025)]), true),
    ("dimensions past 1024, totality", "form_totality",
      .obj [("text", .str "d0<1"), ("dimensions", formDims 1025)], true),
    ("one ln less itself, owed within the step budget", "eval_form", lnZero 1, false),
    ("two ln less themselves, past the step budget", "eval_form", lnZero 2, true),
    ("64 ln less themselves, past the step budget", "eval_form", lnZero 64, true),
    ("4 LAWs of 4 ln, within the step budget", "t3_laws", lnLaws 4 4, false),
    ("64 LAWs of 40 ln, past the step budget", "t3_laws", lnLaws 64 40, true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "form" fn request
    t ← t.check (boundRefusal got == refused)
      s!"form {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Form

open Tests.Calculator

/-- The family `form`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc form (form_corpus, form_numbers)", runFormCalls),
  ("pcalc form bounds", runFormBounds),
]

end Tests.Calculator.Form
