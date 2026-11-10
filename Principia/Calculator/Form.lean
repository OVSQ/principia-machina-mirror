import Principia.Calculator.Interface
import Principia.Calculator.Record
import Principia.Form
import Principia.Strike.Conditions

/-!
# Family `form`: the declared forms

Version 1's `tpc_form` 0.2.1 on the command line, its 15 functions by version 1's names, their
arguments named as version 1's form corpus names them (a ported
function keeps its version 1 name unless it carries a version 1 code; none of this family
does, so all stand):

* The grammar: `parse_form {"text", "mode"}`, `["OK", spelling]`; `form_tree {"text",
  "mode"}`, `["OK", tree]`, the tree as nested lists (S32); `form_names {"text", "mode"}`,
  `["OK", names]`; `grammar_witness_count {}`, 33.
* Dimensions and totality: `form_dimension {"text", "mode", "dimensions"}`, `["OK",
  DIMENSION]`; `form_totality {"text", "dimensions"}`, `["OK", problems]`; `dimensions` an
  object of name and DIMENSION.
* The evaluator: `eval_form {"text", "mode", "bindings"}`, `bindings` an object of name and
  `{"VALUE", "UNIT"}`: `["OK", value, KIND]`, an equation's `["OK", left, right, KIND]`, each
  value in version 1's twelve-digit form, as a text; `["UNBOUND", name]`;
  `["CONVENTION", reason]`.
* The checks over a zone: `names_check`, `d_variable_check`, `t4_homogeneity`,
  `t6_totality`, `t3_laws {"tpk"}`, each `[pass, problems]`; `d_variables {"tpk"}`, a list;
  `form_coverage {"tpk"}`, `[laws, boundaries]`; `ic4a_signature {"trm", "tpk"}`, `[pass,
  problems, undecided]` (version 1 took the Starting Set and read only the Correspondence
  Table; so does this).

A request version 1 refused is answered as version 1 answered it, `["REFUSED", reason]`.
The arguments are read as version 1 read them: a `text` that is not a string is the form's
refusal, "the form is not a string"; `dimensions` or `bindings` that is not an object holds
nothing, and an entry of the wrong kind binds nothing. A `mode` must be a string; one version 1
does not know is its refusal, "unknown mode". Each zone is read as the zones read JSON
(`Strike.toZoneValue`).

Three answers are not values. A value whose sign, range or twelve digits no bounds up to 4096
bits settle is refused `OWED`, the detail "a value whose bounds up to 4096 bits do not settle
it: " and what was met. A value that would cross the bound on an exact value is refused
`BAD_ARGUMENT`, "exact value too large", as every family refuses it. A request of `eval_form`
or `t3_laws` whose decisions pass `stepBudget` precision steps in all is refused
`BAD_ARGUMENT`, "budget exceeded: ..." (`Principia.Form.budgetExceeded`); within the budget it
is answered as it would be without one (`Principia.Form.climb_findSome`).

Bounds: the grammar's own, a form of at most 4,096 code points after NFC and 64 parentheses
open at once (refused as version 1 refused them); every string of a request at most `maxText`
code points before NFC and `maxTextTotal` in all; at most `maxDimensions` entries in a list or
an object of `form_dimension` and `form_totality`, and `maxEntries` in those of the other
functions, so at most 64 bindings and 64 entries of each kind of a zone; at most `stepBudget`
precision steps of the evaluator's decisions across the whole request (`eval_form`,
`t3_laws`; the other functions decide no number).

Measured (one run each on the build machine, the request's text read included): a check over
64 LAWs of 1,900 code points each, 126 KB, takes 0.24 s (`names_check`), 0.12 s (`t3_laws`);
`form_dimension` over a form of 4,000 code points and 1,024 dimensions 0.07 s; `eval_form`
over 64 bindings and 64 functions 0.2 s to 0.9 s. The evaluator's work grows with the
functions a form calls whose values the ladder of bounds must narrow: about 0.4 s to 0.8 s for
each `exp`, `ln`, `sin`, `cos` or `tan` whose twelve digits the bounds up to 4096 bits do not
settle. Without the budget the slowest request found was such a one,
`(ln(x0)+...+ln(x63))-(ln(x0)+...+ln(x63))` in 3,405 bytes (a request of the Calculator's request corpus): 66 s,
refused `OWED`; the slowest answered, `t3_laws` over 64 LAWs of 40 `ln` each, 15 s.

The budget, measured on the build machine: the most steps a request of version 1's corpora
and of the form-numbers corpus spends is 894, `ln(x)-ln(x)` and its kin owed after the whole
ladder, 0.11 s to 0.66 s; a precision step took 0.7 ms to 1.3 ms in every form tried (sums
of 1 to 64 `exp`, `ln`, `sin`, `tan`, square and cube roots less themselves, 40 nested `ln`
or `exp`, `t3_laws` over 64 LAWs of 40 `ln`). `stepBudget`, 1,200, lets the corpora's slowest
through with a third to spare and holds every request under T2's 2 CPU-seconds: the slow
request above is refused in 0.06 s, two `ln` less themselves in 0.63 s, 40 nested `ln` in
1.18 s (the slowest refusal found), the 64 LAWs of 40 `ln` in 0.85 s.
-/

namespace Principia.Calculator.Form

open Principia.Canonical
open Principia.Form (Answer Owed Mode Evaluation)

/-- The most entries a list or an object of a request holds, at any depth: 64 bindings, 64
entries of each kind of a Starting Set or a Correspondence Table, the `eom` family's. -/
def maxEntries : Nat := 64

/-- The most entries of a `dimensions` object, the zones' 1,024. -/
def maxDimensions : Nat := 1024

/-- The most code points a string of a request holds, read before NFC. Version 1's corpus
holds forms of 20,011 code points, refused by the grammar for their length; the zone family's
bound, 32,768, lets the grammar refuse them as version 1 did (16,384 would refuse them first,
and the command would answer otherwise than the forms' runner). -/
def maxText : Nat := 32768

/-- The most code points the strings of a request hold in all, members' names included. -/
def maxTextTotal : Nat := 131072

/-- A request within `entries`, `maxText` and `maxTextTotal`. -/
def within (entries : Nat) (v : Value) : Except Refusal Unit := do
  let s := Record.valueSize v
  if entries < s.entries then
    badArgument s!"a list or an object of the request holds more than {entries} entries (the Calculator's bound)"
  if maxText < s.longest then
    badArgument s!"a string of the request holds more than {maxText} code points (the Calculator's bound)"
  if maxTextTotal < s.text then
    badArgument s!"the strings of the request hold more than {maxTextTotal} code points in all (the Calculator's bound)"

/-- The most precision steps a request's decisions spend (`Principia.Form.climb`): past it the
request is refused `BAD_ARGUMENT`, "budget exceeded". -/
def stepBudget : Nat := 1200

/-- The refusal of a request past the budget. -/
def budgetRefusal : Refusal := ⟨.badArgument, Principia.Form.budgetExceeded⟩

/-- An owed answer's detail, in plain words. -/
def owedDetail : Owed → String
  | .exact w => "a value whose bounds up to 4096 bits do not settle it: " ++ w

/-- The refusal of an owed answer. -/
def owedRefusal (w : Owed) : Refusal := ⟨.owed, owedDetail w⟩

/-- A list of texts. -/
def strs (xs : List String) : Value := .arr (xs.map .str)

/-- A form function's answer: `["OK", payload]`, `["REFUSED", reason]`, the bound on an exact
value's refusal, or `OWED`. -/
def answerOf {α : Type} (f : α → Value) : Answer α → Except Refusal Value
  | .ok a => .ok (.arr [.str "OK", f a])
  | .refused r =>
    if r == Principia.ValueBound.tooLarge then badArgument r
    else .ok (.arr [.str "REFUSED", .str r])
  | .owed w => .error (owedRefusal w)

/-- `eval_form`'s answer, version 1's list. -/
def evaluationValue : Evaluation → Value
  | .value x k => .arr [.str "OK", .str x.text, .str k]
  | .sides l r k => .arr [.str "OK", .str l.text, .str r.text, .str k]
  | .unbound n => .arr [.str "UNBOUND", .str n]
  | .convention r => .arr [.str "CONVENTION", .str r]

/-- `eval_form`'s answer as `pcalc` gives it. -/
def evalAnswer : Answer Evaluation → Except Refusal Value
  | .ok e => .ok (evaluationValue e)
  | .refused r =>
    if r == Principia.ValueBound.tooLarge || r == Principia.Form.budgetExceeded then badArgument r
    else .ok (.arr [.str "REFUSED", .str r])
  | .owed w => .error (owedRefusal w)

/-- A check's `[pass, problems]`, or `OWED`. -/
def verdictAnswer : Except Owed (List String) → Except Refusal Value
  | .ok ps => .ok (.arr [.bool ps.isEmpty, strs ps])
  | .error w => .error (owedRefusal w)

/-- `t3_laws`'s `[pass, problems]`, `OWED`, or the budget's refusal. -/
def lawsAnswer : Except Principia.Form.Stop (List String) → Except Refusal Value
  | .ok ps => .ok (.arr [.bool ps.isEmpty, strs ps])
  | .error (.owed w) => .error (owedRefusal w)
  | .error _ => .error budgetRefusal

/-- A form's text: `none` for any value that is not a string, as version 1 read it. -/
def textOf : Value → Option String
  | .str s => some s
  | _ => none

/-- An object's members; any other value has none. -/
def membersOrNone : Value → List (String × Value)
  | .obj ms => ms
  | _ => []

/-- `{name: DIMENSION}` (version 1's `_dims_of`): a value that is not a string has none. -/
def dimensionsOf (v : Value) : Principia.Form.DimTable :=
  Principia.Form.DimTable.ofStrings ((membersOrNone v).map fun (k, d) => (k, textOf d))

/-- `{name: {VALUE, UNIT}}`: an entry that is not an object binds nothing; a VALUE or a UNIT
absent or not a string is `none`. -/
def bindingsOf (v : Value) : List (String × Principia.Form.BindingArg) :=
  (membersOrNone v).map fun (k, b) =>
    (k, match b with
      | .obj ms => some ((ms.lookup "VALUE").bind textOf, (ms.lookup "UNIT").bind textOf)
      | _ => none)

/-- An argument as the zones read it. -/
def zoneOf (v : Value) : Principia.Zone.Value := Principia.Strike.toZoneValue v

/-- A call of `text` and `mode`, through version 1's argument checks (`withArgs`). -/
def textModeCall (extra : List String) (entries : Nat)
    (k : List Value → Option String → String → Except Refusal Value) : Call := fun v => do
  within entries v
  match ← arguments (["text", "mode"] ++ extra) v with
  | t :: m :: rest => k rest (textOf t) (← asString "mode" m)
  | _ => badArgument "the arguments do not read"

/-- A call over one zone argument. -/
def zoneCall (a : String) (f : Principia.Zone.Value → Except Refusal Value) : Call := fun v => do
  within maxEntries v
  f (zoneOf (← argument1 a v))

/-- The family's functions. -/
def calls : Family := [
  ("d_variable_check", zoneCall "tpk" fun z => verdictAnswer (Principia.Form.dVariableCheck z)),
  ("d_variables", zoneCall "tpk" fun z =>
    match Principia.Form.dVariables z with
    | .ok vs => .ok (strs vs)
    | .error w => .error (owedRefusal w)),
  ("eval_form", textModeCall ["bindings"] maxEntries fun rest t m => do
    let b ← match rest with
      | [b] => pure (bindingsOf b)
      | _ => badArgument "the arguments do not read"
    evalAnswer (Principia.Form.withArgs t m fun s md => Principia.Form.evalForm (some stepBudget) s md b)),
  ("form_coverage", zoneCall "tpk" fun z =>
    let (laws, bnds) := Principia.Form.formCoverage z
    .ok (.arr [strs laws, strs bnds])),
  ("form_dimension", textModeCall ["dimensions"] maxDimensions fun rest t m => do
    let d ← match rest with
      | [d] => pure (dimensionsOf d)
      | _ => badArgument "the arguments do not read"
    answerOf .str (Principia.Form.withArgs t m fun s md => Principia.Form.formDimension s md d)),
  ("form_names", textModeCall [] maxEntries fun _ t m =>
    answerOf strs (Principia.Form.withArgs t m Principia.Form.formNames)),
  ("form_totality", fun v => do
    within maxDimensions v
    let (t, d) ← argument2 "text" "dimensions" v
    let dims := dimensionsOf d
    answerOf strs (Principia.Form.withArgs (textOf t) "predicate" fun s _ =>
      Principia.Form.formTotality s dims)),
  ("form_tree", textModeCall [] maxEntries fun _ t m =>
    answerOf Principia.Form.Tree.toValue (Principia.Form.withArgs t m Principia.Form.formTree)),
  ("grammar_witness_count", fun v => do
    let _ ← arguments [] v
    pure (.int Principia.Form.grammarWitnessCount)),
  ("ic4a_signature", fun v => do
    within maxEntries v
    let (trm, _) ← argument2 "trm" "tpk" v
    match Principia.Form.ic4aSignature (zoneOf trm) with
    | .ok (ps, und) => pure (.arr [.bool ps.isEmpty, strs ps, strs und])
    | .error w => .error (owedRefusal w)),
  ("names_check", zoneCall "tpk" fun z => verdictAnswer (Principia.Form.namesCheck z)),
  ("parse_form", textModeCall [] maxEntries fun _ t m =>
    answerOf .str (Principia.Form.withArgs t m Principia.Form.parseForm)),
  ("t3_laws", zoneCall "tpk" fun z => lawsAnswer (Principia.Form.t3LawsIn (some stepBudget) z)),
  ("t4_homogeneity", zoneCall "tpk" fun z => verdictAnswer (Principia.Form.t4Homogeneity z)),
  ("t6_totality", zoneCall "tpk" fun z => verdictAnswer (Principia.Form.t6Totality z)),
]

/-! ## What the kernel checks -/

/-- The family has version 1's 15 functions. -/
theorem calls_count : calls.length = 15 := rfl

/-- An owed answer is refused `OWED`, its detail the plain words and what was met. -/
theorem answerOf_owed {α : Type} (f : α → Value) (w : String) :
    answerOf f (.owed (.exact w)) =
      .error ⟨.owed, "a value whose bounds up to 4096 bits do not settle it: " ++ w⟩ := rfl

/-- The bound on an exact value is refused `BAD_ARGUMENT`, never answered as a value. -/
theorem evalAnswer_tooLarge :
    evalAnswer (.refused Principia.ValueBound.tooLarge) =
      .error ⟨.badArgument, Principia.ValueBound.tooLarge⟩ := by
  simp [evalAnswer, badArgument]

/-- A request past the precision-step budget is refused `BAD_ARGUMENT`, never answered as a
value or as version 1's refusal. -/
theorem evalAnswer_budget :
    evalAnswer (.refused Principia.Form.budgetExceeded) =
      .error ⟨.badArgument, Principia.Form.budgetExceeded⟩ := by
  simp [evalAnswer, badArgument]

/-- `t3_laws` past the budget is refused `BAD_ARGUMENT`. -/
theorem lawsAnswer_budget : lawsAnswer (.error .budget) = .error budgetRefusal := rfl

end Principia.Calculator.Form
