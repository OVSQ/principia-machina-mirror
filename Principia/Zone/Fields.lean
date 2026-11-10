import Principia.Decimal
import Principia.Dimension
import Principia.Units
import Principia.Zone.Text
import Principia.Form.Grammar

/-!
# Zone entries: the input tree, the verdict and the field checks

v1's zone validators (`tpc_zone` 0.5.1, schema 0.5.0) read a zone as parsed JSON and
never fail on malformed input: every fault is a problem returned to the author
(TPS 5.5). `Value` is that input, as v1's JSON reader gives it; `checkFields` is
v1's `_check_fields`, with `_type_ok`, `_entries`, `_name`, `_names`, `_dupes`
and `_done` beside it.

A zone is judged only where every check v1 makes is in the Calculator. Otherwise
the verdict is `owed`, with the reason, and never a pass. Text is judged with Unicode
15.1.0's general category and NFC, as v1 judged it (`Principia.Zone.Text`). A form field (EQUATION, CONDITION, FORM, IMAGE_FORM) is read by the declared-form
grammar (`Principia.Form.Grammar`), as v1's `_check_fields` read it with `parse_form`;
reading a form is never owed, so no zone is owed today. `Owed.forms` is kept for the
grammar's owed answers, of which it gives none when it reads a form.
-/

namespace Principia.Zone

/-- A zone as parsed JSON. A number with a fraction part is one v1 reads as a
float, which no field of a zone accepts. -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | real
  | str (s : String)
  | arr (xs : List Value)
  | obj (kvs : List (String × Value))
  deriving Repr, Inhabited

namespace Value

mutual
/-- Every string of a value, object keys included. -/
def strings : Value → List String
  | .str s => [s]
  | .arr xs => stringsOfList xs
  | .obj kvs => stringsOfObj kvs
  | _ => []
/-- Every string of a list of values. -/
def stringsOfList : List Value → List String
  | [] => []
  | x :: xs => x.strings ++ stringsOfList xs
/-- Every key and string of an object. -/
def stringsOfObj : List (String × Value) → List String
  | [] => []
  | (k, v) :: kvs => k :: v.strings ++ stringsOfObj kvs
end

mutual
/-- Every string field of an object at any depth, with its key. -/
def fieldStrings : Value → List (String × String)
  | .arr xs => fieldStringsOfList xs
  | .obj kvs => fieldStringsOfObj kvs
  | _ => []
/-- Every string field of a list of values. -/
def fieldStringsOfList : List Value → List (String × String)
  | [] => []
  | x :: xs => x.fieldStrings ++ fieldStringsOfList xs
/-- Every string field of an object, at any depth. -/
def fieldStringsOfObj : List (String × Value) → List (String × String)
  | [] => []
  | (k, v) :: kvs => (match v with | .str s => [(k, s)] | _ => []) ++ v.fieldStrings ++ fieldStringsOfObj kvs
end

mutual
/-- Every object key of a value, at any depth. -/
def keys : Value → List String
  | .arr xs => keysOfList xs
  | .obj kvs => keysOfObj kvs
  | _ => []
/-- Every object key of a list of values. -/
def keysOfList : List Value → List String
  | [] => []
  | x :: xs => x.keys ++ keysOfList xs
/-- Every key of an object, at any depth. -/
def keysOfObj : List (String × Value) → List String
  | [] => []
  | (k, v) :: kvs => k :: v.keys ++ keysOfObj kvs
end

end Value

/-- An object's field. -/
abbrev Entry := List (String × Value)

/-- v1's `e.get(f)`. -/
def get? (e : Entry) (f : String) : Option Value := e.lookup f

/-- v1's `f in e`. -/
def has (e : Entry) (f : String) : Bool := (e.lookup f).isSome

/-- The string a field holds, if it holds one. -/
def getStr? (e : Entry) (f : String) : Option String :=
  match get? e f with
  | some (.str s) => some s
  | _ => none

/-! ## The owed verdict -/

/-- Why a zone is not judged yet. -/
inductive Owed where
  /-- A form field the declared-form grammar owes. -/
  | forms
  deriving DecidableEq, Repr

/-- The owed refusal's text. -/
def Owed.message : Owed → String
  | .forms => "declared forms not yet ported"

/-- A zone validator's result: v1's verdict, or owed. -/
inductive Verdict where
  /-- v1's `[pass, problems]`, problems sorted and without repeats; it passes when
  there are none. -/
  | checked (problems : List String)
  /-- Not judged: what the Calculator still lacks. -/
  | owed (why : Owed)
  deriving DecidableEq, Repr

/-- The verdict passes: judged, with no problem. -/
def Verdict.passes : Verdict → Bool
  | .checked ps => ps.isEmpty
  | .owed _ => false

/-- The form fields. -/
def formFields : List String := ["EQUATION", "CONDITION", "FORM", "IMAGE_FORM"]

/-- The declared-form grammar's owed reason as the zones' (the grammar gives none when it
reads a form). -/
def ofFormOwed : Form.Owed → Owed
  | .exact _ => .forms

/-- A form field whose reading the grammar owes, anywhere in a zone. -/
def formOwedOf (zone : Value) : Option Owed :=
  zone.fieldStrings.findSome? fun (k, v) =>
    if formFields.contains k then
      match Form.parseField k v with
      | .owed w => some (ofFormOwed w)
      | _ => none
    else none

/-- What a zone needs that the Calculator lacks: a form field whose reading the grammar
owes. -/
def owedOf (zone : Value) : Option Owed := formOwedOf zone

/-- Strings sorted by code point (insertion). -/
def insertStr (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: insertStr x ys

/-- v1's `_done`: each problem escaped, sorted, without repeats. -/
def done (probs : List String) : List String :=
  (probs.map escape).foldl (fun acc p => insertStr p acc) []

/-! ## Fields -/

/-- Set-valued fields, sorted in serialization; duplicates refused. -/
def setFields : List String := ["REFS", "OVER", "BEARS"]
/-- Sequence fields: order kept. -/
def seqFields : List String := ["KEY"]
/-- Fields holding a list of objects. -/
def objListFields : List String := ["LIMITING"]
/-- Integer fields. -/
def intFields : List String := ["N_X", "S_MAX"]
/-- Decimal fields. -/
def decFields : List String := ["VALUE", "UNCERTAINTY", "K"]
/-- Fields of the zone's mutable state, never permitted in it (TPS 2.1.3). -/
def mutableFields : List String := ["STATE", "SCRUTINY", "RIDER", "NOTE", "CHECKS_OWED", "RECORDS"]

/-- v1's `_type_ok`. -/
def typeOk (f : String) (v : Value) : Bool :=
  if setFields.contains f || seqFields.contains f then
    match v with
    | .arr xs => xs.all fun | .str _ => true | _ => false
    | _ => false
  else if objListFields.contains f then
    match v with
    | .arr xs => xs.all fun | .obj _ => true | _ => false
    | _ => false
  else if intFields.contains f then
    match v with
    | .int _ => true
    | _ => false
  else
    match v with
    | .str _ => true
    | _ => false

/-- Strings of a list value. -/
def strItems : Value → List String
  | .arr xs => xs.filterMap fun | .str s => some s | _ => none
  | _ => []

/-- A list of strings repeats one. -/
def hasRepeat : List String → Bool
  | [] => false
  | x :: xs => xs.contains x || hasRepeat xs

/-- v1's `_unit_against` and the UNIT field's parse: the seam for the unit grammar.
`unitDimension u` is `.ok` with the unit's canonical DIMENSION, or `.error` with the
refusal's text. -/
structure UnitHook where
  /-- The dimension of a unit, or why it is not one. -/
  unitDimension : String → Except String String

/-- The Calculator's unit grammar (`Principia.Units`, v1's `unit_parse`): a unit's
canonical DIMENSION, or the reason it is not one. The reason is taken before the unit
grammar escapes it, since `done` escapes every problem, as v1's `_show` does. -/
def UnitHook.calculator : UnitHook where
  unitDimension u := match Units.tokens u with
    | .error r => .error r
    | .ok items => .ok (Dimension.canon (Units.dimExps items))

/-- The checks of one field's value, once its type is right (the `elif` chain of
`_check_fields`). A form field is read by the declared-form grammar; its owed answers
make the zone owed before this is reached (`owedOf`). -/
def valueProblems (units : UnitHook) (tag f : String) (v : Value) : List String :=
  let strs := match v with
    | .str s => [s]
    | _ => if setFields.contains f || seqFields.contains f then strItems v else []
  let bad := match strs.findSome? firstBad with
    | some b => [tag ++ ": field " ++ f ++ " contains disallowed character " ++ b]
    | none => []
  let rest := match v with
    | .str s =>
      if f == "DIMENSION" && (Dimension.normalize s).isNone then
        if Dimension.outOfRange s then [tag ++ ": DIMENSION " ++ s ++ ": an exponent is out of range"]
        else [tag ++ ": DIMENSION " ++ s ++ " is not a dimension"]
      else if decFields.contains f && (Decimal.canon s).isNone then
        [tag ++ ": " ++ f ++ " " ++ s ++ " is not a decimal"]
      else if f == "UNIT" then
        match units.unitDimension s with
        | .ok _ => []
        | .error m => [tag ++ ": " ++ m]
      else if formFields.contains f then
        match Form.parseField f s with
        | .refused r => [tag ++ ": " ++ f ++ " does not parse: " ++ r]
        | _ => []
      else []
    | _ => if setFields.contains f && hasRepeat (strItems v) then
        [tag ++ ": field " ++ f ++ " has duplicate entries"] else []
  bad ++ rest

/-- v1's `_check_fields`: unknown and mutable fields, missing required fields, each
present field's type and value, and NAME an identifier. -/
def checkFields (units : UnitHook) (tag : String) (e : Entry) (req opt : List String) :
    List String :=
  let allowed := req ++ opt
  let extra := e.filterMap fun (f, _) =>
    if allowed.contains f then none
    else if mutableFields.contains f then some (tag ++ ": mutable field " ++ f ++ " is not permitted in the TFK")
    else some (tag ++ ": unknown field " ++ f)
  let missing := req.filterMap fun f => if has e f then none else some (tag ++ ": missing field " ++ f)
  let values := allowed.flatMap fun f =>
    match get? e f with
    | none => []
    | some v => if typeOk f v then valueProblems units tag f v else [tag ++ ": field " ++ f ++ " has the wrong type"]
  let name := match getStr? e "NAME" with
    | some n => if req.contains "NAME" && !isIdent n then [tag ++ ": NAME " ++ n ++ " is not an identifier"] else []
    | none => []
  extra ++ missing ++ values ++ name

/-- v1's `_entries`: the objects of a list-valued part, and problems for the rest. -/
def entries (label : String) (x : Value) : List Entry × List String :=
  match x with
  | .arr xs =>
    xs.foldr (fun v (es, ps) => match v with
      | .obj e => (e :: es, ps)
      | _ => (es, (label ++ ": entry is not an object") :: ps)) ([], [])
  | _ => ([], [label ++ " is not a list"])

/-- v1's `_name`: the field's string, or `?`. -/
def nameOf (e : Entry) (f : String := "NAME") : String := (getStr? e f).getD "?"

/-- v1's `_dupes` over `_names`: the strings that occur twice or more, sorted. -/
def dupes (names : List String) : List String :=
  let rec go : List String → List String → List String
    | [], _ => []
    | x :: xs, seen => if seen.contains x then x :: go xs seen else go xs (x :: seen)
  go names [] |>.foldl (fun acc p => insertStr p acc) []

/-- The NAME-like field of each entry that holds a string. -/
def names (es : List Entry) (f : String := "NAME") : List String := es.filterMap (getStr? · f)

end Principia.Zone
