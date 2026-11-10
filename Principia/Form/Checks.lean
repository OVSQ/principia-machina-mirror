import Principia.Zone.Fields
import Principia.Form.Homogeneity

/-!
# Declared forms: the checks over a Starting Set and a Correspondence Table

v1's `tpc_form` 0.2.1 checks that read a zone: `names_check` (S5, part of T1),
`form_coverage`, `d_variables` and `d_variable_check` (part of T1),
`t4_homogeneity` (T4's law half), `t6_totality` (T6) and `ic4a_signature` (IC4 (a),
syntactic). T3 over the laws, which evaluates, is in `Principia.Form.Evaluation`.

A zone is read as `Principia.Zone.Value`, v1's JSON. Each check never fails on malformed
input: an entry that is not an object, a field of the wrong type, a form that does not
parse are each left to the check that reports them, as in v1. A form is read after NFC and
a problem escaped by general category, as v1 did, at Unicode 15.1.0 (`Principia.Zone.Text`). The checks here owe nothing; their type is the evaluation's, which
can owe a value.
-/

namespace Principia.Form

open Principia.Zone (Value Entry getStr? get? has nameOf firstBad)

/-! ## Reading a zone -/

/-- v1's `_entries_of`: the object entries of a list-valued part of an object; nothing
when the zone is not an object or the part is not a list. -/
def entriesOf (zone : Value) (key : String) : List Entry :=
  match zone with
  | .obj kvs =>
    match kvs.lookup key with
    | some (.arr xs) => xs.filterMap fun | .obj e => some e | _ => none
    | _ => []
  | _ => []

/-- A part of an object, `.null` when absent or when the value is not an object (v1's
`zone.get(key)`). -/
def partOf (zone : Value) (key : String) : Value :=
  match zone with
  | .obj kvs => (kvs.lookup key).getD .null
  | _ => .null

/-- v1's `_set`: a field's strings, when it is a list of strings; else none. -/
def stringSet (e : Entry) (f : String) : List String :=
  match get? e f with
  | some (.arr xs) =>
    if xs.all (fun | .str _ => true | _ => false) then xs.filterMap fun | .str s => some s | _ => none
    else []
  | _ => []

/-- v1's `_first_bad(f) is not None`. -/
def hasBad (f : String) : Except Owed Bool := pure (firstBad f).isSome

/-- A parse inside a check: the tree, `none` when the form does not parse (with the
reason), or owed. -/
def parseIn (text : String) (mode : Mode) : Except Owed (Except String Tree) :=
  match parse text mode with
  | .ok t => .ok (.ok t)
  | .refused r => .ok (.error r)
  | .owed w => .error w

/-- v1's `_done`: problems escaped, sorted and without repeats. -/
def finish (probs : List String) : Except Owed (List String) := pure (Zone.done probs)

/-- `a` less `b`, both sorted without repeats. -/
def setMinus (a b : List String) : List String := a.filter fun x => !b.contains x

/-- Names sorted in code point order, repeats kept (Python's `sorted`). -/
def sortKeep (xs : List String) : List String :=
  let rec ins (x : String) : List String → List String
    | [] => [x]
    | y :: ys => if x < y then x :: y :: ys else y :: ins x ys
  xs.foldl (fun acc x => ins x acc) []

/-! ## S5: names -/

/-- `names_check` (S5, part of T1): every LAW with EQUATION and BOUNDARY with CONDITION
names only its REFS members and every REFS member; a form that does not parse is reported
here. A form holding a disallowed code point is left to T1's field check. The problems,
sorted (v1's `[pass, problems]`: it passes when there are none). -/
def namesCheck (tpk : Value) : Except Owed (List String) := do
  let mut probs : List String := []
  for (kind, field, mode) in [("LAW", "EQUATION", Mode.equation), ("BOUNDARY", "CONDITION", .predicate)] do
    for e in entriesOf tpk kind do
      let some f := getStr? e field | continue
      if ← hasBad f then continue
      let tag := kind ++ ":" ++ nameOf e
      match ← parseIn f mode with
      | .error r => probs := probs ++ [tag ++ ": " ++ field ++ " does not parse: " ++ r]
      | .ok tree =>
        let named := sortedSet tree.names
        let refs := sortedSet (stringSet e "REFS")
        probs := probs ++ (setMinus named refs).map fun n =>
          tag ++ ": " ++ field ++ " names " ++ n ++ ", which is not in REFS"
        probs := probs ++ (setMinus refs named).map fun n =>
          tag ++ ": REFS " ++ n ++ " is not named in " ++ field
  finish probs

/-- `form_coverage`: the LAWs without EQUATION and the BOUNDARYs without CONDITION, their
names sorted: what stays INSPECTION under T4, T3 over laws and T6. -/
def formCoverage (tpk : Value) : List String × List String :=
  (sortKeep ((entriesOf tpk "LAW").filter (!has · "EQUATION") |>.map (nameOf ·)),
   sortKeep ((entriesOf tpk "BOUNDARY").filter (!has · "CONDITION") |>.map (nameOf ·)))

/-! ## The D variables -/

/-- Each D variable of the LAWs' EQUATIONs with the LAWs that use it, sorted (v1's
`_law_dvars`): a form holding a disallowed code point, or that does not parse, uses
none. -/
def lawDVariables (tpk : Value) : Except Owed (List (String × List String)) := do
  let mut acc : List (String × List String) := []
  for e in entriesOf tpk "LAW" do
    let some f := getStr? e "EQUATION" | continue
    if ← hasBad f then continue
    let .ok tree ← parseIn f .equation | continue
    for s in tree.dVariables do
      let law := "LAW:" ++ nameOf e
      acc := match acc.lookup s with
        | some _ => acc.map fun (k, v) => if k == s then (k, insertSorted law v) else (k, v)
        | none => acc ++ [(s, [law])]
  return (sortedSet (acc.map (·.1))).map fun s => (s, (acc.lookup s).getD [])

/-- `d_variables`: the distinct D variables of the Starting Set's forms, in code
point order. -/
def dVariables (tpk : Value) : Except Owed (List String) :=
  (lawDVariables tpk).map (·.map (·.1))

/-- `d_variable_check` (part of T1): every D variable is a DOF and the TARGET of no
CONSTRAINT, whatever its ACTION; under D_VARIABLES ONE (ONE when PARAMETERS or
D_VARIABLES is absent) the forms use one D variable, under SEVERAL any number; a
PARAMETERS part that is not an object, or a D_VARIABLES other than ONE, applies no count.
The problems, sorted. -/
def dVariableCheck (tpk : Value) : Except Owed (List String) := do
  let .obj kvs := tpk | return []
  let uses ← lawDVariables tpk
  let dofs := (entriesOf tpk "DOF").filterMap (getStr? · "NAME")
  let targets (s : String) : List String :=
    sortedSet ((entriesOf tpk "CONSTRAINT").filterMap fun c =>
      if getStr? c "TARGET" == some s then some ("CONSTRAINT:" ++ nameOf c) else none)
  let mut probs : List String := []
  for (s, laws) in uses do
    for law in laws do
      unless dofs.contains s do
        probs := probs ++ [law ++ ": EQUATION's D variable " ++ s ++ " is not a DOF"]
      for c in targets s do
        probs := probs ++ [law ++ ": EQUATION's D variable " ++ s ++ " is the TARGET of " ++ c]
  let countOne : Bool := match kvs.lookup "PARAMETERS" with
    | none => true
    | some (.obj pm) =>
      match pm.lookup "D_VARIABLES" with
      | none => true
      | some (.str "ONE") => true
      | some _ => false
    | some _ => false
  if countOne && uses.length > 1 then
    probs := probs ++ ["TPK: D_VARIABLES is ONE (ONE when absent), but the forms use D variables " ++
      ", ".intercalate (uses.map fun (s, laws) => s ++ " (" ++ ", ".intercalate laws ++ ")")]
  finish probs

/-! ## T4 and T6 -/

/-- The DIMENSIONs of the Starting Set's DOFs and CONSTANTs, the first entry of each NAME
counting (v1's `_tpk_dims`). -/
def tpkDims (tpk : Value) : DimTable :=
  ((entriesOf tpk "DOF") ++ (entriesOf tpk "CONSTANT")).foldl (fun acc e =>
    match getStr? e "NAME" with
    | some n => if (acc.lookup n).isSome then acc else acc ++ [(n, (getStr? e "DIMENSION").bind dimsOf?)]
    | none => acc) []

/-- `t4_homogeneity`, fundamental test T4's law half: every LAW's EQUATION is
dimensionally homogeneous under the DIMENSIONs of the DOFs and CONSTANTs it names. A form
that does not parse is T1's to report. -/
def t4Homogeneity (tpk : Value) : Except Owed (List String) := do
  let dims := tpkDims tpk
  let mut probs : List String := []
  for e in entriesOf tpk "LAW" do
    let some f := getStr? e "EQUATION" | continue
    let .ok tree ← parseIn f .equation | continue
    if let .error r := tree.dims dims then
      probs := probs ++ ["LAW:" ++ nameOf e ++ ": EQUATION " ++ r ++ " (T4)"]
  finish probs

/-- `t6_totality`, fundamental test T6: every BOUNDARY's CONDITION is homogeneous and
every partial operation in it is guarded by a conjunct beside it. -/
def t6Totality (tpk : Value) : Except Owed (List String) := do
  let dims := tpkDims tpk
  let mut probs : List String := []
  for e in entriesOf tpk "BOUNDARY" do
    let some f := getStr? e "CONDITION" | continue
    let .ok (.pred p) ← parseIn f .predicate | continue
    let tag := "BOUNDARY:" ++ nameOf e
    match p.totalityProblems dims with
    | .error r => probs := probs ++ [tag ++ ": CONDITION " ++ r ++ " (T6)"]
    | .ok found => probs := probs ++ found.map fun q => tag ++ ": CONDITION " ++ q ++ " (T6)"
  finish probs

/-! ## IC4 (a), syntactic (S8) -/

/-- An expression with its identifiers renamed, D's operand and variable included. -/
def Expr.rename (m : String → String) : Expr → Expr
  | .num c => .num c
  | .ident n => .ident (m n)
  | .neg e => .neg (e.rename m)
  | .paren e => .paren (e.rename m)
  | .bin op l r => .bin op (l.rename m) (r.rename m)
  | .pow b p q => .pow (b.rename m) p q
  | .fn f a => .fn f (a.rename m)
  | .deriv x s n => .deriv (m x) (m s) n

/-- A form with its identifiers renamed. -/
def Tree.rename (m : String → String) : Tree → Tree
  | .eq l r => .eq (l.rename m) (r.rename m)
  | .expr e => .expr (e.rename m)
  | .pred p => .pred p

/-- Entries sorted by NAME, stably (v1's `sorted(..., key=_name)`). -/
def sortByName (es : List Entry) : List Entry :=
  let rec ins (e : Entry) : List Entry → List Entry
    | [] => [e]
    | x :: xs => if nameOf e < nameOf x then e :: x :: xs else x :: ins e xs
  es.foldl (fun acc e => ins e acc) []

/-- `ic4a_signature`, IC4 (a) read syntactically: for every SIGNATURE with FORM and
IMAGE_FORM, IMAGE_FORM is FORM with every DOF replaced by its entry's
ENVIRONMENT_QUANTITY, as canonical spellings. The problems, sorted, and the signatures
undecided because a name in FORM has no entry (IC2's gap, not IC4's failure). -/
def ic4aSignature (trm : Value) : Except Owed (List String × List String) := do
  let .obj _ := trm | return ([], [])
  let qOf : List (String × String) := (sortByName (entriesOf trm "ENTRIES")).foldl (fun acc e =>
    match getStr? e "DOF", getStr? e "ENVIRONMENT_QUANTITY" with
    | some d, some q => if (acc.lookup d).isSome then acc else acc ++ [(d, q)]
    | _, _ => acc) []
  let mut probs : List String := []
  let mut undecided : List String := []
  for sg in entriesOf (partOf trm "HEADER") "SIGNATURE" do
    let some f := getStr? sg "FORM" | continue
    let some im := getStr? sg "IMAGE_FORM" | continue
    let tag := "SIGNATURE:" ++ nameOf sg
    let .ok tf ← parseIn f .form | continue
    let .ok ti ← parseIn im .form | continue
    let missing := (sortedSet tf.names).filter fun n => (qOf.lookup n).isNone
    if !missing.isEmpty then
      undecided := undecided ++ ["IC4(a): " ++ tag ++ ": DOF " ++ ", ".intercalate missing ++ " untied, not decided"]
      continue
    let got := (tf.rename fun n => (qOf.lookup n).getD n).print
    let want := ti.print
    if got != want then
      probs := probs ++ ["IC4(a): " ++ tag ++ ": FORM under the entries reads " ++ got ++ ", not IMAGE_FORM " ++ want]
  return (← finish probs, sortedSet undecided)

end Principia.Form
