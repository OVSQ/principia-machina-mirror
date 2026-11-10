import Principia.Provision.Reader
import Principia.Form
import Principia.StartingSet
import Principia.Digest

/-!
# A Provision's text: its reading and its digest

v1's `module_parse` and `module_digest` (tpm_module_spec 0.2.0 sections 3 and 4; TPS 5.22.2,
5.22.3). A Provision's text is one JSON object read by the strict reader, every field present
and an unknown field refused: ID and VERSION; TITLE and SOURCE; PREREQUISITES, the slots it
binds; PARAMETERS, each written into the Starting Set as a CONSTANT, DECLARED with its value
or AUTHOR with none; SUMS over a list slot; TERMS, each an expression of the declared-form
grammar without D, aimed at a DOF slot; ASSUMPTIONS and BOUNDARIES with their `{SLOT}`
placeholders; the NOT_CHOSEN and NOT_INCLUDED lines; EXCLUDES, INTERACTS_WITH and one to eight
TEST_BINDINGS, each a Starting Set passing fundamental test T1 with the slots' names, the
values and the answers. The checks run in v1's order, and the first problem is the refusal.

The digest (S49) is SHA-256 over `["TPC-MODULE", "1", canonical text]`: the fields of the
schema in their fixed order, every other object's members in code point order of their keys,
lists in their order, strings after line-ending normalization and NFC, escaped only for the
quotation mark, the backslash and the control characters, and no white space. The canonical
text and the preimage are computed here, and the digest is taken through the `DigestHook`
(the Calculator's is SHA-256).
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-! ## The parsed text -/

/-- A PREREQUISITE: a slot the Provision binds. -/
structure Slot where
  /-- The slot's name. -/
  slot : String
  /-- `DOF` or `CONSTANT`: the kind of Starting Set entry it binds. -/
  entryKind : String
  /-- Its DIMENSION, normalized. -/
  dim : String
  /-- The fewest names it takes. -/
  min : Nat
  /-- The most names it takes. -/
  max : Nat
  deriving Repr, Inhabited

/-- A PARAMETER, written into the Starting Set as a CONSTANT. -/
structure Parameter where
  name : String
  /-- Its DIMENSION, normalized. -/
  dim : String
  /-- `DECLARED` or `AUTHOR`. -/
  supply : String
  value : Option String
  unit : Option String
  uncertainty : Option String
  overridable : Option String
  deriving Repr, Inhabited

/-- A SUM over a list slot's names. -/
structure SumOver where
  name : String
  /-- The DOF slot it sums over. -/
  over : String
  /-- The EACH expression, as parsed. -/
  each : Form.Expr
  /-- Its canonical spelling. -/
  canon : String
  deriving Repr, Inhabited

/-- A TERM: a force aimed at a DOF slot. -/
structure Term where
  target : String
  /-- `+` or `-`. -/
  sign : String
  /-- The EXPR, as parsed. -/
  expr : Form.Expr
  canon : String
  label : String
  deriving Repr, Inhabited

/-- An ASSUMPTION the Provision writes. -/
structure Assumption where
  name : String
  proposition : String
  refs : List String
  deriving Repr, Inhabited

/-- A BOUNDARY the Provision writes. -/
structure Boundary where
  name : String
  predicate : String
  /-- The CONDITION, as parsed. -/
  condition : Form.Pred
  canon : String
  deriving Repr, Inhabited

/-- An INTERACTS_WITH question. -/
structure Question where
  /-- The ID or pattern of the Provisions it is raised with. -/
  withPattern : String
  qid : String
  yesLine : String
  noLine : String
  deriving Repr, Inhabited

/-- A TEST_BINDING: a fixture Starting Set with the slots' names, the values and the
answers. -/
structure Binding where
  name : String
  tpk : Value
  bind : Entry
  values : Entry
  answers : Entry
  deriving Repr, Inhabited

/-- A Provision's text, read and checked (v1's `_parse`). -/
structure Provision where
  id : String
  version : String
  /-- The value the strict reader gave: the canonical text is written from it. -/
  value : Value
  slots : List Slot
  params : List Parameter
  sums : List SumOver
  terms : List Term
  assumptions : List Assumption
  boundaries : List Boundary
  notChosen : String
  notIncluded : List String
  excludes : List String
  questions : List Question
  bindings : List Binding
  deriving Repr, Inhabited

/-- `ID VERSION`, as v1's messages name a Provision. -/
def Provision.cv (M : Provision) : String := M.id ++ " " ++ M.version

/-- The slot of a name. -/
def Provision.slotOf? (M : Provision) (s : String) : Option Slot := M.slots.find? (·.slot == s)

/-- The parameter of a name. -/
def Provision.paramOf? (M : Provision) (n : String) : Option Parameter := M.params.find? (·.name == n)

/-! ## Form trees -/

/-- The form grammar's answer as a computation: its refusal (already shown) or owed. -/
def ofForm {α : Type} : Form.Answer α → Run α
  | .ok a => pure a
  | .refused r => refuse r
  | .owed (.exact w) => owe (.exact w)

/-- Whether an expression holds a D. -/
def exprHasD : Form.Expr → Bool
  | .num _ | .ident _ => false
  | .neg e | .paren e | .pow e _ _ | .fn _ e => exprHasD e
  | .bin _ l r => exprHasD l || exprHasD r
  | .deriv _ _ _ => true

/-- An expression with every identifier `x` that `m` maps replaced (v1's `_subst`). -/
def exprSubst (m : String → Option Form.Expr) : Form.Expr → Form.Expr
  | .ident x => (m x).getD (.ident x)
  | .num c => .num c
  | .neg e => .neg (exprSubst m e)
  | .paren e => .paren (exprSubst m e)
  | .bin op l r => .bin op (exprSubst m l) (exprSubst m r)
  | .pow b p q => .pow (exprSubst m b) p q
  | .fn f a => .fn f (exprSubst m a)
  | .deriv x s n => .deriv x s n

/-- A predicate with every identifier `x` that `m` maps replaced. -/
def predSubst (m : String → Option Form.Expr) : Form.Pred → Form.Pred
  | .cmp op l r => .cmp op (exprSubst m l) (exprSubst m r)
  | .and a b => .and (predSubst m a) (predSubst m b)
  | .or a b => .or (predSubst m a) (predSubst m b)
  | .not a => .not (predSubst m a)
  | .paren a => .paren (predSubst m a)

/-- v1's `_idents`: the identifiers a tree names, D's operand and variable included, sorted
without repeats. -/
def identsOf (names : List String) : List String := sortedSet names

/-- v1's `_form_tree` in expression mode. -/
def exprTree (tag field text : String) : Run Form.Expr :=
  match Form.formTree text .expression with
  | .ok (.expr e) => pure e
  | .ok _ => refuse (tag ++ ": " ++ field ++ " does not parse: internal: not an expression")
  | .refused r => refuse (tag ++ ": " ++ field ++ " does not parse: " ++ r)
  | .owed (.exact w) => owe (.exact w)

/-- v1's `_form_tree` in predicate mode. -/
def predTree (tag field text : String) : Run Form.Pred :=
  match Form.formTree text .predicate with
  | .ok (.pred p) => pure p
  | .ok _ => refuse (tag ++ ": " ++ field ++ " does not parse: internal: not a predicate")
  | .refused r => refuse (tag ++ ": " ++ field ++ " does not parse: " ++ r)
  | .owed (.exact w) => owe (.exact w)

/-! ## The checks (section 3) -/

/-- The fields of the text, in their fixed order. -/
def topFields : List String :=
  ["ID", "VERSION", "TITLE", "SOURCE", "PREREQUISITES", "PARAMETERS", "SUMS", "TERMS",
   "ASSUMPTIONS", "BOUNDARIES", "NOT_CHOSEN", "NOT_INCLUDED", "EXCLUDES", "INTERACTS_WITH",
   "TEST_BINDINGS"]

/-- The fields of each list of objects, in their fixed order. -/
def fieldOrder : String → Option (List String)
  | "PREREQUISITES" => some ["SLOT", "KIND", "DIMENSION", "MIN", "MAX", "LABEL"]
  | "PARAMETERS" => some ["NAME", "DIMENSION", "SUPPLY", "LABEL", "VALUE", "UNIT", "UNCERTAINTY",
                          "OVERRIDABLE"]
  | "SUMS" => some ["NAME", "OVER", "EACH"]
  | "TERMS" => some ["TARGET", "SIGN", "EXPR", "LABEL"]
  | "ASSUMPTIONS" => some ["NAME", "PROPOSITION", "REFS"]
  | "BOUNDARIES" => some ["NAME", "PREDICATE", "CONDITION"]
  | "INTERACTS_WITH" => some ["WITH", "QUESTION_ID", "QUESTION", "YES_LINE", "NO_LINE"]
  | "TEST_BINDINGS" => some ["NAME", "TPK", "BIND", "VALUES", "ANSWERS"]
  | _ => none

/-- v1's `_placeholders`: every brace opens a `{SLOT}` naming a slot of this Provision. -/
def placeholders (tag : String) (s : String) (slots : List String) : Run Unit := do
  let rec go : Nat → List Char → Run Unit
    | 0, _ => pure ()
    | _ + 1, [] => pure ()
    | _ + 1, '}' :: _ => refuse (tag ++ ": a brace outside a {SLOT} placeholder")
    | f + 1, '{' :: rest =>
      match rest.findIdx? (· == '}') with
      | none => refuse (tag ++ ": a brace outside a {SLOT} placeholder")
      | some j =>
        let x := String.ofList (rest.take j)
        if slots.contains x then go f (rest.drop (j + 1))
        else refuse (tag ++ ": {" ++ x ++ "} is not a slot of this module")
    | f + 1, _ :: rest => go f rest
  go (s.length + 1) s.toList

/-- v1's VALUE OBJECT checks (6.3 B4), `tag` naming the value. -/
def valueObject (tag : String) (v : Value) (dim : String) : Run Unit := do
  let .obj o := v | refuse (tag ++ " has the wrong type")
  for k in keysOf o do
    unless ["VALUE", "UNIT", "UNCERTAINTY"].contains k do refuse (tag ++ ": unknown field " ++ k)
  if has o "VALUE" && !has o "UNIT" then refuse (tag ++ ": VALUE requires UNIT")
  if has o "UNIT" && !has o "VALUE" then refuse (tag ++ ": UNIT requires VALUE")
  if has o "UNCERTAINTY" && !has o "VALUE" then refuse (tag ++ ": UNCERTAINTY requires VALUE")
  for f in ["VALUE", "UNIT", "UNCERTAINTY"] do
    if let some fv := get? o f then
      let x ← str tag f fv
      if f == "VALUE" && (Decimal.canon x).isNone then refuse (tag ++ ": VALUE " ++ x ++ " is not a decimal")
      if f == "UNIT" then
        if let .error r := unitParse x then refuse (tag ++ ": " ++ r)
      if f == "UNCERTAINTY" then
        if (Decimal.canon x).isNone then refuse (tag ++ ": UNCERTAINTY " ++ x ++ " is not a decimal")
        if Decimal.sign x < 0 then refuse (tag ++ ": UNCERTAINTY " ++ x ++ " is negative")
  if let some (.str u) := get? o "UNIT" then
    if let .ok (_, ud) := unitParse u then
      if ud != dim then refuse (tag ++ ": UNIT " ++ u ++ " has dimension " ++ ud ++ ", not " ++ dim)

/-- An entry name refusal. -/
def entryNameMsg (tag n : String) : String :=
  tag ++ ": NAME " ++ n ++ " is not an entry name (an identifier with a lower-case letter)"

/-- v1's `t1_well_formed` through the zones' check: its first problem, or none; owed as the
zones owe. -/
def t1First (tpk : Value) : Run (Option String) :=
  match StartingSet.wellFormed .calculator tpk with
  | .checked [] => pure none
  | .checked (p :: _) => pure (some p)
  | .owed o => owe (.exact o.message)

/-- The PREREQUISITES (3.2). -/
def readSlots (v : Value) : Run (List Slot) := do
  let mut slots : List Slot := []
  for e in ← objs "MODULE" "PREREQUISITES" v 16 do
    let tag := tagOf "PREREQUISITE:" e "SLOT"
    fields tag e ["SLOT", "KIND", "DIMENSION", "MIN", "MAX", "LABEL"]
    let s ← str tag "SLOT" (field e "SLOT")
    unless isSlot s do refuse (tag ++ ": SLOT " ++ s ++ " is not a slot name")
    let k ← str tag "KIND" (field e "KIND")
    unless k == "DOF" || k == "CONSTANT" do refuse (tag ++ ": KIND " ++ k ++ " is not DOF or CONSTANT")
    let d ← dimension tag (← str tag "DIMENSION" (field e "DIMENSION"))
    let mut bounds : List Nat := []
    for f in ["MIN", "MAX"] do
      let n? : Option Nat := match field e f with
        | .int n => if 1 ≤ n && n ≤ 16 then some n.toNat else none
        | _ => none
      let some n := n? | refuse (tag ++ ": " ++ f ++ " is not an integer from 1 to 16")
      bounds := bounds ++ [n]
    let mn := bounds.getD 0 0
    let mx := bounds.getD 1 0
    discard <| str tag "LABEL" (field e "LABEL") (blankOk := false)
    if mn > mx then refuse (tag ++ ": MIN is greater than MAX")
    if k == "CONSTANT" && !(mn == 1 && mx == 1) then refuse (tag ++ ": a CONSTANT slot takes exactly one name")
    slots := slots ++ [⟨s, k, d, mn, mx⟩]
  if let some d := leastDup (slots.map (·.slot)) then refuse ("MODULE: duplicate slot " ++ d)
  pure slots

/-- The PARAMETERS (3.3). -/
def readParams (v : Value) : Run (List Parameter) := do
  let mut params : List Parameter := []
  for e in ← objs "MODULE" "PARAMETERS" v 32 do
    let tag := tagOf "PARAMETER:" e "NAME"
    fields tag e ["NAME", "DIMENSION", "SUPPLY", "LABEL"] ["VALUE", "UNIT", "UNCERTAINTY", "OVERRIDABLE"]
    let n ← str tag "NAME" (field e "NAME")
    unless isEntryName n do refuse (entryNameMsg tag n)
    let d ← dimension tag (← str tag "DIMENSION" (field e "DIMENSION"))
    let sup ← str tag "SUPPLY" (field e "SUPPLY")
    unless sup == "DECLARED" || sup == "AUTHOR" do refuse (tag ++ ": SUPPLY " ++ sup ++ " is not DECLARED or AUTHOR")
    discard <| str tag "LABEL" (field e "LABEL") (blankOk := false)
    if has e "VALUE" then
      let x ← str tag "VALUE" (field e "VALUE")
      if (Decimal.canon x).isNone then refuse (tag ++ ": VALUE " ++ x ++ " is not a decimal")
    if has e "UNIT" then
      if let .error r := unitParse (← str tag "UNIT" (field e "UNIT")) then refuse (tag ++ ": " ++ r)
    if has e "UNCERTAINTY" then
      let x ← str tag "UNCERTAINTY" (field e "UNCERTAINTY")
      if (Decimal.canon x).isNone then refuse (tag ++ ": UNCERTAINTY " ++ x ++ " is not a decimal")
      if Decimal.sign x < 0 then refuse (tag ++ ": UNCERTAINTY " ++ x ++ " is negative")
    if has e "OVERRIDABLE" then
      let o ← str tag "OVERRIDABLE" (field e "OVERRIDABLE")
      unless o == "YES" || o == "NO" do refuse (tag ++ ": OVERRIDABLE " ++ o ++ " is not YES or NO")
    if sup == "DECLARED" then
      for f in ["VALUE", "UNIT", "OVERRIDABLE"] do
        unless has e f do refuse (tag ++ ": DECLARED requires " ++ f)
    else
      for f in ["VALUE", "UNIT", "UNCERTAINTY", "OVERRIDABLE"] do
        if has e f then refuse (tag ++ ": AUTHOR forbids " ++ f)
    if let some u := getStr? e "UNIT" then
      if let .ok (_, ud) := unitParse u then
        if ud != d then refuse (tag ++ ": UNIT " ++ u ++ " has dimension " ++ ud ++ ", not " ++ d)
    params := params ++ [⟨n, d, sup, getStr? e "VALUE", getStr? e "UNIT", getStr? e "UNCERTAINTY",
      getStr? e "OVERRIDABLE"⟩]
  if let some d := leastDup (params.map (·.name)) then refuse ("MODULE: duplicate parameter " ++ d)
  pure params

/-- The SUMS (3.4). -/
def readSums (v : Value) (slots : List Slot) (pnames : List String) : Run (List SumOver) := do
  let mut sums : List SumOver := []
  for e in ← objs "MODULE" "SUMS" v 16 do
    let tag := tagOf "SUM:" e "NAME"
    fields tag e ["NAME", "OVER", "EACH"]
    let n ← str tag "NAME" (field e "NAME")
    unless isSlot n do refuse (tag ++ ": NAME " ++ n ++ " is not a slot name")
    if slots.any (·.slot == n) then refuse (tag ++ ": NAME " ++ n ++ " is the name of a slot")
    let o ← str tag "OVER" (field e "OVER")
    unless slots.any (fun s => s.slot == o && s.entryKind == "DOF") do
      refuse (tag ++ ": OVER " ++ o ++ " is not a DOF slot")
    let each ← exprTree tag "EACH" (← str tag "EACH" (field e "EACH"))
    if exprHasD each then refuse (tag ++ ": EACH uses D")
    for x in identsOf each.names do
      if x != o && !pnames.contains x then
        refuse (tag ++ ": EACH names " ++ x ++ ", which is not " ++ o ++ " or a parameter")
    sums := sums ++ [⟨n, o, each, (Form.Tree.expr each).print⟩]
  if let some d := leastDup (sums.map (·.name)) then refuse ("MODULE: duplicate sum " ++ d)
  pure sums

/-- The TERMS (3.5). -/
def readTerms (v : Value) (slots : List Slot) (pnames : List String) (sums : List SumOver) :
    Run (List Term) := do
  let mut terms : List Term := []
  let mut i := 0
  for e in ← objs "MODULE" "TERMS" v 16 do
    i := i + 1
    let tag := s!"TERM:{i}"
    fields tag e ["TARGET", "SIGN", "EXPR", "LABEL"]
    let t ← str tag "TARGET" (field e "TARGET")
    unless slots.any (fun s => s.slot == t && s.entryKind == "DOF") do
      refuse (tag ++ ": TARGET " ++ t ++ " is not a DOF slot")
    let sg ← str tag "SIGN" (field e "SIGN")
    unless sg == "+" || sg == "-" do refuse (tag ++ ": SIGN " ++ sg ++ " is not + or -")
    let ex ← exprTree tag "EXPR" (← str tag "EXPR" (field e "EXPR"))
    let canon := (Form.Tree.expr ex).print
    if canon.startsWith "-" then refuse (tag ++ ": EXPR begins with a minus sign; the sign is SIGN's")
    if exprHasD ex then refuse (tag ++ ": EXPR uses D")
    for x in identsOf ex.names do
      let s? := slots.find? (·.slot == x)
      if let some s := s? then
        if s.max > 1 && x != t then refuse (tag ++ ": EXPR names the list slot " ++ x ++ " outside its own TERM")
      if !(s?.isSome || pnames.contains x || sums.any (·.name == x)) then
        refuse (tag ++ ": EXPR names " ++ x ++ ", which is not a slot, parameter or sum of this module")
    let lab ← str tag "LABEL" (field e "LABEL") (blankOk := false)
    terms := terms ++ [⟨t, sg, ex, canon, lab⟩]
  pure terms

/-- The ASSUMPTIONS (3.6). -/
def readAssumptions (v : Value) (slots : List Slot) (pnames : List String) : Run (List Assumption) := do
  let mut asms : List Assumption := []
  for e in ← objs "MODULE" "ASSUMPTIONS" v 32 do
    let tag := tagOf "ASSUMPTION:" e "NAME"
    fields tag e ["NAME", "PROPOSITION", "REFS"]
    let n ← str tag "NAME" (field e "NAME")
    unless isEntryName n do refuse (entryNameMsg tag n)
    let prop ← str tag "PROPOSITION" (field e "PROPOSITION") (blankOk := false)
    placeholders (tag ++ ": PROPOSITION") prop (slots.map (·.slot))
    let refs ← strs tag "REFS" (field e "REFS")
    if refs.eraseDups.length != refs.length then refuse (tag ++ ": field REFS has duplicate entries")
    for r in refs do
      unless slots.any (·.slot == r) || pnames.contains r do
        refuse (tag ++ ": REFS " ++ r ++ " is not a slot or parameter of this module")
    asms := asms ++ [⟨n, prop, refs⟩]
  pure asms

/-- The BOUNDARIES (3.7). -/
def readBoundaries (v : Value) (slots : List Slot) (pnames : List String) (sums : List SumOver) :
    Run (List Boundary) := do
  let mut bnds : List Boundary := []
  for e in ← objs "MODULE" "BOUNDARIES" v 16 do
    let tag := tagOf "BOUNDARY:" e "NAME"
    fields tag e ["NAME", "PREDICATE", "CONDITION"]
    let n ← str tag "NAME" (field e "NAME")
    unless isEntryName n do refuse (entryNameMsg tag n)
    let pred ← str tag "PREDICATE" (field e "PREDICATE") (blankOk := false)
    placeholders (tag ++ ": PREDICATE") pred (slots.map (·.slot))
    let cond ← predTree tag "CONDITION" (← str tag "CONDITION" (field e "CONDITION"))
    for x in identsOf cond.names do
      let s? := slots.find? (·.slot == x)
      if let some s := s? then
        if s.max > 1 then refuse (tag ++ ": CONDITION names the list slot " ++ x ++ " outside a sum")
      if !(s?.isSome || pnames.contains x || sums.any (·.name == x)) then
        refuse (tag ++ ": CONDITION names " ++ x ++ ", which is not a slot, parameter or sum of this module")
    bnds := bnds ++ [⟨n, pred, cond, (Form.Tree.pred cond).print⟩]
  pure bnds

/-- The INTERACTS_WITH questions (3.8). -/
def readQuestions (v : Value) (mid : String) : Run (List Question) := do
  let mut qs : List Question := []
  let mut i := 0
  for e in ← objs "MODULE" "INTERACTS_WITH" v 16 do
    i := i + 1
    let tag := s!"INTERACTS_WITH:{i}"
    fields tag e ["WITH", "QUESTION_ID", "QUESTION", "YES_LINE", "NO_LINE"]
    let w ← str tag "WITH" (field e "WITH")
    unless isPattern w do refuse (tag ++ ": WITH " ++ w ++ " is not a module ID or pattern")
    if idMatches w mid then refuse (tag ++ ": WITH " ++ w ++ " matches the module's own ID")
    let q ← str tag "QUESTION_ID" (field e "QUESTION_ID")
    unless isSlot q do refuse (tag ++ ": QUESTION_ID " ++ q ++ " is not a question ID")
    discard <| str tag "QUESTION" (field e "QUESTION") (blankOk := false)
    let yes ← str tag "YES_LINE" (field e "YES_LINE") (blankOk := false)
    let no ← str tag "NO_LINE" (field e "NO_LINE") (blankOk := false)
    qs := qs ++ [⟨w, q, yes, no⟩]
  if let some d := leastDup (qs.map (·.qid)) then refuse ("MODULE: duplicate question " ++ d)
  pure qs

/-- The TEST_BINDINGS (3.9). -/
def readBindings (v : Value) (slots : List Slot) (params : List Parameter) : Run (List Binding) := do
  let some tb := objList? v | refuse "MODULE: field TEST_BINDINGS has the wrong type"
  if tb.isEmpty then refuse "MODULE: field TEST_BINDINGS is empty (a module declares at least one test binding)"
  if tb.length > 8 then refuse "MODULE: field TEST_BINDINGS has more than 8 entries"
  let mut bindings : List Binding := []
  for e in tb do
    let tag := tagOf "TEST_BINDING:" e "NAME"
    fields tag e ["NAME", "TPK", "BIND", "VALUES", "ANSWERS"]
    let n ← str tag "NAME" (field e "NAME")
    unless isSlot n do refuse (tag ++ ": NAME " ++ n ++ " is not a binding name")
    let tpk := field e "TPK"
    let .obj _ := tpk | refuse (tag ++ ": field TPK has the wrong type")
    if let some p ← t1First tpk then refuse (tag ++ ": TPK fails T1: " ++ p)
    let .obj b := field e "BIND" | refuse (tag ++ ": field BIND has the wrong type")
    for k in keysOf b do
      unless slots.any (·.slot == k) do refuse (tag ++ ": BIND: unknown slot " ++ k)
    for s in slots do
      unless has b s.slot do refuse (tag ++ ": BIND: slot " ++ s.slot ++ " is not bound")
    for s in slots do
      if (strList? (field b s.slot)).isNone then refuse (tag ++ ": BIND: slot " ++ s.slot ++ " has the wrong type")
    let .obj vals := field e "VALUES" | refuse (tag ++ ": field VALUES has the wrong type")
    for k in keysOf vals do
      unless params.any (·.name == k) do refuse (tag ++ ": VALUES: unknown parameter " ++ k)
    for k in keysOf vals do
      let x := field vals k
      match x with
      | .obj [] => pure ()
      | _ =>
        let dim := ((params.find? (·.name == k)).map (·.dim)).getD ""
        valueObject (tag ++ ": VALUES: " ++ k) x dim
    let .obj ans := field e "ANSWERS" | refuse (tag ++ ": field ANSWERS has the wrong type")
    for k in keysOf ans do
      unless isAnswerKey k do refuse (tag ++ ": ANSWERS: " ++ k ++ " is not a question")
      match field ans k with
      | .str "YES" | .str "NO" => pure ()
      | _ => refuse (tag ++ ": ANSWERS: " ++ k ++ " is not YES or NO")
    bindings := bindings ++ [⟨n, tpk, b, vals, ans⟩]
  if let some d := leastDup (bindings.map (·.name)) then refuse ("MODULE: duplicate test binding " ++ d)
  pure bindings

/-- v1's `_parse`: a Provision's text read and checked, in v1's order. -/
def parseText (text : Value) : Run Provision := do
  let v ← readText text
  let .obj o := v | refuse "MODULE: the text is not a JSON object"
  fields "MODULE" o topFields
  let mid ← str "MODULE" "ID" (field o "ID")
  unless isProvisionId mid do refuse ("MODULE: ID " ++ mid ++ " is not a module ID")
  let ver ← str "MODULE" "VERSION" (field o "VERSION")
  unless isVersion ver do refuse ("MODULE: VERSION " ++ ver ++ " is not a version")
  discard <| str "MODULE" "TITLE" (field o "TITLE") (blankOk := false)
  discard <| str "MODULE" "SOURCE" (field o "SOURCE") (blankOk := false)
  let slots ← readSlots (field o "PREREQUISITES")
  let params ← readParams (field o "PARAMETERS")
  let pnames := params.map (·.name)
  let sums ← readSums (field o "SUMS") slots pnames
  let terms ← readTerms (field o "TERMS") slots pnames sums
  let asms ← readAssumptions (field o "ASSUMPTIONS") slots pnames
  if let some d := leastDup (pnames ++ asms.map (·.name)) then refuse ("MODULE: duplicate entry name " ++ d)
  let bnds ← readBoundaries (field o "BOUNDARIES") slots pnames sums
  if let some d := leastDup (pnames ++ asms.map (·.name) ++ bnds.map (·.name)) then
    refuse ("MODULE: duplicate entry name " ++ d)
  let nc ← str "MODULE" "NOT_CHOSEN" (field o "NOT_CHOSEN") (blankOk := false)
  let ni ← strs "MODULE" "NOT_INCLUDED" (field o "NOT_INCLUDED") (some 32)
  let mut i := 0
  for x in ni do
    i := i + 1
    if Zone.blank x then refuse s!"MODULE: NOT_INCLUDED {i} is blank"
  if ni.eraseDups.length != ni.length then refuse "MODULE: field NOT_INCLUDED has duplicate entries"
  let ex ← strs "MODULE" "EXCLUDES" (field o "EXCLUDES") (some 32)
  for p in ex do
    unless isPattern p do refuse ("MODULE: EXCLUDES " ++ p ++ " is not a module ID or pattern")
    if idMatches p mid then refuse ("MODULE: EXCLUDES " ++ p ++ " matches the module's own ID")
  if ex.eraseDups.length != ex.length then refuse "MODULE: field EXCLUDES has duplicate entries"
  let qs ← readQuestions (field o "INTERACTS_WITH") mid
  let bs ← readBindings (field o "TEST_BINDINGS") slots params
  pure { id := mid, version := ver, value := v, slots, params, sums, terms, assumptions := asms,
         boundaries := bnds, notChosen := nc, notIncluded := ni, excludes := ex, questions := qs,
         bindings := bs }

/-! ## module_parse's answer -/

/-- What `module_parse` answers: the ID, the VERSION and each part's summary. -/
structure Parsed where
  id : String
  version : String
  slots : List (String × String × String × Nat × Nat)
  params : List (String × String × String)
  sums : List (String × String × String)
  terms : List (String × String × String)
  assumptions : List String
  boundaries : List (String × String)
  excludes : List String
  questions : List (String × String)
  bindings : List String
  deriving DecidableEq, Repr

/-- The summary of a parsed text. -/
def Provision.parsed (M : Provision) : Parsed where
  id := M.id
  version := M.version
  slots := M.slots.map fun s => (s.slot, s.entryKind, s.dim, s.min, s.max)
  params := M.params.map fun p => (p.name, p.supply, p.dim)
  sums := M.sums.map fun s => (s.name, s.over, s.canon)
  terms := M.terms.map fun t => (t.target, t.sign, t.canon)
  assumptions := M.assumptions.map (·.name)
  boundaries := M.boundaries.map fun b => (b.name, b.canon)
  excludes := sortStrs M.excludes
  questions := M.questions.map fun q => (q.withPattern, q.qid)
  bindings := M.bindings.map (·.name)

/-- v1's `module_parse`. -/
def parse (text : Value) : Answer Parsed := finish ((parseText text).map Provision.parsed)

/-! ## The canonical text and the digest (section 4, S49) -/

/-- v1's `_ct_str`: a string after `_text`, quoted, with only `"`, `\` and the control
characters escaped (`\u00XX`, lower case). -/
def ctStr (s : String) : Run String := do
  let t ← text s
  pure (String.ofList ('"' :: t.toList.flatMap Canonical.escapeChar ++ ['"']))

mutual
/-- v1's `_ct_value`: a value outside the schema's objects, members in code point order of
their keys. -/
def ctValue : Value → Run String
  | .bool true => pure "true"
  | .bool false => pure "false"
  | .null | .real => pure "null"
  | .str s => ctStr s
  | .int n => pure (toString n)
  | .arr xs => do pure ("[" ++ ",".intercalate (← ctValues xs) ++ "]")
  | .obj kvs => do
    let ms ← ctMembers kvs
    pure ("{" ++ ",".intercalate ((ms.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)) ++ "}")
/-- Each value of a list. -/
def ctValues : List Value → Run (List String)
  | [] => pure []
  | x :: xs => do pure ((← ctValue x) :: (← ctValues xs))
/-- Each member of an object: its key and its text. -/
def ctMembers : List (String × Value) → Run (List (String × String))
  | [] => pure []
  | (k, x) :: kvs => do pure ((k, (← ctStr k) ++ ":" ++ (← ctValue x)) :: (← ctMembers kvs))
end

/-- v1's `_canonical_text`: the schema's objects in their fixed field order. -/
def canonicalText (v : Value) : Run String := do
  let .obj o := v | refuse "internal: the text is not an object"
  let mut parts : List String := []
  for k in topFields do
    let x := field o k
    match fieldOrder k with
    | some order =>
      let es := (objList? x).getD []
      let mut items : List String := []
      for e in es do
        let mut fs : List String := []
        for f in order do
          if let some fv := get? e f then fs := fs ++ [(← ctStr f) ++ ":" ++ (← ctValue fv)]
        items := items ++ ["{" ++ ",".intercalate fs ++ "}"]
      parts := parts ++ [(← ctStr k) ++ ":[" ++ ",".intercalate items ++ "]"]
    | none => parts := parts ++ [(← ctStr k) ++ ":" ++ (← ctValue x)]
  pure ("{" ++ ",".intercalate parts ++ "}")

/-- The preimage of a Provision's digest (S49): `["TPC-MODULE", "1", canonical text]`. -/
def Provision.preimage (M : Provision) : Run String := do
  pure (Digest.preimage ["TPC-MODULE", "1", ← canonicalText M.value])

/-- A Provision's digest, through the hook. -/
def Provision.digest (D : DigestHook) (M : Provision) : Run String := do
  D.digest (← M.preimage)

/-- v1's `module_digest`: the text's digest, or `module_parse`'s refusal. -/
def digest (D : DigestHook) (text : Value) : Answer String :=
  finish do (← parseText text).digest D

end Principia.Provision
