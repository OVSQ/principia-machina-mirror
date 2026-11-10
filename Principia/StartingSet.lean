import Principia.Zone.Fields
import Principia.Form.Checks

/-!
# The Starting Set's well-formedness (fundamental test T1)

v1's `t1_well_formed` (`tpc_zone` 0.5.1, schema 0.5.0; guide 3.6). Every entry carries its kind's fields and no others; every NAME is
an identifier and unique across the Starting Set; every citation resolves to the
kind it must; DOF and CONSTANT carry a DIMENSION that reads; decimals read; no entry
cites itself; a CONSTANT's or a FIX's UNIT has the DIMENSION it states a value of.
Schema 0.5.0: the PARAMETERS part carries D_VARIABLES ONE or SEVERAL only; a DOF's
ROLE is INPUT; a LAW's ROLE, required, is EOM(<a DOF>), CONSTRAINT, CONSTITUTIVE,
INVARIANT or DEFINITION.

A declared form parses (`Principia.Form.Grammar`) and names exactly the
members of its REFS, both ways (S5); the D-variable rules hold
(`Principia.Form.dVariableCheck`): every D variable a DOF that no CONSTRAINT targets, and
under ONE a single D variable.
-/

namespace Principia.StartingSet

open Principia.Zone

/-- The six kinds, in order. -/
def kinds : List String := ["DOF", "CONSTANT", "LAW", "ASSUMPTION", "CONSTRAINT", "BOUNDARY"]

/-- Each kind's required and optional fields. -/
def kindFields : String → List String × List String
  | "DOF" => (["NAME", "DIMENSION"], ["ROLE"])
  | "CONSTANT" => (["NAME", "DIMENSION"], ["VALUE", "UNIT", "UNCERTAINTY"])
  | "LAW" => (["NAME", "STATEMENT", "REFS", "ROLE"], ["EQUATION"])
  | "ASSUMPTION" => (["NAME", "PROPOSITION", "REFS"], [])
  | "CONSTRAINT" => (["NAME", "TARGET", "ACTION", "STATEMENT"], ["VALUE", "UNIT"])
  | "BOUNDARY" => (["NAME", "PREDICATE", "REFS"], ["CONDITION"])
  | _ => ([], [])

/-- A LAW's ROLE words besides EOM(<NAME>). -/
def lawRoleWords : List String := ["CONSTRAINT", "CONSTITUTIVE", "INVARIANT", "DEFINITION"]

/-- v1's `_EOM_ROLE`: `EOM(<identifier>)`, no space; the identifier. -/
def eomName? (role : String) : Option String :=
  if role.startsWith "EOM(" && role.endsWith ")" && role.length ≥ 5 then
    let n := String.ofList ((role.toList.drop 4).dropLast)
    if isIdent n then some n else none
  else none

/-- The words of v1's refusal of a LAW's ROLE. -/
def roleGrammar : String := "is not EOM(<DOF>), CONSTRAINT, CONSTITUTIVE, INVARIANT or DEFINITION"

/-- One entry, with its kind, name and tag. -/
structure Item where
  /-- Its kind. -/
  kind : String
  /-- Its NAME, or `?`. -/
  name : String
  /-- `KIND:NAME`, the problems' prefix. -/
  tag : String
  /-- The entry. -/
  entry : Entry

/-- v1's `_unit_against`: a UNIT that reads must have the DIMENSION it states a
value of; silent when either does not read (that is reported where it is found). -/
def unitAgainst (units : UnitHook) (tag : String) (unit : Option Value) (dimension : Option String)
    (whose : String) : List String :=
  match unit, dimension with
  | some (.str u), some d =>
    match units.unitDimension u with
    | .ok ud => if ud != d then [tag ++ ": UNIT " ++ u ++ " has dimension " ++ ud ++ ", not " ++ d ++ whose] else []
    | .error _ => []
  | _, _ => []

/-- S5: a LAW's EQUATION or a BOUNDARY's CONDITION, when it is a string free of disallowed
code points that parses, names exactly its REFS members, both ways. The grammar's owed
answers make the Starting Set owed before this is reached (`wellFormed`). -/
def formNamesProblems (tag kind : String) (e : Entry) (refs : List String) : List String :=
  let fieldMode : Option (String × Form.Mode) :=
    if kind == "LAW" then some ("EQUATION", .equation)
    else if kind == "BOUNDARY" then some ("CONDITION", .predicate) else none
  match fieldMode with
  | some (field, mode) =>
    match getStr? e field with
    | some f =>
      if (firstBad f).isSome then [] else
      match Form.formNames f mode with
      | .ok named =>
        (named.filter (!refs.contains ·)).map (fun x => tag ++ ": " ++ field ++ " names " ++ x ++ ", which is not in REFS") ++
        (refs.eraseDups.filter (!named.contains ·)).map (fun x => tag ++ ": REFS " ++ x ++ " is not named in " ++ field)
      | _ => []
    | none => []
  | none => []

/-- The problems of one entry against the whole Starting Set: ROLE, REFS, TARGET,
ACTION and the CONSTANT's fields. `kindOf` and `dimOf` read the first entry of each
NAME. -/
def itemProblems (units : UnitHook) (kindOf : String → Option String) (dimOf : String → Option String)
    (it : Item) : List String :=
  let e := it.entry
  let tag := it.tag
  let role := match getStr? e "ROLE" with
    | some r =>
      if it.kind == "DOF" && r != "INPUT" then [tag ++ ": ROLE " ++ r ++ " is not INPUT"]
      else if it.kind == "LAW" && !lawRoleWords.contains r then
        match eomName? r with
        | none => [tag ++ ": ROLE " ++ r ++ " " ++ roleGrammar]
        | some m => if kindOf m != some "DOF" then [tag ++ ": ROLE " ++ r ++ " names " ++ m ++ ", which is not a DOF"] else []
      else []
    | none => []
  let refs := match get? e "REFS" with
    | some v =>
      if ["LAW", "ASSUMPTION", "BOUNDARY"].contains it.kind && typeOk "REFS" v then
        ((strItems v).eraseDups.filterMap fun r =>
          if r == it.name then some (tag ++ ": cites itself")
          else match kindOf r with
            | none => some (tag ++ ": REFS " ++ r ++ " does not resolve")
            | some k => if k == "DOF" || k == "CONSTANT" then none
              else some (tag ++ ": REFS " ++ r ++ " is a " ++ k ++ ", not a DOF or CONSTANT")) ++
        formNamesProblems tag it.kind e (strItems v)
      else []
    | none => []
  let constraint :=
    if it.kind != "CONSTRAINT" then [] else
    let t := getStr? e "TARGET"
    let target := match t with
      | some t => if t == it.name then [tag ++ ": cites itself"]
        else if kindOf t != some "DOF" then [tag ++ ": TARGET " ++ t ++ " is not a DOF"] else []
      | none => []
    let a := getStr? e "ACTION"
    let action := match a with
      | some a =>
        if a != "REMOVE" && a != "FIX" then [tag ++ ": ACTION " ++ a ++ " is not REMOVE or FIX"]
        else
          (if a == "FIX" && !has e "VALUE" then [tag ++ ": FIX requires VALUE"] else []) ++
          (if a == "FIX" && !has e "UNIT" then [tag ++ ": FIX requires UNIT"] else []) ++
          (if a == "REMOVE" && has e "VALUE" then [tag ++ ": REMOVE forbids VALUE"] else []) ++
          (if a == "REMOVE" && has e "UNIT" then [tag ++ ": REMOVE forbids UNIT"] else [])
      | none => []
    let unit := match a, t with
      | some "FIX", some t =>
        if kindOf t == some "DOF" && t != it.name then unitAgainst units tag (get? e "UNIT") (dimOf t) (" of TARGET " ++ t)
        else []
      | _, _ => []
    target ++ action ++ unit
  let constant :=
    if it.kind != "CONSTANT" then [] else
    (if has e "VALUE" && !has e "UNIT" then [tag ++ ": VALUE requires UNIT"] else []) ++
    (if has e "UNIT" && !has e "VALUE" then [tag ++ ": UNIT requires VALUE"] else []) ++
    (if has e "UNCERTAINTY" && !has e "VALUE" then [tag ++ ": UNCERTAINTY requires VALUE"] else []) ++
    (match getStr? e "UNCERTAINTY" with
      | some u => if Decimal.sign u < 0 then [tag ++ ": UNCERTAINTY " ++ u ++ " is negative"] else []
      | none => []) ++
    unitAgainst units tag (get? e "UNIT") ((getStr? e "DIMENSION").bind Dimension.normalize) ""
  role ++ refs ++ constraint ++ constant

/-- The problems of a Starting Set that `owedOf` passed, before `done`. -/
def problems (units : UnitHook) : Value → List String
  | .obj z =>
    let unknown := z.filterMap fun (k, _) =>
      if kinds.contains k || k == "PARAMETERS" then none else some ("TPK: unknown kind " ++ k)
    let params := match get? z "PARAMETERS" with
      | none => []
      | some (.obj pm) =>
        checkFields units "TPK PARAMETERS" pm [] ["D_VARIABLES"] ++
          match getStr? pm "D_VARIABLES" with
          | some dv => if dv == "ONE" || dv == "SEVERAL" then []
            else ["TPK PARAMETERS: D_VARIABLES " ++ dv ++ " is not ONE or SEVERAL"]
          | none => []
      | some _ => ["TPK: PARAMETERS is not an object"]
    let parts := kinds.map fun k =>
      let (es, ps) := entries ("TPK kind " ++ k) ((get? z k).getD (.arr []))
      (es.map fun e => ({ kind := k, name := nameOf e, tag := k ++ ":" ++ nameOf e, entry := e } : Item), ps)
    let items := parts.flatMap (·.1)
    let shape := parts.flatMap (·.2)
    let fields := items.flatMap fun it =>
      let (req, opt) := kindFields it.kind
      checkFields units it.tag it.entry req opt
    let dup := (dupes (names (items.map (·.entry)))).map ("TPK: duplicate name " ++ ·)
    -- The first entry of each NAME gives its kind and its DIMENSION.
    let named := items.filterMap fun it => (getStr? it.entry "NAME").map fun n => (n, it)
    let kindOf (n : String) : Option String := (named.lookup n).map (·.kind)
    let dimOf (n : String) : Option String :=
      (named.lookup n).bind fun it => (getStr? it.entry "DIMENSION").bind Dimension.normalize
    unknown ++ params ++ shape ++ fields ++ dup ++ items.flatMap (itemProblems units kindOf dimOf)
  | _ => ["TPK: zone is not an object"]

/-- Fundamental test T1, well-formedness: v1's verdict, or owed. -/
def wellFormed (units : UnitHook) (tpk : Value) : Verdict :=
  match owedOf tpk with
  | some o => .owed o
  | none =>
    -- The forms' own checks; `namesCheck` reads every form `formNamesProblems` reads, so
    -- an owed answer there makes the verdict owed, never a silent pass.
    match Form.namesCheck tpk, Form.dVariableCheck tpk with
    | .error w, _ | _, .error w => .owed (ofFormOwed w)
    | .ok _, .ok dv => .checked (done (problems units tpk ++ dv))

end Principia.StartingSet
