import Principia.Zone.Fields
import Principia.Form.Grammar

/-!
# The Correspondence Table's well-formedness

v1's `trm_well_formed` (`tpc_zone` 0.5.1, schema 0.5.0; TPS 2.3.11, guide 4.3):
the table's schema against its Starting Set, structural only (the isomorphism
checks IC1 to IC5 are separate). A HEADER with the REFERENT INVENTORY
(`ENVIRONMENT_INVENTORY` on the wire), the SIGNATURE and the TRANSFORMATIONS, then
the ENTRIES; every entry's DOF a DOF of the Starting Set, its ENVIRONMENT_QUANTITY in
the inventory, its DOMAIN and FALSIFIER not blank, its FALSIFIER_CLASS F1, F2 or F3,
and what it BEARS a LAW or CONSTRAINT of the Starting Set.

A SIGNATURE's FORM and IMAGE_FORM come together; FORM, when it parses, names
exactly the members of OVER, and IMAGE_FORM names only quantities of the inventory
(`Principia.Form.Grammar`).
-/

namespace Principia.Correspondence

open Principia.Zone

/-- The parts of the table. -/
def partsOf : List String := ["HEADER", "ENTRIES"]
/-- The parts of the HEADER. -/
def headerParts : List String := ["ENVIRONMENT_INVENTORY", "SIGNATURE", "TRANSFORMATIONS"]
/-- An inventory entry's fields. -/
def inventoryFields : List String := ["ENVIRONMENT_QUANTITY", "DIMENSION"]
/-- A SIGNATURE's required and optional fields. -/
def signatureFields : List String × List String := (["NAME", "OVER", "IMAGE"], ["FORM", "IMAGE_FORM"])
/-- A TRANSFORMATION's fields. -/
def transformationFields : List String := ["NAME", "STATEMENT"]
/-- An ENTRY's fields. -/
def entryFields : List String :=
  ["NAME", "DOF", "DOMAIN", "ENVIRONMENT_QUANTITY", "IDENTIFICATION", "FALSIFIER", "FALSIFIER_CLASS",
    "BEARS", "DIMENSION"]

/-- v1's `_tpk_names`: the NAMEs of the Starting Set's entries of these kinds. -/
def tpkNames (tpk : Value) (kinds : List String) : List String :=
  match tpk with
  | .obj z => kinds.flatMap fun k =>
    match get? z k with
    | some (.arr xs) => xs.filterMap fun | .obj e => getStr? e "NAME" | _ => none
    | _ => []
  | _ => []

/-- A SIGNATURE's forms: FORM and IMAGE_FORM come together; FORM, a string free
of disallowed code points that parses, names exactly OVER's members (when OVER is a list
of strings); IMAGE_FORM names only quantities of the inventory. The grammar's owed
answers make the table owed before this is reached (`owedOf`). -/
def signatureFormProblems (tag : String) (e : Entry) (quantities : List String) : List String :=
  let pairing :=
    (if has e "FORM" && !has e "IMAGE_FORM" then [tag ++ ": FORM requires IMAGE_FORM"] else []) ++
    (if has e "IMAGE_FORM" && !has e "FORM" then [tag ++ ": IMAGE_FORM requires FORM"] else [])
  let names (f : String) : Option (List String) :=
    if (firstBad f).isSome then none else
    match Form.formNames f .form with
    | .ok ns => some ns
    | _ => none
  let form := match getStr? e "FORM", get? e "OVER" with
    | some f, some ov =>
      if typeOk "OVER" ov then
        match names f with
        | some named =>
          let over := (strItems ov).eraseDups
          (named.filter (!over.contains ·)).map (fun x => tag ++ ": FORM names " ++ x ++ ", which is not in OVER") ++
          (over.filter (!named.contains ·)).map (fun x => tag ++ ": OVER " ++ x ++ " is not named in FORM")
        | none => []
      else []
    | _, _ => []
  let image := match getStr? e "IMAGE_FORM" with
    | some f => match names f with
      | some named => (named.filter (!quantities.contains ·)).map fun x =>
          tag ++ ": IMAGE_FORM names " ++ x ++ ", which is not in the ENVIRONMENT INVENTORY"
      | none => []
    | none => []
  pairing ++ form ++ image

/-- The problems of the HEADER, given the Starting Set's DOFs; and the inventory's
quantities. -/
def headerProblems (units : UnitHook) (dofs : List String) (h : Entry) : List String × List String :=
  let unknown := h.filterMap fun (p, _) =>
    if headerParts.contains p then none else some ("TrM HEADER: unknown part " ++ p)
  let missing := headerParts.filterMap fun p =>
    if has h p then none else some ("TrM HEADER: missing part " ++ p)
  let (env, envShape) := entries "TrM ENVIRONMENT_INVENTORY" ((get? h "ENVIRONMENT_INVENTORY").getD (.arr []))
  let envProbs := env.flatMap fun e =>
    let tag := "ENV:" ++ nameOf e "ENVIRONMENT_QUANTITY"
    checkFields units tag e inventoryFields [] ++
      match getStr? e "ENVIRONMENT_QUANTITY" with
      | some q => if isIdent q then [] else [tag ++ ": ENVIRONMENT_QUANTITY " ++ q ++ " is not an identifier"]
      | none => []
  let quantities := names env "ENVIRONMENT_QUANTITY"
  let envDup := (dupes quantities).map ("TrM: duplicate environment quantity " ++ ·)
  let (sig, sigShape) := entries "TrM SIGNATURE" ((get? h "SIGNATURE").getD (.arr []))
  let sigProbs := sig.flatMap fun e =>
    let tag := "SIGNATURE:" ++ nameOf e
    checkFields units tag e signatureFields.1 signatureFields.2 ++
      (match get? e "OVER" with
      | some v => if typeOk "OVER" v then
          (strItems v).eraseDups.filterMap fun d =>
            if dofs.contains d then none else some (tag ++ ": OVER " ++ d ++ " is not a TPK DOF")
        else []
      | none => []) ++
      signatureFormProblems tag e quantities
  let sigDup := (dupes (names sig)).map ("TrM: duplicate signature name " ++ ·)
  let (trf, trfShape) := entries "TrM TRANSFORMATIONS" ((get? h "TRANSFORMATIONS").getD (.arr []))
  let trfProbs := trf.flatMap fun e => checkFields units ("TRANSFORMATION:" ++ nameOf e) e transformationFields []
  let trfDup := (dupes (names trf)).map ("TrM: duplicate transformation name " ++ ·)
  (unknown ++ missing ++ envShape ++ envProbs ++ envDup ++ sigShape ++ sigProbs ++ sigDup ++ trfShape ++
    trfProbs ++ trfDup, quantities)

/-- The problems of one ENTRY. -/
def entryProblems (units : UnitHook) (dofs bearable quantities : List String) (e : Entry) : List String :=
  let tag := "ENTRY:" ++ nameOf e
  checkFields units tag e entryFields [] ++
  (match getStr? e "DOF" with
    | some d => if dofs.contains d then [] else [tag ++ ": DOF " ++ d ++ " is not a TPK DOF"]
    | none => []) ++
  (match getStr? e "ENVIRONMENT_QUANTITY" with
    | some q => if quantities.contains q then []
      else [tag ++ ": ENVIRONMENT_QUANTITY " ++ q ++ " is not in the ENVIRONMENT INVENTORY"]
    | none => []) ++
  (match getStr? e "DOMAIN" with
    | some d => if blank d then [tag ++ ": DOMAIN is empty"] else []
    | none => []) ++
  (match getStr? e "FALSIFIER" with
    | some f => if blank f then [tag ++ ": FALSIFIER is empty"] else []
    | none => []) ++
  (match getStr? e "FALSIFIER_CLASS" with
    | some c => if c == "F0" then [tag ++ ": FALSIFIER_CLASS F0 is inadmissible"]
      else if ["F1", "F2", "F3"].contains c then []
      else [tag ++ ": FALSIFIER_CLASS " ++ c ++ " is not one of F1 F2 F3"]
    | none => []) ++
  (match get? e "BEARS" with
    | some v => if typeOk "BEARS" v then
        (strItems v).eraseDups.filterMap fun b =>
          if bearable.contains b then none else some (tag ++ ": BEARS " ++ b ++ " is not a TPK LAW or CONSTRAINT")
      else []
    | none => [])

/-- The problems of a table that `owedOf` passed, before `done`. -/
def problems (units : UnitHook) (trm tpk : Value) : List String :=
  match trm with
  | .obj t =>
    let unknown := t.filterMap fun (p, _) => if partsOf.contains p then none else some ("TrM: unknown part " ++ p)
    let missing := partsOf.filterMap fun p => if has t p then none else some ("TrM: missing part " ++ p)
    let dofs := tpkNames tpk ["DOF"]
    let bearable := tpkNames tpk ["LAW", "CONSTRAINT"]
    let (header, quantities) := match (get? t "HEADER").getD (.obj []) with
      | .obj h => headerProblems units dofs h
      | _ => (["TrM: HEADER is not an object"], [])
    let (ents, entShape) := entries "TrM ENTRIES" ((get? t "ENTRIES").getD (.arr []))
    let entProbs := ents.flatMap (entryProblems units dofs bearable quantities)
    let entDup := (dupes (names ents)).map ("TrM: duplicate entry name " ++ ·)
    unknown ++ missing ++ header ++ entShape ++ entProbs ++ entDup
  | _ => ["TrM: zone is not an object"]

/-- The table's well-formedness against its Starting Set: v1's verdict, or owed.
Only the table's own text is read, so only it can make the verdict owed. -/
def wellFormed (units : UnitHook) (trm tpk : Value) : Verdict :=
  match owedOf trm with
  | some o => .owed o
  | none => .checked (done (problems units trm tpk))

end Principia.Correspondence
