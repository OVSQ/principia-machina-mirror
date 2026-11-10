import Principia.Correspondence
import Principia.StartingSet.Tests

/-!
# The isomorphism checks IC1 to IC4

v1's `ic_checks` (`tpc_tests` 0.2.1; guide 4.6; TPS 2.3.7 to 2.3.14), as the
Correspondence Table is entered, over the inventory it maps onto: the Starting Set's DOF
less the TARGETs of REMOVE constraints. An entry on a REMOVEd DOF maps outside it
(CODOMAIN).

* IC1 every quantity of the REFERENT INVENTORY is identified by some entry;
* IC2 every DOF of the inventory is some entry's DOF; a failure is a named gap, disposed
  of at the final pass;
* IC3 no DOF is identified with two quantities, and no quantity with two DOF
  (TRANSFORMATIONS are prose, so distinct quantity names are inequivalent: this errs
  toward rejection, never acceptance);
* IC4 (b) each entry's DIMENSION equals its DOF's and its quantity's; (c) every DOF a
  law it BEARS names, and the TARGET of every constraint it BEARS, is identified. IC4 (a)
  read syntactically where a SIGNATURE carries FORM and IMAGE_FORM
  (`Principia.Form.ic4aSignature`); the image holding in the environment stays INSPECTION.

REJECT on any problem; else GAP with the untied DOF named; else PASS. NOT_RUN when the
Starting Set fails T1 or the table is not well formed.
-/

namespace Principia.Correspondence

open Principia.Zone
open Principia.StartingSet.Tests

/-- The checks' verdict. -/
inductive IcVerdict where
  | notRun
  | reject
  | gap
  | pass
  deriving DecidableEq, Repr

/-- v1's word for the verdict. -/
def IcVerdict.word : IcVerdict → String
  | .notRun => "NOT_RUN"
  | .reject => "REJECT"
  | .gap => "GAP"
  | .pass => "PASS"

/-- `[verdict, problems, gaps]`. -/
structure IcResult where
  verdict : IcVerdict
  problems : List String
  gaps : List String
  deriving Repr

/-- v1's `_verdict`: problems escaped, sorted, without repeats; gaps sorted, without
repeats; REJECT on a problem, else GAP on a gap, else PASS. -/
def icVerdict (probs gaps : List String) : IcResult :=
  let ps := done probs
  let gs := gaps.foldl (fun acc p => insertStr p acc) []
  ⟨if !ps.isEmpty then .reject else if !gs.isEmpty then .gap else .pass, ps, gs⟩

/-- An entry's string field, which a well-formed table guarantees. -/
def fld (e : Entry) (f : String) : String := (getStr? e f).getD ""

/-- Entries sorted by NAME (insertion; NAMEs are unique in a well-formed table). -/
def insertByName (x : Entry) : List Entry → List Entry
  | [] => [x]
  | y :: ys => if fld x "NAME" < fld y "NAME" then x :: y :: ys else y :: insertByName x ys

/-- The checks once both zones are well formed (the body of v1's `ic_checks`), with IC4
(a)'s problems. -/
def icBody (trm tpk : Value) (ic4a : List String) : IcResult :=
  let dofs := dofDims tpk
  let rem := removed tpk
  let inventory := ((dofs.map (·.1)).filter fun d => (rem.lookup d).isNone).foldl (fun acc p => insertStr p acc) []
  let header : Value := match trm with
    | .obj t => (get? t "HEADER").getD .null
    | _ => .null
  -- The inventory's quantities with their DIMENSIONs; a later entry of one name wins.
  let env : List (String × Option String) :=
    (entriesOf header "ENVIRONMENT_INVENTORY").foldl (fun acc e =>
      let q := fld e "ENVIRONMENT_QUANTITY"
      (acc.filter (·.1 != q)) ++ [(q, Dimension.normalize (fld e "DIMENSION"))]) []
  let ents := (entriesOf trm "ENTRIES").foldl (fun acc e => insertByName e acc) []
  let laws := entriesOf tpk "LAW"
  let cons := entriesOf tpk "CONSTRAINT"
  let lawOf (n : String) : Option Entry := (laws.reverse.find? (fld · "NAME" == n))
  let conOf (n : String) : Option Entry := (cons.reverse.find? (fld · "NAME" == n))
  let codomain := ents.filterMap fun e =>
    (rem.lookup (fld e "DOF")).map fun cs =>
      "CODOMAIN: ENTRY:" ++ fld e "NAME" ++ " identifies DOF " ++ fld e "DOF" ++ ", which " ++
        ", ".intercalate (cs.map ("CONSTRAINT:" ++ ·)) ++ " removes"
  let identified := (ents.filter fun e => (rem.lookup (fld e "DOF")).isNone).map (fld · "DOF")
  let covered := ents.map (fld · "ENVIRONMENT_QUANTITY")
  let ic1 := (env.map (·.1)).filterMap fun q =>
    if covered.contains q then none else some ("IC1: environment quantity " ++ q ++ " is identified by no entry")
  let gaps := inventory.filterMap fun d => if identified.contains d then none else some ("IC2: DOF " ++ d ++ " is untied")
  let ic3dof := ((ents.map (fld · "DOF")).eraseDups).filterMap fun d =>
    let es := ents.filter (fld · "DOF" == d)
    let qs := (es.map (fld · "ENVIRONMENT_QUANTITY")).eraseDups.foldl (fun acc p => insertStr p acc) []
    if qs.length > 1 then
      some ("IC3: DOF " ++ d ++ " is identified with inequivalent quantities " ++ ", ".intercalate qs ++
        " (" ++ ", ".intercalate (es.map ("ENTRY:" ++ fld · "NAME")) ++ ")")
    else none
  let ic3q := ((ents.map (fld · "ENVIRONMENT_QUANTITY")).eraseDups).filterMap fun q =>
    let es := ents.filter (fld · "ENVIRONMENT_QUANTITY" == q)
    let ds := (es.map (fld · "DOF")).eraseDups.foldl (fun acc p => insertStr p acc) []
    if ds.length > 1 then
      some ("IC3: environment quantity " ++ q ++ " is identified with DOF " ++ ", ".intercalate ds ++
        " (" ++ ", ".intercalate (es.map ("ENTRY:" ++ fld · "NAME")) ++ ")")
    else none
  let ic4 := ents.flatMap fun e =>
    let tag := "ENTRY:" ++ fld e "NAME"
    let dim := (Dimension.normalize (fld e "DIMENSION")).getD ""
    let b1 := match dofs.lookup (fld e "DOF") with
      | some (some dd) => if dim != dd then
          [("IC4(b): " ++ tag ++ ": DIMENSION " ++ dim ++ " differs from DOF " ++ fld e "DOF" ++ "'s " ++ dd)]
        else []
      | _ => []
    let b2 := match env.lookup (fld e "ENVIRONMENT_QUANTITY") with
      | some (some qd) => if dim != qd then
          [("IC4(b): " ++ tag ++ ": DIMENSION " ++ dim ++ " differs from environment quantity " ++
            fld e "ENVIRONMENT_QUANTITY" ++ "'s " ++ qd)]
        else []
      | _ => []
    let c := (setOf e "BEARS").eraseDups.flatMap fun b =>
      match lawOf b with
      | some l => (setOf l "REFS").eraseDups.filterMap fun r =>
          if (dofs.lookup r).isSome && !identified.contains r then
            some ("IC4(c): " ++ tag ++ ": BEARS LAW:" ++ b ++ ", which names DOF " ++ r ++ " that no entry identifies")
          else none
      | none => match conOf b with
        | some c => match getStr? c "TARGET" with
          | some t => if identified.contains t then []
            else ["IC4(c): " ++ tag ++ ": BEARS CONSTRAINT:" ++ b ++ ", whose TARGET " ++ t ++ " no entry identifies"]
          | none => []
        | none => []
    b1 ++ b2 ++ c
  icVerdict (codomain ++ ic1 ++ ic3dof ++ ic3q ++ ic4 ++ ic4a) gaps

/-- v1's `ic_checks`: NOT_RUN unless the Starting Set passes T1 and the table is well
formed; owed where either zone check owes. -/
def isomorphismChecks (trm tpk : Value) : Except Owing IcResult := do
  match StartingSet.wellFormed .calculator tpk with
  | .owed o => throw (.zone o)
  | .checked (_ :: _) => return ⟨.notRun, ["IC: the TPK does not pass T1"], []⟩
  | .checked [] => pure ()
  match wellFormed .calculator trm tpk with
  | .owed o => throw (.zone o)
  | .checked (_ :: _) => return ⟨.notRun, ["IC: the TrM is not well-formed"], []⟩
  | .checked [] => pure ()
  let (ic4a, _) ← formAnswer (Form.ic4aSignature trm)
  pure (icBody trm tpk ic4a)

/-! ## Theorems -/

/-- PASS only with no problem and no gap; a problem always REJECTs. -/
theorem icVerdict_pass_iff (ps gs : List String) :
    (icVerdict ps gs).verdict = .pass ↔ done ps = [] ∧ gs.foldl (fun acc p => insertStr p acc) [] = [] := by
  unfold icVerdict
  by_cases h1 : done ps = [] <;> by_cases h2 : gs.foldl (fun acc p => insertStr p acc) [] = [] <;> simp_all

/-- The checks do not run on a Starting Set that fails T1. -/
theorem isomorphismChecks_notRun_of_t1 {trm tpk : Value} {p : String} {ps : List String}
    (h : StartingSet.wellFormed .calculator tpk = .checked (p :: ps)) :
    isomorphismChecks trm tpk = .ok ⟨.notRun, ["IC: the TPK does not pass T1"], []⟩ := by
  simp [isomorphismChecks, h, pure, Except.pure]

end Principia.Correspondence
