import Principia.Criteria
import Principia.Correspondence.Isomorphism

/-!
# The Research Assembly's final pass

v1's `final_checks` (`tpc_tests` 0.2.1; TPS 2.3.7): after the Criteria Set is
entered, T3 over the constraints (and, by the declared-form grammar, the laws), and the
disposition of IC2's gaps under the Criteria Set's IC2_POLICY, GAP when absent: under
REJECT each gap is also a problem. NOT_RUN when a zone fails its checks: the Starting
Set's fundamental tests, the Criteria Set's well-formedness, or the isomorphism checks
(NOT_RUN or REJECT). Owed where a check it reaches is owed.
-/

namespace Principia.ResearchAssembly

open Principia.Zone
open Principia.StartingSet.Tests
open Principia.Correspondence

/-- A part of the Research Assembly, or null when absent. -/
def part (tfk : Entry) (k : String) : Value := (get? tfk k).getD .null

/-- v1's `final_checks` over `{"TPK", "TrM", "TMS"}`. -/
def finalChecks (tfk : Value) : Except Owing IcResult := do
  let .obj a := tfk | return ⟨.notRun, ["final pass: the TFK is not an object"], []⟩
  let tpk := part a "TPK"
  let trm := part a "TrM"
  let tms := part a "TMS"
  let run ← fundamentalTests tpk
  if !run.pass then return ⟨.notRun, ["final pass: the TPK does not pass T1, T2, T5, T4 and T6"], []⟩
  match Criteria.wellFormed .calculator tms with
  | .owed o => throw (.zone o)
  | .checked (_ :: _) => return ⟨.notRun, ["final pass: the TMS is not well-formed"], []⟩
  | .checked [] => pure ()
  let ic ← isomorphismChecks trm tpk
  if ic.verdict == .notRun || ic.verdict == .reject then
    return ⟨.notRun, ["final pass: the TrM does not pass IC1-IC4"], []⟩
  let t3 ← t3Consistency tpk tms
  let policy := match tms with
    | .obj z => match get? z "PARAMETERS" with
      | some (.obj pm) => (getStr? pm "IC2_POLICY").getD "GAP"
      | _ => "GAP"
    | _ => "GAP"
  let rejected := if policy == "REJECT" then ic.gaps.map (· ++ " and IC2_POLICY is REJECT") else []
  pure (icVerdict (t3 ++ rejected) ic.gaps)

end Principia.ResearchAssembly
