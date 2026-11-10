import Principia.Provision.Reader
import Principia.StartingSet
import Principia.Zone.Preimage

/-!
# The Starting Set's preimage, as the Provision functions take it

v1's `tpc_module` took D(TPK) and `_entry_list` from `tpc_zone`; so do these, from the one port
of v1's canonical serialization, `Principia.Zone.Preimage`. `Zone.entryList` is v1's
`_entry_list`, by which two entries a Provision emits under one name are compared (TPS
5.22.7), as v1 compares them; `dTpk` is D(TPK), SHA-256 over the TPK's preimage
(`Zone.zonePreimage`), taken through the `DigestHook` (the Calculator's is SHA-256,
`DigestHook.calculator`). A TPK reaches it only after T1 has passed it;
one the serializer refuses all the same is refused here as internal, where v1 raised.
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get?)

/-- A kind's fields in their order: the required, then the optional. -/
def kindFieldList (kind : String) : List String :=
  (StartingSet.kindFields kind).1 ++ (StartingSet.kindFields kind).2

/-- The objects of a kind's list, or none. -/
def kindEntries (tpk : Entry) (kind : String) : List Entry :=
  match get? tpk kind with
  | some (.arr xs) => xs.filterMap fun | .obj e => some e | _ => none
  | _ => []

/-- D(TPK)'s preimage: the zones' (`Principia.Zone.zonePreimage`). -/
def tpkPreimage (tpk : Value) : Run String :=
  match Zone.zonePreimage .tpk tpk with
  | .ok p => pure p
  | .error f => refuse ("internal: the TPK has no preimage: " ++ f)

/-- D(TPK), through the hook. -/
def dTpk (D : DigestHook) (tpk : Value) : Run String := do D.digest (← tpkPreimage tpk)

/-- D(TPK)'s preimage is the zones' preimage of the TPK. -/
theorem tpkPreimage_zone {tpk : Value} {p : String} (h : Zone.zonePreimage .tpk tpk = .ok p) :
    tpkPreimage tpk = .ok p := by
  simp [tpkPreimage, h, pure, Except.pure]

/-- Under the Calculator's hook, D(TPK) is the zones' D(TPK): SHA-256 of the same preimage. -/
theorem dTpk_calculator {tpk : Value} {d : String} (h : Zone.dTpk tpk = .ok d) :
    dTpk DigestHook.calculator tpk = .ok d := by
  unfold Zone.dTpk Zone.zoneDigest at h
  cases hp : Zone.zonePreimage .tpk tpk with
  | error f => simp [hp, Functor.map, Except.map] at h
  | ok p =>
    simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
    simp [dTpk, tpkPreimage_zone hp, bind, Except.bind, DigestHook.digest, DigestHook.calculator,
      h, pure, Except.pure]

end Principia.Provision
