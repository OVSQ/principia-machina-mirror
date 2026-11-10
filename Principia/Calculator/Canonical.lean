import Principia.Calculator.Interface

/-!
# Family `canonical`: the canonical serialization

* `canon {"value": v}`: v1's canon of `v`, as a string; null and objects are refused,
  as v1 refuses them.
* `canonical_json {"value": v}`: TPM's canonical JSON of `v` (tpm_record_schema 11.4),
  as a string: the text a digest is taken over.
-/

namespace Principia.Calculator.Canonical

open Principia.Canonical

/-- The family's functions. -/
def calls : Family := [
  ("canon", fun v => do
    match (← argument1 "value" v).canon with
    | some t => pure (.str t)
    | none => badArgument "canon writes no null and no object"),
  ("canonical_json", fun v => do
    match (← argument1 "value" v).canonicalJson with
    | some t => pure (.str t)
    | none => badArgument "the value holds an object with a key twice")]

end Principia.Calculator.Canonical
