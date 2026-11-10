import Principia.Calculator.Biblio
import Principia.Calculator.Canonical
import Principia.Calculator.Cluster
import Principia.Calculator.Derivation
import Principia.Calculator.Digest
import Principia.Calculator.Eom
import Principia.Calculator.Falcon
import Principia.Calculator.Form
import Principia.Calculator.Fundamental
import Principia.Calculator.Governor
import Principia.Calculator.Hold
import Principia.Calculator.Identity
import Principia.Calculator.Interface
import Principia.Calculator.Landing
import Principia.Calculator.Lint
import Principia.Calculator.Permissions
import Principia.Calculator.Probe
import Principia.Calculator.Provision
import Principia.Calculator.Record
import Principia.Calculator.SR9
import Principia.Calculator.Score
import Principia.Calculator.Sha256
import Principia.Calculator.Sponsor
import Principia.Calculator.Strike
import Principia.Calculator.Unicode
import Principia.Calculator.Units
import Principia.Calculator.Volunteer
import Principia.Calculator.Yardstick
import Principia.Calculator.Zone

/-!
# The Calculator: `pcalc <family> <function>`

`pcalc <family> <function>` reads one JSON value on stdin (the request: an object of
named arguments) and writes one line on stdout: the answer's canonical JSON
(tpm_record_schema 11.4) and a line feed, exit code 0. It reads nothing else and
writes nothing else; the same request gives the same bytes.

A refusal is the line `{"detail":"<sentence>","refused":"<CODE>"}` and a nonzero exit
code: 2 when `pcalc` was called wrongly (`USAGE`, `UNKNOWN_FAMILY`, `UNKNOWN_FUNCTION`),
1 when the request is refused: its text (`NOT_UTF8`, `TOO_LARGE`, `NO_VALUE`,
`TRAILING_TEXT`, `UNEXPECTED_END`, `UNEXPECTED_CHARACTER`, `TOO_DEEP`, `BAD_NUMBER`,
`NUMBER_TOO_LONG`, `EXPONENT_TOO_LONG`, `NUMBER_TOO_LARGE`, `BAD_ESCAPE`,
`LONE_SURROGATE`, `CONTROL_CHARACTER`, `DUPLICATE_KEY`; `Canonical.readText`), its arguments
(`BAD_ARGUMENT`), an answer with no canonical JSON (`NO_CANONICAL_TEXT`), or an answer the
Calculator does not compute yet (`OWED`), its detail saying what is owed.

## Adding a family

1. In the family's own file, or in the Calculator's own folder of the library, one file per family, define
   `calls : Family`: one `(name, call)` pair per function, the name v1's where the
   function ports v1's, each call reading its arguments with `argument1` to
   `argument3` and the `as…` readers of `Principia.Calculator.Interface`.
2. Import that file here and add one line to `families`, each in its place: the imports and
   the families are kept one per line in code point order, every line of `families` ending
   with a comma, so that two families added at once touch different lines.
3. Add request and answer pairs to the Calculator's corpus. The theorems below check that
   the families are in order, that no two families and no two functions of a family share a
   name.
-/

namespace Principia.Calculator

open Principia.Canonical

/-- Every family `pcalc` answers, by name: one line each, in code point order of the name,
each line ending with a comma (`families_names_sorted`). -/
def families : List (String × Family) := [
  ("biblio", Biblio.calls),
  ("canonical", Canonical.calls),
  ("cluster", Cluster.calls),
  ("derivation", Derivation.calls),
  ("digest", Digest.calls),
  ("eom", Eom.calls),
  ("falcon", Falcon.calls),
  ("form", Form.calls),
  ("fundamental", Fundamental.calls),
  ("governor", Governor.calls),
  ("hold", Hold.calls),
  ("identity", Identity.calls),
  ("landing", Landing.calls),
  ("lint", Lint.calls),
  ("permissions", Permissions.calls),
  ("probe", Probe.calls),
  ("provision", Provision.calls),
  ("record", Record.calls),
  ("score", Score.calls),
  ("sha256", Sha256.calls),
  ("sponsor", Sponsor.calls),
  ("sr9", SR9.calls),
  ("strike", Strike.calls),
  ("unicode", Unicode.calls),
  ("units", Units.calls),
  ("volunteer", Volunteer.calls),
  ("yardstick", Yardstick.calls),
  ("zone", Zone.calls),
]

/-- The function a family and a function name call, or why there is none. -/
def lookupCall (family function : String) : Except Refusal Call :=
  match families.lookup family with
  | none => .error ⟨.unknownFamily, s!"there is no family {quote family}"⟩
  | some calls =>
    match calls.lookup function with
    | none => .error ⟨.unknownFunction, s!"the family {quote family} has no function {quote function}"⟩
    | some call => .ok call

/-- The answer to a request already read. -/
def respondTo (family function : String) (request : Value) : Except Refusal Value := do
  (← lookupCall family function) request

/-- The answer to a request, or why there is none. -/
def respond (family function : String) (input : ByteArray) : Except Refusal Value := do
  let call ← lookupCall family function
  match readText input with
  | .error f =>
    .error ⟨.text f.error, match f.position with
      | some p => s!"the request's text is refused at character {p}"
      | none => "the request's bytes are refused"⟩
  | .ok v => call v

/-- A refusal's line. -/
def refusalLine (r : Refusal) : String × UInt32 :=
  ((r.value.canonicalJson.getD "") ++ "\n", r.exitCode)

/-- What `pcalc <family> <function>` writes on stdout, and its exit code. -/
def answer (family function : String) (input : ByteArray) : String × UInt32 :=
  match respond family function input with
  | .error r => refusalLine r
  | .ok v =>
    match v.canonicalJson with
    | some t => (t ++ "\n", 0)
    | none => refusalLine ⟨.noCanonicalText, "the answer holds an object with a key twice"⟩

/-- What `pcalc` writes when called with neither a family and a function nor `version`. -/
def usage : String × UInt32 :=
  refusalLine ⟨.usage, "call pcalc <family> <function> with one JSON value on stdin, or pcalc version"⟩

/-! ## What the kernel checks about the table -/

/-- No two families share a name. -/
theorem families_names_nodup : (families.map Prod.fst).Nodup := by decide

/-- The families are listed in code point order of their names, each name after the one
before it, so a new family has one place to go. -/
theorem families_names_sorted : (families.map Prod.fst).Pairwise (· < ·) := by decide

/-- No family has two functions of one name. -/
theorem functions_names_nodup : ∀ f ∈ families, (f.2.map Prod.fst).Nodup := by decide

/-- A refusal's line is canonical JSON whatever its sentence says. -/
theorem refusal_canonical (r : Refusal) :
    r.value.canonicalJson = some ("{\"detail\":" ++ quote r.detail ++ ",\"refused\":" ++
      quote r.code.word ++ "}") := by
  have hs : sortMembers [("detail", quote r.detail), ("refused", quote r.code.word)] =
      [("detail", quote r.detail), ("refused", quote r.code.word)] :=
    List.mergeSort_of_pairwise (by simp [keyLe])
  have hq1 : quote "detail" = "\"detail\"" := by decide
  have hq2 : quote "refused" = "\"refused\"" := by decide
  have ha : adjacentKeysDistinct [("detail", quote r.detail), ("refused", quote r.code.word)] =
      true := by
    simp [adjacentKeysDistinct]
  simp [Refusal.value, Value.canonicalJson, Value.canonicalJsonMembers, objectText, hs, hq1, hq2,
    ha]
  apply String.toList_inj.mp
  simp

end Principia.Calculator
