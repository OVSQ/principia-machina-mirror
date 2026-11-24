import Tests.Calculator.Common

/-!
The Calculator's runners of the family `zone`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- Version 1's names of the zone functions whose names carry a version 1 code, and the
Calculator's PMA words for them; every other function of `zone_corpus.json` keeps its name. -/
def zoneNames : List (String × String) := [
  ("t1_well_formed", "starting_set_well_formed"),
  ("trm_well_formed", "correspondence_table_well_formed"),
  ("tms_well_formed", "criteria_set_well_formed"),
  ("d_tpk", "digest_starting_set"),
  ("d_trm", "digest_correspondence_table"),
  ("d_tms", "digest_criteria_set"),
  ("d_tfk_of", "digest_research_assembly_of")]

/-- `zone_corpus.json`: all its cases through `zone <fn>`, version 1's names mapped
(`zoneNames`); version 1's `canon` text of the answer compared with `expect`, `null` for
none. None is owed, and none refused. -/
def runZoneCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/zone_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := (zoneNames.lookup v1).getD v1
    let some expect := member c "expect" | throw (IO.userError s!"{id}: no expect")
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "zone" fn input
    let text (v : Value) : Option String := match v with
      | .null => some "null"
      | _ => v.canon
    let ok := match got, expect with
      | .ok v, .str e => text v == some e
      | .ok (.bool b), .bool e => b == e
      | _, _ => false
    t ← t.check ok s!"zone {fn} {id}: expected {repr (expect.canonicalJson)}, got {repr (got.toOption.map text)} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- A Criteria Set term of `n` `NEG:` around `A`. -/
def negTerm (n : Nat) : String := String.join (List.replicate n "NEG:") ++ "A"

/-- The zone family's bounds (`Calculator.Zone`), each at its value and one past it. -/
def runZoneBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("DOF at 1024", "starting_set_well_formed", .obj [("tpk", dofTpk 1024)], false),
    ("DOF past 1024", "starting_set_well_formed", .obj [("tpk", dofTpk 1025)], true),
    ("DOF at 1024, the digest", "digest_starting_set", .obj [("tpk", dofTpk 1024)], false),
    ("DOF past 1024, the digest", "digest_starting_set", .obj [("tpk", dofTpk 1025)], true),
    ("a term at 32768 code points", "canonical_term", .obj [("t", .str (negTerm 8191))], false),
    ("a term past 32768 code points", "canonical_term",
      .obj [("t", .str (negTerm 8191 ++ "1234"))], true),
    -- "zone", "value" and "TMS" hold 12 code points.
    ("text at 131072 code points in all", "zone_preimage",
      .obj [("zone", .str "TMS"), ("value", .arr (textsOf (131072 - 12)))], false),
    ("text past 131072 code points in all", "zone_preimage",
      .obj [("zone", .str "TMS"), ("value", .arr (textsOf (131073 - 12)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "zone" fn request
    t ← t.check (boundRefusal got == refused)
      s!"zone {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Zone

open Tests.Calculator

/-- The family `zone`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc zone (zone_corpus)", runZoneCalls),
  ("pcalc zone bounds", runZoneBounds),
]

end Tests.Calculator.Zone
