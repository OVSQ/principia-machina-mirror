import Principia.Calculator.Interface
import Principia.Calculator.Record
import Principia.Zone
import Principia.Zone.Preimage
import Principia.Strike.Conditions

/-!
# Family `zone`: the zones' checks, digests and preimages, the dimensions and the decimals

Version 1's `tpc_zone` 0.5.1 on the command line, its arguments named as version 1's corpus
(the zones' corpus) names them. A function whose version 1 name carries a version 1
code takes the Research Assembly's words; the rest keep version 1's names.

* The checks, each answering version 1's `[pass, problems]`, `[true, []]` when the zone
  passes: `starting_set_well_formed {"tpk"}` (version 1's `t1_well_formed`),
  `correspondence_table_well_formed {"trm", "tpk"}` (`trm_well_formed`),
  `criteria_set_well_formed {"tms"}` (`tms_well_formed`); `canonical_term {"t"}`, a Criteria
  Set term's canonical spelling.
* The canonical serialization: `zone_preimage {"zone", "value"}`, the zone `TPK`, `TrM` or
  `TMS`; `digest_starting_set {"tpk"}` (`d_tpk`), `digest_correspondence_table {"trm"}`
  (`d_trm`), `digest_criteria_set {"tms"}` (`d_tms`), `digest_research_assembly_of {"tfk"}`
  (`d_tfk_of`), each 64 lowercase hexadecimal characters; `classify_successor {"a", "b"}`,
  `IDENTICAL`, `YARDSTICK_ONLY`, `CORRESPONDENCE_CHANGED` or `KERNEL_CHANGED`. A zone the
  serializer cannot write (version 1 raised on it) is refused `BAD_ARGUMENT`, the detail
  naming what it met.
* The dimensions and decimals: `canon_dimension {"exps"}` (an object of base and integer
  exponent; other members ignored, as version 1 ignored them), `normalize_dimension {"s"}`,
  `is_canonical_dimension {"s"}`, `dimension_out_of_range {"s"}`, `canon_decimal {"s"}`.
  As version 1, a value that is not a string does not read: `null`, or `false`.

Each zone is read as the zones read JSON (`Strike.toZoneValue`: a number with a fraction is a
float, which no field accepts). A check that the Calculator owes is refused `OWED`; reading a
form is never owed (`Zone.owedOf_eq_none`), so none is, and the arm is kept for the grammar.

Bounds, the record family's (`Calculator.Record.sizeWithin`): at most 1,024 entries in any
list or object of a request, so at most 1,024 entries of each kind of a zone; strings of at
most 16,384 code points each and 131,072 in all, members' names included.
-/

namespace Principia.Calculator.Zone

open Principia.Canonical

/-- The most entries a list or an object of a request holds, at any depth: the record
family's. -/
def maxEntries : Nat := 1024

/-- The most code points a string of a request holds, a member's name included. Version 1's
corpus holds a Criteria Set term nested 5,001 deep, 20,005 code points, so the record
family's 16,384 would refuse it. -/
def maxText : Nat := 32768

/-- The most code points the strings of a request hold in all, members' names included. -/
def maxTextTotal : Nat := 131072

/-- A request within `maxEntries`, `maxText` and `maxTextTotal`. -/
def within (v : Value) : Except Refusal Unit := do
  let s := Record.valueSize v
  if maxEntries < s.entries then
    badArgument s!"a list or an object of the request holds more than {maxEntries} entries (the Calculator's bound)"
  if maxText < s.longest then
    badArgument s!"a string of the request holds more than {maxText} code points (the Calculator's bound)"
  if maxTextTotal < s.text then
    badArgument s!"the strings of the request hold more than {maxTextTotal} code points in all (the Calculator's bound)"

/-- An argument as the zones read it. -/
def zoneOf (v : Value) : Principia.Zone.Value := Principia.Strike.toZoneValue v

/-- An owed verdict's detail, in plain words. -/
def owedDetail (o : Principia.Zone.Owed) : String :=
  "the zone check waits on the declared forms to read a form field: " ++ o.message

/-- A verdict as `pcalc` gives it: `[pass, problems]`, or the refusal `OWED`. -/
def verdictAnswer : Principia.Zone.Verdict → Except Refusal Value
  | .checked ps => .ok (.arr [.bool ps.isEmpty, .arr (ps.map .str)])
  | .owed o => .error ⟨.owed, owedDetail o⟩

/-- A serialization's text, or the refusal of a zone it cannot write. -/
def faultAnswer : Except Principia.Zone.Fault String → Except Refusal Value
  | .ok s => .ok (.str s)
  | .error f => badArgument s!"the zone cannot be serialized: {f}"

/-- A text that may not be one: `none` for anything but a string, as version 1 read it. -/
def textOf : Value → Option String
  | .str s => some s
  | _ => none

/-- An optional text as JSON: `null` for none. -/
def orNull : Option String → Value
  | some s => .str s
  | none => .null

/-- `canon_dimension`'s exponents: each base's member, an integer; a base absent is 0. -/
def exponentsOf (v : Value) : Except Refusal Dimension.Exponents := do
  let ms ← asObject "exps" v
  let read : List (Dimension.Base × Int) ← Dimension.Base.all.mapM fun b => do
    let name := String.ofList b.spell
    match ms.lookup name with
    | none => pure (b, (0 : Int))
    | some x => pure (b, ← asInteger s!"the exponent of {name}" x)
  pure fun b => ((read.find? (·.1 == b)).map (·.2)).getD 0

/-- A one-argument call over a zone, the request within the bounds. -/
def zoneCall (a : String) (f : Principia.Zone.Value → Except Refusal Value) : Call := fun v => do
  within v
  f (zoneOf (← argument1 a v))

/-- A one-argument call over a text `s`, the request within the bounds. -/
def textCall (f : Option String → Value) : Call := fun v => do
  within v
  pure (f (textOf (← argument1 "s" v)))

/-- The family's functions. -/
def calls : Family := [
  ("canon_decimal", textCall fun s => orNull (s.bind Decimal.canon)),
  ("canon_dimension", fun v => do
    within v
    pure (.str (Dimension.canon (← exponentsOf (← argument1 "exps" v))))),
  ("canonical_term", fun v => do
    within v
    pure (.str (Criteria.canonicalTerm (← asString "t" (← argument1 "t" v))))),
  ("classify_successor", fun v => do
    within v
    let (a, b) ← argument2 "a" "b" v
    faultAnswer ((·.word) <$> Principia.Zone.classifySuccessor (zoneOf a) (zoneOf b))),
  ("correspondence_table_well_formed", fun v => do
    within v
    let (trm, tpk) ← argument2 "trm" "tpk" v
    verdictAnswer (Correspondence.wellFormed .calculator (zoneOf trm) (zoneOf tpk))),
  ("criteria_set_well_formed", zoneCall "tms" fun z =>
    verdictAnswer (Criteria.wellFormed .calculator z)),
  ("digest_correspondence_table", zoneCall "trm" fun z => faultAnswer (Principia.Zone.dTrm z)),
  ("digest_criteria_set", zoneCall "tms" fun z => faultAnswer (Principia.Zone.dTms z)),
  ("digest_research_assembly_of", zoneCall "tfk" fun z => faultAnswer (Principia.Zone.dTfkOf z)),
  ("digest_starting_set", zoneCall "tpk" fun z => faultAnswer (Principia.Zone.dTpk z)),
  ("dimension_out_of_range", textCall fun s =>
    .bool (match s with
      | some t => Dimension.outOfRange t
      | none => false)),
  ("is_canonical_dimension", textCall fun s =>
    .bool (match s with
      | some t => Dimension.isCanonical t
      | none => false)),
  ("normalize_dimension", textCall fun s => orNull (s.bind Dimension.normalize)),
  ("starting_set_well_formed", zoneCall "tpk" fun z =>
    verdictAnswer (StartingSet.wellFormed .calculator z)),
  ("zone_preimage", fun v => do
    within v
    let (n, value) ← argument2 "zone" "value" v
    let name ← asString "zone" n
    match Principia.Zone.ZoneName.ofString? name with
    | some zn => faultAnswer (Principia.Zone.zonePreimage zn (zoneOf value))
    | none => badArgument s!"{quote name} is not a zone: TPK, TrM or TMS"),
]

/-! ## What the kernel checks -/

/-- A checked verdict is answered `[pass, problems]`, passing exactly when there is no
problem; the family refuses `OWED` only on an owed verdict. -/
theorem verdictAnswer_checked (ps : List String) :
    verdictAnswer (.checked ps) = .ok (.arr [.bool ps.isEmpty, .arr (ps.map .str)]) := rfl

/-- No zone check of the Correspondence Table is ever owed. -/
theorem correspondence_never_owed (trm tpk : Principia.Zone.Value) (o : Principia.Zone.Owed) :
    Correspondence.wellFormed .calculator trm tpk ≠ .owed o := by
  unfold Correspondence.wellFormed
  rw [Principia.Zone.owedOf_eq_none]
  simp

/-- No zone check of the Criteria Set is ever owed. -/
theorem criteria_never_owed (tms : Principia.Zone.Value) (o : Principia.Zone.Owed) :
    Criteria.wellFormed .calculator tms ≠ .owed o := by
  unfold Criteria.wellFormed
  rw [Principia.Zone.owedOf_eq_none]
  simp

end Principia.Calculator.Zone
