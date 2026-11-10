import Principia
import Lean.Data.Json

/-!
The runner of `vectors/zone_corpus.json` for the zones (v1's `tpc_zone` 0.5.1): the checks
`t1_well_formed`, `trm_well_formed`, `tms_well_formed` and `canonical_term`, and the canonical
serialization (`Principia.Zone.Preimage`): `zone_preimage`, `d_tpk`, `d_trm`, `d_tms`,
`d_tfk_of` and `classify_successor`, the digests SHA-256 (`Principia.Sha256`; decision D2,
option 1). Each case's input is read into `Principia.Zone.Value` as v1's JSON reader gives it
(a number with a fraction part is a float). A verdict is compared with the case's `expect`:
its pass flag as a value, and its problems by v1's text, `[true,[]]` or `[false,[p1,p2,...]]`
(the problems themselves are compared only as that text, since v1's text does not quote
them). A canonical term, a preimage, a digest and a successor class's word are compared as
strings, exactly; a zone the serializer refuses fails its case (v1 raised on none of them).

An owed case is neither a pass nor a failure: it must be listed, with its reason,
in `vectors/zone_corpus.owed.json`, and every case listed there must come out owed
for that reason; none is. The dimension and decimal helpers of the corpus are run with the
units.
-/

open Lean
open Principia
open Principia.Zone

namespace Tests.Zone

/-- A JSON value as v1 reads it. -/
partial def toValue : Json → Value
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent == 0 then .int n.mantissa else .real
  | .str s => .str s
  | .arr a => .arr (a.toList.map toValue)
  | .obj kvs => .obj (kvs.foldl (fun acc k v => acc ++ [(k, toValue v)]) [])

/-- v1's text of a validator's result (`tpc_strike.canon`). -/
def render (ps : List String) : String :=
  if ps.isEmpty then "[true,[]]" else "[false,[" ++ ",".intercalate ps ++ "]]"

/-- An owed reason as the owed list spells it. -/
def owedWord : Owed → String
  | .forms => "forms"


/-- The functions this runner reads. -/
def mine : List String :=
  ["t1_well_formed", "trm_well_formed", "tms_well_formed", "canonical_term", "zone_preimage",
   "d_tpk", "d_trm", "d_tms", "d_tfk_of", "classify_successor"]

/-- A case of the canonical serialization: its answer as v1's text, or the serializer's
refusal; `none` for a function of the checks. -/
def serialized (fn : String) (input : Json) : Except String (Option (Except Fault String)) := do
  let z (k : String) : Except String Value := do pure (toValue (← input.getObjVal? k))
  match fn with
  | "zone_preimage" =>
    let name ← input.getObjValAs? String "zone"
    let some zn := ZoneName.ofString? name | throw s!"no zone {name}"
    pure (some (zonePreimage zn (← z "value")))
  | "d_tpk" => pure (some (dTpk (← z "tpk")))
  | "d_trm" => pure (some (dTrm (← z "trm")))
  | "d_tms" => pure (some (dTms (← z "tms")))
  | "d_tfk_of" => pure (some (dTfkOf (← z "tfk")))
  | "classify_successor" => pure (some ((·.word) <$> classifySuccessor (← z "a") (← z "b")))
  | _ => pure none

/-- Run the corpus: passes and failures; owed cases are counted and printed. -/
def runZone : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/zone_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/zone_corpus.owed.json"))
  let owedList ← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)
  let listed ← owedList.toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String) := []
  for c in cases do
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    unless mine.contains fn do continue
    let id ← IO.ofExcept (c.getObjValAs? String "id")
    let input ← IO.ofExcept (c.getObjVal? "input")
    let expect ← IO.ofExcept (c.getObjVal? "expect")
    let verdict? : Option Verdict ← match fn with
      | "t1_well_formed" => do
        let z := toValue (← IO.ofExcept (input.getObjVal? "tpk"))
        pure (some (StartingSet.wellFormed .calculator z))
      | "trm_well_formed" => do
        let z := toValue (← IO.ofExcept (input.getObjVal? "trm"))
        let t := toValue (← IO.ofExcept (input.getObjVal? "tpk"))
        pure (some (Correspondence.wellFormed .calculator z t))
      | "tms_well_formed" => do
        let z := toValue (← IO.ofExcept (input.getObjVal? "tms"))
        pure (some (Criteria.wellFormed .calculator z))
      | _ => pure none
    if fn == "canonical_term" then
      let t ← IO.ofExcept (input.getObjValAs? String "t")
      let e ← IO.ofExcept (expect.getStr?)
      let got := Criteria.canonicalTerm t
      if got == e then pass := pass + 1
      else
        IO.eprintln s!"FAIL zone {id}: expected {repr e}, got {repr got}"
        fail := fail + 1
      continue
    if let some got ← IO.ofExcept (serialized fn input) then
      let e ← IO.ofExcept (expect.getStr?)
      match got with
      | .ok g =>
        if g == e then pass := pass + 1
        else
          IO.eprintln s!"FAIL zone {id}:\n  expected {repr e}\n  got      {repr g}"
          fail := fail + 1
      | .error f =>
        IO.eprintln s!"FAIL zone {id}: the serializer refuses the zone: {f}"
        fail := fail + 1
      continue
    match verdict? with
    | none => throw (IO.userError s!"zone {id}: no verdict for {fn}")
    | some (.owed why) => owed := owed ++ [(id, owedWord why)]
    | some (.checked ps) =>
      let e ← IO.ofExcept expect.getStr?
      let got := render ps
      if (e.startsWith "[true,") == ps.isEmpty && got == e then pass := pass + 1
      else
        IO.eprintln s!"FAIL zone {id}:\n  expected {repr e}\n  got      {repr got}"
        fail := fail + 1
  -- The owed cases are exactly the listed ones, each for its listed reason.
  for (id, why) in owed do
    unless listed.contains (id, why) do
      IO.eprintln s!"FAIL zone {id}: owed ({why}) but not listed so in vectors/zone_corpus.owed.json"
      fail := fail + 1
  for (id, why) in listed do
    unless owed.contains (id, why) do
      IO.eprintln s!"FAIL zone {id}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  let count (w : String) := (owed.filter (·.2.startsWith w)).length
  IO.println s!"zone: {owed.length} owed (declared forms {count "forms"})"
  return (pass, fail)

/-- `U+XXXX` as a code point. -/
def readCodePoint (s : String) : Option Nat :=
  if s.startsWith "U+" then
    (s.drop 2).toString.toList.foldlM (fun acc d =>
      let v := if '0' ≤ d && d ≤ '9' then some (d.toNat - '0'.toNat)
        else if 'A' ≤ d && d ≤ 'F' then some (d.toNat - 'A'.toNat + 10) else none
      v.map (acc * 16 + ·)) 0
  else none

/-- `vectors/zone_text.json`: probe code points, each with its general category in Python's
`unicodedata` 15.1.0 and v1's verdict on it. The Calculator's category
(`Principia.Unicode.generalCategory`) and its text rule (`Principia.Zone.disallowed`) must
agree with both, and a message must show a refused code point as `<U+XXXX>` and an allowed
one as itself. -/
def runZoneText : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/zone_text.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let cp ← IO.ofExcept (c.getObjValAs? String "cp")
    let v1 ← IO.ofExcept (c.getObjValAs? String "v1")
    let cat ← IO.ofExcept (c.getObjValAs? String "category")
    let some n := readCodePoint cp | throw (IO.userError s!"not a code point: {cp}")
    let ch := Char.ofNat n
    let gotCat := (Unicode.generalCategory ch).code
    let refuses := disallowed ch
    let agrees := (v1 == "refuses" && refuses) || (v1 == "allows" && !refuses)
    let shown := escape ch.toString
    let escapes := if refuses then shown == "<" ++ cp ++ ">" else shown == ch.toString
    if gotCat == cat && agrees && escapes && ch.toNat == n then pass := pass + 1
    else
      IO.eprintln s!"FAIL zone_text {cp}: category {gotCat}, expected {cat}; refused {refuses}, v1 {v1}; escape {repr shown}"
      fail := fail + 1
  return (pass, fail)

end Tests.Zone
