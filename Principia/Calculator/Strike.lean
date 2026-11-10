import Principia.Calculator.Interface
import Principia.Strike
import Principia.Strike.Bounded
import Principia.Strike.Conditions

/-!
# Family `strike`: SR4's distance, SR3's scope and mechanical tests, SR5, SR6, SR8 and the CONDITIONS

v1 `tpc_strike`'s functions, their arguments named as v1's corpus names them.

* `assumption_closure {"rid", "records"}`: the identifiers in code point order.
* `a_of_r {"rid", "records", "tfk_assumptions"?}`: a count.
* `d_of_r {"rid", "records", "tfk_assumptions"?}`: `[a, s]`.
* `d_compare {"d1": [a, s], "d2": [a, s]}`: -1, 0 or 1.
* `sr5_order {"d1", "d2"}`: `"r1"`, `"r2"` or `"AUDIT"`.
* `sr6_independence_count {"sets": [[id, ...], ...], "same_model"?: [bool, ...]}`.
* `sr6_audit_opens {"n_ind", "n_x"}`: a boolean.
* `sr8_scale_factor {"measurements": [{"x", "u"}, ...]}`: `S`, correctly rounded to
  twelve significant digits (the digits v1's `canon` wrote).
* `mm_contradicts {"x1", "u1", "x2", "u2", "k", "S"?}` and
  `lm_contradicts {"x_l", "x_m", "u_m", "k", "S"?}`: booleans; `S` at least 1, 1 when
  absent.

Bounds, measured: `maxRecords` records holding `maxRecordEntries` assumptions and
citations in all, `maxSets` sets holding at most
`maxPackingIdentifiers` identifiers once the SAME-MODEL ones are dropped, `maxMeasurements`
measurements of at most `maxMeasurementDigits` digits. SR8's scale factor and SR3's two
tests compute within the bound on an exact value (`Principia.Strike.Bounded`): one whose
values would cross it is refused, "exact value too large".

`records` maps an identifier to `{"assumptions"?, "cites"?, "steps"}` (absent lists are
empty, as v1's `get` read them; other members are ignored). Every number is exact. A
request v1 refused (a non-positive uncertainty, more than 24 contradictions, an `N_x`
below 2) is refused with v1's message; so is one v1 could not run (a record missing).

## SR3's scope and the CONDITIONS of a comparison

v1's functions that read the Research Assembly (`tfk`) and the register (`records`, a list
of records; `words`, each record's status word), each argument any JSON value, as v1 took
it; `quantity` names an entry of the Correspondence Table:

* `sr3_scope {"tfk", "quantity"}`: `"MECHANICAL"` or `"INSPECTION"`, or v1's refusal as a
  value, `["REFUSED", reason]`.
* `conditions_of {"records", "id"}`: `["OK", [situations, points]]`.
* `comparison_set {"records", "words", "tfk", "quantity"}`: `["OK", [[id1, id2, mode], ...]]`.
* `sr8_groups {"records", "words", "tfk", "quantity"}`: `["OK", [[mode, [ids]], ...]]`.

The register functions' refusals are values too, `["REFUSED", [[code, field, message]]]`,
as v1 wrote them. Owed, and refused `OWED`: the CONDITIONS of a record with an AT point
whose value in coherent SI carries a power of pi.

Bounds, measured. The Research Assembly is bounded by what the request's reader takes,
1 MiB nested at most 64 deep: `sr3_scope` reads it once, in time that grows with its size,
and the slowest found, an entry whose name of 349,506 hidden characters is quoted escaped
in the refusal, takes 0.47 s. `conditions_of` reads one record's CONDITIONS,
`comparison_set` and `sr8_groups` those of every standing record of the quantity, each over
the whole register: at most `maxRegisterRecords` records holding `maxRegisterEntries`
ASSUMPTIONS and CITES entries for the first, `maxScopeRecords` holding `maxScopeEntries`
for the other two. The records' AT points are at most `maxPoints` in all, each VALUE and
UNIT at most `maxPointText` characters, and each point's value in coherent SI, in a RESULT
or a VERIFICATION, within the bound on an exact value and at most `maxPointBits` bits
above and below its fraction line, checked before the function runs; such a value, formed
from so few characters, is formed and refused in a few hundredths of a second.
-/

namespace Principia.Calculator.Strike

open Principia.Canonical

/-! ## The family's bounds, measured -/

/-- The most records a request holds, and the most assumptions and citations they hold
in all: the closure walk checks each identifier against those seen. 2000 records holding
20,000 take 0.11 s when the assumptions repeat, and 1.15 s when the 18,000 of them are
distinct, each then checked against all those gathered before it. -/
def maxRecords : Nat := 2000

/-- See `maxRecords`. -/
def maxRecordEntries : Nat := 20000

/-- The most identifiers the contradictions kept for SR6 hold in all. SR6's count runs
v1's search by bounding over the identifiers interned, so its time does not grow with their
length, but its worst case is not known. The slowest families found, 24 sets whose
conflicts and sizes were searched for the most work, take 0.33 s at 128 identifiers in a
1 MiB request, 0.76 s at 192 and 1.3 s at 256. -/
def maxPackingIdentifiers : Nat := 128

/-- The most sets SR6 is given, its SAME-MODEL ones included. -/
def maxSets : Nat := 1000

/-- The most measurements SR8 scales, and the most digits of each value and uncertainty:
the exact sums run over fractions whose denominators grow with both (100 measurements of
4096 digits took 183 s; of 30 digits, a fraction of a second). -/
def maxMeasurements : Nat := 100

/-- See `maxMeasurements`. -/
def maxMeasurementDigits : Nat := 30

/-- The most members the register `records` holds for `conditions_of`: its identifiers are
each checked against those before them, and 50,000 records took 17.8 s. At the bounds, 2000
records citing each other in a cycle, holding 3000 distinct assumptions, the record read
with 1000 AT points of 2047 bits, take 0.58 s. -/
def maxRegisterRecords : Nat := 2000

/-- The most ASSUMPTIONS and CITES entries the register's records hold in all for
`conditions_of`: the closure walk checks each assumption against those it holds, and 2000
records holding 18,000 distinct assumptions took 1.0 s. -/
def maxRegisterEntries : Nat := 5000

/-- The most members the register holds for `comparison_set` and `sr8_groups`, which walk
a closure over the whole register for every standing record of the quantity, and write a
pair for every two of them: 2000 standing records holding 20,000 citations took 422 s. At
the bounds, 200 standing records citing each other in a cycle, holding 300 distinct
assumptions and five AT points of 2047 bits each, beside a Research Assembly filling the
rest of 1 MiB, take 0.77 s, the 19,900 pairs written; with 800 distinct assumptions, past
this bound, they took 0.55 s. -/
def maxScopeRecords : Nat := 200

/-- The most ASSUMPTIONS and CITES entries the register's records hold in all for
`comparison_set` and `sr8_groups` (see `maxScopeRecords`). -/
def maxScopeEntries : Nat := 500

/-- The most AT points the register's records hold in all: 1000 of 2047 bits take 0.4 s. -/
def maxPoints : Nat := 1000

/-- The most characters of an AT point's VALUE, and of its UNIT. -/
def maxPointText : Nat := 64

/-- The most bits above, and below, the fraction line of an AT point's value in coherent
SI: its twelve-digit text is found from its digits, at a cost that grows with the square of
their number. One point in a unit of 22 characters whose value has 52,097 digits took
1.4 s, and a hundred 138 s. -/
def maxPointBits : Nat := 2048

/-- One record of `records`: its assumptions, citations and step count. -/
def readRecord (id : String) (v : Value) : Except Refusal (String × Principia.Strike.StrikeRecord × Bool) := do
  let ms ← asObject s!"the record {quote id}" v
  let as ← match optional ms "assumptions" with
    | some x => asStrings "assumptions" x
    | none => pure []
  let cs ← match optional ms "cites" with
    | some x => asStrings "cites" x
    | none => pure []
  let steps ← match optional ms "steps" with
    | some x => some <$> asCount "steps" x
    | none => pure none
  pure (id, ⟨as, cs, steps.getD 0⟩, steps.isSome)

/-- The records, by identifier, with whether each gave its step count. -/
def readRecords (v : Value) : Except Refusal (List (String × Principia.Strike.StrikeRecord × Bool)) := do
  let ms ← asObject "records" v
  atMost "records" maxRecords ms
  let recs ← ms.mapM fun (id, r) => readRecord id r
  let entries := (recs.map fun (_, r, _) => r.assumptions.length + r.cites.length).sum
  if maxRecordEntries < entries then
    badArgument s!"the records hold more than {maxRecordEntries} assumptions and citations in all (the Calculator's bound)"
  pure recs

/-- The records as SR4 reads them. -/
def toRecords (rs : List (String × Principia.Strike.StrikeRecord × Bool)) : Principia.Strike.Records :=
  rs.map fun (id, r, _) => (id, r)

/-- A distance `[a, s]`. -/
def readDistance (what : String) (v : Value) : Except Refusal Principia.Strike.Distance := do
  match ← asList what v with
  | [a, s] => pure ⟨← asCount what a, ← asCount what s⟩
  | _ => badArgument s!"{what} is not [a, s]"

/-- `S`: at least 1, held as its square; 1 when absent. -/
def readScale (ms : List (String × Value)) : Except Refusal Principia.Strike.ScaleFactor := do
  match optional ms "S" with
  | none => pure .one
  | some x =>
    let s ← asNumber "S" x
    if h : 1 ≤ s ∧ 1 ≤ s * s then pure ⟨s * s, h.2⟩
    else badArgument "S is at least 1 (SR8's scale factor)"

/-- A record missing from `records`. -/
def missingRecord {α : Type} : Except Refusal α :=
  badArgument "a record the closure reaches is not in records"

/-- `rid`, `records` and, where the function takes it, `tfk_assumptions`. -/
def closureArgs (takesTfk : Bool) (v : Value) :
    Except Refusal (String × List (String × Principia.Strike.StrikeRecord × Bool) × List String) := do
  let ms ← membersOf (["rid", "records"] ++ if takesTfk then ["tfk_assumptions"] else []) v
  let rid ← asString "rid" (← needed ms "rid")
  let recs ← readRecords (← needed ms "records")
  let tfk ← match optional ms "tfk_assumptions" with
    | some x => asStrings "tfk_assumptions" x
    | none => pure []
  pure (rid, recs, tfk)

/-- The entries of a record's list member, `0` when it is absent or not a list. -/
def entriesOf (r : List (String × Value)) (k : String) : Nat :=
  match r.lookup k with
  | some (.arr xs) => xs.length
  | _ => 0

/-- A record's AT points, none when its AT is absent or not a list. -/
def pointsOf (r : List (String × Value)) : List Value :=
  match r.lookup "AT" with
  | some (.arr qs) => qs
  | _ => []

/-- A string member of an AT point, at most `maxPointText` characters; `none` when absent
or not a string. -/
def pointText (q : List (String × Value)) (k : String) : Except Refusal (Option String) :=
  match q.lookup k with
  | some (.str s) =>
    if maxPointText < s.length then
      badArgument s!"an AT point's {k} has more than {maxPointText} characters (the Calculator's bound)"
    else .ok (some s)
  | _ => .ok none

/-- An AT point within the bounds. Its VALUE and UNIT hold at most `maxPointText`
characters each; when `read`, and the point has a DOF and normalizes as the CONDITIONS read
it, its value in coherent SI is within the bound on an exact value ("exact value too
large") and holds at most `maxPointBits` bits above and below its fraction line. -/
def pointWithin (read : Bool) (q : Value) : Except Refusal Unit := do
  let .obj m := q | pure ()
  let value ← pointText m "VALUE"
  let unit ← pointText m "UNIT"
  let some (.str _) := m.lookup "DOF" | pure ()
  if !read then return ()
  match Principia.Units.normalizeMeasurementArg value (some "0") unit with
  | .error _ => pure ()
  | .ok n =>
    let c := n.x.coef
    if !Principia.ValueBound.within c then badArgument Principia.ValueBound.tooLarge
    if maxPointBits < Principia.ValueBound.numBits c ||
        maxPointBits < Principia.ValueBound.denBits c then
      badArgument s!"an AT point's value holds more than {maxPointBits} bits above or below its fraction line (the Calculator's bound)"

/-- A register within the bounds: at most `maxRecs` members, whose records hold at most
`maxEntries` ASSUMPTIONS and CITES entries and `maxPoints` AT points in all, each point
within `pointWithin`, its value checked in a RESULT or a VERIFICATION, the records whose AT
the CONDITIONS read. A `records` that is not a list is v1's refusal to give. -/
def registerWithin (maxRecs maxEntries : Nat) (records : Value) : Except Refusal Unit := do
  let .arr rs := records | pure ()
  atMost "records" maxRecs rs
  let recs := rs.filterMap fun | .obj r => some r | _ => none
  if maxEntries < (recs.map fun r => entriesOf r "ASSUMPTIONS" + entriesOf r "CITES").sum then
    badArgument s!"the records hold more than {maxEntries} ASSUMPTIONS and CITES entries in all (the Calculator's bound)"
  atMost "the AT points" maxPoints (recs.flatMap pointsOf)
  for r in recs do
    let read := match r.lookup "CLASS" with
      | some (.str "RESULT") | some (.str "VERIFICATION") => true
      | _ => false
    for q in pointsOf r do
      pointWithin read q

/-- A register function's answer as `pcalc` gives it: version 1's `["OK", result]`, or its
refusal `["REFUSED", [[code, field, message]]]`, both values; an answer the Calculator does
not compute yet is refused as owed, its detail saying what is owed. -/
def registerAnswer {α : Type} (f : α → Value) : Principia.Strike.Answer α → Except Refusal Value
  | .ok a => .ok (.arr [.str "OK", f a])
  | .refused r => .ok r.toValue
  | .owed why => .error ⟨.owed, why⟩

/-- `records`, `words`, `tfk` and `quantity`, each as given. -/
def scopeArgs (v : Value) : Except Refusal (Value × Value × Value × Value) := do
  match ← arguments ["records", "words", "tfk", "quantity"] v with
  | [r, w, t, q] => pure (r, w, t, q)
  | _ => badArgument "the arguments do not read"

/-- The family's functions. -/
def calls : Family := [
  ("assumption_closure", fun v => do
    let (rid, recs, _) ← closureArgs false v
    match Principia.Strike.assumptionClosure rid (toRecords recs) with
    | some ids => pure (.arr (ids.map .str))
    | none => missingRecord),
  ("a_of_r", fun v => do
    let (rid, recs, tfk) ← closureArgs true v
    match Principia.Strike.aOfR rid (toRecords recs) tfk with
    | some n => pure (.int n)
    | none => missingRecord),
  ("d_of_r", fun v => do
    let (rid, recs, tfk) ← closureArgs true v
    unless (recs.find? (·.1 == rid)).any (·.2.2) do
      badArgument s!"the record {quote rid} gives no steps"
    match Principia.Strike.dOfR rid (toRecords recs) tfk with
    | some d => pure (.arr [.int d.assumptions, .int d.steps])
    | none => missingRecord),
  ("d_compare", fun v => do
    let (a, b) ← argument2 "d1" "d2" v
    let c := Principia.Strike.dCompare (← readDistance "d1" a) (← readDistance "d2" b)
    pure (.int (match c with | .lt => -1 | .eq => 0 | .gt => 1))),
  ("sr5_order", fun v => do
    let (a, b) ← argument2 "d1" "d2" v
    pure (.str (Principia.Strike.sr5Order (← readDistance "d1" a) (← readDistance "d2" b)).toV1)),
  ("sr6_independence_count", fun v => do
    let ms ← membersOf ["sets", "same_model"] v
    let setsList ← asList "sets" (← needed ms "sets")
    atMost "sets" maxSets setsList
    let sets ← setsList.mapM (asStrings "a set")
    let flags ← match optional ms "same_model" with
      | some x => some <$> (← asList "same_model" x).mapM (asBool "a SAME-MODEL flag")
      | none => pure none
    if flags.any (·.length != sets.length) then
      badArgument "same_model does not hold one flag per set"
    let kept : List (List String) := match flags with
      | some fs => (sets.zip fs).filterMap fun (p : List String × Bool) => if p.2 then none else some p.1
      | none => sets
    if Principia.Strike.sr6PackingGuard < kept.length then
      badArgument s!"sr6: input exceeds exact packing guard ({Principia.Strike.sr6PackingGuard})"
    if maxPackingIdentifiers < (kept.map List.length).sum then
      badArgument s!"the sets kept hold more than {maxPackingIdentifiers} identifiers in all (the Calculator's bound)"
    match Principia.Strike.sr6IndependenceCount sets flags with
    | some n => pure (.int n)
    | none => badArgument s!"sr6: input exceeds exact packing guard ({Principia.Strike.sr6PackingGuard})"),
  ("sr6_audit_opens", fun v => do
    let (a, b) ← argument2 "n_ind" "n_x" v
    match Principia.Strike.sr6AuditOpens (← asCount "n_ind" a) (← asCount "n_x" b) with
    | some o => pure (.bool o)
    | none => badArgument "sr6: N_x is a TMS parameter, at least 2"),
  ("sr8_scale_factor", fun v => do
    let mlist ← asList "measurements" (← argument1 "measurements" v)
    atMost "measurements" maxMeasurements mlist
    let ms ← mlist.mapM fun m => do
      let o ← asObject "a measurement" m
      pure ({ value := ← asShortNumber "x" maxMeasurementDigits (← needed o "x"),
              uncertainty := ← asShortNumber "u" maxMeasurementDigits (← needed o "u") } :
        Principia.Strike.Measurement)
    match ← bounded (Principia.Strike.Bounded.sr8ScaleFactor ms) with
    | some s =>
      let (m, e) := s.digits 12
      pure (.num ⟨m, e⟩)
    | none => badArgument "sr8: every M record needs u_c > 0"),
  ("mm_contradicts", fun v => do
    let ms ← membersOf ["x1", "u1", "x2", "u2", "k", "S"] v
    let n (k : String) : Except Refusal Rat := do asNumber k (← needed ms k)
    pure (.bool (← bounded (Principia.Strike.Bounded.mmContradicts (← n "x1") (← n "u1")
      (← n "x2") (← n "u2") (← n "k") (← readScale ms))))),
  ("lm_contradicts", fun v => do
    let ms ← membersOf ["x_l", "x_m", "u_m", "k", "S"] v
    let n (k : String) : Except Refusal Rat := do asNumber k (← needed ms k)
    pure (.bool (← bounded (Principia.Strike.Bounded.lmContradicts (← n "x_l") (← n "x_m")
      (← n "u_m") (← n "k") (← readScale ms))))),
  ("sr3_scope", fun v => do
    let (tfk, q) ← argument2 "tfk" "quantity" v
    pure (match Principia.Strike.sr3Scope (Principia.Strike.toZoneValue tfk)
        (Principia.Strike.toZoneValue q) with
      | .ok s => .str s.toV1
      | .error r => .arr [.str "REFUSED", .str r])),
  ("conditions_of", fun v => do
    let (records, id) ← argument2 "records" "id" v
    registerWithin maxRegisterRecords maxRegisterEntries records
    registerAnswer Principia.Strike.Conditions.toValue
      (Principia.Strike.conditionsOf records id)),
  ("comparison_set", fun v => do
    let (records, words, tfk, q) ← scopeArgs v
    registerWithin maxScopeRecords maxScopeEntries records
    registerAnswer Principia.Strike.pairsValue
      (Principia.Strike.comparisonSet records words tfk q)),
  ("sr8_groups", fun v => do
    let (records, words, tfk, q) ← scopeArgs v
    registerWithin maxScopeRecords maxScopeEntries records
    registerAnswer Principia.Strike.groupsValue
      (Principia.Strike.sr8Groups records words tfk q))]

end Principia.Calculator.Strike
