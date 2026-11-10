import Principia.Calculator.Interface
import Principia.Calculator.SR9
import Principia.Yardstick.Bounded
import Principia.Strike.Conditions

/-!
# Family `yardstick`: a declared yardstick's key and its SR9 checks

Version 1's `tpc_yardstick` functions on the command line (`Principia.Yardstick`), through the
bound on an exact value (`Principia.Yardstick.Bounded`), their arguments named as version 1's
corpus (the yardsticks' corpus) names them:

* `yardstick_key {"tms", "name", "rid", "records", "fields"?}`: `["OK", [value, ...]]`, the
  key of record `rid`. Each value is written exactly, as a text: a canonical decimal when it
  has a finite decimal expansion, else `numerator/denominator` (`Exact.renderRat`); twelve
  digits would not hold a key's order.
* `yardstick_checks {"tms", "name", "suite"}`: `["OK", [c1, witnesses], [c2, violations,
  exempt], [c4, witnesses]]`.
* `yardstick_harness {"tms", "name", "suite"}`: `["OK", c1, c2, c4, count]`.

`records` is a suite's records and `suite` a suite, as the `sr9` family reads them
(`Calculator.SR9.readSuite`: at most 50 records and contradictions, 500 assumptions and
citations); the field table is `fields`, `{rid: {field: text}}`, beside `records`, or the
suite's member `fields`. Version 1's refusals stay values, `["REFUSED", reason]`, exit code 0;
where version 1 raised, the request is refused `BAD_ARGUMENT`; a value past the bound on an
exact value is refused "exact value too large"; an owed result answers `OWED` (none occurs).
-/

namespace Principia.Calculator.Yardstick

open Principia.Canonical
open Principia.Strike.SR9
open Principia.Yardstick (Outcome Checks)

/-- A request's value as the zones read it. -/
def zoneOf (v : Value) : Zone.Value := Principia.Strike.toZoneValue v

/-- The field table: each record's row of string-valued cells; anything else holds nothing. -/
def fieldTable : Value → List (String × List (String × String))
  | .obj rows => rows.map fun (rid, row) => (rid, match row with
      | .obj cells => cells.filterMap fun (k, c) => match c with
        | .str s => some (k, s)
        | _ => none
      | _ => [])
  | _ => []

/-- The member `k` of an object, if present. -/
def memberOf (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

/-- A suite as the `sr9` family reads it, with its field table. -/
def readSuiteWithTable (v : Value) : Except Refusal (Suite × List (String × List (String × String))) := do
  let ms ← asObject "suite" v
  let s ← SR9.readSuite (.obj (ms.filter (·.1 != "fields")))
  pure (s, ((memberOf v "fields").map fieldTable).getD [])

def strs (xs : List String) : Value := .arr (xs.map .str)

/-- An answer: version 1's value, the bound's refusal, or a raise refused. -/
def answer {α : Type} (f : α → List Value) :
    Principia.ValueBound.Bounded (Option (Outcome α)) → Except Refusal Value
  | .error e => badArgument e
  | .ok none => badArgument "version 1 raised on this request"
  | .ok (some (.ok a)) => .ok (.arr (.str "OK" :: f a))
  | .ok (some (.refused r)) => .ok (.arr [.str "REFUSED", .str r])
  | .ok (some (.owed o)) => .error ⟨.owed, "the yardstick waits on: " ++ o.message⟩

def checksItems (c : Checks) : List Value :=
  let (c1, c2, c4) := c
  [.arr [.bool c1.1, strs c1.2], .arr [.bool c2.1, strs c2.2.1, strs c2.2.2],
    .arr [.bool c4.1, strs c4.2]]

/-- The Criteria Set's checks never consult the units. -/
def noUnits : Zone.UnitHook := ⟨fun _ => .error "a Criteria Set has no UNIT"⟩

/-- The family's functions. -/
def calls : Family := [
  ("yardstick_checks", fun v => do
    let (tms, n, sj) ← argument3 "tms" "name" "suite" v
    let name ← asString "name" n
    let (s, table) ← readSuiteWithTable sj
    answer checksItems
      (Principia.Yardstick.Bounded.yardstickChecks noUnits (zoneOf tms) name s table)),
  ("yardstick_harness", fun v => do
    let (tms, n, sj) ← argument3 "tms" "name" "suite" v
    let name ← asString "name" n
    let (s, table) ← readSuiteWithTable sj
    answer (fun (a, b, c, k) => [.bool a, .bool b, .bool c, .int k])
      (Principia.Yardstick.Bounded.yardstickHarness noUnits (zoneOf tms) name s table)),
  ("yardstick_key", fun v => do
    let ms ← membersOf ["tms", "name", "rid", "records", "fields"] v
    let tms ← needed ms "tms"
    let name ← asString "name" (← needed ms "name")
    let rid ← asString "rid" (← needed ms "rid")
    let s ← SR9.readSuite (.obj [("records", ← needed ms "records")])
    let table := ((ms.lookup "fields").map fieldTable).getD []
    answer (fun k => [strs (k.map Exact.renderRat)])
      (Principia.Yardstick.Bounded.yardstickKey noUnits (zoneOf tms) name rid s.records
        s.assembly table)),
]

end Principia.Calculator.Yardstick
