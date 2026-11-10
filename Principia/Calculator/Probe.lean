import Principia.Calculator.Interface
import Principia.Calculator.Strike
import Principia.Probe

/-!
# Family `probe`: probes and their comparison

v1's `tpc_probe` 0.2.0 (`Principia.Probe`), one function each, its arguments named as v1's
`run_case` names them; an argument v1 read with `args.get` may be absent or `null`:
* `uniform {"tag", "r", "counter"}`: the uniform value of a draw.
* `compare {"kind", "original", "reproduction", "standing"?, "k"?, "material_ratio"?}`:
  the comparison of a reproduction with its target.
* `load {"records", "r"}`: LOAD, the standing records that reach `r`.
* `expected_loss {"e_lo", "load"}`: EXPECTED LOSS.
* `ratio_step {"state", "r", "params"?}`: the PARROT RATIO's epoch.
* `schedule_step {"state", "r", "params"?}`: the CANARY SCHEDULE's tier, bursts and gaps.
* `probe_draw {"schedule", "ratio", "reset", "has_own_record", "r", "params"?}`: the probe
  draw.
* `probe_step {"state", "r", "has_own_record", "params"?}`: one probe step.
* `reset_update {"reset", "event", "account_state", "params"?}`: the RESET's end by state.
* `historical_view {"revisions", "target"}`: the historical view of a register revision.

A number written with a fraction or an exponent is read as v1 read a float, one written
without as v1 read an int. The answer is v1's text of the result (`render_compare`,
`render_load`, `render_probe`, `render_step`, ..., or v1's twelve-digit number for `uniform`
and `expected_loss`). A request v1 refused is refused here with v1's message as the detail
(`BAD_ARGUMENT`), the checks made in v1's order; an M `compare` whose values would cross the
bound on an exact value is refused alike, "exact value too large". Every answer is computed,
the draws with SHA-256 and exact numbers, so none is refused `OWED`.

At most `maxRecords` records for `load`, whose walk from every standing record costs about
the cube of their number; at most `maxRevisions` revisions and `maxAllocated` allocated
identifiers in all for `historical_view`, each checked against those before it; and at
most `maxStanding` standing records of at most `maxStandingDigits` digits each for an M
`compare`, whose SR8 scale factor over them is the strike family's `sr8_scale_factor`,
bounded alike.
-/

namespace Principia.Calculator.Probe

open Principia.Canonical
open Principia.Probe (Datum Answer)

/-- The most records a `load` request holds: 400, none reaching `r`, so that every walk runs
the whole chain, take about 0.2 s. -/
def maxRecords : Nat := 400

/-- The most revisions a `historical_view` request holds: 4000 take about 0.13 s. -/
def maxRevisions : Nat := 4000

/-- The most allocated identifiers, over all revisions, a `historical_view` request
holds: each is checked against those before it, and 4000 take about 0.11 s. -/
def maxAllocated : Nat := 4000

/-- The most standing records an M `compare` holds: the strike family's bound on SR8's
measurements. -/
def maxStanding : Nat := Principia.Calculator.Strike.maxMeasurements

/-- The most digits a standing record's value or uncertainty carries: the strike family's
bound on an SR8 measurement's. -/
def maxStandingDigits : Nat := Principia.Calculator.Strike.maxMeasurementDigits

/-- A request's value as v1's functions received it: an integer as Python's `int`, a number
with a fraction or an exponent as Python's `float`. -/
partial def datum : Value → Datum
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .num x =>
    .real (if 0 ≤ x.exponent then ((x.mantissa * 10 ^ x.exponent.toNat : Int) : Rat)
      else mkRat x.mantissa (10 ^ (-x.exponent).toNat))
  | .str s => .str s
  | .arr xs => .arr (xs.map datum)
  | .obj ms => .obj (ms.map fun (k, v) => (k, datum v))

/-- An answer as `pcalc` gives it: v1's text, or v1's message as a refusal. -/
def answer {α : Type} (render : α → String) : Answer α → Except Refusal Value
  | .ok a => .ok (.str (render a))
  | .refused m => badArgument m

/-- The request's members as v1's functions received them: those in `needed'` must be
present, the others may be absent (`null`). -/
def read (needed' optional' : List String) (v : Value) : Except Refusal (String → Datum) := do
  let ms ← membersOf (needed' ++ optional') v
  for n in needed' do
    let _ ← needed ms n
  pure fun k => ((ms.lookup k).map datum).getD .null

/-- The number of entries of a list or an object, `0` for anything else. -/
def entries : Value → Nat
  | .arr xs => xs.length
  | .obj ms => ms.length
  | _ => 0

/-- The allocated identifiers of a `historical_view` request, over all its revisions. -/
def allocated : Value → Nat
  | .arr revs => revs.foldl (fun n rv => n + match rv with
      | .obj ms => ((ms.lookup "allocated").map entries).getD 0
      | _ => 0) 0
  | _ => 0

/-- The member `k` of a request, `null` when absent. -/
def memberOf (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => (ms.lookup k).getD .null
  | _ => .null

/-- An M `compare`'s standing records within the bounds: at most `maxStanding`, each value
and uncertainty of at most `maxStandingDigits` digits. -/
def standingWithin (v : Value) : Except Refusal Unit := do
  match memberOf v "standing" with
  | .arr ms =>
    atMost "standing" maxStanding ms
    for m in ms do
      for k in ["x", "u"] do
        if maxStandingDigits < numberDigits (memberOf m k) then
          badArgument s!"a standing record's {k} has more than {maxStandingDigits} digits (the Calculator's bound)"
  | _ => pure ()

/-- The family's functions. -/
def calls : Family := [
  ("compare", fun v => do
    let g ← read ["kind", "original", "reproduction"] ["standing", "k", "material_ratio"] v
    standingWithin v
    answer Principia.Probe.renderCompare
      (Principia.Probe.compare (g "kind") (g "original") (g "reproduction") (g "standing") (g "k")
        (g "material_ratio"))),
  ("expected_loss", fun v => do
    let g ← read ["e_lo", "load"] [] v
    answer Exact.printRat12 (Principia.Probe.expectedLoss (g "e_lo") (g "load"))),
  ("historical_view", fun v => do
    let g ← read ["revisions", "target"] [] v
    let revs := memberOf v "revisions"
    atMost "revisions" maxRevisions (List.replicate (entries revs) ())
    atMost "allocated identifiers" maxAllocated (List.replicate (allocated revs) ())
    answer Principia.Probe.renderView (Principia.Probe.historicalView (g "revisions") (g "target"))),
  ("load", fun v => do
    let g ← read ["records", "r"] [] v
    atMost "records" maxRecords (List.replicate (entries (memberOf v "records")) ())
    answer Principia.Probe.renderLoad (Principia.Probe.load (g "records") (g "r"))),
  ("probe_draw", fun v => do
    let g ← read ["schedule", "ratio", "reset", "has_own_record", "r"] ["params"] v
    answer Principia.Probe.renderProbe
      (Principia.Probe.probeDraw (g "schedule") (g "ratio") (g "reset") (g "has_own_record") (g "r")
        (g "params"))),
  ("probe_step", fun v => do
    let g ← read ["state", "r", "has_own_record"] ["params"] v
    answer Principia.Probe.renderStep
      (Principia.Probe.probeStep (g "state") (g "r") (g "params") (g "has_own_record"))),
  ("ratio_step", fun v => do
    let g ← read ["state", "r"] ["params"] v
    answer Principia.Probe.renderRatio (Principia.Probe.ratioStep (g "state") (g "r") (g "params"))),
  ("reset_update", fun v => do
    let g ← read ["reset", "event", "account_state"] ["params"] v
    answer Principia.Probe.renderReset
      (Principia.Probe.resetUpdate (g "reset") (g "event") (g "account_state") (g "params"))),
  ("schedule_step", fun v => do
    let g ← read ["state", "r"] ["params"] v
    answer Principia.Probe.renderSchedule
      (Principia.Probe.scheduleStep (g "state") (g "r") (g "params"))),
  ("uniform", fun v => do
    let g ← read ["tag", "r", "counter"] [] v
    answer Exact.printRat12 (Principia.Probe.uniform (g "tag") (g "r") (g "counter"))),
]

end Principia.Calculator.Probe
