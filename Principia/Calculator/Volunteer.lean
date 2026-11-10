import Principia.Calculator.Interface
import Principia.Calculator.Probe
import Principia.Volunteer

/-!
# Family `volunteer`: the VOLUNTEER law

v1's `tpc_volunteer` 0.1.0 (`Principia.Volunteer`), one function each, named and with its
arguments named as v1's `run_case` names them; `params` may be absent or `null`, as v1 read it
with `args.get`:
* `standing {"facts", "params"?}`: GOOD STANDING and its first failing clause.
* `refill {"bucket", "now", "params"?}`: the token bucket refilled to `now`.
* `take {"bucket"}`: a token taken, when there is one.
* `retry {"attempt", "r", "params"?}`: RETRY AFTER, full jitter under BACKOFF CAP.
* `intake {"intake", "volunteer_blocks", "landed_blocks", "params"?}`: INTAKE's EWMA.
* `p_nw {"intake", "params"?}`: the random early throttle.
* `pv {"state", "r", "params"?}`: the `p_v` epoch.
* `share {"window", "g", "v_max"}`: the VOLUNTEER SHARE cap.
* `draw {"state", "call", "r", "params"?}`: the draw itself.

A number written with a fraction or an exponent is read as v1 read a float, one written
without as v1 read an int (`Calculator.Probe.datum`). The answer is v1's text of the result
(`render_standing`, `render_bucket`, `render_take`, `render_pv`, `render_share`,
`render_draw`, or v1's twelve-digit number for `retry`, `intake` and `p_nw`), each number the
exact value correctly rounded to twelve significant digits. A request v1 refused is refused
here with v1's message as the detail (`BAD_ARGUMENT`), the checks made in v1's order. Every
answer is computed, the draws with SHA-256 and exact numbers, so none is refused `OWED`.

Each function's work is linear in its request, which the request reader bounds: a `share`
window's entries are summed once, RETRY AFTER's `2^attempt` is formed only below 1024.
-/

namespace Principia.Calculator.Volunteer

open Principia.Canonical
open Principia.Calculator.Probe (read answer)

/-- The family's functions. -/
def calls : Family := [
  ("draw", fun v => do
    let g ← read ["state", "call", "r"] ["params"] v
    answer Principia.Volunteer.renderDraw
      (Principia.Volunteer.volunteerDraw (g "state") (g "call") (g "r") (g "params"))),
  ("intake", fun v => do
    let g ← read ["intake", "volunteer_blocks", "landed_blocks"] ["params"] v
    answer Exact.printRat12
      (Principia.Volunteer.intakeUpdate (g "intake") (g "volunteer_blocks") (g "landed_blocks")
        (g "params"))),
  ("p_nw", fun v => do
    let g ← read ["intake"] ["params"] v
    answer Exact.printRat12 (Principia.Volunteer.pNw (g "intake") (g "params"))),
  ("pv", fun v => do
    let g ← read ["state", "r"] ["params"] v
    answer Principia.Volunteer.renderPv (Principia.Volunteer.pvStep (g "state") (g "r") (g "params"))),
  ("refill", fun v => do
    let g ← read ["bucket", "now"] ["params"] v
    answer Principia.Volunteer.renderBucket
      (Principia.Volunteer.bucketRefill (g "bucket") (g "now") (g "params"))),
  ("retry", fun v => do
    let g ← read ["attempt", "r"] ["params"] v
    answer Exact.printRat12 (Principia.Volunteer.retryAfter (g "attempt") (g "r") (g "params"))),
  ("share", fun v => do
    let g ← read ["window", "g", "v_max"] [] v
    answer Principia.Volunteer.renderShare
      (Principia.Volunteer.volunteerShare (g "window") (g "g") (g "v_max"))),
  ("standing", fun v => do
    let g ← read ["facts"] ["params"] v
    answer Principia.Volunteer.renderStanding
      (Principia.Volunteer.goodStanding (g "facts") (g "params"))),
  ("take", fun v => do
    let g ← read ["bucket"] [] v
    answer Principia.Volunteer.renderTake (Principia.Volunteer.bucketTake (g "bucket"))),
]

end Principia.Calculator.Volunteer
