import Principia.Exact
import Principia.Probe

/-!
# The VOLUNTEER law

v1's tpc_volunteer 0.1.0: the VOLUNTEER channel's law as pure functions of recorded state and
a supplied random value. GOOD STANDING and its first failing clause; the token bucket on the
call (VOLUNTEER RATE tokens an hour up to VOLUNTEER BURST); RETRY AFTER with full jitter
under BACKOFF CAP; INTAKE's EWMA and the random early throttle `p_nw`; the `p_v` epoch drawn
from P_V BOUNDS; the VOLUNTEER SHARE cap; and the draw itself, which answers a call REFUSED,
NO WORK, WORK (an ITEM or a PROBE) or FALCON. Each function takes its arguments as v1 took
them, JSON-shaped (`Probe.Datum`), and refuses what v1 refused with v1's fixed message
(`ERROR:<message>` in its text), the checks made in v1's order.

**The draws.** Every uniform value is the probe draw's (`Probe.uniformValue`): `m / 2^52`,
`m` the first 52 bits of the SHA-256 of the netstring of `[tag, "1", r, counter]`, which v1's
double held exactly. The tags are v1's: `TPC-VOLUNTEER-RETRY`, `TPC-PV-ROTATE`, `TPC-PV-DRAW`,
`TPC-VOLUNTEER-NW`, `TPC-VOLUNTEER-PV` and `TPC-VOLUNTEER-KIND` (counters 0 and 1).

**Numbers are exact.** Where v1 computed in doubles, the value here is the exact rational of
the decimals given; where v1's text printed a double (`canon_float`, C's `%.12g`), the text
prints the exact value correctly rounded to twelve significant digits (`Exact.printRat12`), as
the probe family does. A case of v1's corpus whose double fell on the other side of a
twelfth-digit rounding, or of a comparison, than the exact value is a recorded divergence of
the corpus, never a widened tolerance.

**One case v1 left undefined.** A REFUSED answer's state carries the `p_v` it was given; v1
printed it without checking it, and a `p_v` that is neither `null` nor a number made v1 raise
an error of another kind than its refusals. Here such a `p_v` is refused `state`, the
message `pv_step` gives it on every answered call.

PROVED: the bucket's tokens after `refill` never exceed VOLUNTEER BURST
(`bucketRefill_le_burst`); `p_nw` lies in `[0, 1]` (`pNw_bounds`); RETRY AFTER never exceeds
BACKOFF CAP (`retryAfter_le_cap`); a `p_v` drawn by `pv` lies inside P_V BOUNDS, and a `p_v`
kept inside them stays inside (`pvStep_drawn_bounds`, `pvStep_inside`).
-/

namespace Principia.Volunteer

open Principia.Probe (Datum Answer need check boolText isHex32 hexText uniformValue countMax)

/-! ## Arguments as v1 took them -/

/-- v1's bound on server times: the last second of the year 9999. -/
def timeMax : Int := 253402300799

/-- v1's `_pf`: a declared number within `lo..hi`, either end open when asked, refused
`params:<key>` otherwise. -/
def pf (params : Datum) (key : String) (lo hi : Rat) (loOpen hiOpen : Bool := false) :
    Answer Rat := do
  let v ← need ((params.get? key).bind Datum.num?) ("params:" ++ key)
  check (!(v < lo || v > hi || (loOpen && v == lo) || (hiOpen && v == hi))) ("params:" ++ key)
  return v

/-- v1's `_pi`: a declared integer within `lo..hi`, refused `params:<key>` otherwise. -/
def pi (params : Datum) (key : String) (lo hi : Int) : Answer Int :=
  need ((params.get? key).bind (·.intIn? lo hi)) ("params:" ++ key)

/-- v1's `_num(x)` within `[0, 1]`. -/
def unit? (d : Datum) : Option Rat := d.num?.filter fun x => 0 ≤ x && x ≤ 1

/-! ## GOOD STANDING (GS1) -/

/-- The facts' keys, in v1's order. -/
def standingKeys : List String :=
  ["certificate_current", "dis_match", "state", "reset_in_force", "suspended", "in_tier"]

/-- v1's `good_standing`: certificate current, D(IS) matching, state GREEN, no reset in
force, not SUSPENDED, and, under VOLUNTEER TIER = TRUST TIER, in the tier; the first failing
clause is the reason. -/
def goodStanding (facts params : Datum) : Answer (Bool × String) := do
  check (facts.keysAre standingKeys) "facts"
  let b (k : String) := (facts.getD k).bool?
  let some cert := b "certificate_current" | .refused "facts"
  let some dis := b "dis_match" | .refused "facts"
  let some reset := b "reset_in_force" | .refused "facts"
  let some susp := b "suspended" | .refused "facts"
  let some inTier := b "in_tier" | .refused "facts"
  let st ← need ((facts.getD "state").str?.filter fun s =>
    s = "GREEN" ∨ s = "YELLOW" ∨ s = "ORANGE" ∨ s = "SUSPENDED") "facts"
  let tier ← need ((params.get? "VOLUNTEER TIER").bind Datum.str? |>.filter fun t =>
    t = "ANY GREEN" ∨ t = "TRUST TIER") "params:VOLUNTEER TIER"
  if !cert then return (false, "CERTIFICATE")
  if !dis then return (false, "D(IS)")
  if st ≠ "GREEN" then return (false, "STATE")
  if reset then return (false, "RESET")
  if susp then return (false, "SUSPENDED")
  if tier = "TRUST TIER" && !inTier then return (false, "TIER")
  return (true, "GOOD STANDING")

/-- v1's `render_standing`. -/
def renderStanding (d : Bool × String) : String := boolText d.1 ++ "|" ++ d.2

/-! ## The token bucket (BR1, BT1) -/

/-- A token bucket: its tokens and the server time they were counted at. -/
structure Bucket where
  tokens : Rat
  updated : Int
  deriving Repr

/-- v1's `_bucket`. -/
def readBucket (d : Datum) : Answer Bucket := do
  check (d.keysAre ["tokens", "updated"]) "bucket"
  let t ← need ((d.getD "tokens").num?.filter (0 ≤ ·)) "bucket"
  let u ← need ((d.getD "updated").intIn? 0 timeMax) "bucket"
  return ⟨t, u⟩

/-- BR1 on checked values: `min(BURST, tokens + RATE (now - updated) / 3600)`, counted at
`now`. -/
def refillCore (b : Bucket) (now : Int) (rate : Rat) (burst : Int) : Bucket :=
  let t := b.tokens + rate * ((now - b.updated : Int) : Rat) / 3600
  ⟨if t > (burst : Rat) then (burst : Rat) else t, now⟩

/-- v1's `bucket_refill`. -/
def bucketRefill (bucket now params : Datum) : Answer Bucket := do
  let b ← readBucket bucket
  let n ← need ((now.intIn? 0 timeMax).filter (b.updated ≤ ·)) "now"
  let rate ← pf params "VOLUNTEER RATE" 0 1000000000 (loOpen := true)
  let burst ← pi params "VOLUNTEER BURST" 1 countMax
  return refillCore b n rate burst

/-- BT1 on a checked bucket: a token is taken when there is one. -/
def takeCore (b : Bucket) : Bool × Bucket :=
  if 1 ≤ b.tokens then (true, ⟨b.tokens - 1, b.updated⟩) else (false, b)

/-- v1's `bucket_take`. -/
def bucketTake (bucket : Datum) : Answer (Bool × Bucket) := do
  return takeCore (← readBucket bucket)

/-- v1's `render_bucket`. -/
def renderBucket (b : Bucket) : String := Exact.printRat12 b.tokens ++ "|" ++ toString b.updated

/-- v1's `render_take`. -/
def renderTake (d : Bool × Bucket) : String := boolText d.1 ++ "|" ++ renderBucket d.2

/-! ## RETRY AFTER (RA1) -/

/-- RA1's bound: BACKOFF CAP once `2^attempt` overflows v1's double (`attempt ≥ 1024`), else
`min(CAP, BASE 2^attempt)`. -/
def retryBound (attempt : Nat) (base cap : Rat) : Rat :=
  if 1024 ≤ attempt then cap
  else
    let b := base * ((2 ^ attempt : Nat) : Rat)
    if b > cap then cap else b

/-- RA1 on checked values: the draw `TPC-VOLUNTEER-RETRY` 0 times the bound. -/
def retryCore (attempt : Nat) (rs : String) (base cap : Rat) : Rat :=
  uniformValue "TPC-VOLUNTEER-RETRY" rs 0 * retryBound attempt base cap

/-- v1's BACKOFF BASE and BACKOFF CAP, in order. -/
def backoff (params : Datum) : Answer (Rat × Rat) := do
  let base ← pf params "BACKOFF BASE" 1 timeMax
  let cap ← pf params "BACKOFF CAP" 1 timeMax
  check (base ≤ cap) "params:BACKOFF CAP"
  return (base, cap)

/-- v1's `retry_after`: seconds. -/
def retryAfter (attempt r params : Datum) : Answer Rat := do
  let a ← need (attempt.intIn? 0 countMax) "attempt"
  check (isHex32 r) "r"
  let (base, cap) ← backoff params
  return retryCore a.toNat (hexText r) base cap

/-! ## INTAKE (IU1) and the random early throttle -/

/-- v1's `intake_update`: `(1 - w_q) intake + w_q share`, the share 0 when no block landed. -/
def intakeUpdate (intake volunteerBlocks landedBlocks params : Datum) : Answer Rat := do
  let i ← need (unit? intake) "intake"
  let v ← need (volunteerBlocks.intIn? 0 countMax) "blocks"
  let l ← need (landedBlocks.intIn? 0 countMax) "blocks"
  check (v ≤ l) "blocks"
  let w ← pf params "INTAKE w_q" 0 1
  let share : Rat := if l = 0 then 0 else (v : Rat) / (l : Rat)
  return (1 - w) * i + w * share

/-- `p_nw` on checked values: 0 at or below INTAKE MIN, linear to INTAKE MAX_P at INTAKE MAX,
1 above. -/
def pNwCore (i lo hi mp : Rat) : Rat :=
  if i ≤ lo then 0 else if i > hi then 1 else (i - lo) / (hi - lo) * mp

/-- v1's INTAKE MIN, INTAKE MAX and INTAKE MAX_P, in order. -/
def intakeParams (params : Datum) : Answer (Rat × Rat × Rat) := do
  let lo ← pf params "INTAKE MIN" 0 1
  let hi ← pf params "INTAKE MAX" 0 1
  let mp ← pf params "INTAKE MAX_P" 0 1
  check (lo < hi) "params:INTAKE MAX"
  return (lo, hi, mp)

/-- v1's `p_nw`. -/
def pNw (intake params : Datum) : Answer Rat := do
  let i ← need (unit? intake) "intake"
  let (lo, hi, mp) ← intakeParams params
  return pNwCore i lo hi mp

/-! ## The p_v epoch (PV1) -/

/-- A `p_v` step: the value in force and whether an epoch started on this call. -/
structure PvStep where
  pv : Rat
  started : Bool
  deriving Repr

/-- v1's P_V BOUNDS: two numbers, `0 < lo ≤ hi < 1`. -/
def pvBounds (params : Datum) : Answer (Rat × Rat) := do
  let b ← need ((params.get? "P_V BOUNDS").bind Datum.arr?) "params:P_V BOUNDS"
  match b with
  | [x, y] =>
    match x.num?, y.num? with
    | some lo, some hi =>
      check (0 < lo && hi < 1 && lo ≤ hi) "params:P_V BOUNDS"
      return (lo, hi)
    | _, _ => .refused "params:P_V BOUNDS"
  | _ => .refused "params:P_V BOUNDS"

/-- PV1 on values: a new epoch when there is no `p_v` or `u0` falls below P_V ROTATION, its
value `lo + u1 (hi - lo)`. -/
def pvPure (pv : Option Rat) (u0 u1 lo hi rot : Rat) : PvStep :=
  match pv with
  | none => ⟨lo + u1 * (hi - lo), true⟩
  | some p => if u0 < rot then ⟨lo + u1 * (hi - lo), true⟩ else ⟨p, false⟩

/-- PV1 on checked values: `u0` the draw `TPC-PV-ROTATE` 0, `u1` the draw `TPC-PV-DRAW` 0. -/
def pvCore (pv : Option Rat) (rs : String) (lo hi rot : Rat) : PvStep :=
  pvPure pv (uniformValue "TPC-PV-ROTATE" rs 0) (uniformValue "TPC-PV-DRAW" rs 0) lo hi rot

/-- A `p_v` state's value: `null`, or a number in `[0, 1]`. -/
def readPv (state : Datum) : Answer (Option Rat) := do
  check (state.keysAre ["p_v"]) "state"
  match state.getD "p_v" with
  | .null => return none
  | d => return some (← need (unit? d) "state")

/-- v1's `pv_step`. -/
def pvStep (state r params : Datum) : Answer PvStep := do
  let pv ← readPv state
  check (isHex32 r) "r"
  let (lo, hi) ← pvBounds params
  let rot ← pf params "P_V ROTATION" 0 1
  return pvCore pv (hexText r) lo hi rot

/-- v1's `render_pv`. -/
def renderPv (d : PvStep) : String := Exact.printRat12 d.pv ++ "|" ++ boolText d.started

/-! ## The VOLUNTEER SHARE cap (VS1) -/

/-- A share: `q`, the window's weight `W`, its volunteer weight `W_v`, and the weight
admitted, `g q`. -/
structure Share where
  q : Rat
  w : Rat
  wv : Rat
  admitted : Rat
  deriving Repr

/-- v1's `_clip`. -/
def clip (x lo hi : Rat) : Rat := if x < lo then lo else if x > hi then hi else x

/-- v1's `volunteer_share`: `q = clip((v_max (W + g) - W_v) / g, 0, 1)`. -/
def volunteerShare (window g vMax : Datum) : Answer Share := do
  let es ← need window.arr? "window"
  let gf ← need (g.num?.filter (0 < ·)) "g"
  let vm ← need (vMax.num?.filter fun v => 0 < v && v < 1) "v_max"
  let ws ← es.mapM fun e => do
    check (e.keysAre ["volunteer", "weight"]) "window"
    let vol ← need (e.getD "volunteer").bool? "window"
    let w ← need ((e.getD "weight").num?.filter (0 ≤ ·)) "window"
    return (vol, w)
  let wAll := ws.foldl (fun s x => s + x.2) 0
  let wV := ws.foldl (fun s x => if x.1 then s + x.2 else s) 0
  let q := clip ((vm * (wAll + gf) - wV) / gf) 0 1
  return ⟨q, wAll, wV, gf * q⟩

/-- v1's `render_share`. -/
def renderShare (d : Share) : String :=
  "|".intercalate ([d.q, d.w, d.wv, d.admitted].map Exact.printRat12)

/-! ## The draw (VD1-VD7) -/

/-- A volunteer state as the draw writes it back. `retryUntil` and `closedUntil` are absent
until set; `pv` is the `p_v` state's value. -/
structure DrawState where
  bucket : Bucket
  retryUntil : Option Rat
  attempt : Int
  refusals : Int
  period : Int
  closedUntil : Option Int
  intake : Rat
  pv : Option Rat
  deriving Repr

/-- The draw's record: the answer, its kind and reason, RETRY AFTER, and the `p_nw`, `p_v`,
INTAKE and attempt it was drawn with. -/
structure DrawRecord where
  answer : String
  kind : Option String
  reason : Option String
  retryAfter : Rat
  pNw : Option Rat
  pv : Option Rat
  intake : Rat
  attempt : Int
  deriving Repr

/-- The state's keys and the call's, in v1's order. -/
def stateKeys : List String :=
  ["bucket", "retry_until", "attempt", "refusals", "period", "closed_until", "intake", "p_v"]

def callKeys : List String :=
  ["now", "block", "period", "has_item", "has_falcon", "has_own_record", "ratio_k", "standing"]

/-- The PROBE's kind (VD5): a parrot when `w < k / (1 + k)`, a CONSISTENCY PARROT when also
`x < CONSISTENCY SHARE` and the account has an own record, else a CANARY. -/
def probeKind (rs : String) (k share : Rat) (ownRecord : Bool) : String :=
  if uniformValue "TPC-VOLUNTEER-KIND" rs 0 < k / (1 + k) then
    if uniformValue "TPC-VOLUNTEER-KIND" rs 1 < share && ownRecord then "CONSISTENCY PARROT"
    else "CORROBORATION PARROT"
  else "CANARY"

/-- v1's `volunteer_draw`: one call on the VOLUNTEER channel, its record and the state after
it. -/
def volunteerDraw (state call r params : Datum) : Answer (DrawRecord × DrawState) := do
  check (state.keysAre stateKeys && call.keysAre callKeys) "state"
  let bucket0 ← readBucket (state.getD "bucket")
  let ru ← match state.getD "retry_until" with
    | .null => pure none
    | d => do pure (some (← need (d.num?.filter (0 ≤ ·)) "state"))
  let attempt ← need ((state.getD "attempt").intIn? 0 countMax) "state"
  let refusals0 ← need ((state.getD "refusals").intIn? 0 countMax) "state"
  let period0 ← need ((state.getD "period").intIn? 0 countMax) "state"
  let closed ← match state.getD "closed_until" with
    | .null => pure none
    | d => do pure (some (← need (d.intIn? 0 countMax) "state"))
  let intake ← need (unit? (state.getD "intake")) "state"
  let pvs := state.getD "p_v"
  check (pvs.keysAre ["p_v"]) "state"
  let now ← need ((call.getD "now").intIn? 0 timeMax) "call"
  let block ← need ((call.getD "block").intIn? 0 countMax) "call"
  let period ← need (((call.getD "period").intIn? 0 countMax).filter (period0 ≤ ·)) "call"
  let some hasItem := (call.getD "has_item").bool? | .refused "call"
  let some hasFalcon := (call.getD "has_falcon").bool? | .refused "call"
  let some ownRecord := (call.getD "has_own_record").bool? | .refused "call"
  let k ← need ((call.getD "ratio_k").num?.filter (0 < ·)) "call"
  check (isHex32 r) "r"
  let rs := hexText r
  let limit ← pi params "EARLY CALL LIMIT" 0 countMax
  let cool ← pi params "VOLUNTEER COOL-OFF" 1 countMax
  let share ← pf params "CONSISTENCY SHARE" 0 1
  let (standing, _) ← goodStanding (call.getD "standing") params
  let refusals := if period = period0 then refusals0 else 0
  let refused (reason : String) (bucket : Bucket) (count : Bool) :
      Answer (DrawRecord × DrawState) := do
    let (base, cap) ← backoff params
    let ra := retryCore attempt.toNat rs base cap
    let retryEnd : Rat := match ru with
      | some u => if u > (now : Rat) + ra then u else (now : Rat) + ra
      | none => (now : Rat) + ra
    let (nref, nclosed) :=
      if count then
        if refusals + 1 > limit then (0, some (block + cool)) else (refusals + 1, closed)
      else (refusals, closed)
    let pvKept ← match pvs.getD "p_v" with
      | .null => pure none
      | d => do pure (some (← need d.num? "state"))
    return (⟨"REFUSED", none, some reason, ra, none, none, intake, attempt⟩,
      ⟨bucket, some retryEnd, attempt, nref, period, nclosed, intake, pvKept⟩)
  if !standing then return ← refused "STANDING" bucket0 false
  if let some c := closed then
    if block < c then return ← refused "CLOSED" bucket0 false
  let bucket1 ← bucketRefill (state.getD "bucket") (call.getD "now") params
  if let some u := ru then
    if (now : Rat) < u then return ← refused "EARLY" bucket1 true
  let (took, bucket2) := takeCore bucket1
  if !took then return ← refused "TOKEN" bucket1 true
  let pv ← pvStep pvs r params
  let pnw ← pNw (state.getD "intake") params
  let (answer, kind, reason, attempt') :=
    if hasFalcon then ("FALCON", some "FALCON", none, attempt)
    else if uniformValue "TPC-VOLUNTEER-NW" rs 0 < pnw then
      ("NO WORK", none, some "THROTTLE", attempt + 1)
    else if uniformValue "TPC-VOLUNTEER-PV" rs 0 < pv.pv then
      ("WORK", some (probeKind rs k share ownRecord), none, 0)
    else if hasItem then ("WORK", some "ITEM", none, 0)
    else ("NO WORK", none, some "EMPTY", attempt + 1)
  check (attempt' ≤ countMax) "attempt"
  let (base, cap) ← backoff params
  let ra := retryCore attempt'.toNat rs base cap
  return (⟨answer, kind, reason, ra, some pnw, some pv.pv, intake, attempt'⟩,
    ⟨bucket2, some ((now : Rat) + ra), attempt', refusals, period, closed, intake, some pv.pv⟩)

/-- A value or `-`. -/
def orDash {α : Type} (f : α → String) : Option α → String
  | some a => f a
  | none => "-"

/-- v1's `render_draw`: the answer, the draw and the state, one line each. -/
def renderDraw (d : DrawRecord × DrawState) : String :=
  let (rec, st) := d
  "\n".intercalate [
    "|".intercalate ["answer", rec.answer, orDash id rec.kind, orDash id rec.reason,
      Exact.printRat12 rec.retryAfter],
    "|".intercalate ["draw", orDash Exact.printRat12 rec.pNw, orDash Exact.printRat12 rec.pv,
      Exact.printRat12 rec.intake, toString rec.attempt],
    "|".intercalate ["state", renderBucket st.bucket, orDash Exact.printRat12 st.retryUntil,
      toString st.attempt, toString st.refusals, toString st.period,
      orDash toString st.closedUntil, orDash Exact.printRat12 st.pv]]

end Principia.Volunteer

namespace Principia.Volunteer

open Principia.Probe

/-! ## PROVED -/

/-- `pf` gives a value within its bounds. -/
theorem pf_bounds {params : Datum} {key : String} {lo hi v : Rat} {a b : Bool}
    (h : pf params key lo hi a b = .ok v) : lo ≤ v ∧ v ≤ hi := by
  unfold pf at h
  cases hv : (params.get? key).bind Datum.num? with
  | none => rw [hv] at h; simp at h
  | some x =>
    rw [hv] at h
    simp only [need_some, ok_bind] at h
    rw [bind_eq_ok] at h
    obtain ⟨_, hc, hr⟩ := h
    simp only [pure_eq, Answer.ok.injEq] at hr
    subst hr
    rw [check_eq_ok] at hc
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    exact ⟨Rat.not_lt.mp hc.1.1.1, Rat.not_lt.mp hc.1.1.2⟩

/-- BR1 never fills past BURST. -/
theorem refillCore_le_burst (b : Bucket) (now : Int) (rate : Rat) (burst : Int) :
    (refillCore b now rate burst).tokens ≤ burst := by
  unfold refillCore
  simp only
  split
  · exact Rat.le_refl
  · exact Rat.not_lt.mp ‹_›

/-- The bucket's tokens after `refill` never exceed VOLUNTEER BURST as declared. -/
theorem bucketRefill_le_burst {bucket now params : Datum} {b : Bucket}
    (h : bucketRefill bucket now params = .ok b) :
    ∃ burst : Int, pi params "VOLUNTEER BURST" 1 countMax = .ok burst ∧ b.tokens ≤ burst := by
  unfold bucketRefill at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨b0, _, n, _, rate, _, burst, hb, he⟩ := h
  exact ⟨burst, hb, he ▸ refillCore_le_burst b0 n rate burst⟩

/-- RA1's bound never exceeds the cap. -/
theorem retryBound_le_cap (attempt : Nat) (base cap : Rat) :
    retryBound attempt base cap ≤ cap := by
  unfold retryBound
  split
  · exact Rat.le_refl
  · simp only
    split
    · exact Rat.le_refl
    · exact Rat.not_lt.mp ‹_›

/-- RA1's bound is not negative for a positive base and cap. -/
theorem retryBound_nonneg (attempt : Nat) {base cap : Rat} (hb : 0 ≤ base) (hc : 0 ≤ cap) :
    0 ≤ retryBound attempt base cap := by
  unfold retryBound
  split
  · exact hc
  · simp only
    split
    · exact hc
    · exact Rat.mul_nonneg hb Rat.natCast_nonneg

/-- RETRY AFTER on checked values lies in `[0, cap]`. -/
theorem retryCore_bounds (attempt : Nat) (rs : String) {base cap : Rat} (hb : 0 ≤ base)
    (hc : 0 ≤ cap) :
    0 ≤ retryCore attempt rs base cap ∧ retryCore attempt rs base cap ≤ cap := by
  unfold retryCore
  have h0 := uniformValue_nonneg "TPC-VOLUNTEER-RETRY" rs 0
  have h1 := uniformValue_lt_one "TPC-VOLUNTEER-RETRY" rs 0
  have hn := retryBound_nonneg attempt hb hc
  have hl := retryBound_le_cap attempt base cap
  have hm := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) hn
  exact ⟨Rat.mul_nonneg h0 hn, by grind⟩

/-- `backoff` gives a base and a cap of at least 1. -/
theorem backoff_bounds {params : Datum} {base cap : Rat}
    (h : backoff params = .ok (base, cap)) : 1 ≤ base ∧ 1 ≤ cap := by
  unfold backoff at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨b, hb, c, hc, _, _, hbe, hce⟩ := h
  subst hbe hce
  exact ⟨(pf_bounds hb).1, (pf_bounds hc).1⟩

/-- RETRY AFTER never exceeds BACKOFF CAP as declared, and is not negative. -/
theorem retryAfter_le_cap {attempt r params : Datum} {v : Rat}
    (h : retryAfter attempt r params = .ok v) :
    ∃ base cap : Rat, backoff params = .ok (base, cap) ∧ 0 ≤ v ∧ v ≤ cap := by
  unfold retryAfter at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨a, _, _, _, ⟨base, cap⟩, hbc, he⟩ := h
  have hb := backoff_bounds hbc
  have hr := retryCore_bounds a.toNat (hexText r) (base := base) (cap := cap)
    (Rat.le_trans (by decide) hb.1) (Rat.le_trans (by decide) hb.2)
  exact ⟨base, cap, hbc, he ▸ hr.1, he ▸ hr.2⟩

/-- `p_nw` on checked values lies in `[0, 1]` when INTAKE MAX_P does. -/
theorem pNwCore_bounds (i lo hi mp : Rat) (hm : 0 ≤ mp) (hm1 : mp ≤ 1) :
    0 ≤ pNwCore i lo hi mp ∧ pNwCore i lo hi mp ≤ 1 := by
  unfold pNwCore
  split
  · exact ⟨Rat.le_refl, by decide⟩
  · split
    · exact ⟨by decide, Rat.le_refl⟩
    · have h : lo < i := Rat.not_le.mp ‹_›
      have h2 : i ≤ hi := Rat.not_lt.mp ‹_›
      have hd : 0 < hi - lo := by grind
      have hinv : 0 ≤ (hi - lo)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
      have hone : (hi - lo) * (hi - lo)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
      have ht0 : 0 ≤ (i - lo) * (hi - lo)⁻¹ := Rat.mul_nonneg (by grind) hinv
      have ht1 : (i - lo) * (hi - lo)⁻¹ ≤ (hi - lo) * (hi - lo)⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right (by grind) hinv
      have h3 := Rat.mul_le_mul_of_nonneg_left hm1 ht0
      rw [Rat.div_def]
      exact ⟨Rat.mul_nonneg ht0 hm, by grind⟩

/-- INTAKE MAX_P as read lies in `[0, 1]`. -/
theorem intakeParams_maxP {params : Datum} {lo hi mp : Rat}
    (h : intakeParams params = .ok (lo, hi, mp)) : 0 ≤ mp ∧ mp ≤ 1 := by
  unfold intakeParams at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, m, hm, _, _, _, _, rfl⟩ := h
  exact pf_bounds hm

/-- `p_nw` lies in `[0, 1]`. -/
theorem pNw_bounds {intake params : Datum} {p : Rat} (h : pNw intake params = .ok p) :
    0 ≤ p ∧ p ≤ 1 := by
  unfold pNw at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨i, _, ⟨lo, hi, mp⟩, hip, hp⟩ := h
  have hm := intakeParams_maxP hip
  exact hp ▸ pNwCore_bounds i lo hi mp hm.1 hm.2

/-- A drawn `p_v` lies in `[lo, hi]`. -/
theorem fresh_bounds {u lo hi : Rat} (h0 : 0 ≤ u) (h1 : u < 1) (hl : lo ≤ hi) :
    lo ≤ lo + u * (hi - lo) ∧ lo + u * (hi - lo) ≤ hi := by
  have hd : 0 ≤ hi - lo := by grind
  have hm := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) hd
  have hn := Rat.mul_nonneg h0 hd
  exact ⟨by grind, by grind⟩

/-- PV1 on values: a started epoch's value lies in `[lo, hi]`; a kept value is the one
given. -/
theorem pvPure_spec (pv : Option Rat) {u0 u1 lo hi rot : Rat} (h0 : 0 ≤ u1) (h1 : u1 < 1)
    (hl : lo ≤ hi) :
    ((pvPure pv u0 u1 lo hi rot).started = true →
      lo ≤ (pvPure pv u0 u1 lo hi rot).pv ∧ (pvPure pv u0 u1 lo hi rot).pv ≤ hi) ∧
    ((pvPure pv u0 u1 lo hi rot).started = false → pv = some (pvPure pv u0 u1 lo hi rot).pv) := by
  cases pv with
  | none => exact ⟨fun _ => fresh_bounds h0 h1 hl, fun h => Bool.noConfusion h⟩
  | some p =>
    by_cases hr : u0 < rot
    · simp only [pvPure, hr, ↓reduceIte]
      exact ⟨fun _ => fresh_bounds h0 h1 hl, fun h => Bool.noConfusion h⟩
    · simp only [pvPure, hr, ↓reduceIte]
      exact ⟨fun h => Bool.noConfusion h, by simp⟩

/-- PV1 on checked values, the draws in `[0, 1)`. -/
theorem pvCore_spec (pv : Option Rat) (rs : String) {lo hi rot : Rat} (hl : lo ≤ hi) :
    ((pvCore pv rs lo hi rot).started = true →
      lo ≤ (pvCore pv rs lo hi rot).pv ∧ (pvCore pv rs lo hi rot).pv ≤ hi) ∧
    ((pvCore pv rs lo hi rot).started = false → pv = some (pvCore pv rs lo hi rot).pv) :=
  pvPure_spec pv (uniformValue_nonneg _ _ _) (uniformValue_lt_one _ _ _) hl

/-- P_V BOUNDS as read: `0 < lo ≤ hi < 1`. -/
theorem pvBounds_spec {params : Datum} {lo hi : Rat} (h : pvBounds params = .ok (lo, hi)) :
    0 < lo ∧ lo ≤ hi ∧ hi < 1 := by
  unfold pvBounds at h
  simp only [bind_eq_ok] at h
  obtain ⟨b, _, hb⟩ := h
  match b, hb with
  | [x, y], hb =>
    simp only at hb
    split at hb
    · rename_i l u _ _
      simp only [bind_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, hc, rfl, rfl⟩ := hb
      rw [check_eq_ok] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hc.1.1, hc.2, hc.1.2⟩
    · cases hb

/-- A `p_v` drawn by `pv` lies inside P_V BOUNDS as declared. -/
theorem pvStep_drawn_bounds {state r params : Datum} {d : PvStep}
    (h : pvStep state r params = .ok d) (hs : d.started = true) :
    ∃ lo hi : Rat, pvBounds params = .ok (lo, hi) ∧ lo ≤ d.pv ∧ d.pv ≤ hi := by
  unfold pvStep at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨pv, _, _, _, ⟨lo, hi⟩, hb, rot, _, he⟩ := h
  have hl := (pvBounds_spec hb).2.1
  subst he
  exact ⟨lo, hi, hb, (pvCore_spec pv (hexText r) (rot := rot) hl).1 hs⟩

/-- A `p_v` inside P_V BOUNDS stays inside them: the value `pv` gives is the one drawn, or
the one given. -/
theorem pvStep_inside {state r params : Datum} {d : PvStep} {lo hi : Rat}
    (h : pvStep state r params = .ok d) (hb : pvBounds params = .ok (lo, hi))
    (hin : ∀ p, readPv state = .ok (some p) → lo ≤ p ∧ p ≤ hi) :
    lo ≤ d.pv ∧ d.pv ≤ hi := by
  unfold pvStep at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨pv, hpv, _, _, ⟨lo', hi'⟩, hb', rot, _, he⟩ := h
  rw [hb] at hb'
  simp only [Answer.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  have hl := (pvBounds_spec hb).2.1
  have spec := pvCore_spec pv (hexText r) (rot := rot) hl
  subst he
  cases hs : (pvCore pv (hexText r) lo hi rot).started with
  | true => exact spec.1 hs
  | false =>
    have hk := spec.2 hs
    rw [hk] at hpv
    exact hin _ hpv

/-- A value `need` gives is the option's. -/
theorem need_eq_ok {α : Type} {o : Option α} {m : String} {a : α} (h : need o m = .ok a) :
    o = some a := by
  cases o with
  | none => simp at h
  | some x => simp only [need_some, Answer.ok.injEq] at h; rw [h]

/-- BT1: a take succeeds exactly when the bucket holds a whole token. -/
theorem takeCore_took (b : Bucket) : (takeCore b).1 = true ↔ 1 ≤ b.tokens := by
  unfold takeCore
  split <;> simp_all

/-- BT1: a successful take removes exactly one token and keeps the time counted at. -/
theorem takeCore_taken {b : Bucket} (h : (takeCore b).1 = true) :
    (takeCore b).2.tokens = b.tokens - 1 ∧ (takeCore b).2.updated = b.updated := by
  unfold takeCore at h ⊢
  split at h <;> simp_all

/-- BT1: a refused take leaves the bucket as it was. -/
theorem takeCore_refused {b : Bucket} (h : (takeCore b).1 = false) : (takeCore b).2 = b := by
  unfold takeCore at h ⊢
  split at h <;> simp_all

/-- BT1: a take never leaves the tokens negative. -/
theorem takeCore_nonneg {b : Bucket} (h : 0 ≤ b.tokens) : 0 ≤ (takeCore b).2.tokens := by
  unfold takeCore
  split
  · show 0 ≤ b.tokens - 1
    grind
  · exact h

/-- A bucket as read holds no negative tokens. -/
theorem readBucket_nonneg {d : Datum} {b : Bucket} (h : readBucket d = .ok b) :
    0 ≤ b.tokens := by
  unfold readBucket at h
  simp only [bind_eq_ok, pure_eq] at h
  obtain ⟨_, _, t, ht, u, _, he⟩ := h
  cases he
  have hs := need_eq_ok ht
  rw [Option.filter_eq_some_iff] at hs
  simpa using hs.2

/-- `bucket_take` takes from the bucket as read and leaves no negative tokens. -/
theorem bucketTake_spec {bucket : Datum} {d : Bool × Bucket} (h : bucketTake bucket = .ok d) :
    ∃ b, readBucket bucket = .ok b ∧ d = takeCore b ∧ 0 ≤ d.2.tokens := by
  unfold bucketTake at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨b, hb, he⟩ := h
  subst he
  exact ⟨b, hb, rfl, takeCore_nonneg (readBucket_nonneg hb)⟩

/-- `clip` to `[0, 1]` lies in `[0, 1]`. -/
theorem clip_unit (x : Rat) : 0 ≤ clip x 0 1 ∧ clip x 0 1 ≤ 1 := by
  unfold clip
  split
  · exact ⟨Rat.le_refl, by decide⟩
  · split
    · exact ⟨by decide, Rat.le_refl⟩
    · exact ⟨Rat.not_lt.mp ‹_›, Rat.not_lt.mp ‹_›⟩

/-- VS1 on values: the weight admitted, `g clip(x, 0, 1)`, is nothing or at most `g x`. -/
theorem clip_admitted {g : Rat} (x : Rat) (hg : 0 < g) :
    g * clip x 0 1 = 0 ∨ g * clip x 0 1 ≤ g * x := by
  unfold clip
  split
  · left
    exact Rat.mul_zero g
  · right
    split
    · exact Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt ‹_›) (Rat.le_of_lt hg)
    · exact Rat.le_refl

/-- VS1 on values: the share after admission never exceeds `v_max` unless nothing is
admitted. -/
theorem shareCap {g vm w wv : Rat} (hg : 0 < g) :
    g * clip ((vm * (w + g) - wv) / g) 0 1 = 0 ∨
      wv + g * clip ((vm * (w + g) - wv) / g) 0 1 ≤ vm * (w + g) := by
  have hc : g * ((vm * (w + g) - wv) / g) = vm * (w + g) - wv := by
    rw [Rat.div_def, Rat.mul_comm (vm * (w + g) - wv), ← Rat.mul_assoc,
      Rat.mul_inv_cancel _ (Rat.ne_of_gt hg), Rat.one_mul]
  rcases clip_admitted ((vm * (w + g) - wv) / g) hg with h | h
  · exact Or.inl h
  · right
    rw [hc] at h
    grind

/-- VOLUNTEER SHARE (VS1): on an answer, `q` lies in `[0, 1]`, the weight admitted is `g q`,
and the share after admission never exceeds `v_max` unless nothing is admitted, over the
values of `g` and `v_max` as read. -/
theorem volunteerShare_spec {window g vMax : Datum} {s : Share}
    (h : volunteerShare window g vMax = .ok s) :
    ∃ gf vm : Rat, g.num? = some gf ∧ vMax.num? = some vm ∧ 0 < gf ∧ 0 < vm ∧ vm < 1 ∧
      0 ≤ s.q ∧ s.q ≤ 1 ∧ s.admitted = gf * s.q ∧
      (s.admitted = 0 ∨ s.wv + s.admitted ≤ vm * (s.w + gf)) := by
  unfold volunteerShare at h
  simp only [bind_eq_ok, pure_eq, Answer.ok.injEq] at h
  obtain ⟨_, _, gf, hg, vm, hv, _, _, he⟩ := h
  subst he
  have hg' := need_eq_ok hg
  have hv' := need_eq_ok hv
  rw [Option.filter_eq_some_iff] at hg' hv'
  simp only [decide_eq_true_eq, Bool.and_eq_true] at hg' hv'
  exact ⟨gf, vm, hg'.1, hv'.1, hg'.2, hv'.2.1, hv'.2.2, (clip_unit _).1, (clip_unit _).2, rfl,
    shareCap hg'.2⟩

end Principia.Volunteer
