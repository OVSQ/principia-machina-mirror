import Principia.Calculator.Interface
import Principia.Governor

/-!
# Family `governor`: the governor's admission

The admission of `Principia.Governor` on the command line, for Custos's
governor meter. Its eight functions, their arguments named as the governor's corpus
names them:
* `admit {"state", "request"}`: the decision and the charge, in one call:
  `{"decision": "ADMITTED", "charge"}`, or `{"decision": "REFUSED", "status", "refusal",
  ..., "charge"}` with the refusal `SWITCH` and its `reason` and `retry_after`, `RATE` with
  its `payer` and `retry_after`, `SLOTS` with its
  `cap` and `retry_after`, `PRESSURE` (GA4, 503) with the `level` and `retry_after`, or
  `TRAFFIC` (GA3, 429) with the `stage` and `retry_after`. Every refusal carries
  `retry_after`, a whole number of seconds with the jitter: a switch's,
  and the rate's when the request never conforms, is `retry_after_base` with the jitter
  `jitter {"base": retry_after_base, "draw"}`, the request's draw; or
  `{"decision": "CACHED ONLY", "charge": null}`, lane 6 served cached pages only.
  `charge` is `null` outside lanes 2 to 4 and with the governor
  off, else `{"agent": [level, since], "sponsor": [level, since]}`, the buckets once the
  request's seats are charged; Custos applies it to an admitted request only.
* `charge {"state", "request"}`: the charge alone.
* `lane {"kind"}`: `{"lane", "number"}`, the request's lane by its word and its number.
* `seat_cost {"kind", "records", "rows", "seat_table"?}`: the seats an op costs, a
  number; the seat table's starting values, as `seat_table` overrides them. A falcon
  RETURN's rows round up: 4 plus 1 per started group of 20 rows (inventory U4, the
  Declarer's choice), a number for every row count. `PROPOSE_PROVISION` costs 4.
* `jitter {"base", "draw", "share"?}`: the seconds of jitter added to a wait of `base`
  seconds; `share` overrides RETRY-AFTER jitter.
* `pressure_level {"use", "prev", "external_until", "now", "tuning"?}`: the PRESSURE LEVEL's
  update (`Principia.Governor.levelStep`): `{"level", "kept", "ratio"}`, the level in force,
  the level the hysteresis keeps (the next update's `prev`) and the ratio r as `[num, den]`
  in lowest terms. `use` is `{"hour", "day", "thirty_days"}`, CPU use in thousandths of a
  CPU second; `prev` a level's word; the external reading in force while `now` is before
  `external_until`.
* `traffic_step {"traffic", "now", "event" | "end", "tuning"?}`: one step of an account's
  traffic record (`Principia.Governor.Traffic`): with `event`, a TRAFFIC EVENT's word
  (`REPEAT`, `ERROR STREAK`, `BACKOFF VIOLATION`, `CAP OVERRUN`), `trafficStep`; with `end`,
  `{"kind", "ending", "retry_after"}`, a request's end (`ending` one of `SWITCH`,
  `TRAFFIC`, `PRESSURE`, `RATE`, `SLOTS`, `SHAPE`, `FAILED`, `SUCCEEDED`; `retry_after` the
  one sent, or `null`), `afterRequest`. The answer is `{"raises", "traffic"}`: whether TE2
  is raised, which Custos then steps as an event, and the record after.
* `traffic_stage {"traffic", "now", "kind", "tuning"?}`: what GA3 reads of the record at
  `now` for a request of `kind`: `{"stage", "breaker", "flood", "served_retry_after",
  "backoff_violation"}`, the stage in force, the breaker's and the FLOOD INTERVAL's waits
  before the jitter (or `null`), the Retry-After a served call carries (or `null`), and
  whether the request is a TE3.

A traffic record is an object of the members `stage` (a stage's word), `breaker_until`,
`trial_pending`, `retry_after`, `backoff_until`, `streak`, `te3_times`, `throttled_times`,
`penalized_times` (lists of times), `last_event`, `flood_inquire` and `flood_release` (a
time or `null`), every one needed.

The words are the wire words of `Principia.Governor` (rule R1). A state is an object of
the members `now`, `agent_stop`, `suspended`, `governor_off`, `agent_seats`,
`sponsor_seats` (each `[level, since]`, the level in 3600ths of a seat), `agent_in_flight`,
`sponsor_in_flight`, `finishing_in_flight`, `starting_in_flight`, every one needed, so that
no switch or count is taken as its default by omission; the pressure levels' members, each
optional so that a state written before them reads as it did: `pressure` (a level's word,
CLEAR when absent: the level in force, or with `use` the level the hysteresis kept), `use`
(as `pressure_level`'s; the level then computed by `levelStep`), `external_until` (0 when
absent) and `anonymous_in_flight` (0 when absent); and `tuning`, which may be absent,
of the members `agent_seat_rate`, `agent_seat_burst`, `sponsor_seat_rate`,
`sponsor_seat_burst`, `slots_per_agent`, `slots_per_sponsor`, `retry_after_jitter` (a
share `[num, den]`, `den` positive), `slot_retry_after`, `retry_after_base`, `kappa_m` (a
share), `anonymous_slots` and `pseudo_lag` (each four counts, CLEAR to OVERLOADED), each
overriding its starting value, and the readings of the pressure levels, each a word
defaulting to the Declarer's selection: `descent` (`STRAIGHT`, `ONE STEP`, `BANDS`),
`pressure_retry_after` (`SLOT`, `PSEUDO LAG`, `BASE`), `threshold_rule` (`AT THRESHOLD`,
`ABOVE THRESHOLD`), `external_order` (`RAISE AFTER`, `RAISE BEFORE`) and `anonymous_full`
(`CACHED`, `SLOTS`); `retry_after_cap`, `penalty_hour`, `flood_interval` and
`error_streak`, counts; and the readings of the traffic stages, each a word
defaulting to the Declarer's selection: `penalized_payer` (`AGENT`, `AGENT AND SPONSOR`),
`doubling` (`PER REFUSAL`, `PER EVENT`), `trial_success` (`ADMITTED`, `PASSED TRAFFIC`)
and `te2_causes` (`ACCOUNT CAUSES`, `WITH FLEET`). A state may carry `traffic`, the asking
account's record, a NORMAL account with no history when absent. A request is `{"kind",
"seats", "draw"?}`, the draw `[num, den]`, `[0, 1]` (no jitter) when absent.

Bounds: every step is a fixed number of sums, products and quotients of the request's
numbers, which the reader bounds below 2^1024, and one pass over a traffic record's lists
of times, so no request costs more than its reading.
The slowest accepted request measured, an `admit` with every number near 2^1024, took
0.08 s on the command line, about as long as `pcalc` takes to start.
-/

namespace Principia.Calculator.Governor

open Principia.Canonical
open Principia.Parameters
open Principia.Governor (MeteredState Request SeatBucket JitterDraw Charge Decision seatCost
  admit charge jitter PressureReadings ByHorizon levelStep pressureRatio Descent PressureRetry
  ThresholdRule ExternalOrder AnonymousFull TrafficState TrafficStage TrafficEvent TrafficReadings
  PenalizedPayer Doubling TrialSuccess Te2Causes Ending RequestEnd trafficStep afterRequest
  floodWait breakerWait servedRetry backoffViolation)

/-! ## Reading -/

/-- An object's members, each named in `names`; another member is refused. -/
def objectOf (what : String) (names : List String) (v : Value) :
    Except Refusal (List (String × Value)) := do
  let ms ← asObject what v
  match ms.find? (fun m => !names.contains m.1) with
  | some m => badArgument s!"{what} has no member {quote m.1}"
  | none => pure ms

/-- A member an object needs. -/
def required (what : String) (ms : List (String × Value)) (k : String) :
    Except Refusal Value :=
  match ms.lookup k with
  | some x => .ok x
  | none => badArgument s!"{what} lacks the member {quote k}"

/-- A pair of counts `[a, b]`. -/
def pairOf (what : String) : Value → Except Refusal (Nat × Nat)
  | .arr [a, b] => do pure (← asCount what a, ← asCount what b)
  | _ => badArgument s!"{what} is not a pair of counts"

/-- A share `[num, den]`, `den` positive. -/
def ratioOf (what : String) (v : Value) : Except Refusal Ratio := do
  let (n, d) ← pairOf what v
  if h : 0 < d then pure ⟨n, d, h⟩ else badArgument s!"{what} has the denominator 0"

/-- A count member, its default when absent. -/
def countOr (what : String) (ms : List (String × Value)) (k : String) (d : Nat) :
    Except Refusal Nat :=
  match ms.lookup k with
  | some v => asCount s!"{what}'s {k}" v
  | none => pure d

/-- The tuning's members. -/
def tuningMembers : List String := ["agent_seat_rate", "agent_seat_burst", "sponsor_seat_rate",
  "sponsor_seat_burst", "slots_per_agent", "slots_per_sponsor", "retry_after_jitter",
  "slot_retry_after", "retry_after_base", "kappa_m", "anonymous_slots", "pseudo_lag",
  "descent", "pressure_retry_after", "threshold_rule", "external_order", "anonymous_full",
  "retry_after_cap", "penalty_hour", "flood_interval", "error_streak", "penalized_payer",
  "doubling", "trial_success", "te2_causes"]

/-- Four counts, CLEAR to OVERLOADED. -/
def byLevelOf (what : String) : Value → Except Refusal (ByLevel Nat)
  | .arr [a, b, c, d] => do
    pure ⟨← asCount what a, ← asCount what b, ← asCount what c, ← asCount what d⟩
  | _ => badArgument s!"{what} is not four counts"

/-- A word member, its default when absent. -/
def wordOr (α : Type) [WireWord α] (what : String) (ms : List (String × Value)) (k : String)
    (d : α) : Except Refusal α :=
  match ms.lookup k with
  | some v => asWord α s!"{what}'s {k}" v
  | none => pure d

/-- The readings of the pressure levels in `tuning`: each the Declarer's selection
when absent. -/
def readingsOf (v : Option Value) : Except Refusal PressureReadings := do
  let some v := v | pure {}
  let ms ← objectOf "the tuning" tuningMembers v
  let g : PressureReadings := {}
  let w := "the tuning"
  pure {
    descent := ← wordOr Descent w ms "descent" g.descent
    retry := ← wordOr PressureRetry w ms "pressure_retry_after" g.retry
    threshold := ← wordOr ThresholdRule w ms "threshold_rule" g.threshold
    external := ← wordOr ExternalOrder w ms "external_order" g.external
    anonymousFull := ← wordOr AnonymousFull w ms "anonymous_full" g.anonymousFull }

/-- The readings of the traffic stages in `tuning`: each the Declarer's selection when
absent. -/
def trafficReadingsOf (v : Option Value) : Except Refusal TrafficReadings := do
  let some v := v | pure {}
  let ms ← objectOf "the tuning" tuningMembers v
  let g : TrafficReadings := {}
  let w := "the tuning"
  pure {
    payer := ← wordOr PenalizedPayer w ms "penalized_payer" g.payer
    doubling := ← wordOr Doubling w ms "doubling" g.doubling
    trial := ← wordOr TrialSuccess w ms "trial_success" g.trial
    te2 := ← wordOr Te2Causes w ms "te2_causes" g.te2 }

/-- The tuning options in force: the starting values, as `tuning` overrides them. -/
def tuningOf (v : Value) : Except Refusal GovernorTuning := do
  let ms ← objectOf "the tuning" tuningMembers v
  let g : GovernorTuning := {}
  let n := countOr "the tuning" ms
  pure { g with
    retryAfterBase := ⟨← n "retry_after_base" g.retryAfterBase.count⟩
    retryAfterCap := ⟨← n "retry_after_cap" g.retryAfterCap.count⟩
    penaltyHour := ⟨← n "penalty_hour" g.penaltyHour.count⟩
    floodInterval := ⟨← n "flood_interval" g.floodInterval.count⟩
    errorStreak := ← n "error_streak" g.errorStreak
    kappaM := ← match ms.lookup "kappa_m" with
      | some r => ratioOf "the tuning's kappa_m" r
      | none => pure g.kappaM
    anonymousSlots := ← match ms.lookup "anonymous_slots" with
      | some x => byLevelOf "the tuning's anonymous_slots" x
      | none => pure g.anonymousSlots
    pseudoLag := ← match ms.lookup "pseudo_lag" with
      | some x => do
        let b ← byLevelOf "the tuning's pseudo_lag" x
        pure ⟨⟨b.clear⟩, ⟨b.busy⟩, ⟨b.strained⟩, ⟨b.overloaded⟩⟩
      | none => pure g.pseudoLag
    agentSeatRate := ← n "agent_seat_rate" g.agentSeatRate
    agentSeatBurst := ← n "agent_seat_burst" g.agentSeatBurst
    sponsorSeatRate := ← n "sponsor_seat_rate" g.sponsorSeatRate
    sponsorSeatBurst := ← n "sponsor_seat_burst" g.sponsorSeatBurst
    slotsPerAgent := ← n "slots_per_agent" g.slotsPerAgent
    slotsPerSponsor := ← n "slots_per_sponsor" g.slotsPerSponsor
    slotRetryAfter := ⟨← n "slot_retry_after" g.slotRetryAfter.count⟩
    retryAfterJitter := ← match ms.lookup "retry_after_jitter" with
      | some r => ratioOf "the tuning's retry_after_jitter" r
      | none => pure g.retryAfterJitter }

/-- The seat table: the starting values, as `seat_table` overrides them; a falcon RETURN
priced per 0 rows is refused. -/
def seatTableOf (v : Value) : Except Refusal SeatTable := do
  let ms ← objectOf "the seat table" ["push_base", "push_per_record", "return_base",
    "return_per_record", "falcon_return_base", "falcon_return_rows_per_seat",
    "queue_head_acquisition"] v
  let g : SeatTable := {}
  let n := countOr "the seat table" ms
  let rowsPerSeat ← n "falcon_return_rows_per_seat" g.falconReturnRowsPerSeat
  if rowsPerSeat = 0 then badArgument "the seat table's falcon_return_rows_per_seat is 0"
  pure { g with
    pushBase := ← n "push_base" g.pushBase
    pushPerRecord := ← n "push_per_record" g.pushPerRecord
    returnBase := ← n "return_base" g.returnBase
    returnPerRecord := ← n "return_per_record" g.returnPerRecord
    falconReturnBase := ← n "falcon_return_base" g.falconReturnBase
    falconReturnRowsPerSeat := rowsPerSeat
    queueHeadAcquisition := ← n "queue_head_acquisition" g.queueHeadAcquisition }

/-- A seat bucket, `[level, since]`. -/
def bucketOf (what : String) (v : Value) : Except Refusal SeatBucket := do
  let (level, since) ← pairOf what v
  pure ⟨level, since⟩

/-- The metered use over the three horizons, `{"hour", "day", "thirty_days"}`. -/
def useOf (v : Value) : Except Refusal (ByHorizon Nat) := do
  let what := "the use"
  let ms ← objectOf what ["hour", "day", "thirty_days"] v
  let count (k : String) : Except Refusal Nat := do asCount s!"the use's {k}" (← required what ms k)
  pure ⟨← count "hour", ← count "day", ← count "thirty_days"⟩

/-- A list of times, in seconds. -/
def timesOf (what : String) (v : Value) : Except Refusal (List Nat) := do
  (← asList what v).mapM (asCount s!"an entry of {what}")

/-- A time or `null`. -/
def optionalCount (what : String) : Value → Except Refusal (Option Nat)
  | .null => pure none
  | v => some <$> asCount what v

/-- The members of an account's traffic record. -/
def trafficMembers : List String := ["stage", "breaker_until", "trial_pending", "retry_after",
  "backoff_until", "streak", "te3_times", "throttled_times", "penalized_times", "last_event",
  "flood_inquire", "flood_release"]

/-- An account's traffic record, every member needed. -/
def trafficOf (v : Value) : Except Refusal TrafficState := do
  let what := "the traffic"
  let ms ← objectOf what trafficMembers v
  let need := required what ms
  let count (k : String) : Except Refusal Nat := do asCount s!"the traffic's {k}" (← need k)
  pure {
    stage := ← asWord TrafficStage "a TRAFFIC STAGE" (← need "stage")
    breakerUntil := ← count "breaker_until"
    trialPending := ← asBool "the traffic's trial_pending" (← need "trial_pending")
    retryAfter := ← count "retry_after"
    backoffUntil := ← count "backoff_until"
    streak := ← count "streak"
    te3Times := ← timesOf "the traffic's te3_times" (← need "te3_times")
    throttledTimes := ← timesOf "the traffic's throttled_times" (← need "throttled_times")
    penalizedTimes := ← timesOf "the traffic's penalized_times" (← need "penalized_times")
    lastEvent := ← count "last_event"
    floodInquire := ← optionalCount "the traffic's flood_inquire" (← need "flood_inquire")
    floodRelease := ← optionalCount "the traffic's flood_release" (← need "flood_release") }

/-- A metered state. -/
def stateOf (v : Value) : Except Refusal MeteredState := do
  let what := "the state"
  let ms ← objectOf what ["now", "tuning", "agent_stop", "suspended", "governor_off",
    "agent_seats", "sponsor_seats", "agent_in_flight", "sponsor_in_flight",
    "finishing_in_flight", "starting_in_flight", "pressure", "use", "external_until",
    "anonymous_in_flight", "traffic"] v
  let need := required what ms
  let count (k : String) : Except Refusal Nat := do asCount s!"the state's {k}" (← need k)
  let flag (k : String) : Except Refusal Bool := do asBool s!"the state's {k}" (← need k)
  pure {
    now := ← count "now"
    tuning := ← match ms.lookup "tuning" with
      | some t => tuningOf t
      | none => pure {}
    agentStop := ← flag "agent_stop"
    suspended := ← flag "suspended"
    governorOff := ← flag "governor_off"
    agentSeats := ← bucketOf "the state's agent_seats" (← need "agent_seats")
    sponsorSeats := ← bucketOf "the state's sponsor_seats" (← need "sponsor_seats")
    agentInFlight := ← count "agent_in_flight"
    sponsorInFlight := ← count "sponsor_in_flight"
    finishingInFlight := ← count "finishing_in_flight"
    startingInFlight := ← count "starting_in_flight"
    pressure := ← wordOr PressureLevel what ms "pressure" .clear
    use := ← match ms.lookup "use" with
      | some u => some <$> useOf u
      | none => pure none
    externalUntil := ← countOr what ms "external_until" 0
    anonymousInFlight := ← countOr what ms "anonymous_in_flight" 0
    readings := ← readingsOf (ms.lookup "tuning")
    traffic := ← match ms.lookup "traffic" with
      | some x => trafficOf x
      | none => pure {}
    trafficReadings := ← trafficReadingsOf (ms.lookup "tuning") }

/-- A governed request's kind, by its wire word. -/
def kindOf (v : Value) : Except Refusal GovernedRequest :=
  asWord GovernedRequest "a governed request's kind" v

/-- A jitter's draw, `[num, den]`. -/
def drawOf (v : Value) : Except Refusal JitterDraw := do
  let (n, d) ← pairOf "the draw" v
  pure ⟨n, d⟩

/-- A governed request. -/
def requestOf (v : Value) : Except Refusal Request := do
  let what := "the request"
  let ms ← objectOf what ["kind", "seats", "draw"] v
  let need := required what ms
  pure {
    kind := ← kindOf (← need "kind")
    seats := ← asCount "the request's seats" (← need "seats")
    draw := ← match ms.lookup "draw" with
      | some d => drawOf d
      | none => pure {} }

/-! ## Writing -/

/-- A wire word as a value. -/
def word {α : Type} [WireWord α] (a : α) : Value := .str (WireWord.toWire a)

/-- A count as a value. -/
def count (n : Nat) : Value := .int n

/-- A bucket as `[level, since]`. -/
def bucketValue (b : SeatBucket) : Value := .arr [count b.level, count b.since]

/-- A charge, or `null`. -/
def chargeValue : Option Charge → Value
  | none => .null
  | some c => .obj [("agent", bucketValue c.agentSeats), ("sponsor", bucketValue c.sponsorSeats)]

/-- A decision and the charge, as `admit` answers them. -/
def decisionValue (d : Decision) (c : Option Charge) : Value :=
  match d with
  | .admitted => .obj [("charge", chargeValue c), ("decision", word d.word)]
  | .cachedOnly => .obj [("charge", chargeValue c), ("decision", word d.word)]
  | .refused f =>
    let head := [("charge", chargeValue c), ("decision", word d.word),
      ("refusal", word f.word), ("status", count f.status)]
    match f with
    | .switch r ra => .obj (head ++ [("reason", word r), ("retry_after", count ra)])
    | .rate p ra => .obj (head ++ [("payer", word p), ("retry_after", count ra)])
    | .slots cap ra => .obj (head ++ [("cap", word cap), ("retry_after", count ra)])
    | .pressure l ra => .obj (head ++ [("level", word l), ("retry_after", count ra)])
    | .traffic st ra => .obj (head ++ [("retry_after", count ra), ("stage", word st)])

/-- A refusal's value carries `retry_after`, its Retry-After as a whole number. -/
theorem decisionValue_retry_after (f : Principia.Governor.Refusal) (c : Option Charge) :
    ∃ ms, decisionValue (.refused f) c = .obj ms ∧ ("retry_after", count f.retryAfter) ∈ ms := by
  cases f <;> simp [decisionValue, Principia.Governor.Refusal.retryAfter]

/-- Every `REFUSED` decision `admit` answers carries a natural `retry_after`:
never `null`. -/
theorem admit_retry_after (s : MeteredState) (r : Request) (f : Principia.Governor.Refusal)
    (h : admit s r = .refused f) :
    ∃ ms, ∃ n : Nat, decisionValue (admit s r) (charge s r) = .obj ms ∧
      ("retry_after", Value.int n) ∈ ms := by
  obtain ⟨ms, hv, hm⟩ := decisionValue_retry_after f (charge s r)
  exact ⟨ms, f.retryAfter, by rw [h]; exact hv, hm⟩

/-- A time or `null`. -/
def optionalValue : Option Nat → Value
  | some n => count n
  | none => .null

/-- An account's traffic record, its members in byte order. -/
def trafficValue (s : TrafficState) : Value :=
  .obj [("backoff_until", count s.backoffUntil), ("breaker_until", count s.breakerUntil),
    ("flood_inquire", optionalValue s.floodInquire),
    ("flood_release", optionalValue s.floodRelease), ("last_event", count s.lastEvent),
    ("penalized_times", .arr (s.penalizedTimes.map count)), ("retry_after", count s.retryAfter),
    ("stage", word s.stage), ("streak", count s.streak),
    ("te3_times", .arr (s.te3Times.map count)),
    ("throttled_times", .arr (s.throttledTimes.map count)),
    ("trial_pending", .bool s.trialPending)]

/-- A request's end, `{"kind", "ending", "retry_after"}`, the Retry-After a number or `null`. -/
def requestEndOf (v : Value) : Except Refusal RequestEnd := do
  let what := "the end"
  let ms ← objectOf what ["kind", "ending", "retry_after"] v
  let need := required what ms
  pure {
    kind := ← asWord GovernedRequest "a governed request's kind" (← need "kind")
    ending := ← asWord Ending "a request's ending" (← need "ending")
    retryAfter := ← optionalCount "the end's retry_after" (← need "retry_after") }

/-- An exact fraction `[num, den]`, in lowest terms; the ratio is never negative. -/
def fractionValue (q : Rat) : Value := .arr [.int q.num, count q.den]

/-- The family's functions. -/
def calls : Family := [
  ("admit", fun v => do
    let (s, r) ← argument2 "state" "request" v
    let s ← stateOf s
    let r ← requestOf r
    pure (decisionValue (admit s r) (charge s r))),
  ("charge", fun v => do
    let (s, r) ← argument2 "state" "request" v
    let s ← stateOf s
    let r ← requestOf r
    pure (chargeValue (charge s r))),
  ("jitter", fun v => do
    let ms ← membersOf ["base", "draw", "share"] v
    let base ← asCount "the base" (← needed ms "base")
    let d ← drawOf (← needed ms "draw")
    let g : GovernorTuning := {}
    let t ← match optional ms "share" with
      | some sh => do pure { g with retryAfterJitter := ← ratioOf "the share" sh }
      | none => pure g
    pure (count (jitter t base d))),
  ("pressure_level", fun v => do
    let ms ← membersOf ["use", "prev", "external_until", "now", "tuning"] v
    let u ← useOf (← needed ms "use")
    let prev ← asWord PressureLevel "a PRESSURE LEVEL" (← needed ms "prev")
    let untilT ← asCount "the external_until" (← needed ms "external_until")
    let now ← asCount "the now" (← needed ms "now")
    let t ← match optional ms "tuning" with
      | some x => tuningOf x
      | none => pure {}
    let rd ← readingsOf (optional ms "tuning")
    let r := pressureRatio u t
    let st := levelStep rd prev r untilT now
    pure (.obj [("kept", word st.base), ("level", word st.inForce), ("ratio", fractionValue r)])),
  ("traffic_step", fun v => do
    let ms ← membersOf ["traffic", "now", "event", "end", "tuning"] v
    let s ← trafficOf (← needed ms "traffic")
    let now ← asCount "the now" (← needed ms "now")
    let t ← match optional ms "tuning" with
      | some x => tuningOf x
      | none => pure {}
    let rd ← trafficReadingsOf (optional ms "tuning")
    match optional ms "event", optional ms "end" with
    | some e, none =>
      let e ← asWord TrafficEvent "a TRAFFIC EVENT" e
      pure (.obj [("raises", .bool false), ("traffic", trafficValue (trafficStep t rd s e now))])
    | none, some q =>
      let a := afterRequest t rd s (← requestEndOf q) now
      pure (.obj [("raises", .bool a.raisesStreak), ("traffic", trafficValue a.traffic)])
    | _, _ => badArgument "the function takes one of the arguments \"event\" and \"end\""),
  ("traffic_stage", fun v => do
    let ms ← membersOf ["traffic", "now", "kind", "tuning"] v
    let s ← trafficOf (← needed ms "traffic")
    let now ← asCount "the now" (← needed ms "now")
    let k ← kindOf (← needed ms "kind")
    let t ← match optional ms "tuning" with
      | some x => tuningOf x
      | none => pure {}
    let rd ← trafficReadingsOf (optional ms "tuning")
    let s' := s.settled t now
    pure (.obj [("backoff_violation", .bool (backoffViolation s now)),
      ("breaker", optionalValue (breakerWait rd s' now)),
      ("flood", optionalValue (floodWait t s' k now)),
      ("served_retry_after", optionalValue (servedRetry t s' now)),
      ("stage", word s'.stage)])),
  ("lane", fun v => do
    let k ← kindOf (← argument1 "kind" v)
    pure (.obj [("lane", word (laneOf k)), ("number", count (laneOf k).number)])),
  ("seat_cost", fun v => do
    let ms ← membersOf ["kind", "records", "rows", "seat_table"] v
    let k ← kindOf (← needed ms "kind")
    let records ← asCount "the records" (← needed ms "records")
    let rows ← asCount "the rows" (← needed ms "rows")
    let t ← match optional ms "seat_table" with
      | some st => seatTableOf st
      | none => pure {}
    match seatCost t k records rows with
    | some n => pure (count n)
    | none => badArgument "the seat table states no cost for this request"),
]

end Principia.Calculator.Governor
