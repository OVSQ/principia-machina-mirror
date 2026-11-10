import Principia.Parameters
import Principia.Wire
import Principia.Governor.Pressure
import Principia.Governor.Traffic

/-!
# The governor's admission

The admission rule: lanes 0 to 6, seats, slots and Retry-After stay, and their decision
function is `Principia.Governor.admit : MeteredState → Request → Decision`, with the
theorem that lanes 0 to 2 are never refused on budget. This file is the first port,
admission, built in three increments as the Declarer chose: version 1's rules as
TPS 0.5.0 states them, since version 1 never wrote the governor's code (its TPX 0.6.0
has none) and has no corpus for it. Sources: TPS 5.3.31 to 5.3.38, 5.9.18, 7.2.21,
7.2.24 and 7.2.30; the lane table and the values are
`Principia.Parameters`. Vectors: the governor's corpus, their expectations computed by
a hand-written script, a transcription of the same rules written apart
from this file (GCRA by its theoretical arrival time, in exact fractions), run by
the governor's test runner.

## What a request goes through

Version 1 orders the steps GA0 to GA9 and ends a request at its first refusal
(TPS 5.3.35). This port decides five of them, below; GA7 is dropped, as the Declarer
chose; the PRE-GATE, the meter (GA0, GA9), the shape check (GA1) and the step inside the
op (GA8) stay Custos's, GA9's traffic counters stepped by
`Principia.Governor.Traffic`'s pure functions.

* **GA2, the switches**: the Operator's AGENT STOP refuses lanes 2 to 4, then an account
  CONTAINED (TPS 5.3.37), then one SUSPENDED under CR6 or CR11; 403 with the reason
  and RETRY-AFTER's base with its jitter, as the Declarer chose.
  STATUS, RELEASE and INQUIRE pass (TPS 5.3.35, 5.3.38).
* **GA3, the traffic stages**: a CONTAINED account's INQUIRE or RELEASE inside the FLOOD
  INTERVAL since its last answer (5.3.37 refuses it "at GA2", so it holds with GOVERNOR
  OFF), then the traffic breaker open (THROTTLED or PENALIZED) for every op but STATUS,
  RELEASE and INQUIRE, HEARTBEAT among them; 429 with the Retry-After and its jitter (TPS
  5.3.35, 5.3.37, 5.9.18). Under PENALIZED, GA5 charges at the agent's seat rate halved
  as the Declarer chose. With GOVERNOR OFF the breaker is skipped, as the Declarer chose.
  `Principia.Governor.Traffic` states the events, the stages and the readings.
* **GA4, the pressure**: the lane against the PRESSURE LEVEL (TPS 5.3.34): BUSY refuses
  lane 4, STRAINED and OVERLOADED lanes 3 to 5; 503 with the Retry-After of the reading
  `retry` (SLOT RETRY-AFTER and its jitter, as the Declarer chose). Lane 6 runs under
  the level's anonymous slots and is served cached pages only at OVERLOADED. The level is
  the one Custos passes, or `levelStep`'s update from the uses
  (`Principia.Governor.Pressure`). With GOVERNOR OFF the step is skipped.
* **GA5, the rate**: an op's SEATS, its declared cost, are charged by GCRA to the
  sponsor first, then to the agent, at SEAT RATES (120 an hour, burst 20, for an agent;
  240 an hour, burst 30, for a sponsor). Lane 2 is debited and never refused; lanes 3
  and 4 are refused 429 with the time to conformance (TPS 5.3.35, 5.3.36, 7.2.24), or,
  for a request that never conforms (a seat rate of 0), RETRY-AFTER's base, each with its
  jitter, as the Declarer chose: every refusal carries a Retry-After. With
  GOVERNOR OFF the step is skipped: nothing is charged and nothing refused on the rate.
* **GA6, the slots**: the agent's slot (one request in flight), its sponsor's (two),
  then the lane pool: six agent-lane slots, two kept for lane 2, so lanes 3 and 4
  together hold at most four; 503 with SLOT RETRY-AFTER, 5 seconds at the starting
  value, and its jitter (TPS 5.3.33, 5.3.35, 5.3.36, 5.9.18).

Lanes 0 and 1 are never refused on budget, and lane 2 never on budget, rate, pressure
or share (TPS 5.3.33); lane 2 is refused by GA3, as 5.3.37 names HEARTBEAT, a traffic
refusal being an account cause and not one on budget. Lanes 0 and 1 are admitted, lane 5
refused by GA4 alone, lane 6 decided by its slots and the level; a state that passes no
level is at CLEAR, where GA4 refuses nothing, and one that passes no traffic record is a
NORMAL account with no history, where GA3 refuses nothing, so a state written before GA4
or GA3 is decided as it was.

## Readings

Where the text needs a reading to be computed, the reading taken and why:

* **GCRA as a bucket.** GCRA at RATE seats an hour with burst BURST is the bucket of
  depth BURST seats that drains at RATE seats an hour (ITU-T I.371's continuous-state
  leaky bucket, the same algorithm as its virtual scheduling); version 1 words its own
  token bucket so (TPS 5.9.16, VOLUNTEER BURST). A request of `c` seats conforms when
  the bucket, drained to now, holds room for `c` more. Levels are kept in 3600ths of a
  seat, so a drain over whole seconds at a whole rate is a whole number and nothing is
  rounded.
* **Lane 2's debit** may fill a bucket past its depth (the debt GCRA keeps when it
  debits a request it does not refuse); the debt drains as the bucket does.
* **The time to conformance** is the request's, when the sponsor's and the agent's
  buckets both conform, rounded up to the whole second: Retry-After is a whole number
  of seconds (TPS 5.9.18), and a shorter wait would see a client that honours it
  exactly (TPS 5.4.13) refused again. It is not capped: RETRY-AFTER's base and cap are
  the traffic stages' (TPS 5.3.37). A request rated at 0 seats an hour that does not
  conform now never will, and has no time to conformance.
* **A request dearer than a burst** conforms for that payer when the payer's bucket,
  drained to now, is empty, and is charged in full, its debt draining as lane 2's does
  (the Declarer's choice): so a falcon RETURN of any size can be returned. Its time to
  conformance is the time the bucket takes to empty.
* **The jitter**: "up to 10 per cent random jitter to every Retry-After, drawn
  independently of the response content" (TPS 5.9.18). Custos draws a fraction and
  passes it in the request; the seconds added are that fraction of the jitter share of
  the wait, rounded down, so the Retry-After never exceeds the wait by more than the
  share. A slot refusal's wait is SLOT RETRY-AFTER, jittered alike.
* **The slots**: lane 2 may take any of the six agent-lane slots; lanes 3 and 4 any
  but the two kept. The counts are of requests in flight before this one.
* **A clock behind a bucket**: a bucket last charged after `now` is not drained.

## Where TPS 0.5.0 is silent or disagrees: the Declarer's answers

* GA6 answers 503 "with a short Retry-After" and states no value: SLOT RETRY-AFTER, a
  tuning option, 5 seconds at its starting value (an ESTIMATE, tuned in the sandboxes),
  jittered as every Retry-After. RETRY-AFTER's base of 60 seconds is not taken: work
  finishing in lane 2 would wait a minute.
* The seat table prices no queue head's acquisition: it costs 1 seat, as POLL and
  HEARTBEAT. A request dearer than its payer's burst conforms on an empty bucket (the
  reading above). A falcon RETURN's "4 + 1 per 20 result rows" rounds up (inventory U4,
  the Declarer's choice): a started group of 20 rows costs a seat, so `seatCost` answers
  every row count. The lane of an AGENT core write (U10) stays open.
* The Provision proposal op, which TPS 0.5.0 does not govern, is `proposeProvision`, wire
  word `PROPOSE_PROVISION`, in LANE 4 beside VOLUNTEER at 4 seats (the Declarer's choice):
  shed first under pressure and refused on budget.
* GA7 CONTENTION refuses "when a lane's pool is full", which GA6 has refused before it:
  it is dropped, every refusal at a full pool being GA6's 503, the per-sponsor slot cap
  and the seat rate bounding a sponsor's share.
* GOVERNOR OFF "returns admission to the slot caps alone" (TPS 5.3.38): it is a field of
  the metered state under which `admit` skips GA3's breaker, GA4 and GA5 and keeps GA2's
  switches (CONTAINED and its FLOOD INTERVAL among them) and GA6's slots for lanes 2 to 4; GA5 skipped, `charge`
  debits nothing. Lane 6 is then admitted without its anonymous slots: their cap is set
  by the level, which GA4 skipped does not read (a reading of this port, reviewed with
  it). A governor fault "fails closed to the slot caps" (TPS 5.3.31): that
  fault mode stays Custos's own fallback when its tables are unreachable. GOVERNOR OFF
  is not read as that fault mode, which would lift AGENT STOP and let a SUSPENDED
  account land.
* The seats GA5 debits when GA6 then refuses: none. `charge` is the debit, which Custos
  applies to an admitted request only.

* GA4's 503 and the readings TPS leaves open: the descent under hysteresis, GA4's
  Retry-After, X1's threshold and the external reading's order, each a field of
  `PressureReadings` defaulting to the Declarer's selection; and a full lane 6 below
  OVERLOADED, served cached pages by default (5.3.40 ER3: a 503 "in OVERLOADED only").
  `Principia.Governor.Pressure` states them.

* GA3's four readings TPS leaves open: whose seat rate halves under PENALIZED, when
  the Retry-After doubles, what makes the trial a success and which refusals count toward
  TE2, each a field of `TrafficReadings` defaulting to the Declarer's selection.
  `Principia.Governor.Traffic` states them and the readings of this port where TPS is
  silent. With it the governor's three increments are built; the theorems about lanes
  0 to 2 survived each.
-/

namespace Principia.Governor

open Principia.Parameters

/-! ## Seats -/

/-- Seats are counted in 3600ths: a bucket that drains one seat an hour drains one
3600th a second. -/
def seatUnit : Nat := 3600

/-- The seats an op costs, its SEATS (TPS 7.2.24, 7.2.30), for an AGENT account's
request; `records` is the count a PUSH or RETURN carries, `rows` a falcon RETURN's
result rows. A request outside the agent lanes is charged no seats. The queue head's
acquisition costs `queueHeadAcquisition`, 1 as POLL and HEARTBEAT, as the Declarer chose.
A falcon RETURN's rows round up: a started group of `falconReturnRowsPerSeat` rows costs a
seat (inventory U4, the Declarer's choice). Every request has a cost; `none` is kept for a
cost the seat table may leave unstated. -/
def seatCost (t : SeatTable) (k : GovernedRequest) (records rows : Nat) : Option Nat :=
  match k with
  | .status => some t.status
  | .pollByHeadOrHolder => some t.poll
  | .pollOther => some t.poll
  | .heartbeat => some t.heartbeat
  | .inquire => some t.inquire
  | .petition => some t.petition
  | .releaseOp => some t.releaseOp
  | .volunteer => some t.volunteer
  | .workReturn => some (t.returnBase + t.returnPerRecord * records)
  | .push => some (t.pushBase + t.pushPerRecord * records)
  | .agentCoreRead => some t.coreRead
  | .structureTestOp => some t.structureTest
  | .falconReturn =>
    some (t.falconReturnBase +
      (rows + t.falconReturnRowsPerSeat - 1) / t.falconReturnRowsPerSeat)
  | .proposeProvision => some t.proposeProvision
  | .queueHeadAcquisition => some t.queueHeadAcquisition
  | .declarerOrOperator | .essentialJob | .signedInUser | .structureTestButton
  | .deferrableJob | .falconJob | .bibliographyRecheckJob | .structureTestJob
  | .configurationStrataJob | .anonymousRead => some 0

/-- One payer's seat bucket: its level in 3600ths of a seat as of `since`, the server
time (whole seconds) it was last charged. -/
structure SeatBucket where
  /-- The level, in 3600ths of a seat; past the depth after lane 2's debits. -/
  level : Nat := 0
  /-- When the level was set. -/
  since : Nat := 0
  deriving Repr, DecidableEq

namespace SeatBucket

/-- The level drained at `rate` seats an hour from `since` to `now`; not drained when
`now` is not after `since`. -/
def drained (b : SeatBucket) (rate now : Nat) : Nat :=
  b.level - rate * (now - b.since)

/-- The most the drained level may be for a request of `seats` to conform: the room it
needs below the depth, `burst` seats; `0`, an empty bucket, for a request dearer than the
burst. -/
def room (burst seats : Nat) : Nat := burst * seatUnit - seats * seatUnit

/-- A request of `seats` conforms: the drained level leaves room for it below the depth,
`burst` seats; a request dearer than the burst conforms when the bucket is empty, and is
charged in full, its debt draining as lane 2's does. -/
def conforms (b : SeatBucket) (rate burst now seats : Nat) : Bool :=
  decide (b.drained rate now ≤ room burst seats)

/-- The bucket once `seats` are charged at `now`. -/
def debit (b : SeatBucket) (rate now seats : Nat) : SeatBucket :=
  ⟨b.drained rate now + seats * seatUnit, max b.since now⟩

/-- `a / d` rounded up. -/
def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d

/-- Seconds from `now` until a request of `seats` conforms, if no other charge comes:
`0` when it conforms now; `none` when it never will (a rate of 0). -/
def wait (b : SeatBucket) (rate burst now seats : Nat) : Option Nat :=
  if b.conforms rate burst now seats then some 0
  else if rate = 0 then none
  else some ((b.since - now) + ceilDiv (b.drained rate now - room burst seats) rate)

end SeatBucket

/-! ## The request, the state and the decision -/

/-- Custos's draw for a Retry-After's jitter: the fraction `num / den` of the most
jitter allowed. A numerator past the denominator counts as the denominator; a
denominator of 0 draws no jitter. -/
structure JitterDraw where
  /-- The numerator. -/
  num : Nat := 0
  /-- The denominator. -/
  den : Nat := 1
  deriving Repr, DecidableEq

/-- A governed request. -/
structure Request where
  /-- What it is, as the LANE TABLE sorts it; its lane is `laneOf kind`. -/
  kind : GovernedRequest
  /-- Its declared cost, `seatCost`; read for a request in lanes 2 to 4. -/
  seats : Nat := 0
  /-- The jitter's draw, for a Retry-After. -/
  draw : JitterDraw := {}
  deriving Repr

/-- What Custos has recorded that bears on one request (TPS 5.3.32, 5.3.42: "STATE IN
TABLES"). The agent and sponsor fields are the asking AGENT account's and its
sponsor's; for a request outside lanes 2 to 4 they are not read. -/
structure MeteredState where
  /-- Server time, whole seconds. -/
  now : Nat
  /-- The tuning options in force. -/
  tuning : GovernorTuning := {}
  /-- The Operator's AGENT STOP (TPS 5.3.38). -/
  agentStop : Bool := false
  /-- The asking AGENT account is SUSPENDED under CR6 or CR11 (TPS 5.3.35). -/
  suspended : Bool := false
  /-- GOVERNOR OFF (TPS 5.3.38): admission skips the rate, and keeps the switches and the
  slots, as the Declarer chose. -/
  governorOff : Bool := false
  /-- The agent's seat bucket. -/
  agentSeats : SeatBucket := {}
  /-- Its sponsor's seat bucket. -/
  sponsorSeats : SeatBucket := {}
  /-- The agent's requests in flight. -/
  agentInFlight : Nat := 0
  /-- Its sponsor's agents' requests in flight. -/
  sponsorInFlight : Nat := 0
  /-- Lane 2's requests in flight, fleet-wide. -/
  finishingInFlight : Nat := 0
  /-- Lanes 3 and 4's requests in flight, fleet-wide. -/
  startingInFlight : Nat := 0
  /-- The PRESSURE LEVEL (TPS 5.3.34): with no `use`, the level in force; with `use`, the
  level the hysteresis kept at the last update, from which `levelStep` steps. -/
  pressure : PressureLevel := .clear
  /-- The metered use over the three horizons, in thousandths of a CPU second, when Custos
  passes the uses rather than the level (TPS 5.3.32). -/
  use : Option (ByHorizon Nat) := none
  /-- The external reading's raised step is in force while `now` is before this (TPS
  5.3.31): the reading's time plus `externalReadingStep`; read with `use`. -/
  externalUntil : Nat := 0
  /-- Lane 6's anonymous expensive actions in flight (TPS 5.3.33, 5.3.40). -/
  anonymousInFlight : Nat := 0
  /-- The readings of the pressure levels in force. -/
  readings : PressureReadings := {}
  /-- The asking AGENT account's traffic record (TPS 5.3.37): NORMAL with no history when
  absent, so a state written before GA3 is decided as it was. -/
  traffic : TrafficState := {}
  /-- The readings of the traffic stages in force. -/
  trafficReadings : TrafficReadings := {}
  deriving Repr

/-- The PRESSURE LEVEL in force: the level Custos passed, or the update of the level the
hysteresis kept from the uses and the external reading. -/
def MeteredState.level (s : MeteredState) : PressureLevel :=
  match s.use with
  | none => s.pressure
  | some u => (levelStep s.readings s.pressure (pressureRatio u s.tuning) s.externalUntil s.now).inForce

/-- The account's traffic record in force now: PENALIZED ended PENALTY HOUR after its last
event. -/
def MeteredState.trafficNow (s : MeteredState) : TrafficState :=
  s.traffic.settled s.tuning s.now

/-- A seat rate halved (TPS 5.3.37, PENALIZED: `penalizedSeatRateFactor`), rounded up so that
a positive rate stays positive. -/
def halve (rate : Nat) : Nat :=
  (rate * penalizedSeatRateFactor.num + penalizedSeatRateFactor.den - 1) /
    penalizedSeatRateFactor.den

/-- The seat rates GA5 charges and drains at: the tuning's, the agent's halved under
PENALIZED (and the sponsor's too under the reading `agentAndSponsor`). -/
def MeteredState.seatTuning (s : MeteredState) : GovernorTuning :=
  if s.trafficNow.stage = .penalized then
    { s.tuning with
      agentSeatRate := halve s.tuning.agentSeatRate
      sponsorSeatRate := match s.trafficReadings.payer with
        | .agent => s.tuning.sponsorSeatRate
        | .agentAndSponsor => halve s.tuning.sponsorSeatRate }
  else s.tuning

/-- A switch that refuses (GA2). -/
inductive Switch where
  /-- The Operator's AGENT STOP. -/
  | agentStop
  /-- The account is SUSPENDED under CR6 or CR11. -/
  | suspended
  /-- The account is CONTAINED (TPS 5.3.35, 5.3.37). -/
  | contained
  deriving Repr, DecidableEq

/-- Whose seats refused (GA5). -/
inductive Payer where
  /-- The sponsor's. -/
  | sponsor
  /-- The agent's. -/
  | agent
  deriving Repr, DecidableEq

/-- Which slot cap refused (GA6). -/
inductive SlotCap where
  /-- The agent's: one request in flight. -/
  | agent
  /-- Its sponsor's: two. -/
  | sponsor
  /-- The lane pool. -/
  | pool
  /-- Lane 6's anonymous slots for the level (TPS 5.3.34), under the reading `slots`. -/
  | anonymous
  deriving Repr, DecidableEq

/-- A refusal, with what the client contract sends (TPS 5.9.18). -/
inductive Refusal where
  /-- 403 with the reason and the Retry-After in seconds: RETRY-AFTER's base with the
  jitter, as the Declarer chose. -/
  | switch (reason : Switch) (retryAfter : Nat)
  /-- 429 with the Retry-After in seconds, jitter included: the time to conformance, or
  RETRY-AFTER's base when the request never conforms, as the Declarer chose. -/
  | rate (payer : Payer) (retryAfter : Nat)
  /-- 503 with its "short Retry-After" in seconds: SLOT RETRY-AFTER with the jitter. -/
  | slots (cap : SlotCap) (retryAfter : Nat)
  /-- GA4: 503, the lane refused at the level, with the Retry-After reading (b) gives. -/
  | pressure (level : PressureLevel) (retryAfter : Nat)
  /-- GA3: 429, the traffic breaker open (THROTTLED or PENALIZED) or a CONTAINED account's
  INQUIRE or RELEASE inside the FLOOD INTERVAL, with the Retry-After and its jitter. -/
  | traffic (stage : TrafficStage) (retryAfter : Nat)
  deriving Repr, DecidableEq

/-- The HTTP status a refusal is answered with (TPS 5.9.18). -/
def Refusal.status : Refusal → Nat
  | .switch .. => 403
  | .rate .. => 429
  | .slots .. => 503
  | .pressure .. => 503
  | .traffic .. => 429

/-- A refusal on budget, in the widest sense version 1's lane 2 rule names ("never
refused on budget, rate, pressure or share", TPS 5.3.33): of these this port refuses on
the rate and the pressure. -/
def Refusal.onBudget : Refusal → Bool
  | .rate .. => true
  | .pressure .. => true
  | _ => false

/-- The decision. -/
inductive Decision where
  /-- Admitted; an agent's request is charged `charge`. -/
  | admitted
  /-- Refused. -/
  | refused (refusal : Refusal)
  /-- Lane 6: served cached pages only (TPS 5.3.34, OVERLOADED; 5.3.40). -/
  | cachedOnly
  deriving Repr, DecidableEq

/-! ## The steps -/

/-- The agent lanes, 2 to 4: where the switches, the seats and the slots act. -/
def agentLane : Lane → Bool
  | .finishing | .starting | .optional => true
  | _ => false

/-- STATUS, RELEASE and INQUIRE pass the switches (TPS 5.3.35, 5.3.38). -/
def passesSwitches : GovernedRequest → Bool
  | .status | .releaseOp | .inquire => true
  | _ => false

/-- The seconds of jitter added to a wait of `base` seconds: the draw's fraction of
RETRY-AFTER jitter's share of `base`, rounded down. -/
def jitter (t : GovernorTuning) (base : Nat) (d : JitterDraw) : Nat :=
  base * t.retryAfterJitter.num * min d.num d.den / (t.retryAfterJitter.den * d.den)

/-- A Retry-After: the wait and its jitter. -/
def withJitter (t : GovernorTuning) (base : Nat) (d : JitterDraw) : Nat :=
  base + jitter t base d

/-- The sponsor's bucket conforms. -/
def sponsorConforms (s : MeteredState) (r : Request) : Bool :=
  s.sponsorSeats.conforms s.seatTuning.sponsorSeatRate s.tuning.sponsorSeatBurst s.now r.seats

/-- The agent's bucket conforms. -/
def agentConforms (s : MeteredState) (r : Request) : Bool :=
  s.agentSeats.conforms s.seatTuning.agentSeatRate s.tuning.agentSeatBurst s.now r.seats

/-- The request's time to conformance: the later of the sponsor's and the agent's;
`none` when either never conforms. -/
def conformanceWait (s : MeteredState) (r : Request) : Option Nat :=
  match s.sponsorSeats.wait s.seatTuning.sponsorSeatRate s.tuning.sponsorSeatBurst s.now r.seats,
    s.agentSeats.wait s.seatTuning.agentSeatRate s.tuning.agentSeatBurst s.now r.seats with
  | some a, some b => some (max a b)
  | _, _ => none

/-- GA2: the switch that refuses, if any, in TPS 5.3.35's order: AGENT STOP, CONTAINED,
SUSPENDED. -/
def switchStep (s : MeteredState) (r : Request) : Option Switch :=
  if passesSwitches r.kind then none
  else if s.agentStop then some .agentStop
  else if s.trafficNow.stage = .contained then some .contained
  else if s.suspended then some .suspended
  else none

/-- The traffic stages' refusals (TPS 5.3.35, 5.3.37), each 429 with its Retry-After and the
jitter: a CONTAINED account's INQUIRE or RELEASE inside the FLOOD INTERVAL, which 5.3.37
refuses "at GA2" and so holds with the governor off, as the switches do; then GA3,
the breaker open for every op but STATUS, RELEASE and INQUIRE, skipped with the governor
off. A CONTAINED account's other ops are GA2's 403. -/
def trafficCheck (s : MeteredState) (r : Request) : Option Refusal :=
  match floodWait s.tuning s.trafficNow r.kind s.now with
  | some w => some (.traffic .contained (withJitter s.tuning w r.draw))
  | none =>
    if s.governorOff ∨ passesSwitches r.kind then none
    else match breakerWait s.trafficReadings s.trafficNow s.now with
      | some w => some (.traffic s.trafficNow.stage (withJitter s.tuning w r.draw))
      | none => none

/-- The Retry-After of a refusal the law gives no wait of its own (a switch's, and the
rate's when the request never conforms): RETRY-AFTER's base with the jitter, as the
Declarer chose. -/
def baseRetry (s : MeteredState) (r : Request) : Nat :=
  withJitter s.tuning s.tuning.retryAfterBase.count r.draw

/-- GA5's Retry-After: the request's time to conformance with the jitter, or `baseRetry`
when it never conforms. -/
def rateRetry (s : MeteredState) (r : Request) : Nat :=
  match conformanceWait s r with
  | some w => withJitter s.tuning w r.draw
  | none => baseRetry s r

/-- GA5 for lanes 3 and 4: the refusal, if any, sponsor first, then agent. -/
def rateStep (s : MeteredState) (r : Request) : Option Refusal :=
  let retry := rateRetry s r
  if !sponsorConforms s r then some (.rate .sponsor retry)
  else if !agentConforms s r then some (.rate .agent retry)
  else none

/-- GA6: the slot cap that refuses, if any, in version 1's order. -/
def slotStep (s : MeteredState) (lane : Lane) : Option SlotCap :=
  if s.tuning.slotsPerAgent ≤ s.agentInFlight then some .agent
  else if s.tuning.slotsPerSponsor ≤ s.sponsorInFlight then some .sponsor
  else if agentLaneSlots ≤ s.finishingInFlight + s.startingInFlight then some .pool
  else if lane ≠ .finishing ∧ agentLaneSlots - slotsKeptForFinishing ≤ s.startingInFlight then
    some .pool
  else none

/-- GA5 as the lane takes it: lane 2 is debited and never refused; lanes 3 and 4 by
`rateStep`; with the governor off, skipped. -/
def rateCheck (s : MeteredState) (r : Request) : Option Refusal :=
  if laneOf r.kind = .finishing ∨ s.governorOff then none else rateStep s r

/-- GA6's Retry-After: SLOT RETRY-AFTER with the jitter. -/
def slotRetry (s : MeteredState) (r : Request) : Nat :=
  withJitter s.tuning s.tuning.slotRetryAfter.count r.draw

/-- GA4's Retry-After at the level, by reading (b): SLOT RETRY-AFTER, the
level's PSEUDO-LAG, or RETRY-AFTER's base, each with the jitter. -/
def pressureRetry (s : MeteredState) (r : Request) (l : PressureLevel) : Nat :=
  let base := match s.readings.retry with
    | .slot => s.tuning.slotRetryAfter.count
    | .pseudoLag => (s.tuning.pseudoLag.at l).count
    | .base => s.tuning.retryAfterBase.count
  withJitter s.tuning base r.draw

/-- GA4: the lane against the level (TPS 5.3.34, 5.3.35), a refusal answering 503;
skipped with the governor off. Lane 6's entry is `anonymousDecision`'s. -/
def pressureStep (s : MeteredState) (r : Request) : Option Refusal :=
  if s.governorOff then none
  else match pressureAdmission s.level (laneOf r.kind) with
    | .refused => some (.pressure s.level (pressureRetry s r s.level))
    | _ => none

/-- The decision for a request in lanes 2 to 4: the first refusal of GA2, GA3, GA4, GA5 and
GA6, in that order. -/
def agentDecision (s : MeteredState) (r : Request) : Decision :=
  match switchStep s r, trafficCheck s r, pressureStep s r, rateCheck s r,
    slotStep s (laneOf r.kind) with
  | some w, _, _, _, _ => .refused (.switch w (baseRetry s r))
  | none, some f, _, _, _ => .refused f
  | none, none, some f, _, _ => .refused f
  | none, none, none, some f, _ => .refused f
  | none, none, none, none, some c => .refused (.slots c (slotRetry s r))
  | none, none, none, none, none => .admitted

/-- Lane 6 (TPS 5.3.34, 5.3.40): cached pages only when OVERLOADED; else the anonymous
expensive actions under the level's slot cap, a full cap answered as the reading
`anonymousFull` says (cached pages, the default, or 503 with SLOT RETRY-AFTER). With the
governor off, admitted (GA4 skipped). -/
def anonymousDecision (s : MeteredState) (r : Request) : Decision :=
  if s.governorOff then .admitted
  else match pressureAdmission s.level .anonymous with
    | .cachedOnly => .cachedOnly
    | _ =>
      if s.tuning.anonymousSlots.at s.level ≤ s.anonymousInFlight then
        match s.readings.anonymousFull with
        | .cached => .cachedOnly
        | .slots => .refused (.slots .anonymous (slotRetry s r))
      else .admitted

/-- The admission decision: lanes 2 to 4 by `agentDecision`, lane 6 by
`anonymousDecision`, lanes 0, 1 and 5 by GA4 alone. -/
def admit (s : MeteredState) (r : Request) : Decision :=
  if agentLane (laneOf r.kind) then agentDecision s r
  else if laneOf r.kind = .anonymous then anonymousDecision s r
  else match pressureStep s r with
    | some f => .refused f
    | none => .admitted

/-- What GA5 debits: the sponsor's and the agent's buckets once the request's seats
are charged. -/
structure Charge where
  /-- The sponsor's bucket after the charge. -/
  sponsorSeats : SeatBucket
  /-- The agent's bucket after the charge. -/
  agentSeats : SeatBucket
  deriving Repr, DecidableEq

/-- The charge of an agent's request (lanes 2 to 4); `none` outside them, and with the
governor off, which skips GA5. Custos applies it to an admitted request. -/
def charge (s : MeteredState) (r : Request) : Option Charge :=
  if agentLane (laneOf r.kind) ∧ s.governorOff = false then
    some ⟨s.sponsorSeats.debit s.seatTuning.sponsorSeatRate s.now r.seats,
      s.agentSeats.debit s.seatTuning.agentSeatRate s.now r.seats⟩
  else none

/-! ## Theorems -/

/-- GA4 refuses only on pressure. -/
theorem pressureStep_pressure (s : MeteredState) (r : Request) (f : Refusal)
    (h : pressureStep s r = some f) : ∃ l ra, f = .pressure l ra := by
  unfold pressureStep at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨_, _, rfl⟩
    · cases h

/-- GA4 passes lanes 0 to 2 at every level (TPS 5.3.33, 5.3.34). -/
theorem pressureStep_lanes_zero_to_two (s : MeteredState) (r : Request)
    (hl : (laneOf r.kind).number ≤ 2) : pressureStep s r = none := by
  unfold pressureStep
  split
  · rfl
  · rw [pressureAdmission_lanes_zero_to_two _ _ hl]

/-- GA3 refuses only on the traffic stages. -/
theorem trafficCheck_traffic (s : MeteredState) (r : Request) (f : Refusal)
    (h : trafficCheck s r = some f) : ∃ st ra, f = .traffic st ra := by
  unfold trafficCheck at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · split at h
    · cases h
    · split at h
      · cases h; exact ⟨_, _, rfl⟩
      · cases h

/-- With the governor off, GA3's breaker is skipped: the traffic stages refuse only a
CONTAINED account's INQUIRE or RELEASE inside the FLOOD INTERVAL, GA2's refusal. -/
theorem trafficCheck_governorOff (s : MeteredState) (r : Request) (hg : s.governorOff = true) :
    trafficCheck s r = (floodWait s.tuning s.trafficNow r.kind s.now).map
      fun w => .traffic .contained (withJitter s.tuning w r.draw) := by
  unfold trafficCheck
  split
  · rename_i w hw; rw [hw]; rfl
  · rename_i hw; rw [hw]; simp [hg]

/-- Lanes 0 and 1 are admitted. -/
theorem admit_operator_people (s : MeteredState) (r : Request)
    (h : laneOf r.kind = .operator ∨ laneOf r.kind = .people) : admit s r = .admitted := by
  have hp : pressureStep s r = none :=
    pressureStep_lanes_zero_to_two s r (by rcases h with h | h <;> simp [h, Lane.number])
  rcases h with h | h <;> simp [admit, h, agentLane, hp]

/-- A refusal of `admit` is, for a request in lanes 2 to 4, the first refusal of GA2, GA3,
GA4, GA5 and GA6; for lane 6, its full slot cap under the reading `slots`; for lanes 0, 1
and 5, GA4's. -/
theorem admit_refused (s : MeteredState) (r : Request) (f : Refusal)
    (h : admit s r = .refused f) :
    (agentLane (laneOf r.kind) = true ∧
      ((∃ w, switchStep s r = some w ∧ f = .switch w (baseRetry s r)) ∨
        (switchStep s r = none ∧ trafficCheck s r = some f) ∨
        (switchStep s r = none ∧ trafficCheck s r = none ∧ pressureStep s r = some f) ∨
        (switchStep s r = none ∧ trafficCheck s r = none ∧ pressureStep s r = none ∧
          rateCheck s r = some f) ∨
        (switchStep s r = none ∧ trafficCheck s r = none ∧ pressureStep s r = none ∧
          rateCheck s r = none ∧
          ∃ c, slotStep s (laneOf r.kind) = some c ∧ f = .slots c (slotRetry s r)))) ∨
      (laneOf r.kind = .anonymous ∧ f = .slots .anonymous (slotRetry s r)) ∨
      (agentLane (laneOf r.kind) = false ∧ laneOf r.kind ≠ .anonymous ∧
        pressureStep s r = some f) := by
  unfold admit at h
  by_cases hag : agentLane (laneOf r.kind) = true
  · rw [ite_eq_left hag] at h
    refine .inl ⟨hag, ?_⟩
    unfold agentDecision at h
    cases h1 : switchStep s r <;> cases ht : trafficCheck s r <;> cases h0 : pressureStep s r <;>
      cases h2 : rateCheck s r <;> cases h3 : slotStep s (laneOf r.kind) <;>
      simp only [h1, ht, h0, h2, h3] at h <;> cases h <;> simp
  · rw [ite_eq_right hag] at h
    by_cases h6 : laneOf r.kind = .anonymous
    · rw [ite_eq_left h6] at h
      refine .inr (.inl ⟨h6, ?_⟩)
      unfold anonymousDecision at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · cases h; rfl
          · cases h
    · rw [ite_eq_right h6] at h
      refine .inr (.inr ⟨by simpa using hag, h6, ?_⟩)
      split at h
      · rename_i g hg; cases h; exact hg
      · cases h

/-- Lane 2 never reaches `rateStep`. -/
theorem rateCheck_finishing (s : MeteredState) (r : Request)
    (h : laneOf r.kind = .finishing) : rateCheck s r = none := by
  simp [rateCheck, h]

/-- Lane 2 is refused only by a switch (403), a slot cap (503) or the traffic stages (429:
the breaker, which 5.3.37 lets refuse HEARTBEAT, and the FLOOD INTERVAL): never on budget,
rate, pressure or share (TPS 5.3.33). -/
theorem finishing_refusals (s : MeteredState) (r : Request) (f : Refusal)
    (hl : laneOf r.kind = .finishing) (h : admit s r = .refused f) :
    (∃ w ra, f = .switch w ra) ∨ (∃ c ra, f = .slots c ra) ∨ (∃ st ra, f = .traffic st ra) := by
  have hp := pressureStep_lanes_zero_to_two s r (by simp [hl, Lane.number])
  obtain ⟨-, ⟨w, -, hw⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c, -, hc⟩⟩ |
      ⟨h6, -⟩ | ⟨hag, -⟩ := admit_refused s r f h
  · exact .inl ⟨w, _, hw⟩
  · exact .inr (.inr (trafficCheck_traffic s r f ht))
  · rw [hp] at hq; cases hq
  · rw [rateCheck_finishing s r hl] at hr; cases hr
  · exact .inr (.inl ⟨c, _, hc⟩)
  · rw [hl] at h6; cases h6
  · rw [hl] at hag; cases hag

/-- SC5: lanes 0 to 2 are never refused on budget. -/
theorem never_refused_on_budget (s : MeteredState) (r : Request) (f : Refusal)
    (hl : (laneOf r.kind).number ≤ 2) (h : admit s r = .refused f) : f.onBudget = false := by
  have hfin : laneOf r.kind = .finishing := by
    cases hk : laneOf r.kind
    case finishing => rfl
    case operator | people =>
      rw [admit_operator_people s r (by simp [hk])] at h; cases h
    all_goals (rw [hk] at hl; simp [Lane.number] at hl)
  rcases finishing_refusals s r f hfin h with ⟨w, ra, rfl⟩ | ⟨c, ra, rfl⟩ | ⟨st, ra, rfl⟩ <;> rfl

/-- Lanes 0 to 2 are never refused on pressure (TPS 5.3.33, 5.3.34): the admission's
reading of `pressureAdmission_lanes_zero_to_two`. -/
theorem pressure_lanes_zero_to_two (s : MeteredState) (r : Request) (l : PressureLevel)
    (ra : Nat) (hl : (laneOf r.kind).number ≤ 2) : admit s r ≠ .refused (.pressure l ra) := by
  intro h
  have := never_refused_on_budget s r _ hl h
  simp [Refusal.onBudget] at this

/-- STATUS, RELEASE and INQUIRE pass the switches (TPS 5.3.35, 5.3.38). -/
theorem passing_ops_pass_switches (s : MeteredState) (r : Request) (w : Switch) (ra : Nat)
    (hp : passesSwitches r.kind = true) : admit s r ≠ .refused (.switch w ra) := by
  intro h
  obtain ⟨-, ⟨w', hw', -⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c, -, hc⟩⟩ |
      ⟨-, hc⟩ | ⟨-, -, hq⟩ := admit_refused s r _ h
  · simp [switchStep, hp] at hw'
  · obtain ⟨st, ra, h'⟩ := trafficCheck_traffic s r _ ht; cases h'
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
  · rw [rateCheck] at hr
    split at hr
    · cases hr
    · unfold rateStep at hr
      split at hr
      · cases hr
      · split at hr <;> cases hr
  · cases hc
  · cases hc
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'

/-- A switch refuses a request in lanes 2 to 4 first. -/
theorem switches_refuse' (s : MeteredState) (r : Request) (w : Switch)
    (ha : agentLane (laneOf r.kind) = true) (hw : switchStep s r = some w) :
    admit s r = .refused (.switch w (baseRetry s r)) := by
  simp [admit, ha, agentDecision, hw]

/-- STATUS, RELEASE and INQUIRE pass the traffic stages at every stage (TPS 5.3.37): GA3
refuses one of them only when the account is CONTAINED and it is an INQUIRE or a RELEASE
inside the FLOOD INTERVAL since its last answer; STATUS never. -/
theorem passing_ops_pass_stages (s : MeteredState) (r : Request)
    (hp : passesSwitches r.kind = true) :
    trafficCheck s r = none ∨
      (s.trafficNow.stage = .contained ∧ (r.kind = .inquire ∨ r.kind = .releaseOp) ∧
        ∃ ra, trafficCheck s r = some (.traffic .contained ra)) := by
  unfold trafficCheck
  split
  · rename_i w hw
    refine .inr ⟨?_, ?_, _, rfl⟩
    · unfold floodWait at hw; split at hw
      · assumption
      · cases hw
    · unfold floodWait at hw
      split at hw
      · revert hw
        cases hk : r.kind <;> simp
      · cases hw
  · rw [ite_eq_left (Or.inr hp)]; exact .inl rfl

/-- STATUS is never refused by GA2 or GA3. -/
theorem status_passes (s : MeteredState) (r : Request) (hk : r.kind = .status) :
    switchStep s r = none ∧ trafficCheck s r = none := by
  have hp : passesSwitches r.kind = true := by simp [hk, passesSwitches]
  refine ⟨by simp [switchStep, hp], ?_⟩
  rcases passing_ops_pass_stages s r hp with h | ⟨-, hk', -⟩
  · exact h
  · rw [hk] at hk'; rcases hk' with h | h <;> cases h

/-- A CONTAINED account is refused every op of lanes 2 to 4 but STATUS, RELEASE and
INQUIRE, HEARTBEAT among them, so a lock it holds ends at its expiry (TPS 5.3.37): 403 with
AGENT STOP or CONTAINED, whether the governor is on or off. -/
theorem contained_refuses (s : MeteredState) (r : Request)
    (ha : agentLane (laneOf r.kind) = true) (hp : passesSwitches r.kind = false)
    (hc : s.trafficNow.stage = .contained) :
    admit s r = .refused (.switch .agentStop (baseRetry s r)) ∨
      admit s r = .refused (.switch .contained (baseRetry s r)) := by
  by_cases hs : s.agentStop = true
  · exact .inl (switches_refuse' s r _ ha (by simp [switchStep, hp, hs]))
  · exact .inr (switches_refuse' s r _ ha (by simp [switchStep, hp, hs, hc]))

/-- A refusal on the traffic stages is not on budget: `never_refused_on_budget` survives
GA3. -/
theorem traffic_not_on_budget (st : TrafficStage) (ra : Nat) :
    (Refusal.traffic st ra).onBudget = false := rfl

/-- The jitter adds at most RETRY-AFTER jitter's share of the wait. -/
theorem jitter_le (t : GovernorTuning) (base : Nat) (d : JitterDraw) :
    jitter t base d * t.retryAfterJitter.den ≤ base * t.retryAfterJitter.num := by
  unfold jitter
  rcases Nat.eq_zero_or_pos d.den with h0 | hd
  · simp [h0]
  · have hm : min d.num d.den ≤ d.den := Nat.min_le_right _ _
    have h1 : base * t.retryAfterJitter.num * min d.num d.den ≤
        base * t.retryAfterJitter.num * d.den := Nat.mul_le_mul_left _ hm
    have h2 := Nat.div_mul_le_self (base * t.retryAfterJitter.num * min d.num d.den)
      (t.retryAfterJitter.den * d.den)
    have h3 : base * t.retryAfterJitter.num * min d.num d.den /
        (t.retryAfterJitter.den * d.den) * t.retryAfterJitter.den * d.den ≤
        base * t.retryAfterJitter.num * d.den := by
      rw [Nat.mul_assoc]; exact Nat.le_trans h2 h1
    exact Nat.le_of_mul_le_mul_right h3 hd

/-- A refusal on the rate carries `rateRetry`: the request's time to conformance with its
jitter, or RETRY-AFTER's base with it when the request never conforms. -/
theorem rateCheck_retry (s : MeteredState) (r : Request) (p : Payer) (o : Nat)
    (h : rateCheck s r = some (.rate p o)) : o = rateRetry s r := by
  unfold rateCheck at h
  split at h
  · cases h
  · unfold rateStep at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h

/-- A refusal on the rate is GA5's, so it comes from `rateCheck`. -/
theorem admit_rate (s : MeteredState) (r : Request) (p : Payer) (o : Nat)
    (h : admit s r = .refused (.rate p o)) : rateCheck s r = some (.rate p o) := by
  obtain ⟨-, ⟨w, -, hw⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c, -, hc⟩⟩ |
      ⟨-, hc⟩ | ⟨-, -, hq⟩ := admit_refused s r _ h
  · cases hw
  · obtain ⟨st, ra, h'⟩ := trafficCheck_traffic s r _ ht; cases h'
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
  · exact hr
  · cases hc
  · cases hc
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'

/-- A rate refusal's Retry-After lies between the time to conformance and that time
plus RETRY-AFTER jitter's share of it (TPS 5.9.18); for a request that never conforms it
is `baseRetry`. -/
theorem rate_retryAfter_bounds (s : MeteredState) (r : Request) (p : Payer) (ra : Nat)
    (h : admit s r = .refused (.rate p ra)) :
    (∃ w, conformanceWait s r = some w ∧ w ≤ ra ∧
      (ra - w) * s.tuning.retryAfterJitter.den ≤ w * s.tuning.retryAfterJitter.num) ∨
      (conformanceWait s r = none ∧ ra = baseRetry s r) := by
  have ho := rateCheck_retry s r p _ (admit_rate s r p _ h)
  unfold rateRetry at ho
  cases hw : conformanceWait s r with
  | none => rw [hw] at ho; exact .inr ⟨rfl, ho⟩
  | some w =>
    rw [hw] at ho
    subst ho
    refine .inl ⟨w, rfl, ?_, ?_⟩
    · simp [withJitter]
    · simp only [withJitter, Nat.add_sub_cancel_left]
      exact jitter_le _ _ _

/-! ### Waiting the time to conformance -/

/-- A bucket conforms exactly when its drained level is within the room the seats need. -/
theorem SeatBucket.conforms_iff (b : SeatBucket) (rate burst now seats : Nat) :
    b.conforms rate burst now seats = true ↔ b.drained rate now ≤ SeatBucket.room burst seats := by
  unfold SeatBucket.conforms
  exact decide_eq_true_iff

/-- A request within the burst conforms exactly when the drained level leaves room for its
seats below the depth. -/
theorem SeatBucket.conforms_iff_of_le (b : SeatBucket) (rate burst now seats : Nat)
    (h : seats ≤ burst) :
    b.conforms rate burst now seats = true ↔
      b.drained rate now + seats * seatUnit ≤ burst * seatUnit := by
  rw [SeatBucket.conforms_iff]
  unfold SeatBucket.room
  have : seats * seatUnit ≤ burst * seatUnit := Nat.mul_le_mul_right _ h
  omega

/-- A request dearer than the burst conforms exactly when the bucket, drained to now, is
empty: so a falcon RETURN of any size can be returned. -/
theorem SeatBucket.conforms_dear (b : SeatBucket) (rate burst now seats : Nat)
    (h : burst < seats) :
    b.conforms rate burst now seats = true ↔ b.drained rate now = 0 := by
  rw [SeatBucket.conforms_iff]
  unfold SeatBucket.room
  have : burst * seatUnit ≤ seats * seatUnit := Nat.mul_le_mul_right _ (Nat.le_of_lt h)
  omega

/-- Waiting at least a bucket's wait, with no other charge, the request conforms. -/
theorem SeatBucket.conforms_after_wait (b : SeatBucket) (rate burst now seats w w' : Nat)
    (hw : b.wait rate burst now seats = some w) (hle : w ≤ w') :
    b.conforms rate burst (now + w') seats = true := by
  unfold SeatBucket.wait at hw
  by_cases hc : b.conforms rate burst now seats = true
  · rw [ite_eq_left hc] at hw
    cases hw
    rw [SeatBucket.conforms_iff] at hc ⊢
    unfold SeatBucket.drained at hc ⊢
    have : rate * (now - b.since) ≤ rate * (now + w' - b.since) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [ite_eq_right hc] at hw
    by_cases hr0 : rate = 0
    · rw [ite_eq_left hr0] at hw
      cases hw
    · rw [ite_eq_right hr0] at hw
      cases hw
      have hr : 0 < rate := by omega
      rw [SeatBucket.conforms_iff] at hc ⊢
      unfold SeatBucket.drained at hc ⊢
      unfold SeatBucket.ceilDiv SeatBucket.drained at hle
      generalize hR : SeatBucket.room burst seats = R at hc hle ⊢
      generalize hE : b.level - rate * (now - b.since) - R = E at hle
      generalize hq : (E + rate - 1) / rate = q at hle
      have hdm := Nat.div_add_mod (E + rate - 1) rate
      have hml := Nat.mod_lt (E + rate - 1) hr
      rw [hq] at hdm
      have hRq : E ≤ rate * q := by omega
      have hmono : rate * ((now - b.since) + q) ≤ rate * (now + w' - b.since) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add] at hmono
      omega

/-- A bucket that conforms at a rate conforms at any higher one. -/
theorem SeatBucket.conforms_rate_mono (b : SeatBucket) (rate rate' burst now seats : Nat)
    (hr : rate ≤ rate') (h : b.conforms rate burst now seats = true) :
    b.conforms rate' burst now seats = true := by
  rw [SeatBucket.conforms_iff] at h ⊢
  unfold SeatBucket.drained at h ⊢
  have : rate * (now - b.since) ≤ rate' * (now - b.since) := Nat.mul_le_mul_right _ hr
  omega

/-- A halved rate is no higher than the rate. -/
theorem halve_le (n : Nat) : halve n ≤ n := by
  simp only [halve, penalizedSeatRateFactor, ratio]; omega

/-- PENALIZED at a later time was PENALIZED before: time only ends it. -/
theorem settled_penalized_earlier (t : GovernorTuning) (x : TrafficState) (now w : Nat)
    (h : (x.settled t (now + w)).stage = .penalized) : (x.settled t now).stage = .penalized := by
  unfold TrafficState.settled at h ⊢
  by_cases hp : x.stage = .penalized ∧ x.lastEvent + t.penaltyHour.count ≤ now + w
  · rw [ite_eq_left hp] at h; cases h
  · rw [ite_eq_right hp] at h
    rw [ite_eq_right (fun hq => hp ⟨hq.1, by omega⟩)]
    exact h

/-- The seat rates in force never fall as time passes: PENALIZED's halving only ends. -/
theorem seatTuning_later (s : MeteredState) (w : Nat) :
    s.seatTuning.sponsorSeatRate ≤ ({ s with now := s.now + w } : MeteredState).seatTuning.sponsorSeatRate ∧
      s.seatTuning.agentSeatRate ≤ ({ s with now := s.now + w } : MeteredState).seatTuning.agentSeatRate := by
  unfold MeteredState.seatTuning MeteredState.trafficNow
  dsimp only
  by_cases hl : (s.traffic.settled s.tuning (s.now + w)).stage = .penalized
  · rw [ite_eq_left hl, ite_eq_left (settled_penalized_earlier _ _ _ _ hl)]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [ite_eq_right hl]
    split
    · refine ⟨?_, halve_le _⟩
      cases s.trafficReadings.payer
      · exact Nat.le_refl _
      · exact halve_le _
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Honouring a rate refusal's Retry-After, with no other charge, the request conforms
for the sponsor and the agent alike: a client that waits as told is not refused on the
rate again (TPS 5.4.13, 5.9.18). A request that never conforms is `hc`'s exception. -/
theorem retryAfter_honoured (s : MeteredState) (r : Request) (p : Payer) (ra w' : Nat)
    (h : admit s r = .refused (.rate p ra)) (hc : (conformanceWait s r).isSome = true)
    (hle : ra ≤ w') :
    sponsorConforms { s with now := s.now + w' } r = true ∧
      agentConforms { s with now := s.now + w' } r = true := by
  obtain ⟨w, hw, hwr, -⟩ | ⟨hn, -⟩ := rate_retryAfter_bounds s r p ra h
  case inr => rw [hn] at hc; cases hc
  obtain ⟨hrs, hra⟩ := seatTuning_later s w'
  unfold conformanceWait at hw
  unfold sponsorConforms agentConforms
  split at hw
  · rename_i a b ha hb
    simp only [Option.some.injEq] at hw
    subst hw
    exact ⟨SeatBucket.conforms_rate_mono _ _ _ _ _ _ hrs
        (SeatBucket.conforms_after_wait _ _ _ _ _ _ _ ha (by omega)),
      SeatBucket.conforms_rate_mono _ _ _ _ _ _ hra
        (SeatBucket.conforms_after_wait _ _ _ _ _ _ _ hb (by omega))⟩
  · cases hw

/-- A bucket's wait exists when its rate is positive, whatever the cost. -/
theorem SeatBucket.wait_isSome (b : SeatBucket) (rate burst now seats : Nat)
    (hr : 0 < rate) : (b.wait rate burst now seats).isSome = true := by
  unfold SeatBucket.wait
  split
  · rfl
  · rw [ite_eq_right (by omega)]
    rfl

/-- The halving keeps a positive rate positive. -/
theorem halve_pos (n : Nat) (h : 0 < n) : 0 < halve n := by
  simp only [halve, penalizedSeatRateFactor, ratio]; omega

/-- With positive seat rates, the rates in force are positive. -/
theorem seatTuning_pos (s : MeteredState) (hs : 0 < s.tuning.sponsorSeatRate)
    (ha : 0 < s.tuning.agentSeatRate) :
    0 < s.seatTuning.sponsorSeatRate ∧ 0 < s.seatTuning.agentSeatRate := by
  unfold MeteredState.seatTuning
  split
  · refine ⟨?_, halve_pos _ ha⟩
    cases s.trafficReadings.payer
    · exact hs
    · exact halve_pos _ hs
  · exact ⟨hs, ha⟩

/-- With positive seat rates, every request conforms in time, so every rate refusal's
Retry-After is its time to conformance with the jitter (TPS 5.9.18), a request dearer
than a burst included; `baseRetry` stands in only at a zero rate. -/
theorem rate_retryAfter_present (s : MeteredState) (r : Request) (p : Payer)
    (o : Nat) (h : admit s r = .refused (.rate p o))
    (hs : 0 < s.tuning.sponsorSeatRate) (ha : 0 < s.tuning.agentSeatRate) :
    ∃ w, conformanceWait s r = some w ∧ o = withJitter s.tuning w r.draw := by
  have ho := rateCheck_retry s r p o (admit_rate s r p o h)
  have h1 := SeatBucket.wait_isSome s.sponsorSeats s.seatTuning.sponsorSeatRate
    s.tuning.sponsorSeatBurst s.now r.seats (seatTuning_pos s hs ha).1
  have h2 := SeatBucket.wait_isSome s.agentSeats s.seatTuning.agentSeatRate
    s.tuning.agentSeatBurst s.now r.seats (seatTuning_pos s hs ha).2
  have hc : (conformanceWait s r).isSome = true := by
    unfold conformanceWait
    revert h1 h2
    cases s.sponsorSeats.wait s.seatTuning.sponsorSeatRate s.tuning.sponsorSeatBurst s.now
        r.seats <;>
      cases s.agentSeats.wait s.seatTuning.agentSeatRate s.tuning.agentSeatBurst s.now r.seats <;>
      simp
  unfold rateRetry at ho
  cases hw : conformanceWait s r with
  | none => rw [hw] at hc; cases hc
  | some w => rw [hw] at ho; exact ⟨w, rfl, ho⟩

/-- `baseRetry` lies between RETRY-AFTER's base and that base plus RETRY-AFTER jitter's share
of it (TPS 5.9.18). -/
theorem baseRetry_bounds (s : MeteredState) (r : Request) :
    s.tuning.retryAfterBase.count ≤ baseRetry s r ∧
      (baseRetry s r - s.tuning.retryAfterBase.count) * s.tuning.retryAfterJitter.den ≤
        s.tuning.retryAfterBase.count * s.tuning.retryAfterJitter.num := by
  refine ⟨by simp [baseRetry, withJitter], ?_⟩
  simp only [baseRetry, withJitter, Nat.add_sub_cancel_left]
  exact jitter_le _ _ _

/-- A switch's refusal carries `baseRetry`: RETRY-AFTER's base with the jitter. -/
theorem switch_retryAfter (s : MeteredState) (r : Request) (w : Switch) (ra : Nat)
    (h : admit s r = .refused (.switch w ra)) : ra = baseRetry s r := by
  obtain ⟨-, ⟨w', -, hw⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c, -, hc⟩⟩ |
      ⟨-, hc⟩ | ⟨-, -, hq⟩ := admit_refused s r _ h
  · cases hw; rfl
  · obtain ⟨st, ra, h'⟩ := trafficCheck_traffic s r _ ht; cases h'
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
  · rw [rateCheck] at hr
    split at hr
    · cases hr
    · unfold rateStep at hr
      split at hr
      · cases hr
      · split at hr <;> cases hr
  · cases hc
  · cases hc
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'

/-- A refusal's Retry-After in seconds, jitter included: every refusal carries one
(TPS 5.9.18). -/
def Refusal.retryAfter : Refusal → Nat
  | .switch _ ra | .rate _ ra | .slots _ ra | .pressure _ ra | .traffic _ ra => ra

/-- Every refusal of `admit` carries the Retry-After its step gives it:
`baseRetry` for a switch and for a request that never conforms, the time to conformance
for the rate, SLOT RETRY-AFTER for a slot cap, and for the pressure and the traffic stages
their own waits with the jitter (TPS 5.9.18). -/
theorem admit_refused_retryAfter (s : MeteredState) (r : Request) (f : Refusal)
    (h : admit s r = .refused f) :
    (∃ w, f = .switch w (baseRetry s r)) ∨ (∃ p, f = .rate p (rateRetry s r)) ∨
      (∃ c, f = .slots c (slotRetry s r)) ∨ (∃ l ra, f = .pressure l ra) ∨
      (∃ st ra, f = .traffic st ra) := by
  cases f with
  | switch w ra => exact .inl ⟨w, by rw [switch_retryAfter s r w ra h]⟩
  | rate p ra => exact .inr (.inl ⟨p, by rw [rateCheck_retry s r p ra (admit_rate s r p ra h)]⟩)
  | slots c ra =>
    refine .inr (.inr (.inl ⟨c, ?_⟩))
    obtain ⟨-, ⟨w, -, hw⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c', -, hc⟩⟩ |
        ⟨-, hc⟩ | ⟨-, -, hq⟩ := admit_refused s r _ h
    · cases hw
    · obtain ⟨st, ra, h'⟩ := trafficCheck_traffic s r _ ht; cases h'
    · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
    · rw [rateCheck] at hr
      split at hr
      · cases hr
      · unfold rateStep at hr
        split at hr
        · cases hr
        · split at hr <;> cases hr
    · cases hc; rfl
    · cases hc; rfl
    · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
  | pressure l ra => exact .inr (.inr (.inr (.inl ⟨l, ra, rfl⟩)))
  | traffic st ra => exact .inr (.inr (.inr (.inr ⟨st, ra, rfl⟩)))

/-! ### Admission is monotone in free capacity -/

/-- `s'` holds at least the free capacity of `s`: the same clock, tuning and switches,
buckets charged at the same times to no higher levels, and no more requests in flight. -/
structure Freer (s' s : MeteredState) : Prop where
  /-- The same clock. -/
  now_eq : s'.now = s.now
  /-- The same tuning options. -/
  tuning_eq : s'.tuning = s.tuning
  /-- The same AGENT STOP. -/
  agentStop_eq : s'.agentStop = s.agentStop
  /-- The same suspension. -/
  suspended_eq : s'.suspended = s.suspended
  /-- The governor on or off alike. -/
  governorOff_eq : s'.governorOff = s.governorOff
  /-- The agent's bucket charged at the same time ... -/
  agentSince_eq : s'.agentSeats.since = s.agentSeats.since
  /-- ... to no higher level. -/
  agentLevel_le : s'.agentSeats.level ≤ s.agentSeats.level
  /-- The sponsor's bucket charged at the same time ... -/
  sponsorSince_eq : s'.sponsorSeats.since = s.sponsorSeats.since
  /-- ... to no higher level. -/
  sponsorLevel_le : s'.sponsorSeats.level ≤ s.sponsorSeats.level
  /-- No more of the agent's requests in flight. -/
  agentInFlight_le : s'.agentInFlight ≤ s.agentInFlight
  /-- No more of the sponsor's. -/
  sponsorInFlight_le : s'.sponsorInFlight ≤ s.sponsorInFlight
  /-- No more in lane 2. -/
  finishingInFlight_le : s'.finishingInFlight ≤ s.finishingInFlight
  /-- No more in lanes 3 and 4. -/
  startingInFlight_le : s'.startingInFlight ≤ s.startingInFlight
  /-- The same level as passed or kept. -/
  pressure_eq : s'.pressure = s.pressure
  /-- The same uses. -/
  use_eq : s'.use = s.use
  /-- The same external reading. -/
  externalUntil_eq : s'.externalUntil = s.externalUntil
  /-- The same readings. -/
  readings_eq : s'.readings = s.readings
  /-- No more of lane 6's anonymous expensive actions in flight. -/
  anonymousInFlight_le : s'.anonymousInFlight ≤ s.anonymousInFlight
  /-- The same traffic record. -/
  traffic_eq : s'.traffic = s.traffic
  /-- The same readings of the traffic stages. -/
  trafficReadings_eq : s'.trafficReadings = s.trafficReadings

/-- A lower level conforms whenever a higher one charged at the same time does. -/
theorem SeatBucket.conforms_mono (b b' : SeatBucket) (rate burst now seats : Nat)
    (hs : b'.since = b.since) (hl : b'.level ≤ b.level)
    (h : b.conforms rate burst now seats = true) : b'.conforms rate burst now seats = true := by
  rw [SeatBucket.conforms_iff] at h ⊢
  unfold SeatBucket.drained at h ⊢
  rw [hs]
  omega

/-- Admission is monotone in free capacity: a request admitted at `s` is admitted at any
state with at least as much free capacity. -/
theorem admit_mono (s s' : MeteredState) (r : Request) (hf : Freer s' s)
    (h : admit s r = .admitted) : admit s' r = .admitted := by
  have htn : s'.trafficNow = s.trafficNow := by
    simp [MeteredState.trafficNow, hf.traffic_eq, hf.tuning_eq, hf.now_eq]
  have hst : s'.seatTuning = s.seatTuning := by
    simp [MeteredState.seatTuning, htn, hf.tuning_eq, hf.trafficReadings_eq]
  have hsw : switchStep s' r = switchStep s r := by
    simp [switchStep, hf.agentStop_eq, hf.suspended_eq, htn]
  have htc : trafficCheck s' r = trafficCheck s r := by
    simp [trafficCheck, htn, hf.governorOff_eq, hf.tuning_eq, hf.now_eq, hf.trafficReadings_eq]
  have hsc : sponsorConforms s r = true → sponsorConforms s' r = true := by
    intro hc
    unfold sponsorConforms at hc ⊢
    rw [hst, hf.tuning_eq, hf.now_eq]
    exact SeatBucket.conforms_mono _ _ _ _ _ _ hf.sponsorSince_eq hf.sponsorLevel_le hc
  have hac : agentConforms s r = true → agentConforms s' r = true := by
    intro hc
    unfold agentConforms at hc ⊢
    rw [hst, hf.tuning_eq, hf.now_eq]
    exact SeatBucket.conforms_mono _ _ _ _ _ _ hf.agentSince_eq hf.agentLevel_le hc
  have hrate : rateCheck s r = none → rateCheck s' r = none := by
    unfold rateCheck rateStep
    intro hn
    rw [hf.governorOff_eq]
    by_cases hfin : laneOf r.kind = .finishing ∨ s.governorOff = true
    · rw [ite_eq_left hfin]
    · rw [ite_eq_right hfin] at hn ⊢
      cases h1 : sponsorConforms s r <;> cases h2 : agentConforms s r <;>
        simp [h1, h2] at hn
      simp [hsc h1, hac h2]
  have hslot : slotStep s (laneOf r.kind) = none → slotStep s' (laneOf r.kind) = none := by
    intro hn
    have := hf.agentInFlight_le
    have := hf.sponsorInFlight_le
    have := hf.finishingInFlight_le
    have := hf.startingInFlight_le
    unfold slotStep at hn ⊢
    rw [hf.tuning_eq]
    split at hn
    · cases hn
    · split at hn
      · cases hn
      · split at hn
        · cases hn
        · split at hn
          · cases hn
          · rename_i h4
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_right (fun ⟨ha, hb⟩ => h4 ⟨ha, by omega⟩)]
  have hlevel : s'.level = s.level := by
    simp [MeteredState.level, hf.pressure_eq, hf.use_eq, hf.readings_eq, hf.tuning_eq,
      hf.externalUntil_eq, hf.now_eq]
  have hpress : pressureStep s' r = pressureStep s r := by
    simp [pressureStep, pressureRetry, hlevel, hf.governorOff_eq, hf.readings_eq,
      hf.tuning_eq]
  unfold admit at h ⊢
  by_cases hag : agentLane (laneOf r.kind) = true
  · rw [ite_eq_left hag] at h ⊢
    unfold agentDecision at h ⊢
    cases h1 : switchStep s r <;> cases ht : trafficCheck s r <;> cases h0 : pressureStep s r <;>
      cases h2 : rateCheck s r <;> cases h3 : slotStep s (laneOf r.kind) <;>
      simp only [h1, ht, h0, h2, h3] at h <;> try cases h
    rw [hsw, h1, htc, ht, hpress, h0, hrate h2, hslot h3]
  · rw [ite_eq_right hag] at h ⊢
    split
    · rename_i h6
      rw [ite_eq_left h6] at h
      unfold anonymousDecision at h ⊢
      rw [hf.governorOff_eq, hlevel, hf.tuning_eq, hf.readings_eq]
      have := hf.anonymousInFlight_le
      by_cases hg : s.governorOff = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ite_false] at h ⊢
        split at h
        · cases h
        · by_cases hc : s.tuning.anonymousSlots.at s.level ≤ s.anonymousInFlight
          · rw [ite_eq_left hc] at h; split at h <;> cases h
          · rw [ite_eq_right (by omega)]
    · rename_i h6
      rw [ite_eq_right h6] at h
      rw [hpress]
      exact h

/-! ### Admission is monotone in the level -/

/-- The admission table admits at a lower level whatever it admits at a higher one, in
every lane but lane 6 (TPS 5.3.34). -/
theorem pressureAdmission_mono (p p' : PressureLevel) (l : Lane) (hl : l ≠ .anonymous)
    (hp : p'.rank ≤ p.rank) (h : pressureAdmission p l ≠ .refused) :
    pressureAdmission p' l ≠ .refused := by
  cases p <;> cases p' <;> cases l <;> simp_all [pressureAdmission, PressureLevel.rank]

/-- A lower level never refuses what a higher admits (TPS 5.3.34): with the level passed,
and all else the same, a request outside lane 6 admitted at a level is admitted at every
level below it. -/
theorem pressure_mono (s : MeteredState) (r : Request) (p p' : PressureLevel)
    (hl : laneOf r.kind ≠ .anonymous) (hp : p'.rank ≤ p.rank)
    (h : admit { s with pressure := p, use := none } r = .admitted) :
    admit { s with pressure := p', use := none } r = .admitted := by
  have hstep : pressureStep { s with pressure := p, use := none } r = none →
      pressureStep { s with pressure := p', use := none } r = none := by
    unfold pressureStep MeteredState.level
    simp only
    intro hn
    split
    · rfl
    · rename_i hg
      rw [ite_eq_right hg] at hn
      have hn' : pressureAdmission p (laneOf r.kind) ≠ .refused := by
        intro he; rw [he] at hn; cases hn
      have := pressureAdmission_mono p p' _ hl hp hn'
      split
      · contradiction
      · rfl
  unfold admit at h ⊢
  by_cases hag : agentLane (laneOf r.kind) = true
  · rw [ite_eq_left hag] at h ⊢
    unfold agentDecision at h ⊢
    revert h
    cases h1 : switchStep { s with pressure := p, use := none } r <;>
      cases ht : trafficCheck { s with pressure := p, use := none } r <;>
      cases h0 : pressureStep { s with pressure := p, use := none } r <;>
      cases h2 : rateCheck { s with pressure := p, use := none } r <;>
      cases h3 : slotStep { s with pressure := p, use := none } (laneOf r.kind) <;>
      simp only [reduceCtorEq, false_imp_iff] <;> intro _
    have e1 : switchStep { s with pressure := p', use := none } r =
        switchStep { s with pressure := p, use := none } r := rfl
    have et : trafficCheck { s with pressure := p', use := none } r =
        trafficCheck { s with pressure := p, use := none } r := rfl
    have e2 : rateCheck { s with pressure := p', use := none } r =
        rateCheck { s with pressure := p, use := none } r := rfl
    have e3 : slotStep { s with pressure := p', use := none } (laneOf r.kind) =
        slotStep { s with pressure := p, use := none } (laneOf r.kind) := rfl
    rw [e1, h1, et, ht, hstep h0, e2, h2, e3, h3]
  · rw [ite_eq_right hag] at h ⊢
    rw [ite_eq_right hl] at h ⊢
    split at h
    · cases h
    · rename_i hn
      rw [hstep hn]

/-! ### The charge -/

/-- The charge raises each bucket, drained to now at the seat rates in force (halved under
PENALIZED), by exactly the request's seats. -/
theorem charge_exact (s : MeteredState) (r : Request) (c : Charge)
    (h : charge s r = some c) :
    c.sponsorSeats.level =
        s.sponsorSeats.drained s.seatTuning.sponsorSeatRate s.now + r.seats * seatUnit ∧
      c.agentSeats.level =
        s.agentSeats.drained s.seatTuning.agentSeatRate s.now + r.seats * seatUnit := by
  unfold charge at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- Only an agent's request is charged, and only with the governor on. -/
theorem charge_agent_lanes (s : MeteredState) (r : Request) :
    (charge s r).isSome = (agentLane (laneOf r.kind) && !s.governorOff) := by
  unfold charge
  cases ha : agentLane (laneOf r.kind) <;> cases hg : s.governorOff <;> simp

/-! ### The slots' Retry-After -/

/-- `rateCheck` refuses only on the rate. -/
theorem rateCheck_rate (s : MeteredState) (r : Request) (f : Refusal)
    (h : rateCheck s r = some f) : ∃ p o, f = .rate p o := by
  unfold rateCheck at h
  split at h
  · cases h
  · unfold rateStep at h
    split at h
    · cases h; exact ⟨_, _, rfl⟩
    · split at h
      · cases h; exact ⟨_, _, rfl⟩
      · cases h

/-- A slot refusal's Retry-After lies between SLOT RETRY-AFTER and that wait plus
RETRY-AFTER jitter's share of it: every 503 carries one (TPS 5.9.18). -/
theorem slot_retryAfter_bounds (s : MeteredState) (r : Request) (c : SlotCap) (ra : Nat)
    (h : admit s r = .refused (.slots c ra)) :
    s.tuning.slotRetryAfter.count ≤ ra ∧
      (ra - s.tuning.slotRetryAfter.count) * s.tuning.retryAfterJitter.den ≤
        s.tuning.slotRetryAfter.count * s.tuning.retryAfterJitter.num := by
  have hb : s.tuning.slotRetryAfter.count ≤ slotRetry s r ∧
      (slotRetry s r - s.tuning.slotRetryAfter.count) * s.tuning.retryAfterJitter.den ≤
        s.tuning.slotRetryAfter.count * s.tuning.retryAfterJitter.num := by
    refine ⟨by simp [slotRetry, withJitter], ?_⟩
    simp only [slotRetry, withJitter, Nat.add_sub_cancel_left]
    exact jitter_le _ _ _
  obtain ⟨-, ⟨w, -, hw⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c', -, hc⟩⟩ |
      ⟨-, hc⟩ | ⟨-, -, hq⟩ := admit_refused s r _ h
  · cases hw
  · obtain ⟨st, ra, h'⟩ := trafficCheck_traffic s r _ ht; cases h'
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'
  · obtain ⟨p, o, hpo⟩ := rateCheck_rate s r _ hr
    cases hpo
  · cases hc; exact hb
  · cases hc; exact hb
  · obtain ⟨l, ra, h'⟩ := pressureStep_pressure s r _ hq; cases h'

/-! ### GOVERNOR OFF -/

/-- With the governor off, no request is refused on budget: GA5 is skipped. -/
theorem governorOff_never_on_budget (s : MeteredState) (r : Request) (f : Refusal)
    (hg : s.governorOff = true) (h : admit s r = .refused f) : f.onBudget = false := by
  obtain ⟨-, ⟨w, -, rfl⟩ | ⟨-, ht⟩ | ⟨-, -, hq⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, -, -, c, -, rfl⟩⟩ |
      ⟨-, rfl⟩ | ⟨-, -, hq⟩ := admit_refused s r f h
  · rfl
  · obtain ⟨st, ra, rfl⟩ := trafficCheck_traffic s r f ht; rfl
  · simp [pressureStep, hg] at hq
  · simp [rateCheck, hg] at hr
  · rfl
  · rfl
  · simp [pressureStep, hg] at hq

/-- With the governor off, GA4 is skipped: no request is refused on pressure, and
lane 6 is never served cached pages only. -/
theorem governorOff_no_pressure (s : MeteredState) (r : Request) (hg : s.governorOff = true) :
    pressureStep s r = none ∧ (∀ l ra, admit s r ≠ .refused (.pressure l ra)) ∧
      admit s r ≠ .cachedOnly := by
  have hp : pressureStep s r = none := by simp [pressureStep, hg]
  refine ⟨hp, fun l ra h => ?_, fun h => ?_⟩
  · have := governorOff_never_on_budget s r _ hg h
    simp [Refusal.onBudget] at this
  · unfold admit at h
    split at h
    · unfold agentDecision at h
      rw [hp] at h
      revert h
      cases switchStep s r <;> cases trafficCheck s r <;> cases rateCheck s r <;>
        cases slotStep s (laneOf r.kind) <;> exact nofun
    · split at h
      · simp [anonymousDecision, hg] at h
      · simp [hp] at h

/-- The switches refuse whether the governor is on or off (GA2): switching it off lifts
no AGENT STOP and lets no SUSPENDED account through. -/
theorem switches_refuse (s : MeteredState) (r : Request) (w : Switch)
    (ha : agentLane (laneOf r.kind) = true) (hw : switchStep s r = some w) :
    admit s r = .refused (.switch w (baseRetry s r)) := by
  simp [admit, ha, agentDecision, hw]

/-- With the governor off, a request in lanes 2 to 4 that passes the switches (and, for a
CONTAINED account's INQUIRE or RELEASE, the FLOOD INTERVAL) is decided by the slots alone
(GA6): refused by the first cap that is full, else admitted. -/
theorem governorOff_slots (s : MeteredState) (r : Request) (hg : s.governorOff = true)
    (ha : agentLane (laneOf r.kind) = true) (hw : switchStep s r = none)
    (hf : floodWait s.tuning s.trafficNow r.kind s.now = none) :
    admit s r = match slotStep s (laneOf r.kind) with
      | some c => .refused (.slots c (slotRetry s r))
      | none => .admitted := by
  have hr : rateCheck s r = none := by simp [rateCheck, hg]
  have hp : pressureStep s r = none := by simp [pressureStep, hg]
  have ht : trafficCheck s r = none := by rw [trafficCheck_governorOff s r hg, hf]; rfl
  simp only [admit, ha, ite_true, agentDecision, hw, hp, hr, ht]
  cases slotStep s (laneOf r.kind) <;> rfl

/-- With the governor off, nothing is charged. -/
theorem governorOff_no_charge (s : MeteredState) (r : Request) (hg : s.governorOff = true) :
    charge s r = none := by
  simp [charge, hg]

/-- The queue head's acquisition is priced: 1 seat at the starting values. -/
theorem seatCost_queueHeadAcquisition (records rows : Nat) :
    seatCost {} .queueHeadAcquisition records rows = some 1 := rfl

/-- A falcon RETURN costs `4 + ceil(rows / 20)` at the seat table's starting values: 4 plus
1 per started group of 20 rows (inventory U4, the Declarer's choice). -/
theorem seatCost_falconReturn (records rows : Nat) :
    seatCost {} .falconReturn records rows = some (4 + (rows + 19) / 20) := rfl

/-- The rounding is up, for any positive rows per seat `p`: the `n` seats past the base
cover the rows (`rows ≤ p * n`), and one seat fewer would not (`p * n < rows + p`). -/
theorem seatCost_falconReturn_ceil (t : SeatTable) (records rows : Nat)
    (hp : 0 < t.falconReturnRowsPerSeat) :
    ∃ n, seatCost t .falconReturn records rows = some (t.falconReturnBase + n) ∧
      rows ≤ t.falconReturnRowsPerSeat * n ∧ t.falconReturnRowsPerSeat * n < rows + t.falconReturnRowsPerSeat := by
  refine ⟨(rows + t.falconReturnRowsPerSeat - 1) / t.falconReturnRowsPerSeat, rfl, ?_⟩
  have h := Nat.div_add_mod (rows + t.falconReturnRowsPerSeat - 1) t.falconReturnRowsPerSeat
  have hm := Nat.mod_lt (rows + t.falconReturnRowsPerSeat - 1) hp
  generalize t.falconReturnRowsPerSeat *
    ((rows + t.falconReturnRowsPerSeat - 1) / t.falconReturnRowsPerSeat) = z at *
  omega

/-- Every falcon RETURN has a cost: no row count leaves its seats open. -/
theorem seatCost_falconReturn_isSome (t : SeatTable) (records rows : Nat) :
    (seatCost t .falconReturn records rows).isSome := rfl

/-- The Provision proposal op costs 4 seats at the seat table's starting values. -/
theorem seatCost_proposeProvision (records rows : Nat) :
    seatCost {} .proposeProvision records rows = some 4 := rfl

/-! ## Wire words

Rule R1 of the collision register: each closed enumeration the admission reads or answers has
capital wire spellings, compared byte for byte, for the Calculator's family `governor`
(`Principia.Calculator.Governor`). A governed request is spelled as TPS names it where it is
one op (`STATUS`, `PUSH`, `RETURN`, `RELEASE`, `STRUCTURE_TEST`), else in the words of its Lean
name; a lane by its name in the LANE TABLE; a switch as TPS 5.3.38 names it. `Decision` and
`Refusal` carry numbers, so their words are their kinds': `DecisionWord` (admitted or
refused) and `RefusalWord` (the step that refused). -/

/-- A decision's kind: `ADMITTED`, `REFUSED` or `CACHED ONLY`. -/
inductive DecisionWord where
  /-- `ADMITTED` -/
  | admitted
  /-- `REFUSED` -/
  | refused
  /-- `CACHED ONLY` -/
  | cachedOnly
  deriving Repr, DecidableEq

/-- A refusal's kind, the step that refused: `SWITCH` (GA2, 403), `TRAFFIC` (GA3, 429),
`PRESSURE` (GA4, 503), `RATE` (GA5, 429) or `SLOTS` (GA6, 503). -/
inductive RefusalWord where
  /-- `SWITCH` -/
  | switch
  /-- `RATE` -/
  | rate
  /-- `SLOTS` -/
  | slots
  /-- `PRESSURE` -/
  | pressure
  /-- `TRAFFIC` -/
  | traffic
  deriving Repr, DecidableEq

/-- A decision's word. -/
def Decision.word : Decision → DecisionWord
  | .admitted => .admitted
  | .refused _ => .refused
  | .cachedOnly => .cachedOnly

/-- A refusal's word. -/
def Refusal.word : Refusal → RefusalWord
  | .switch .. => .switch
  | .rate .. => .rate
  | .slots .. => .slots
  | .pressure .. => .pressure
  | .traffic .. => .traffic

instance : WireWord GovernedRequest where
  members := [.declarerOrOperator, .essentialJob, .signedInUser, .structureTestButton,
    .queueHeadAcquisition, .pollByHeadOrHolder, .heartbeat, .push, .workReturn, .releaseOp,
    .inquire, .petition, .pollOther, .status, .agentCoreRead, .structureTestOp, .volunteer,
    .falconReturn, .proposeProvision, .deferrableJob, .falconJob, .bibliographyRecheckJob,
    .structureTestJob, .configurationStrataJob, .anonymousRead]
  toWire
    | .declarerOrOperator => "DECLARER OR OPERATOR"
    | .essentialJob => "ESSENTIAL JOB"
    | .signedInUser => "SIGNED IN USER"
    | .structureTestButton => "STRUCTURE TEST BUTTON"
    | .queueHeadAcquisition => "QUEUE HEAD ACQUISITION"
    | .pollByHeadOrHolder => "POLL BY HEAD OR HOLDER"
    | .heartbeat => "HEARTBEAT"
    | .push => "PUSH"
    | .workReturn => "RETURN"
    | .releaseOp => "RELEASE"
    | .inquire => "INQUIRE"
    | .petition => "PETITION"
    | .pollOther => "POLL OTHER"
    | .status => "STATUS"
    | .agentCoreRead => "AGENT CORE READ"
    | .structureTestOp => "STRUCTURE_TEST"
    | .volunteer => "VOLUNTEER"
    | .falconReturn => "FALCON RETURN"
    | .proposeProvision => "PROPOSE_PROVISION"
    | .deferrableJob => "DEFERRABLE JOB"
    | .falconJob => "FALCON JOB"
    | .bibliographyRecheckJob => "BIBLIOGRAPHY RECHECK JOB"
    | .structureTestJob => "STRUCTURE TEST JOB"
    | .configurationStrataJob => "CONFIGURATION STRATA JOB"
    | .anonymousRead => "ANONYMOUS READ"
  read_toWire a := by cases a <;> decide

/-- The Provision proposal op's wire word round-trips: `PROPOSE_PROVISION` reads as the
member and the member spells it. -/
theorem proposeProvision_wire :
    WireWord.ofWire? (α := GovernedRequest) "PROPOSE_PROVISION" = some .proposeProvision ∧
      WireWord.toWire GovernedRequest.proposeProvision = "PROPOSE_PROVISION" :=
  ⟨WireWord.ofWire?_toWire (α := GovernedRequest) .proposeProvision, rfl⟩

instance : WireWord Lane where
  members := [.operator, .people, .finishing, .starting, .optional, .background, .anonymous]
  toWire
    | .operator => "OPERATOR"
    | .people => "PEOPLE"
    | .finishing => "FINISHING"
    | .starting => "STARTING"
    | .optional => "OPTIONAL"
    | .background => "BACKGROUND"
    | .anonymous => "ANONYMOUS"
  read_toWire a := by cases a <;> decide

instance : WireWord Switch where
  members := [.agentStop, .suspended, .contained]
  toWire
    | .agentStop => "AGENT STOP"
    | .suspended => "SUSPENDED"
    | .contained => "CONTAINED"
  read_toWire a := by cases a <;> decide

instance : WireWord Payer where
  members := [.sponsor, .agent]
  toWire
    | .sponsor => "SPONSOR"
    | .agent => "AGENT"
  read_toWire a := by cases a <;> decide

instance : WireWord SlotCap where
  members := [.agent, .sponsor, .pool, .anonymous]
  toWire
    | .agent => "AGENT"
    | .sponsor => "SPONSOR"
    | .pool => "POOL"
    | .anonymous => "ANONYMOUS"
  read_toWire a := by cases a <;> decide

instance : WireWord DecisionWord where
  members := [.admitted, .refused, .cachedOnly]
  toWire
    | .admitted => "ADMITTED"
    | .refused => "REFUSED"
    | .cachedOnly => "CACHED ONLY"
  read_toWire a := by cases a <;> decide

instance : WireWord RefusalWord where
  members := [.switch, .rate, .slots, .pressure, .traffic]
  toWire
    | .switch => "SWITCH"
    | .rate => "RATE"
    | .slots => "SLOTS"
    | .pressure => "PRESSURE"
    | .traffic => "TRAFFIC"
  read_toWire a := by cases a <;> decide

instance : WireWord PressureLevel where
  members := [.clear, .busy, .strained, .overloaded]
  toWire
    | .clear => "CLEAR"
    | .busy => "BUSY"
    | .strained => "STRAINED"
    | .overloaded => "OVERLOADED"
  read_toWire a := by cases a <;> decide

instance : WireWord Descent where
  members := [.straight, .oneStep, .bands]
  toWire
    | .straight => "STRAIGHT"
    | .oneStep => "ONE STEP"
    | .bands => "BANDS"
  read_toWire a := by cases a <;> decide

instance : WireWord PressureRetry where
  members := [.slot, .pseudoLag, .base]
  toWire
    | .slot => "SLOT"
    | .pseudoLag => "PSEUDO LAG"
    | .base => "BASE"
  read_toWire a := by cases a <;> decide

instance : WireWord ThresholdRule where
  members := [.atThreshold, .aboveThreshold]
  toWire
    | .atThreshold => "AT THRESHOLD"
    | .aboveThreshold => "ABOVE THRESHOLD"
  read_toWire a := by cases a <;> decide

instance : WireWord ExternalOrder where
  members := [.raiseAfter, .raiseBefore]
  toWire
    | .raiseAfter => "RAISE AFTER"
    | .raiseBefore => "RAISE BEFORE"
  read_toWire a := by cases a <;> decide

instance : WireWord AnonymousFull where
  members := [.cached, .slots]
  toWire
    | .cached => "CACHED"
    | .slots => "SLOTS"
  read_toWire a := by cases a <;> decide

instance : WireWord TrafficEvent where
  members := [.repeatDigest, .errorStreak, .backoffViolation, .capOverrun]
  toWire
    | .repeatDigest => "REPEAT"
    | .errorStreak => "ERROR STREAK"
    | .backoffViolation => "BACKOFF VIOLATION"
    | .capOverrun => "CAP OVERRUN"
  read_toWire a := by cases a <;> decide

instance : WireWord TrafficStage where
  members := [.normal, .throttled, .penalized, .contained]
  toWire
    | .normal => "NORMAL"
    | .throttled => "THROTTLED"
    | .penalized => "PENALIZED"
    | .contained => "CONTAINED"
  read_toWire a := by cases a <;> decide

instance : WireWord Ending where
  members := [.switch, .traffic, .pressure, .rate, .slots, .shape, .failed, .succeeded]
  toWire
    | .switch => "SWITCH"
    | .traffic => "TRAFFIC"
    | .pressure => "PRESSURE"
    | .rate => "RATE"
    | .slots => "SLOTS"
    | .shape => "SHAPE"
    | .failed => "FAILED"
    | .succeeded => "SUCCEEDED"
  read_toWire a := by cases a <;> decide

instance : WireWord PenalizedPayer where
  members := [.agent, .agentAndSponsor]
  toWire
    | .agent => "AGENT"
    | .agentAndSponsor => "AGENT AND SPONSOR"
  read_toWire a := by cases a <;> decide

instance : WireWord Doubling where
  members := [.perRefusal, .perEvent]
  toWire
    | .perRefusal => "PER REFUSAL"
    | .perEvent => "PER EVENT"
  read_toWire a := by cases a <;> decide

instance : WireWord TrialSuccess where
  members := [.admitted, .passedTraffic]
  toWire
    | .admitted => "ADMITTED"
    | .passedTraffic => "PASSED TRAFFIC"
  read_toWire a := by cases a <;> decide

instance : WireWord Te2Causes where
  members := [.accountCauses, .withFleet]
  toWire
    | .accountCauses => "ACCOUNT CAUSES"
    | .withFleet => "WITH FLEET"
  read_toWire a := by cases a <;> decide

end Principia.Governor
