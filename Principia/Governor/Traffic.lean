import Principia.Parameters

/-!
# The governor's traffic stages

GA3 of version 1's admission (TPS 5.3.35, 5.3.37, 5.3.38, 5.9.18; 7.2.21, 7.2.24): the
TRAFFIC EVENTS TE1 to TE4, the TRAFFIC STAGES NORMAL, THROTTLED, PENALIZED and CONTAINED, the
traffic breaker and its trial request, the Retry-After that doubles from RETRY-AFTER's base
to its cap, and the FLOOD INTERVAL. The state is Custos's record of one AGENT account
(TPS 5.3.42, "STATE IN TABLES"); every function here is pure, Custos keeping what it
returns. The admission (`Principia.Governor.admit`) reads the state through `floodWait`,
`breakerWait` and the stage; its check is `Principia.Governor.trafficCheck`. Vectors:
the governor corpus's `traffic_step`, `traffic_stage` and traffic `admit` cases, their
expectations computed by a script of hand-written vectors, a transcription written apart
from this file.

## The events and the stages (TPS 5.3.37, 7.2.21)

Custos attests the events: TE1 REPEAT (one REQUEST DIGEST more than REPEAT LIMIT times in
10 minutes), TE2 ERROR STREAK (`afterRequest` counts the streak and says when it reaches
ERROR STREAK), TE3 BACKOFF VIOLATION (a request before the Retry-After last given the
account: `backoffViolation`), TE4 CAP OVERRUN (a request refused at GA1). `trafficStep`
takes one event:

* TE1 or TE2 throttles: the account is THROTTLED (a THROTTLED counted), the breaker opening
  for RETRY-AFTER's base; a second THROTTLED in an hour PENALIZES it.
* TE3 is counted: three in an hour PENALIZE, ten in 24 hours CONTAIN.
* PENALIZED (a PENALIZED counted when the account was below it) opens the breaker at the
  stage's Retry-After; a third PENALIZED in 24 hours CONTAINS.
* TE4 is recorded and moves no stage: the stage rules name none for it; its 400 counts
  toward TE2's streak.
* Every event is the account's last event, from which PENALIZED ends one hour on.
* A CONTAINED account's events are recorded and move nothing: CONTAINED is left only by the
  Operator (`clearContained`).

The breaker opens with a trial pending: while `now` is before its time GA3 refuses every op
but STATUS, RELEASE and INQUIRE, 429; after it the next request is the trial, decided at
its end by `afterRequest`: success closes the breaker, a THROTTLED account returning to
NORMAL; failure opens it again. One trial at a time is the agent's one slot (GA6). Time
moves PENALIZED back to NORMAL (`settled`); THROTTLED is left by a trial's success. Neither
raises a stage: only events do (`afterRequest_stage_le`, `settled_stage_le`).

## The readings (selected by the Declarer: the first of each)

Each a field of `TrafficReadings`, the selection its default:

* `payer` (a): under PENALIZED the agent's own seat rate halves (`agent`); or the agent's
  and its sponsor's (`agentAndSponsor`). Read by `Principia.Governor`.
* `doubling` (b): the Retry-After doubles at each refusal while PENALIZED, capped at
  RETRY-AFTER's cap (`perRefusal`): GA3's refusal carries the doubled value and the breaker
  runs until it; a failed trial reopens the breaker at the doubled value. Or it doubles at
  each traffic event while PENALIZED (`perEvent`), GA3's refusal carrying the time the
  breaker has left.
* `trial` (c): the trial succeeds when admitted and the operation not refused by GA5 to GA8
  (`admitted`): a GA5 or GA6 refusal or a failed op fails it, a GA4 refusal decides nothing.
  Or when it passes GA3 (`passedTraffic`).
* `te2` (d): TE2's account causes are 403 (a switch), 429 (the rate, the breaker and the
  flood interval: 5.9.18 names each an account cause), 400 (the shape) and an op's failure,
  never a 503 for pressure or slots (`accountCauses`); or those and the 503s (`withFleet`).
  Under `accountCauses` a GA6 refusal never counts toward an event
  (`slots_never_count`). A 503 neither counts nor breaks the streak; a success ends it.

## Where TPS 0.5.0 is silent: the readings of this port, reviewed with it

* A count of THROTTLED counts each TE1 or TE2 that finds the account NORMAL or THROTTLED; a
  count of PENALIZED counts each entry from below, so that the ten TE3 rule is not
  pre-empted by TE3s that come while the account is PENALIZED.
* An event that finds the account PENALIZED keeps it PENALIZED: a TE1 or TE2 opens the
  breaker at the stage's Retry-After, a TE3 below its thresholds is counted.
* PENALIZED's end closes the breaker and the account is NORMAL.
* The Operator's clear starts the account afresh: NORMAL, the counts emptied, the last
  Retry-After given kept.
* A served call's Retry-After (5.9.18: every call served above NORMAL carries one) is the
  time the breaker has left, 0 once it is past, for THROTTLED and PENALIZED, and the FLOOD
  INTERVAL for CONTAINED (5.3.37: "each answer carrying that Retry-After").
* The halved seat rate is rounded up, so that a positive rate stays positive and no
  account is refused for ever by the halving alone.
-/

namespace Principia.Governor

open Principia.Parameters

/-! ## Events, stages, readings -/

/-- A TRAFFIC EVENT (TPS 5.3.37). -/
inductive TrafficEvent where
  /-- TE1 REPEAT. -/
  | repeatDigest
  /-- TE2 ERROR STREAK. -/
  | errorStreak
  /-- TE3 BACKOFF VIOLATION. -/
  | backoffViolation
  /-- TE4 CAP OVERRUN. -/
  | capOverrun
  deriving Repr, DecidableEq

/-- A TRAFFIC STAGE (TPS 5.3.37). -/
inductive TrafficStage where
  /-- NORMAL -/
  | normal
  /-- THROTTLED: the breaker. -/
  | throttled
  /-- PENALIZED: the seat rate halved, the Retry-After doubling. -/
  | penalized
  /-- CONTAINED: every op but STATUS, RELEASE and INQUIRE refused. -/
  | contained
  deriving Repr, DecidableEq

/-- A stage's place, NORMAL 0 to CONTAINED 3. -/
def TrafficStage.rank : TrafficStage → Nat
  | .normal => 0
  | .throttled => 1
  | .penalized => 2
  | .contained => 3

/-- Whose seat rate halves under PENALIZED, reading (a). -/
inductive PenalizedPayer where
  /-- The agent's own. -/
  | agent
  /-- The agent's and its sponsor's. -/
  | agentAndSponsor
  deriving Repr, DecidableEq

/-- When the Retry-After doubles while PENALIZED, reading (b). -/
inductive Doubling where
  /-- At each refusal. -/
  | perRefusal
  /-- At each traffic event. -/
  | perEvent
  deriving Repr, DecidableEq

/-- What makes the trial request a success, reading (c). -/
inductive TrialSuccess where
  /-- Admitted, and the operation not refused by GA5 to GA8. -/
  | admitted
  /-- Passing GA3. -/
  | passedTraffic
  deriving Repr, DecidableEq

/-- TE2's causes, reading (d). -/
inductive Te2Causes where
  /-- 403, 429, 400 and an op's failure; never a 503. -/
  | accountCauses
  /-- Those and the 503s for pressure and slots. -/
  | withFleet
  deriving Repr, DecidableEq

/-- The readings in force, each defaulting to the Declarer's selection. -/
structure TrafficReadings where
  /-- (a) -/
  payer : PenalizedPayer := .agent
  /-- (b) -/
  doubling : Doubling := .perRefusal
  /-- (c) -/
  trial : TrialSuccess := .admitted
  /-- (d) -/
  te2 : Te2Causes := .accountCauses
  deriving Repr, DecidableEq

/-- How a governed request of the account ended, as Custos records it at GA9: refused at a
step (by the refusal's kind), refused at GA1 (400), or admitted and its op failed or
succeeded. -/
inductive Ending where
  /-- 403, GA2. -/
  | switch
  /-- 429, GA3: the breaker or the flood interval. -/
  | traffic
  /-- 503, GA4. -/
  | pressure
  /-- 429, GA5. -/
  | rate
  /-- 503, GA6. -/
  | slots
  /-- 400, GA1. -/
  | shape
  /-- Admitted; the op failed. -/
  | failed
  /-- Admitted; the op succeeded. -/
  | succeeded
  deriving Repr, DecidableEq

/-- A request's end: its op, how it ended and the Retry-After it was answered with, if any,
jitter included. -/
structure RequestEnd where
  /-- The op. -/
  kind : GovernedRequest
  /-- How it ended. -/
  ending : Ending
  /-- The Retry-After sent with the answer. -/
  retryAfter : Option Nat := none
  deriving Repr, DecidableEq

/-- The traffic record of one AGENT account. The default is a NORMAL account with no
history: a state written before GA3 is decided as it was. -/
structure TrafficState where
  /-- The stage, as last stepped (`settled` gives the one in force). -/
  stage : TrafficStage := .normal
  /-- The breaker is open while `now` is before this. -/
  breakerUntil : Nat := 0
  /-- The breaker awaits its trial: set when it opens, cleared by a successful trial. -/
  trialPending : Bool := false
  /-- The stage's current Retry-After, in seconds, before the jitter. -/
  retryAfter : Nat := 0
  /-- The last Retry-After given the account runs until this: a request before it is a TE3. -/
  backoffUntil : Nat := 0
  /-- Consecutive ends counting toward TE2. -/
  streak : Nat := 0
  /-- The times of the TE3s of the last 24 hours. -/
  te3Times : List Nat := []
  /-- The times the account was THROTTLED in the last hour. -/
  throttledTimes : List Nat := []
  /-- The times the account was PENALIZED in the last 24 hours. -/
  penalizedTimes : List Nat := []
  /-- The last event's time: PENALIZED ends PENALTY HOUR after it. -/
  lastEvent : Nat := 0
  /-- A CONTAINED account's last answered INQUIRE. -/
  floodInquire : Option Nat := none
  /-- A CONTAINED account's last answered RELEASE. -/
  floodRelease : Option Nat := none
  deriving Repr, DecidableEq

/-! ## Time -/

/-- The times of `xs` within the window of `w` seconds that ends at `now`. -/
def within (w now : Nat) (xs : List Nat) : List Nat :=
  xs.filter fun x => decide (now < x + w)

/-- A Retry-After capped at RETRY-AFTER's cap. -/
def capped (t : GovernorTuning) (x : Nat) : Nat := min x t.retryAfterCap.count

/-- The state in force at `now`: PENALIZED ends PENALTY HOUR after the last event, the
account NORMAL and its breaker closed. -/
def TrafficState.settled (t : GovernorTuning) (s : TrafficState) (now : Nat) : TrafficState :=
  if s.stage = .penalized ∧ s.lastEvent + t.penaltyHour.count ≤ now then
    { s with stage := .normal, breakerUntil := 0, trialPending := false, retryAfter := 0 }
  else s

/-! ## The event step -/

/-- The breaker opens for `ra` seconds, its trial pending. -/
def TrafficState.openBreaker (s : TrafficState) (now ra : Nat) : TrafficState :=
  { s with breakerUntil := now + ra, trialPending := true, retryAfter := ra }

/-- The breaker opens again for the stage's Retry-After, which then doubles, capped: a
PENALIZED account's refusal under `perRefusal`. -/
def TrafficState.reopen (t : GovernorTuning) (s : TrafficState) (now : Nat) : TrafficState :=
  { s.openBreaker now s.retryAfter with retryAfter := capped t (2 * s.retryAfter) }

/-- CONTAINED: the breaker no longer read. -/
def TrafficState.contain (s : TrafficState) : TrafficState :=
  { s with stage := .contained, breakerUntil := 0, trialPending := false }

/-- PENALIZED: entered from below, counted, and a third in 24 hours CONTAINS; the breaker
opens at RETRY-AFTER's base. Already PENALIZED, the account stays so. -/
def TrafficState.penalize (t : GovernorTuning) (s : TrafficState) (now : Nat) : TrafficState :=
  if s.stage = .penalized then s
  else
    let pe := now :: within containedWindow.count now s.penalizedTimes
    let s := { s with penalizedTimes := pe }
    if containedPenalizedCount ≤ pe.length then s.contain
    else ({ s with stage := .penalized } : TrafficState).openBreaker now (capped t t.retryAfterBase.count)

/-- TE1 or TE2: from NORMAL or THROTTLED, a THROTTLED counted, a second in an hour
PENALIZING, else the breaker open at RETRY-AFTER's base; PENALIZED, the breaker open at the
stage's Retry-After. -/
def TrafficState.throttle (t : GovernorTuning) (s : TrafficState) (now : Nat) : TrafficState :=
  if s.stage = .penalized then s.openBreaker now s.retryAfter
  else
    let th := now :: within penalizedWindow.count now s.throttledTimes
    let s := { s with throttledTimes := th }
    if penalizedThrottledCount ≤ th.length then s.penalize t now
    else ({ s with stage := .throttled } : TrafficState).openBreaker now
      (capped t t.retryAfterBase.count)

/-- TE3: counted; ten in 24 hours CONTAIN, three in an hour PENALIZE. -/
def TrafficState.backoff (t : GovernorTuning) (s : TrafficState) (now : Nat) : TrafficState :=
  let te := now :: within containedWindow.count now s.te3Times
  let s := { s with te3Times := te }
  if containedTe3Count ≤ te.length then s.contain
  else if penalizedTe3Count ≤ (within penalizedWindow.count now te).length then s.penalize t now
  else s

/-- One traffic event at `now` (TPS 5.3.37): the state in force, the event its last, the
Retry-After doubled first under `perEvent` while PENALIZED; a CONTAINED account's event
moves nothing. -/
def trafficStep (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (e : TrafficEvent) (now : Nat) : TrafficState :=
  let s := { s.settled t now with lastEvent := now }
  if s.stage = .contained then s
  else
    let s := if rd.doubling = .perEvent ∧ s.stage = .penalized then
      { s with retryAfter := capped t (2 * s.retryAfter) } else s
    match e with
    | .repeatDigest | .errorStreak => s.throttle t now
    | .backoffViolation => s.backoff t now
    | .capOverrun => s

/-- The Operator's clear of CONTAINED (TPS 5.3.37: "cleared by H-OP on the control panel"):
NORMAL, the counts emptied, the last Retry-After given kept. -/
def clearContained (s : TrafficState) : TrafficState :=
  { backoffUntil := s.backoffUntil }

/-! ## What GA3 reads -/

/-- A request before the last Retry-After given is a TE3 (TPS 5.3.37). -/
def backoffViolation (s : TrafficState) (now : Nat) : Bool :=
  decide (now < s.backoffUntil)

/-- A CONTAINED account's INQUIRE or RELEASE before the FLOOD INTERVAL since its last answer:
the seconds left; `none` when it is answered (TPS 5.3.37). -/
def floodWait (t : GovernorTuning) (s : TrafficState) (k : GovernedRequest) (now : Nat) :
    Option Nat :=
  if s.stage = .contained then
    let last := match k with
      | .inquire => s.floodInquire
      | .releaseOp => s.floodRelease
      | _ => none
    match last with
    | some a => if now < a + t.floodInterval.count then some (a + t.floodInterval.count - now)
      else none
    | none => none
  else none

/-- The breaker open at `now`, THROTTLED or PENALIZED: the Retry-After GA3's 429 carries
before the jitter; `none` when it is closed or past. Under `perRefusal` a PENALIZED
account's refusal carries the stage's Retry-After, which then doubles (`breakerStep`), so
that the refusals carry 60, 120, 240 seconds and on to the cap; else the time the breaker
has left. -/
def breakerWait (rd : TrafficReadings) (s : TrafficState) (now : Nat) : Option Nat :=
  if (s.stage = .throttled ∨ s.stage = .penalized) ∧ s.trialPending ∧ now < s.breakerUntil then
    if s.stage = .penalized ∧ rd.doubling = .perRefusal then some s.retryAfter
    else some (s.breakerUntil - now)
  else none

/-- The Retry-After a served call carries before the jitter (TPS 5.9.18): THROTTLED and
PENALIZED, the time the breaker has left; CONTAINED, the FLOOD INTERVAL; NORMAL, none. -/
def servedRetry (t : GovernorTuning) (s : TrafficState) (now : Nat) : Option Nat :=
  match s.stage with
  | .normal => none
  | .throttled | .penalized => some (s.breakerUntil - now)
  | .contained => some t.floodInterval.count

/-! ## The end of a request -/

/-- The end counts toward TE2, by reading (d). -/
def countsForStreak (c : Te2Causes) : Ending → Bool
  | .switch | .traffic | .rate | .shape | .failed => true
  | .pressure | .slots => c == .withFleet
  | .succeeded => false

/-- The trial's result, by reading (c): `some true` a success, `some false` a failure,
`none` when the end decides nothing (it never reached GA3, or GA4 refused it). -/
def trialResult (c : TrialSuccess) : Ending → Option Bool
  | .switch | .traffic | .shape => none
  | .pressure => match c with
    | .admitted => none
    | .passedTraffic => some true
  | .rate | .slots | .failed => match c with
    | .admitted => some false
    | .passedTraffic => some true
  | .succeeded => some true

/-- `afterRequest`'s answer: the state, and TE2 when the streak reaches ERROR STREAK, the
event Custos then steps with `trafficStep`. -/
structure AfterRequest where
  /-- The state. -/
  traffic : TrafficState
  /-- TE2 raised. -/
  raisesStreak : Bool
  deriving Repr, DecidableEq

/-- The streak after an end: counted, ended by a success, else kept; reaching ERROR STREAK,
it raises TE2 and starts again. -/
def streakStep (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState) (e : Ending) :
    TrafficState × Bool :=
  if countsForStreak rd.te2 e then
    if t.errorStreak ≤ s.streak + 1 then ({ s with streak := 0 }, true)
    else ({ s with streak := s.streak + 1 }, false)
  else if e = .succeeded then ({ s with streak := 0 }, false)
  else (s, false)

/-- The breaker after an end: GA3's refusal of a PENALIZED account under `perRefusal`
opens the breaker again for the Retry-After it carried, which then doubles; the trial's
success closes the breaker (THROTTLED returning to NORMAL); its failure opens it again, for a
PENALIZED account as its refusal does under `perRefusal` and for the stage's Retry-After
under `perEvent`, for a THROTTLED one for RETRY-AFTER's base. -/
def breakerStep (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState) (e : Ending)
    (now : Nat) : TrafficState :=
  if s.stage = .throttled ∨ s.stage = .penalized then
    if s.trialPending ∧ now < s.breakerUntil then
      if e = .traffic ∧ s.stage = .penalized ∧ rd.doubling = .perRefusal then s.reopen t now
      else s
    else if s.trialPending then
      match trialResult rd.trial e with
      | some true =>
        { s with trialPending := false, breakerUntil := 0,
                 stage := if s.stage = .throttled then .normal else s.stage }
      | some false =>
        if s.stage = .penalized then
          if rd.doubling = .perRefusal then s.reopen t now else s.openBreaker now s.retryAfter
        else s.openBreaker now (capped t t.retryAfterBase.count)
      | none => s
    else s
  else s

/-- A CONTAINED account's INQUIRE or RELEASE answered: its time recorded for the FLOOD
INTERVAL. -/
def floodStep (s : TrafficState) (q : RequestEnd) (now : Nat) : TrafficState :=
  if s.stage = .contained ∧ (q.ending = .succeeded ∨ q.ending = .failed) then
    match q.kind with
    | .inquire => { s with floodInquire := some now }
    | .releaseOp => { s with floodRelease := some now }
    | _ => s
  else s

/-- The Retry-After an answer carried recorded: a request before it is a TE3. -/
def recordRetry (s : TrafficState) (q : RequestEnd) (now : Nat) : TrafficState :=
  match q.retryAfter with
  | some ra => { s with backoffUntil := now + ra }
  | none => s

/-- The end of one of the account's governed requests at `now` (GA9, "the traffic counters
updated"): the state in force, the streak, the breaker, the flood interval, and the
Retry-After given recorded, so that a request before it is a TE3. -/
def afterRequest (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (q : RequestEnd) (now : Nat) : AfterRequest :=
  let st := streakStep t rd (s.settled t now) q.ending
  ⟨recordRetry (floodStep (breakerStep t rd st.1 q.ending now) q now) q now, st.2⟩

/-! ## Theorems -/

/-- Time never raises a stage, and keeps CONTAINED. -/
theorem settled_stage (t : GovernorTuning) (s : TrafficState) (now : Nat) :
    (s.settled t now).stage.rank ≤ s.stage.rank ∧
      ((s.settled t now).stage = .contained ↔ s.stage = .contained) := by
  unfold TrafficState.settled
  split
  · rename_i h; rw [h.1]; simp [TrafficStage.rank]
  · exact ⟨Nat.le_refl _, Iff.rfl⟩

theorem settled_stage_le (t : GovernorTuning) (s : TrafficState) (now : Nat) :
    (s.settled t now).stage.rank ≤ s.stage.rank := (settled_stage t s now).1

theorem streakStep_stage (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (e : Ending) : (streakStep t rd s e).1.stage = s.stage := by
  unfold streakStep; split
  · split <;> rfl
  · split <;> rfl

theorem breakerStep_stage (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (e : Ending) (now : Nat) :
    (breakerStep t rd s e now).stage.rank ≤ s.stage.rank ∧
      ((breakerStep t rd s e now).stage = .contained ↔ s.stage = .contained) := by
  unfold breakerStep
  split
  · rename_i hs
    split
    · split <;> simp [TrafficState.reopen, TrafficState.openBreaker]
    · split
      · split
        · dsimp only; split
          · rename_i h; rw [h]; simp [TrafficStage.rank]
          · simp
        · split
          · split <;> simp [TrafficState.reopen, TrafficState.openBreaker]
          · simp [TrafficState.openBreaker]
        · simp
      · simp
  · simp

theorem floodStep_stage (s : TrafficState) (q : RequestEnd) (now : Nat) :
    (floodStep s q now).stage = s.stage := by
  unfold floodStep; split
  · split <;> rfl
  · rfl

/-- The end of a request never raises a stage and never enters or leaves CONTAINED: only a
traffic event raises a stage (TPS 5.3.37). -/
theorem afterRequest_stage (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (q : RequestEnd) (now : Nat) :
    (afterRequest t rd s q now).traffic.stage.rank ≤ (s.settled t now).stage.rank ∧
      ((afterRequest t rd s q now).traffic.stage = .contained ↔ s.stage = .contained) := by
  have h1 := streakStep_stage t rd (s.settled t now) q.ending
  obtain ⟨h2, h3⟩ := breakerStep_stage t rd (streakStep t rd (s.settled t now) q.ending).1
    q.ending now
  have h4 := floodStep_stage (breakerStep t rd (streakStep t rd (s.settled t now) q.ending).1
    q.ending now) q now
  have h5 := (settled_stage t s now).2
  have h6 : ∀ x : TrafficState, (recordRetry x q now).stage = x.stage := by
    intro x; unfold recordRetry; split <;> rfl
  rw [h1] at h2 h3
  simp only [afterRequest, h6, h4]
  exact ⟨h2, h3.trans h5⟩

theorem afterRequest_stage_le (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (q : RequestEnd) (now : Nat) :
    (afterRequest t rd s q now).traffic.stage.rank ≤ (s.settled t now).stage.rank :=
  (afterRequest_stage t rd s q now).1

/-- CONTAINED is entered only by a traffic event and left only by the Operator's clear:
time and the end of a request keep a CONTAINED account CONTAINED and never make one; an
event keeps one CONTAINED. -/
theorem contained_only_by_events (t : GovernorTuning) (rd : TrafficReadings)
    (s : TrafficState) (now : Nat) :
    ((s.settled t now).stage = .contained ↔ s.stage = .contained) ∧
      (∀ q, (afterRequest t rd s q now).traffic.stage = .contained ↔ s.stage = .contained) ∧
      (∀ e, s.stage = .contained → (trafficStep t rd s e now).stage = .contained) := by
  refine ⟨(settled_stage t s now).2, fun q => (afterRequest_stage t rd s q now).2,
    fun e hc => ?_⟩
  have : (s.settled t now).stage = .contained := (settled_stage t s now).2.mpr hc
  unfold trafficStep
  simp [this]

/-! ### The Retry-After stays within its cap -/

theorem capped_le (t : GovernorTuning) (x : Nat) : capped t x ≤ t.retryAfterCap.count :=
  Nat.min_le_right _ _

theorem settled_retry (t : GovernorTuning) (s : TrafficState) (now : Nat)
    (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (s.settled t now).retryAfter ≤ t.retryAfterCap.count := by
  unfold TrafficState.settled; split
  · simp
  · exact h

theorem penalize_retry (t : GovernorTuning) (s : TrafficState) (now : Nat)
    (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (s.penalize t now).retryAfter ≤ t.retryAfterCap.count := by
  unfold TrafficState.penalize; split
  · exact h
  · dsimp only; split
    · exact h
    · exact capped_le _ _

theorem throttle_retry (t : GovernorTuning) (s : TrafficState) (now : Nat)
    (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (s.throttle t now).retryAfter ≤ t.retryAfterCap.count := by
  unfold TrafficState.throttle; split
  · exact h
  · dsimp only; split
    · exact penalize_retry t _ now h
    · exact capped_le _ _

theorem backoff_retry (t : GovernorTuning) (s : TrafficState) (now : Nat)
    (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (s.backoff t now).retryAfter ≤ t.retryAfterCap.count := by
  unfold TrafficState.backoff; dsimp only; split
  · exact h
  · split
    · exact penalize_retry t _ now h
    · exact h

/-- The stage's Retry-After never passes RETRY-AFTER's cap (TPS 5.3.37: "doubling from 60 s
to 3,600 s"), whatever the event. -/
theorem retryAfter_le_cap (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (e : TrafficEvent) (now : Nat) (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (trafficStep t rd s e now).retryAfter ≤ t.retryAfterCap.count := by
  have hs := settled_retry t s now h
  unfold trafficStep
  dsimp only
  split
  · exact hs
  · generalize hu : (if rd.doubling = .perEvent ∧ ({ s.settled t now with lastEvent := now } :
        TrafficState).stage = .penalized then
        ({ ({ s.settled t now with lastEvent := now } : TrafficState) with
          retryAfter := capped t (2 * ({ s.settled t now with lastEvent := now } :
            TrafficState).retryAfter) } : TrafficState)
        else { s.settled t now with lastEvent := now }) = u
    have hu' : u.retryAfter ≤ t.retryAfterCap.count := by
      rw [← hu]; split
      · exact capped_le _ _
      · exact hs
    cases e
    · exact throttle_retry t u now hu'
    · exact throttle_retry t u now hu'
    · exact backoff_retry t u now hu'
    · exact hu'

theorem reopen_retry (t : GovernorTuning) (s : TrafficState) (now : Nat) :
    (s.reopen t now).retryAfter ≤ t.retryAfterCap.count := capped_le _ _

theorem breakerStep_retry (t : GovernorTuning) (rd : TrafficReadings) (u : TrafficState)
    (e : Ending) (now : Nat) (h1 : u.retryAfter ≤ t.retryAfterCap.count) :
    (breakerStep t rd u e now).retryAfter ≤ t.retryAfterCap.count := by
  unfold breakerStep
  split
  · split
    · split
      · exact reopen_retry _ _ _
      · exact h1
    · split
      · split
        · exact h1
        · split
          · split
            · exact reopen_retry _ _ _
            · exact h1
          · exact capped_le _ _
        · exact h1
      · exact h1
  · exact h1

/-- The end of a request keeps the stage's Retry-After within its cap. -/
theorem afterRequest_retryAfter_le_cap (t : GovernorTuning) (rd : TrafficReadings)
    (s : TrafficState) (q : RequestEnd) (now : Nat) (h : s.retryAfter ≤ t.retryAfterCap.count) :
    (afterRequest t rd s q now).traffic.retryAfter ≤ t.retryAfterCap.count := by
  have hs := settled_retry t s now h
  have h1 : (streakStep t rd (s.settled t now) q.ending).1.retryAfter ≤ t.retryAfterCap.count := by
    unfold streakStep; split
    · split <;> exact hs
    · split <;> exact hs
  have h2 := breakerStep_retry t rd _ q.ending now h1
  have h3 : ∀ x : TrafficState, (recordRetry (floodStep x q now) q now).retryAfter = x.retryAfter := by
    intro x; unfold recordRetry floodStep
    split <;> split <;> (try split) <;> rfl
  simp only [afterRequest, h3]
  exact h2

/-! ### A client that waits as told -/

/-- A client that waits the Retry-After it was given never raises TE3 (TPS 5.3.37, 5.4.13):
after a request answered with a Retry-After of `ra` seconds at `now`, a request at or after
`now + ra` is no BACKOFF VIOLATION. -/
theorem honoured_retry_not_te3 (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (q : RequestEnd) (now ra now' : Nat) (hq : q.retryAfter = some ra) (hw : now + ra ≤ now') :
    backoffViolation (afterRequest t rd s q now).traffic now' = false := by
  simp [afterRequest, backoffViolation, recordRetry, hq]
  omega

/-- The rule that slots never count, kept: under the selected TE2 causes a GA6 refusal (503, slots) never counts toward
an event: the streak is kept and no TE2 is raised. -/
theorem slots_never_count (t : GovernorTuning) (rd : TrafficReadings) (s : TrafficState)
    (h : rd.te2 = .accountCauses) :
    streakStep t rd s .slots = (s, false) ∧ streakStep t rd s .pressure = (s, false) := by
  simp [streakStep, countsForStreak, h]

end Principia.Governor
