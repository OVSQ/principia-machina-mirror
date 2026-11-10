import Principia
import Lean.Data.Json

/-!
The runner of `vectors/governor.json` against `Principia.Governor`. Version 1 has no
corpus and no code for the governor; the expectations were computed by
`scripts/governor_hand_vectors.py`, a transcription of TPS 0.5.0's rules written apart
from the Lean file (`--check` compares). `Lean.Json` reads inputs only (collision
register R5).

Case shapes (a kind is a `GovernedRequest` constructor's Lean name):
* `{"function": "lane", "kind", "expected"}`: `laneOf`, as the lane's number.
* `{"function": "seat_cost", "name", "kind", "records", "rows", "seat_table"?,
  "expected"}`: `seatCost`, a number, or `null` for `none`.
* `{"function": "jitter", "name", "base", "draw", "share"?, "expected"}`: `jitter`, the
  seconds added; `share` overrides RETRY-AFTER jitter.
* `{"function": "admit", "name", "state", "request", "expected"}`: `admit` and `charge`.
  The expectation is `{"decision": "admitted", "charge"}` or `{"decision": "refused",
  "status", "refusal", ..., "charge"}`, the refusal `switch` with its `reason` and
  `retry_after`, `rate` with its `payer` and `retry_after`, or `slots` with its `cap` and
  `retry_after`, every `retry_after` a number; a request's `draw` may be absent;
  `charge` is `null` outside lanes 2 to 4, else `{"sponsor": [level, since], "agent":
  [level, since]}`. GA4's refusal is `pressure` with its `level` (a level's Lean name) and
  `retry_after`; lane 6 served cached pages only is `{"decision": "cachedOnly", "charge":
  null}`. A state's `pressure` and the tuning's readings are wire words, as `pcalc` reads
  them.
* `{"function": "level", "name", "use", "prev", "external_until", "now", "tuning"?,
  "expected"}`: `levelStep` over `pressureRatio`, the expectation `{"kept", "level",
  "ratio"}`, the levels as wire words and the ratio `[num, den]` in lowest terms.
* `{"function": "traffic_step", "name", "traffic", "now", "event" | "end", "tuning"?,
  "expected"}`: `trafficStep` for an event's wire word, or `afterRequest` for an end
  `{"kind", "ending", "retry_after"}`; the expectation `{"raises", "traffic"}`, the record
  after. A traffic record's stage and an end's ending are wire words; its times numbers.
  GA3's refusal in an `admit` expectation is `traffic` with its `stage` (a stage's Lean
  name) and `retry_after`; a state may carry `traffic`, a record.
* `{"function": "traffic_stage", "name", "traffic", "now", "kind", "tuning"?, "expected"}`:
  what GA3 reads of the record at `now`: `{"stage", "breaker", "flood",
  "served_retry_after", "backoff_violation"}`, the waits numbers or `null`.

Every case is read into typed values and compared as such. A key the runner does not
know is a defect of the corpus. The runner fails a corpus that leaves a kind without a
lane case. Before the comparison of each `admit` case, the case's expectation is
mutated once (the decision's word, a Retry-After, a cap or a charge's level) and the
mutated text must be refused, so a field the reader skipped cannot pass.
-/

open Lean
open Principia.Parameters
open Principia.Governor

namespace Tests.Governor

/-- Passing and failing checks. -/
structure Count where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr with what was checked. -/
def Count.check (t : Count) (ok : Bool) (what : String) : IO Count := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL governor: {what}"
    return { t with fail := t.fail + 1 }

/-- A defect of the corpus. -/
def defect (what : String) : Except String α := throw s!"governor: {what}"

/-- The object's keys. -/
def keys (j : Json) : Except String (List String) := do
  let o ← j.getObj?
  pure (o.toList.map Prod.fst)

/-- Every key of `j` is one of `allowed`. -/
def onlyKeys (j : Json) (allowed : List String) (at_ : String) : Except String Unit := do
  for k in ← keys j do
    unless allowed.contains k do defect s!"{at_}: unknown key {k}"

def nat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
def bool (j : Json) (k : String) : Except String Bool := j.getObjValAs? Bool k
def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k

/-- A pair of whole numbers `[a, b]`. -/
def pair (j : Json) : Except String (Nat × Nat) := do
  match ← j.getArr? with
  | #[a, b] => pure (← a.getNat?, ← b.getNat?)
  | _ => defect s!"not a pair: {j.compress}"

/-- An optional field: absent is `none`. -/
def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

/-- Every governed request's Lean name. -/
def kindName : GovernedRequest → String
  | .declarerOrOperator => "declarerOrOperator"
  | .essentialJob => "essentialJob"
  | .signedInUser => "signedInUser"
  | .structureTestButton => "structureTestButton"
  | .queueHeadAcquisition => "queueHeadAcquisition"
  | .pollByHeadOrHolder => "pollByHeadOrHolder"
  | .heartbeat => "heartbeat"
  | .push => "push"
  | .workReturn => "workReturn"
  | .releaseOp => "releaseOp"
  | .inquire => "inquire"
  | .petition => "petition"
  | .pollOther => "pollOther"
  | .status => "status"
  | .agentCoreRead => "agentCoreRead"
  | .structureTestOp => "structureTestOp"
  | .volunteer => "volunteer"
  | .falconReturn => "falconReturn"
  | .proposeProvision => "proposeProvision"
  | .deferrableJob => "deferrableJob"
  | .falconJob => "falconJob"
  | .bibliographyRecheckJob => "bibliographyRecheckJob"
  | .structureTestJob => "structureTestJob"
  | .configurationStrataJob => "configurationStrataJob"
  | .anonymousRead => "anonymousRead"

/-- Every governed request. -/
def allKinds : List GovernedRequest :=
  [.declarerOrOperator, .essentialJob, .signedInUser, .structureTestButton,
    .queueHeadAcquisition, .pollByHeadOrHolder, .heartbeat, .push, .workReturn,
    .releaseOp, .inquire, .petition, .pollOther, .status, .agentCoreRead,
    .structureTestOp, .volunteer, .falconReturn, .proposeProvision, .deferrableJob, .falconJob,
    .bibliographyRecheckJob, .structureTestJob, .configurationStrataJob, .anonymousRead]

def kind (j : Json) : Except String GovernedRequest := do
  let s ← str j "kind"
  match allKinds.find? (kindName · == s) with
  | some k => pure k
  | none => defect s!"unknown kind {s}"

/-- A `Ratio` from `[num, den]`, `den` positive. -/
def ratioOf (j : Json) : Except String Ratio := do
  let (n, d) ← pair j
  if h : 0 < d then pure ⟨n, d, h⟩ else defect "a share with denominator 0"

/-- The tuning's keys. -/
def tuningKeys : List String := ["agent_seat_rate", "agent_seat_burst", "sponsor_seat_rate",
  "sponsor_seat_burst", "slots_per_agent", "slots_per_sponsor", "retry_after_jitter",
  "slot_retry_after", "retry_after_base", "kappa_m", "anonymous_slots", "pseudo_lag",
  "descent", "pressure_retry_after", "threshold_rule", "external_order", "anonymous_full",
  "retry_after_cap", "penalty_hour", "flood_interval", "error_streak", "penalized_payer",
  "doubling", "trial_success", "te2_causes"]

/-- Four whole numbers, CLEAR to OVERLOADED. -/
def byLevel (j : Json) : Except String (ByLevel Nat) := do
  match ← j.getArr? with
  | #[a, b, c, d] => pure ⟨← a.getNat?, ← b.getNat?, ← c.getNat?, ← d.getNat?⟩
  | _ => defect s!"not four counts: {j.compress}"

/-- A wire word of `α` at the key `k`, its default when absent. -/
def wordAt (α : Type) [Principia.WireWord α] (j : Json) (k : String) (d : α) : Except String α := do
  match opt j k with
  | none => pure d
  | some _ =>
    let w ← str j k
    match (Principia.WireWord.ofWire? w : Option α) with
    | some a => pure a
    | none => defect s!"{k}: not a word: {w}"

/-- The pressure levels' readings in force: each the Declarer's selection, as the case overrides it. -/
def readingsOf (st : Json) : Except String PressureReadings := do
  let some t := opt st "tuning" | pure {}
  let g : PressureReadings := {}
  pure {
    descent := ← wordAt Descent t "descent" g.descent
    retry := ← wordAt PressureRetry t "pressure_retry_after" g.retry
    threshold := ← wordAt ThresholdRule t "threshold_rule" g.threshold
    external := ← wordAt ExternalOrder t "external_order" g.external
    anonymousFull := ← wordAt AnonymousFull t "anonymous_full" g.anonymousFull }

/-- The readings of the traffic stages in force, as the case overrides them. -/
def trafficReadingsOf (st : Json) : Except String TrafficReadings := do
  let some t := opt st "tuning" | pure {}
  let g : TrafficReadings := {}
  pure {
    payer := ← wordAt PenalizedPayer t "penalized_payer" g.payer
    doubling := ← wordAt Doubling t "doubling" g.doubling
    trial := ← wordAt TrialSuccess t "trial_success" g.trial
    te2 := ← wordAt Te2Causes t "te2_causes" g.te2 }

/-- The tuning options in force: the starting values, as the case overrides them. -/
def tuningOf (st : Json) : Except String GovernorTuning := do
  let some t := opt st "tuning" | pure {}
  onlyKeys t tuningKeys "tuning"
  let g : GovernorTuning := {}
  let n (k : String) (d : Nat) : Except String Nat :=
    match opt t k with
    | some _ => nat t k
    | none => pure d
  pure { g with
    retryAfterBase := ⟨← n "retry_after_base" g.retryAfterBase.count⟩
    retryAfterCap := ⟨← n "retry_after_cap" g.retryAfterCap.count⟩
    penaltyHour := ⟨← n "penalty_hour" g.penaltyHour.count⟩
    floodInterval := ⟨← n "flood_interval" g.floodInterval.count⟩
    errorStreak := ← n "error_streak" g.errorStreak
    kappaM := ← match opt t "kappa_m" with
      | some r => ratioOf r
      | none => pure g.kappaM
    anonymousSlots := ← match opt t "anonymous_slots" with
      | some x => byLevel x
      | none => pure g.anonymousSlots
    pseudoLag := ← match opt t "pseudo_lag" with
      | some x => do
        let b ← byLevel x
        pure ⟨⟨b.clear⟩, ⟨b.busy⟩, ⟨b.strained⟩, ⟨b.overloaded⟩⟩
      | none => pure g.pseudoLag
    agentSeatRate := ← n "agent_seat_rate" g.agentSeatRate
    agentSeatBurst := ← n "agent_seat_burst" g.agentSeatBurst
    sponsorSeatRate := ← n "sponsor_seat_rate" g.sponsorSeatRate
    sponsorSeatBurst := ← n "sponsor_seat_burst" g.sponsorSeatBurst
    slotsPerAgent := ← n "slots_per_agent" g.slotsPerAgent
    slotsPerSponsor := ← n "slots_per_sponsor" g.slotsPerSponsor
    slotRetryAfter := ⟨← n "slot_retry_after" g.slotRetryAfter.count⟩
    retryAfterJitter := ← match opt t "retry_after_jitter" with
      | some r => ratioOf r
      | none => pure g.retryAfterJitter }

/-- The seat table: the starting values, as the case overrides them. -/
def seatTableOf (c : Json) : Except String SeatTable := do
  let some t := opt c "seat_table" | pure {}
  onlyKeys t ["push_base", "push_per_record", "return_base", "return_per_record",
    "falcon_return_base", "falcon_return_rows_per_seat", "queue_head_acquisition"]
    "seat_table"
  let g : SeatTable := {}
  let n (k : String) (d : Nat) : Except String Nat :=
    match opt t k with
    | some _ => nat t k
    | none => pure d
  pure { g with
    pushBase := ← n "push_base" g.pushBase
    pushPerRecord := ← n "push_per_record" g.pushPerRecord
    returnBase := ← n "return_base" g.returnBase
    returnPerRecord := ← n "return_per_record" g.returnPerRecord
    falconReturnBase := ← n "falcon_return_base" g.falconReturnBase
    falconReturnRowsPerSeat := ← n "falcon_return_rows_per_seat" g.falconReturnRowsPerSeat
    queueHeadAcquisition := ← n "queue_head_acquisition" g.queueHeadAcquisition }

def bucketOf (j : Json) (k : String) : Except String SeatBucket := do
  let (level, since) ← pair (← j.getObjVal? k)
  pure ⟨level, since⟩

/-- The use over the three horizons. -/
def useOf (j : Json) : Except String (ByHorizon Nat) := do
  onlyKeys j ["hour", "day", "thirty_days"] "use"
  pure ⟨← nat j "hour", ← nat j "day", ← nat j "thirty_days"⟩

/-- An optional number: `null` is `none`. -/
def optNat (j : Json) (k : String) : Except String (Option Nat) := do
  match ← j.getObjVal? k with
  | .null => pure none
  | v => some <$> v.getNat?

/-- A list of times. -/
def times (j : Json) (k : String) : Except String (List Nat) := do
  (← (← j.getObjVal? k).getArr?).toList.mapM (·.getNat?)

/-- A time or `null`. -/
def optTime (j : Json) (k : String) : Except String (Option Nat) := optNat j k

/-- An account's traffic record, every key needed. -/
def trafficOf (j : Json) : Except String TrafficState := do
  onlyKeys j ["stage", "breaker_until", "trial_pending", "retry_after", "backoff_until",
    "streak", "te3_times", "throttled_times", "penalized_times", "last_event",
    "flood_inquire", "flood_release"] "traffic"
  pure {
    stage := ← wordAt TrafficStage j "stage" .normal
    breakerUntil := ← nat j "breaker_until"
    trialPending := ← bool j "trial_pending"
    retryAfter := ← nat j "retry_after"
    backoffUntil := ← nat j "backoff_until"
    streak := ← nat j "streak"
    te3Times := ← times j "te3_times"
    throttledTimes := ← times j "throttled_times"
    penalizedTimes := ← times j "penalized_times"
    lastEvent := ← nat j "last_event"
    floodInquire := ← optTime j "flood_inquire"
    floodRelease := ← optTime j "flood_release" }

def stateOf (st : Json) : Except String MeteredState := do
  onlyKeys st ["now", "tuning", "agent_stop", "suspended", "governor_off", "agent_seats",
    "sponsor_seats", "agent_in_flight", "sponsor_in_flight", "finishing_in_flight",
    "starting_in_flight", "pressure", "use", "external_until", "anonymous_in_flight",
    "traffic"] "state"
  pure {
    now := ← nat st "now"
    tuning := ← tuningOf st
    agentStop := ← bool st "agent_stop"
    suspended := ← bool st "suspended"
    governorOff := ← bool st "governor_off"
    agentSeats := ← bucketOf st "agent_seats"
    sponsorSeats := ← bucketOf st "sponsor_seats"
    agentInFlight := ← nat st "agent_in_flight"
    sponsorInFlight := ← nat st "sponsor_in_flight"
    finishingInFlight := ← nat st "finishing_in_flight"
    startingInFlight := ← nat st "starting_in_flight"
    pressure := ← wordAt PressureLevel st "pressure" .clear
    use := ← match opt st "use" with
      | some u => some <$> useOf u
      | none => pure none
    externalUntil := ← match opt st "external_until" with
      | some _ => nat st "external_until"
      | none => pure 0
    anonymousInFlight := ← match opt st "anonymous_in_flight" with
      | some _ => nat st "anonymous_in_flight"
      | none => pure 0
    readings := ← readingsOf st
    traffic := ← match opt st "traffic" with
      | some x => trafficOf x
      | none => pure {}
    trafficReadings := ← trafficReadingsOf st }

def drawOf (j : Json) : Except String JitterDraw := do
  let (n, d) ← pair j
  pure ⟨n, d⟩

def requestOf (rq : Json) : Except String Request := do
  onlyKeys rq ["kind", "seats", "draw"] "request"
  pure { kind := ← kind rq, seats := ← nat rq "seats",
          draw := ← match opt rq "draw" with
            | some d => drawOf d
            | none => pure {} }

def chargeOf (e : Json) : Except String (Option Charge) := do
  match ← e.getObjVal? "charge" with
  | .null => pure none
  | c =>
    onlyKeys c ["sponsor", "agent"] "charge"
    pure (some ⟨← bucketOf c "sponsor", ← bucketOf c "agent"⟩)

/-- The expected decision and its HTTP status (`0` when admitted). -/
def decisionOf (e : Json) : Except String (Decision × Nat) := do
  match ← str e "decision" with
  | "admitted" =>
    onlyKeys e ["decision", "charge"] "expected"
    pure (.admitted, 0)
  | "cachedOnly" =>
    onlyKeys e ["decision", "charge"] "expected"
    pure (.cachedOnly, 0)
  | "refused" =>
    let status ← nat e "status"
    let f ← match ← str e "refusal" with
      | "switch" =>
        onlyKeys e ["decision", "status", "refusal", "reason", "retry_after", "charge"]
          "expected"
        let ra ← nat e "retry_after"
        match ← str e "reason" with
        | "agentStop" => pure (Refusal.switch .agentStop ra)
        | "suspended" => pure (Refusal.switch .suspended ra)
        | "contained" => pure (Refusal.switch .contained ra)
        | w => defect s!"unknown switch {w}"
      | "rate" =>
        onlyKeys e ["decision", "status", "refusal", "payer", "retry_after", "charge"]
          "expected"
        let p ← match ← str e "payer" with
          | "sponsor" => pure Payer.sponsor
          | "agent" => pure Payer.agent
          | w => defect s!"unknown payer {w}"
        pure (Refusal.rate p (← nat e "retry_after"))
      | "slots" =>
        onlyKeys e ["decision", "status", "refusal", "cap", "retry_after", "charge"] "expected"
        let ra ← nat e "retry_after"
        match ← str e "cap" with
        | "agent" => pure (Refusal.slots .agent ra)
        | "sponsor" => pure (Refusal.slots .sponsor ra)
        | "pool" => pure (Refusal.slots .pool ra)
        | "anonymous" => pure (Refusal.slots .anonymous ra)
        | w => defect s!"unknown cap {w}"
      | "pressure" =>
        onlyKeys e ["decision", "status", "refusal", "level", "retry_after", "charge"]
          "expected"
        let ra ← nat e "retry_after"
        match ← str e "level" with
        | "clear" => pure (Refusal.pressure .clear ra)
        | "busy" => pure (Refusal.pressure .busy ra)
        | "strained" => pure (Refusal.pressure .strained ra)
        | "overloaded" => pure (Refusal.pressure .overloaded ra)
        | w => defect s!"unknown level {w}"
      | "traffic" =>
        onlyKeys e ["decision", "status", "refusal", "stage", "retry_after", "charge"]
          "expected"
        let ra ← nat e "retry_after"
        match ← str e "stage" with
        | "normal" => pure (Refusal.traffic .normal ra)
        | "throttled" => pure (Refusal.traffic .throttled ra)
        | "penalized" => pure (Refusal.traffic .penalized ra)
        | "contained" => pure (Refusal.traffic .contained ra)
        | w => defect s!"unknown stage {w}"
      | w => defect s!"unknown refusal {w}"
    pure (.refused f, status)
  | w => defect s!"unknown decision {w}"

/-- The case's outcome agrees with the expectation `e`: the decision, its status and the
charge. -/
def agrees (s : MeteredState) (r : Request) (e : Json) : Except String Bool := do
  let (d, status) ← decisionOf e
  let c ← chargeOf e
  let got := admit s r
  let gotStatus := match got with
    | .admitted | .cachedOnly => 0
    | .refused f => f.status
  pure (got == d && gotStatus == status && charge s r == c)

/-- One mutation of an expectation: the first of a Retry-After, a cap or a reason, a
charge's level, the decision's word. -/
def mutate (e : Json) : Json :=
  match e.getObjVal? "retry_after" with
  | .ok .null => e.setObjVal! "retry_after" (toJson (0 : Nat))
  | .ok v =>
    match v.getNat? with
    | .ok n => e.setObjVal! "retry_after" (toJson (n + 1))
    | .error _ => e.setObjVal! "retry_after" Json.null
  | _ =>
    match e.getObjVal? "cap" with
    | .ok (.str "pool") => e.setObjVal! "cap" "agent"
    | .ok _ => e.setObjVal! "cap" "pool"
    | _ =>
      match e.getObjVal? "charge", e.getObjVal? "reason" with
      | .ok (.obj _), _ =>
        match chargeOf e with
        | .ok (some c) =>
          e.setObjVal! "charge" (Json.mkObj [
            ("sponsor", Json.arr #[toJson (c.sponsorSeats.level + 1), toJson c.sponsorSeats.since]),
            ("agent", Json.arr #[toJson c.agentSeats.level, toJson c.agentSeats.since])])
        | _ => e.setObjVal! "decision" "refused"
      | _, .ok (.str "agentStop") => e.setObjVal! "reason" "suspended"
      | _, .ok _ => e.setObjVal! "reason" "agentStop"
      | _, _ => e.setObjVal! "charge" (Json.mkObj [
          ("sponsor", Json.arr #[toJson (0 : Nat), toJson (0 : Nat)]),
          ("agent", Json.arr #[toJson (0 : Nat), toJson (0 : Nat)])])

def runCase (c : Json) : Except String (List (Bool × String)) := do
  match ← str c "function" with
  | "lane" =>
    onlyKeys c ["function", "kind", "expected"] "lane case"
    let k ← kind c
    let n ← nat c "expected"
    pure [((laneOf k).number == n, s!"lane of {kindName k}: expected {n}, got {(laneOf k).number}")]
  | "seat_cost" =>
    onlyKeys c ["function", "name", "kind", "records", "rows", "seat_table", "expected"]
      "seat_cost case"
    let name ← str c "name"
    let got := seatCost (← seatTableOf c) (← kind c) (← nat c "records") (← nat c "rows")
    let e ← optNat c "expected"
    pure [(got == e, s!"{name}: expected {e}, got {got}")]
  | "jitter" =>
    onlyKeys c ["function", "name", "base", "draw", "share", "expected"] "jitter case"
    let name ← str c "name"
    let g : GovernorTuning := {}
    let t ← match opt c "share" with
      | some sh => pure { g with retryAfterJitter := ← ratioOf sh }
      | none => pure g
    let got := jitter t (← nat c "base") (← drawOf (← c.getObjVal? "draw"))
    let e ← nat c "expected"
    pure [(got == e, s!"{name}: expected {e}, got {got}")]
  | "admit" =>
    onlyKeys c ["function", "name", "state", "request", "expected"] "admit case"
    let name ← str c "name"
    let s ← stateOf (← c.getObjVal? "state")
    let r ← requestOf (← c.getObjVal? "request")
    let e ← c.getObjVal? "expected"
    let mutated := match agrees s r (mutate e) with
      | .ok b => !b
      | .error _ => true
    let ok ← agrees s r e
    pure [(mutated, s!"{name}: a mutated expectation passed: {(mutate e).compress}"),
      (ok, s!"{name}: expected {e.compress}, got {repr (admit s r)} charging {repr (charge s r)}")]
  | "level" =>
    onlyKeys c ["function", "name", "use", "prev", "external_until", "now", "tuning",
      "expected"] "level case"
    let name ← str c "name"
    let u ← useOf (← c.getObjVal? "use")
    let prev ← wordAt PressureLevel c "prev" .clear
    let t ← tuningOf c
    let rd ← readingsOf c
    let r := pressureRatio u t
    let st := levelStep rd prev r (← nat c "external_until") (← nat c "now")
    let e ← c.getObjVal? "expected"
    onlyKeys e ["kept", "level", "ratio"] "expected"
    let kept ← wordAt PressureLevel e "kept" .clear
    let level ← wordAt PressureLevel e "level" .clear
    let (n, d) ← pair (← e.getObjVal? "ratio")
    let ratioOk := r.num == (n : Int) && r.den == d
    -- A mutated expectation: the level in force one step on, or the ratio's numerator.
    let mutatedOk := st.inForce != level.up || level == .overloaded
    pure [(st.base == kept && st.inForce == level && ratioOk,
        s!"{name}: expected {e.compress}, got {repr st} ratio {r}"),
      (mutatedOk && (r.num != (n : Int) + 1), s!"{name}: a mutated expectation passed")]
  | "traffic_step" =>
    onlyKeys c ["function", "name", "traffic", "now", "event", "end", "tuning", "expected"]
      "traffic_step case"
    let name ← str c "name"
    let tr ← trafficOf (← c.getObjVal? "traffic")
    let now ← nat c "now"
    let t ← tuningOf c
    let rd ← trafficReadingsOf c
    let (got, raised) ← match opt c "event", opt c "end" with
      | some _, none =>
        let e ← wordAt TrafficEvent c "event" .capOverrun
        pure (trafficStep t rd tr e now, false)
      | none, some q =>
        onlyKeys q ["kind", "ending", "retry_after"] "end"
        let k ← kind q
        let en ← wordAt Ending q "ending" .succeeded
        let ra ← optNat q "retry_after"
        let rq : RequestEnd := ⟨k, en, ra⟩
        let a := afterRequest t rd tr rq now
        pure (a.traffic, a.raisesStreak)
      | _, _ => defect s!"{name}: one of event and end"
    let e ← c.getObjVal? "expected"
    onlyKeys e ["raises", "traffic"] "expected"
    let want ← trafficOf (← e.getObjVal? "traffic")
    let wantRaised ← bool e "raises"
    -- A mutated expectation: the streak one on.
    pure [(got == want && raised == wantRaised,
        s!"{name}: expected {e.compress}, got {repr got} raising {raised}"),
      (got != { want with streak := want.streak + 1 }, s!"{name}: a mutated expectation passed")]
  | "traffic_stage" =>
    onlyKeys c ["function", "name", "traffic", "now", "kind", "tuning", "expected"]
      "traffic_stage case"
    let name ← str c "name"
    let tr ← trafficOf (← c.getObjVal? "traffic")
    let now ← nat c "now"
    let k ← kind c
    let t ← tuningOf c
    let rd ← trafficReadingsOf c
    let s' := tr.settled t now
    let e ← c.getObjVal? "expected"
    onlyKeys e ["stage", "breaker", "flood", "served_retry_after", "backoff_violation"]
      "expected"
    let ok := s'.stage == (← wordAt TrafficStage e "stage" .normal) &&
      breakerWait rd s' now == (← optNat e "breaker") &&
      floodWait t s' k now == (← optNat e "flood") &&
      servedRetry t s' now == (← optNat e "served_retry_after") &&
      backoffViolation tr now == (← bool e "backoff_violation")
    let mutatedOk := breakerWait rd s' now != ((← optNat e "breaker").map (· + 1)) ||
      (← optNat e "breaker").isNone
    pure [(ok, s!"{name}: expected {e.compress}, got {repr s'.stage} {repr (breakerWait rd s' now)} {repr (floodWait t s' k now)} {repr (servedRetry t s' now)}"),
      (mutatedOk, s!"{name}: a mutated expectation passed")]
  | f => defect s!"unknown function {f}"

def run : IO (Nat × Nat) := do
  let text ← IO.FS.readFile "vectors/governor.json"
  let json ← IO.ofExcept (Json.parse text)
  let cases ← IO.ofExcept json.getArr?
  let mut t : Count := {}
  -- The kinds: every constructor listed once, each with a lane case.
  let names := allKinds.map kindName
  t ← t.check (names.length == 25 && names.eraseDups.length == names.length)
    s!"the kinds list: {names}"
  let laned := cases.toList.filterMap fun c =>
    match c.getObjValAs? String "function", c.getObjValAs? String "kind" with
    | .ok "lane", .ok k => some k
    | _, _ => none
  for k in allKinds do
    t ← t.check (laned.contains (kindName k)) s!"no lane case for {kindName k}"
  for c in cases do
    for (ok, what) in ← IO.ofExcept (runCase c) do
      t ← t.check ok what
  return (t.pass, t.fail)

end Tests.Governor
