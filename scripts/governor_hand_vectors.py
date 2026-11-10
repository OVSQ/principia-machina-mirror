#!/usr/bin/env python3
"""governor_hand_vectors.py - the governor's admission vectors, written by hand.

Writes vectors/governor.json, which Tests/Governor.lean runs against Principia.Governor.
Version 1 never wrote the governor's code (its TPX 0.6.0 has none) and has no corpus for
it, so no expectation here can come from version 1's own code. They come from this
script, a transcription of TPS 0.5.0's rules written apart from the Lean file:

  5.3.33  the LANE TABLE (with version 1's ruling at 7.2.30): the lane of every governed request
  5.3.35  GA2 the switches (AGENT STOP, SUSPENDED; STATUS, RELEASE and INQUIRE pass),
          GA5 the rate (GCRA on seats, sponsor first, then agent; lane 2 debited and
          never refused; 429 with the time to conformance), GA6 the slots (the agent's,
          its sponsor's, the lane pool; 503), the first refusal ending the request
  5.3.36  one request in flight per agent, two per sponsor
  5.9.18  403, 429, 503; up to 10 per cent jitter on every Retry-After
  7.2.24  SEATS, SEAT RATES, SLOTS and RETRY-AFTER's jitter, the starting values

and the Declarer's answers where TPS 0.5.0 is silent or disagrees (charter section 4):

  slot    a slot refusal (503) carries SLOT RETRY-AFTER, 5 s, jittered as every
          Retry-After
  seats   (a) the queue head's acquisition costs 1 seat; (b) a request dearer than its
          payer's burst conforms when that payer's bucket is empty and is charged in full
  off     GOVERNOR OFF, a field of the state: GA5 is skipped (nothing charged, nothing
          refused on the rate), GA2's switches and GA6's slots kept; GA4 skipped alike
  levels  the pressure levels' four readings, each a tuning word with option 1 its
          default: the descent STRAIGHT to the level the ratio names (or ONE STEP, or
          BANDS); GA4's Retry-After the SLOT one (or the level's PSEUDO LAG, or the BASE),
          jittered; a level entered AT THRESHOLD as 5.3.34 (or ABOVE THRESHOLD as 7.2.21);
          the external reading's step RAISE AFTER the hysteresis (or RAISE BEFORE it)
  falcon  a falcon RETURN's "4 + 1 per 20 result rows" rounds up: 4 plus 1 per started
          group of 20 rows
  propose the Provision proposal op, PROPOSE_PROVISION, in LANE 4 beside VOLUNTEER at 4
          seats: shed first under pressure, refused on budget
  retry   every refusal carries a Retry-After: a switch's (403), and the rate's when the
          request never conforms, is RETRY-AFTER's base with the jitter; a request's draw
          may be absent, the draw [0, 1] then

The pressure levels (GA4) are transcribed from these:

  5.3.31  an EXTERNAL READING showing the host limiting the site raises the level one
          step for 30 minutes; it can only tighten
  5.3.32  r = max over the hour, the day and 30 days of kappa_M x U_T / (sigma x B_T);
          B_H1 4,000, B_H24 800,000 / 31, B_H30 800,000 CPU seconds; sigma 0.8, kappa_M
          1.3 at its starting value; the use here in thousandths of a CPU second
  5.3.34  CLEAR below 0.60, BUSY from 0.60, STRAINED from 0.75, OVERLOADED from 0.90; a
          level left only when r falls 0.05 below its entry threshold; the table of
          admission by level and lane; lane 6 under its slots by level (7.2.24: 6 / 3 /
          1 / 0), cached pages only at OVERLOADED
  5.3.40  ER3: lane 6's expensive actions answered 503 in OVERLOADED only; a full lane 6
          below it served cached pages (the reading CACHED; SLOTS answers 503 as a full
          agent pool does)

The traffic stages (GA3) are transcribed from these:

  5.3.35  GA2 refuses a CONTAINED account (403, after AGENT STOP, before SUSPENDED); GA3,
          between GA2 and GA4, refuses while the traffic breaker is open, 429 with the
          time remaining
  5.3.37  TE1 to TE4; THROTTLED after TE1 or TE2, the breaker open for 60 s, one trial
          after it, success closing it; PENALIZED after three TE3 in an hour or a second
          THROTTLED in an hour, the seat rate halved, the Retry-After doubling from 60 s
          to 3,600 s, ending an hour after the last event; CONTAINED after ten TE3 in 24
          hours or a third PENALIZED in 24 hours, every op but STATUS, RELEASE and INQUIRE
          refused, HEARTBEAT among them, cleared by the Operator alone; a CONTAINED
          account's INQUIRE and RELEASE answered at most once per FLOOD INTERVAL, an
          earlier call refused 429; a request before the Retry-After last given is a TE3
  5.9.18  429 for account causes, 503 for fleet causes; a call served above NORMAL
          carries a Retry-After
  7.2.21  the stage rules' counts and windows; 7.2.24 RETRY-AFTER, PENALTY HOUR, ERROR
          STREAK, FLOOD INTERVAL at their starting values

  stages  the four readings, each a tuning word with option 1 its default: the AGENT's
          own seat rate halves (or AGENT AND SPONSOR); the Retry-After doubles PER
          REFUSAL while PENALIZED (or PER EVENT); the trial succeeds when ADMITTED and not
          refused by GA5 to GA8 (or when it PASSED TRAFFIC); TE2 counts ACCOUNT CAUSES,
          never a 503 (or WITH FLEET)

and the readings Principia/Governor/Traffic.lean states where TPS is silent: a THROTTLED
counted at each TE1 or TE2 below PENALIZED, a PENALIZED at each entry from below; an event
that finds the account PENALIZED keeps it so; PENALIZED's end closes the breaker; under
PER REFUSAL a refusal carries the stage's Retry-After and the breaker reopens for it, the
value then doubling; a served call's Retry-After the breaker's time left, or the FLOOD
INTERVAL when CONTAINED; the halved rate rounded up. The stage rules are written here as
counts over windows of the times kept, newest first.

The hysteresis is transcribed as each level's exit point, its threshold less 0.05, kept
inclusive or not as the threshold rule keeps the threshold itself; the Lean file compares
the ratio raised 0.05 with the threshold.

GCRA is computed here by its virtual scheduling, the theoretical arrival time (TAT) in
exact fractions of a second (ITU-T I.371), where the Lean code keeps a bucket's level in
3600ths of a seat; a bucket (level, since) is the TAT since + level / rate. The readings
Principia/Governor.lean states are followed: the time to conformance is the request's
(both payers'), rounded up to the whole second; the jitter is the draw's fraction of the
jitter share of the wait, rounded down; a request dearer than a burst waits for its
bucket to empty; a request rated at 0 seats an hour that does not conform now never
will; a bucket charged after now is not drained.

Every number is a Python integer or Fraction, and the sweep's draws come from a fixed
linear congruential generator, so the file is the same under every Python 3.
Usage: python3 -I scripts/governor_hand_vectors.py [--check]; --check writes nothing and
exits 1 when the file differs from what this script gives.
"""
import json
import math
import pathlib
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "vectors" / "governor.json"

# TPS 5.3.33 and version 1's ruling at 7.2.30: the lane of every governed request.
LANE = {
    "declarerOrOperator": 0, "essentialJob": 0,
    "signedInUser": 1, "structureTestButton": 1,
    "queueHeadAcquisition": 2, "pollByHeadOrHolder": 2, "heartbeat": 2, "push": 2,
    "workReturn": 2, "releaseOp": 2, "inquire": 2,
    "petition": 3, "pollOther": 3, "status": 3, "agentCoreRead": 3, "structureTestOp": 3,
    "volunteer": 4, "falconReturn": 4, "proposeProvision": 4,
    "deferrableJob": 5, "falconJob": 5, "bibliographyRecheckJob": 5, "structureTestJob": 5,
    "configurationStrataJob": 5,
    "anonymousRead": 6,
}
KINDS = list(LANE)
AGENT_KINDS = [k for k in KINDS if LANE[k] in (2, 3, 4)]
# The random sweep draws from the kinds as they stood before the proposal op, so its cases
# are unchanged; the proposal op is covered by the named cases.
SWEEP_KINDS = [k for k in KINDS if k != "proposeProvision"]
SWEEP_AGENT_KINDS = [k for k in AGENT_KINDS if k != "proposeProvision"]
PASSES = {"status", "releaseOp", "inquire"}          # GA2: they pass the switches

# 7.2.24 and 7.2.30: the starting values read here.
SEATS = {"status": 1, "poll": 1, "heartbeat": 1, "inquire": 1, "petition": 2,
         "releaseOp": 2, "volunteer": 2, "returnBase": 4, "returnPerRecord": 1,
         "pushBase": 4, "pushPerRecord": 1, "coreRead": 1, "coreWrite": 4,
         "falconReturnBase": 4, "falconReturnRowsPerSeat": 20, "structureTest": 2,
         "queueHeadAcquisition": 1, "proposeProvision": 4}
TUNING = {"agent_seat_rate": 120, "agent_seat_burst": 20, "sponsor_seat_rate": 240,
          "sponsor_seat_burst": 30, "slots_per_agent": 1, "slots_per_sponsor": 2,
          "retry_after_jitter": [10, 100], "slot_retry_after": 5, "retry_after_base": 60,
          "kappa_m": [13, 10], "anonymous_slots": [6, 3, 1, 0], "pseudo_lag": [0, 3, 6, 30],
          "descent": "STRAIGHT", "pressure_retry_after": "SLOT",
          "threshold_rule": "AT THRESHOLD", "external_order": "RAISE AFTER",
          "anonymous_full": "CACHED", "retry_after_cap": 3600, "penalty_hour": 3600,
          "flood_interval": 60, "error_streak": 20, "penalized_payer": "AGENT",
          "doubling": "PER REFUSAL", "trial_success": "ADMITTED",
          "te2_causes": "ACCOUNT CAUSES"}
LEVELS = ["CLEAR", "BUSY", "STRAINED", "OVERLOADED"]        # 5.3.34, in order
LEVEL_NAME = {"CLEAR": "clear", "BUSY": "busy", "STRAINED": "strained",
              "OVERLOADED": "overloaded"}
ENTRY = [Fraction(0), Fraction(60, 100), Fraction(75, 100), Fraction(90, 100)]
HYSTERESIS = Fraction(5, 100)
SIGMA = Fraction(4, 5)
BUDGET = {"hour": Fraction(4000), "day": Fraction(800000, 31),
          "thirty_days": Fraction(800000)}
# 5.3.34's table: the lanes each level refuses (lane 6 apart).
REFUSED_AT = {"CLEAR": set(), "BUSY": {4}, "STRAINED": {3, 4, 5}, "OVERLOADED": {3, 4, 5}}
AGENT_LANE_SLOTS, KEPT_FOR_LANE_2 = 6, 2               # 7.2.21, 5.3.33
SEAT_TABLE_KEYS = {"push_base": "pushBase", "push_per_record": "pushPerRecord",
                   "return_base": "returnBase", "return_per_record": "returnPerRecord",
                   "falcon_return_base": "falconReturnBase",
                   "falcon_return_rows_per_seat": "falconReturnRowsPerSeat",
                   "queue_head_acquisition": "queueHeadAcquisition"}


def seat_cost(kind, records, rows, table):
    """7.2.24: an op's SEATS; None where the table states none."""
    t = dict(SEATS)
    for k, v in (table or {}).items():
        t[SEAT_TABLE_KEYS[k]] = v
    if kind in ("pollByHeadOrHolder", "pollOther"):
        return t["poll"]
    if kind == "agentCoreRead":
        return t["coreRead"]
    if kind == "structureTestOp":
        return t["structureTest"]
    if kind in ("status", "heartbeat", "inquire", "petition", "releaseOp", "volunteer",
                "proposeProvision"):
        return t[kind]
    if kind == "workReturn":
        return t["returnBase"] + t["returnPerRecord"] * records
    if kind == "push":
        return t["pushBase"] + t["pushPerRecord"] * records
    if kind == "falconReturn":
        per = t["falconReturnRowsPerSeat"]
        return t["falconReturnBase"] + math.ceil(Fraction(rows, per))   # rows round up
    if kind == "queueHeadAcquisition":
        return t["queueHeadAcquisition"]   # seats (a): 1, as POLL and HEARTBEAT
    return 0                               # not an agent's request: no seats


def gcra(bucket, rate, burst, now, seats):
    """GCRA for one payer by virtual scheduling. Returns (conforms, wait, bucket after).

    The bucket [level, since] stands for TAT = since + level / rate seconds. The request
    arrives at t = max(now, since). It conforms when max(TAT, t) + seats * I - t is at most
    burst * I, I = 3600 / rate seconds a seat; a request dearer than the burst (seats b)
    when TAT <= t, the bucket empty. Charged, TAT becomes max(TAT, t) + seats * I.
    """
    level, since = bucket
    t = max(now, since)
    dear = seats > burst
    if rate == 0:                          # I is unbounded: the backlog never drains
        conforms = level == 0 if dear else level + seats * 3600 <= burst * 3600
        return conforms, (0 if conforms else None), [level + seats * 3600, t]
    step = Fraction(3600, rate)
    tat = since + Fraction(level, rate)
    start = max(tat, Fraction(t))
    conforms = tat <= t if dear else start + seats * step - t <= burst * step
    after = (start + seats * step - t) * rate
    assert after.denominator == 1
    if conforms:
        wait = 0
    elif dear:
        wait = math.ceil(tat - now)        # until the bucket is empty
    else:
        wait = math.ceil(tat + (seats - burst) * step - now)
    return conforms, wait, [int(after), t]


def jitter(base, share, draw):
    """5.9.18: the draw's fraction of the jitter share of the wait, rounded down."""
    num, den = draw
    if den == 0:
        return 0
    return math.floor(base * Fraction(share[0], share[1]) * Fraction(min(num, den), den))


def ratio(use, kappa):
    """5.3.32: the largest horizon's kappa_M x U_T / (sigma x B_T), U_T in CPU seconds."""
    k = Fraction(kappa[0], kappa[1])
    return max(k * Fraction(use[h], 1000) / (SIGMA * BUDGET[h])
               for h in ("hour", "day", "thirty_days"))


def holds(i, r, rule, widen):
    """r lies in level i's region or above it, the region widened down by `widen`:
    5.3.34 enters a level at its threshold; 7.2.21 ("BUSY to 0.75, STRAINED to 0.90,
    OVERLOADED above") at BUSY's only."""
    point = ENTRY[i] - widen
    if rule == "AT THRESHOLD" or i == 1:
        return r >= point
    return r > point


def named(r, rule):
    """The level the ratio names: the highest whose region r reaches."""
    return max(i for i in range(4) if i == 0 or holds(i, r, rule, 0))


def level_step(prev, r, t, raised):
    """The update: (the level the hysteresis keeps, the level in force), as indices."""
    rule = t["threshold_rule"]

    def lift(i):
        return min(i + 1, 3) if raised and t["external_order"] == "RAISE BEFORE" else i
    target = lift(named(r, rule))
    if target >= prev:
        kept = target
    elif holds(prev, r, rule, HYSTERESIS):       # not yet 0.05 below its threshold
        kept = prev
    elif t["descent"] == "STRAIGHT":
        kept = lift(named(r, rule))
    elif t["descent"] == "ONE STEP":
        kept = lift(prev - 1)
    else:                                         # BANDS
        kept = lift(max(i for i in range(prev) if i == 0 or holds(i, r, rule, HYSTERESIS)))
    in_force = min(kept + 1, 3) if raised and t["external_order"] == "RAISE AFTER" else kept
    return kept, in_force


def level_in_force(state, t):
    prev = LEVELS.index(state.get("pressure", "CLEAR"))
    if "use" not in state:
        return prev
    raised = state["now"] < state.get("external_until", 0)
    return level_step(prev, ratio(state["use"], t["kappa_m"]), t, raised)[1]


# 5.3.37 and 7.2.21: the stage rules, (count, window in seconds).
PENALIZED_TE3, PENALIZED_THROTTLED, PENALIZED_WINDOW = 3, 2, 3600
CONTAINED_TE3, CONTAINED_PENALIZED, CONTAINED_WINDOW = 10, 3, 86400
STAGE_NAME = {"NORMAL": "normal", "THROTTLED": "throttled", "PENALIZED": "penalized",
              "CONTAINED": "contained"}
BREAKER_STAGES = ("THROTTLED", "PENALIZED")


def fresh():
    """An account's traffic record with no history: NORMAL."""
    return {"stage": "NORMAL", "breaker_until": 0, "trial_pending": False, "retry_after": 0,
            "backoff_until": 0, "streak": 0, "te3_times": [], "throttled_times": [],
            "penalized_times": [], "last_event": 0, "flood_inquire": None,
            "flood_release": None}


def recent(times, window, now):
    """The times inside the window of `window` seconds that ends at now."""
    return [x for x in times if x > now - window]


def in_force(tr, t, now):
    """5.3.37: PENALIZED ends PENALTY HOUR after the last event."""
    tr = dict(tr)
    if tr["stage"] == "PENALIZED" and now >= tr["last_event"] + t["penalty_hour"]:
        tr.update(stage="NORMAL", breaker_until=0, trial_pending=False, retry_after=0)
    return tr


def breaker_opens(tr, now, seconds):
    tr.update(breaker_until=now + seconds, trial_pending=True, retry_after=seconds)


def contained(tr):
    tr.update(stage="CONTAINED", breaker_until=0, trial_pending=False)


def base_wait(t):
    return min(t["retry_after_base"], t["retry_after_cap"])


def to_penalized(tr, t, now):
    if tr["stage"] == "PENALIZED":
        return
    tr["penalized_times"] = [now] + recent(tr["penalized_times"], CONTAINED_WINDOW, now)
    if len(tr["penalized_times"]) >= CONTAINED_PENALIZED:
        contained(tr)
    else:
        tr["stage"] = "PENALIZED"
        breaker_opens(tr, now, base_wait(t))


def event(tr, t, e, now):
    """One TRAFFIC EVENT at now (5.3.37)."""
    tr = in_force(tr, t, now)
    tr["last_event"] = now
    if tr["stage"] == "CONTAINED":
        return tr
    if t["doubling"] == "PER EVENT" and tr["stage"] == "PENALIZED":
        tr["retry_after"] = min(2 * tr["retry_after"], t["retry_after_cap"])
    if e in ("REPEAT", "ERROR STREAK"):
        if tr["stage"] == "PENALIZED":
            breaker_opens(tr, now, tr["retry_after"])
        else:
            tr["throttled_times"] = [now] + recent(tr["throttled_times"], PENALIZED_WINDOW, now)
            if len(tr["throttled_times"]) >= PENALIZED_THROTTLED:
                to_penalized(tr, t, now)
            else:
                tr["stage"] = "THROTTLED"
                breaker_opens(tr, now, base_wait(t))
    elif e == "BACKOFF VIOLATION":
        tr["te3_times"] = [now] + recent(tr["te3_times"], CONTAINED_WINDOW, now)
        if len(tr["te3_times"]) >= CONTAINED_TE3:
            contained(tr)
        elif len(recent(tr["te3_times"], PENALIZED_WINDOW, now)) >= PENALIZED_TE3:
            to_penalized(tr, t, now)
    return tr                               # CAP OVERRUN: recorded, no stage moved


def trial_result(reading, ending):
    """The trial reading (stages c): True a success, False a failure, None when the end decides nothing."""
    if ending in ("SWITCH", "TRAFFIC", "SHAPE"):
        return None
    if reading == "PASSED TRAFFIC" or ending == "SUCCEEDED":
        return True
    if ending == "PRESSURE":
        return None
    return False                            # RATE, SLOTS, FAILED under ADMITTED


def end_of(tr, t, q, now):
    """GA9: one request's end. Returns (the record, whether TE2 is raised)."""
    tr = in_force(tr, t, now)
    ending = q["ending"]
    account = ("SWITCH", "TRAFFIC", "RATE", "SHAPE", "FAILED")
    fleet = ("PRESSURE", "SLOTS")
    raised = False
    if ending in account or (ending in fleet and t["te2_causes"] == "WITH FLEET"):
        if tr["streak"] + 1 >= t["error_streak"]:
            tr["streak"], raised = 0, True
        else:
            tr["streak"] += 1
    elif ending == "SUCCEEDED":
        tr["streak"] = 0

    def doubled_again():
        breaker_opens(tr, now, tr["retry_after"])
        tr["retry_after"] = min(2 * tr["retry_after"], t["retry_after_cap"])
    if tr["stage"] in BREAKER_STAGES and tr["trial_pending"]:
        per_refusal = tr["stage"] == "PENALIZED" and t["doubling"] == "PER REFUSAL"
        if now < tr["breaker_until"]:
            if ending == "TRAFFIC" and per_refusal:
                doubled_again()
        else:
            result = trial_result(t["trial_success"], ending)
            if result is True:
                tr.update(trial_pending=False, breaker_until=0)
                if tr["stage"] == "THROTTLED":
                    tr["stage"] = "NORMAL"
            elif result is False:
                if per_refusal:
                    doubled_again()
                elif tr["stage"] == "PENALIZED":
                    breaker_opens(tr, now, tr["retry_after"])
                else:
                    breaker_opens(tr, now, base_wait(t))
    if tr["stage"] == "CONTAINED" and ending in ("SUCCEEDED", "FAILED"):
        if q["kind"] == "inquire":
            tr["flood_inquire"] = now
        elif q["kind"] == "releaseOp":
            tr["flood_release"] = now
    if q["retry_after"] is not None:
        tr["backoff_until"] = now + q["retry_after"]
    return tr, raised


def flood_wait(tr, t, kind, now):
    """5.3.37: a CONTAINED account's INQUIRE or RELEASE inside the FLOOD INTERVAL."""
    if tr["stage"] != "CONTAINED":
        return None
    last = {"inquire": tr["flood_inquire"], "releaseOp": tr["flood_release"]}.get(kind)
    if last is None or now >= last + t["flood_interval"]:
        return None
    return last + t["flood_interval"] - now


def breaker_wait(tr, t, now):
    """GA3's wait while the breaker is open, before the jitter."""
    if tr["stage"] not in BREAKER_STAGES or not tr["trial_pending"] or now >= tr["breaker_until"]:
        return None
    if tr["stage"] == "PENALIZED" and t["doubling"] == "PER REFUSAL":
        return tr["retry_after"]
    return tr["breaker_until"] - now


def served_wait(tr, t, now):
    """5.9.18: the Retry-After of a call served above NORMAL."""
    if tr["stage"] == "NORMAL":
        return None
    if tr["stage"] == "CONTAINED":
        return t["flood_interval"]
    return max(tr["breaker_until"] - now, 0)


def admit(state, request):
    """TPS 5.3.35: the first refusal of GA2 to GA6; the charge GA5 debits."""
    t = dict(TUNING)
    t.update(state.get("tuning", {}))
    tr = in_force(state.get("traffic", fresh()), t, state["now"])
    kind, seats = request["kind"], request["seats"]
    lane = LANE[kind]
    now = state["now"]
    off = state["governor_off"]
    level = level_in_force(state, t)
    word = LEVELS[level]
    draw = request.get("draw", [0, 1])
    base_retry = t["retry_after_base"] + jitter(t["retry_after_base"],   # retry
                                                t["retry_after_jitter"], draw)
    base = t["slot_retry_after"]          # slot: SLOT RETRY-AFTER, jittered
    slot_retry = base + jitter(base, t["retry_after_jitter"], draw)
    wait = {"SLOT": t["slot_retry_after"], "PSEUDO LAG": t["pseudo_lag"][level],
            "BASE": t["retry_after_base"]}[t["pressure_retry_after"]]
    pressure = None
    if not off and lane in REFUSED_AT[word]:
        pressure = {"status": 503, "refusal": "pressure", "level": LEVEL_NAME[word],
                    "retry_after": wait + jitter(wait, t["retry_after_jitter"],
                                                 draw)}
    if lane == 6:                          # 5.3.34, 5.3.40
        if off:
            return {"decision": "admitted", "charge": None}
        if word == "OVERLOADED":
            return {"decision": "cachedOnly", "charge": None}
        if state.get("anonymous_in_flight", 0) >= t["anonymous_slots"][level]:
            if t["anonymous_full"] == "CACHED":
                return {"decision": "cachedOnly", "charge": None}
            return {"decision": "refused", "status": 503, "refusal": "slots",
                    "cap": "anonymous", "retry_after": slot_retry, "charge": None}
        return {"decision": "admitted", "charge": None}
    if lane not in (2, 3, 4):
        if pressure:
            return dict({"decision": "refused"}, **pressure, charge=None)
        return {"decision": "admitted", "charge": None}
    agent_rate, sponsor_rate = t["agent_seat_rate"], t["sponsor_seat_rate"]
    if tr["stage"] == "PENALIZED":            # 5.3.37, stages (a): halved, rounded up
        agent_rate = -(-agent_rate // 2)
        if t["penalized_payer"] == "AGENT AND SPONSOR":
            sponsor_rate = -(-sponsor_rate // 2)
    s_ok, s_wait, s_after = gcra(state["sponsor_seats"], sponsor_rate,
                                 t["sponsor_seat_burst"], now, seats)
    a_ok, a_wait, a_after = gcra(state["agent_seats"], agent_rate,
                                 t["agent_seat_burst"], now, seats)
    charge = None if off else {"sponsor": s_after, "agent": a_after}   # off: GA5 skipped

    def refused(**r):
        return dict({"decision": "refused"}, **r, charge=charge)
    if kind not in PASSES:
        if state["agent_stop"]:
            return refused(status=403, refusal="switch", reason="agentStop",
                           retry_after=base_retry)
        if tr["stage"] == "CONTAINED":
            return refused(status=403, refusal="switch", reason="contained",
                           retry_after=base_retry)
        if state["suspended"]:
            return refused(status=403, refusal="switch", reason="suspended",
                           retry_after=base_retry)
    w = flood_wait(tr, t, kind, now)          # 5.3.37: "otherwise at GA2"
    stage = "CONTAINED"
    if w is None and kind not in PASSES and not off:    # GA3: the breaker
        w, stage = breaker_wait(tr, t, now), tr["stage"]
    if w is not None:
        return refused(status=429, refusal="traffic", stage=STAGE_NAME[stage],
                       retry_after=w + jitter(w, t["retry_after_jitter"], draw))
    if pressure:
        return refused(**pressure)
    if lane in (3, 4) and not off and not (s_ok and a_ok):
        wait = None if s_wait is None or a_wait is None else max(s_wait, a_wait)
        retry = base_retry if wait is None else wait + jitter(wait, t["retry_after_jitter"],
                                                               draw)
        return refused(status=429, refusal="rate", payer="sponsor" if not s_ok else "agent",
                       retry_after=retry)
    if state["agent_in_flight"] >= t["slots_per_agent"]:
        return refused(status=503, refusal="slots", cap="agent", retry_after=slot_retry)
    if state["sponsor_in_flight"] >= t["slots_per_sponsor"]:
        return refused(status=503, refusal="slots", cap="sponsor", retry_after=slot_retry)
    in_flight = state["finishing_in_flight"] + state["starting_in_flight"]
    if in_flight >= AGENT_LANE_SLOTS or (
            lane != 2 and state["starting_in_flight"] >= AGENT_LANE_SLOTS - KEPT_FOR_LANE_2):
        return refused(status=503, refusal="slots", cap="pool", retry_after=slot_retry)
    return {"decision": "admitted", "charge": charge}


def idle(now=10000, **kw):
    """A state with nothing in flight, both buckets empty, no switch on."""
    s = {"now": now, "agent_stop": False, "suspended": False, "governor_off": False,
         "agent_seats": [0, 0],
         "sponsor_seats": [0, 0], "agent_in_flight": 0, "sponsor_in_flight": 0,
         "finishing_in_flight": 0, "starting_in_flight": 0}
    s.update(kw)
    return s


def default_seats(kind):
    c = seat_cost(kind, 3, 40, None)
    return 3 if c is None else c


class Lcg:
    """A 64-bit linear congruential generator (Knuth's MMIX constants)."""
    def __init__(self, seed):
        self.x = seed

    def below(self, n):
        self.x = (6364136223846793005 * self.x + 1442695040888963407) % (1 << 64)
        return (self.x >> 33) % n

    def pick(self, xs):
        return xs[self.below(len(xs))]


def build():
    cases = []

    def lane_case(kind):
        cases.append({"function": "lane", "kind": kind, "expected": LANE[kind]})

    def cost_case(name, kind, records=0, rows=0, table=None):
        c = {"function": "seat_cost", "name": name, "kind": kind, "records": records,
             "rows": rows}
        if table:
            c["seat_table"] = table
        c["expected"] = seat_cost(kind, records, rows, table)
        cases.append(c)

    def jitter_case(name, base, draw, share=None):
        c = {"function": "jitter", "name": name, "base": base, "draw": draw}
        if share:
            c["share"] = share
        c["expected"] = jitter(base, share or TUNING["retry_after_jitter"], draw)
        cases.append(c)

    def admit_case(name, state, kind, seats=None, draw=(0, 1)):
        request = {"kind": kind, "seats": default_seats(kind) if seats is None else seats}
        if draw is not None:                  # retry: an absent draw is [0, 1]
            request["draw"] = list(draw)
        cases.append({"function": "admit", "name": name, "state": state,
                      "request": request, "expected": admit(state, request)})

    # The lane table.
    for k in KINDS:
        lane_case(k)

    # Seat costs (7.2.24, 7.2.30).
    for k in KINDS:
        cost_case(f"cost {k}", k)
    for n in (1, 7, 1000):
        cost_case(f"cost push {n} records", "push", records=n)
        cost_case(f"cost RETURN {n} records", "workReturn", records=n)
    for rows in (20, 40, 320, 340, 21, 39, 1):
        cost_case(f"cost falcon RETURN {rows} rows", "falconReturn", rows=rows)
    cost_case("cost push, tuned", "push", records=5,
              table={"push_base": 6, "push_per_record": 2})
    cost_case("cost falcon RETURN, tuned per 10 rows", "falconReturn", rows=30,
              table={"falcon_return_base": 1, "falcon_return_rows_per_seat": 10})
    cost_case("cost falcon RETURN, tuned, off the multiple", "falconReturn", rows=35,
              table={"falcon_return_rows_per_seat": 10})

    # The jitter (5.9.18).
    for base in (0, 1, 9, 10, 11, 30, 31, 3600, 10 ** 12):
        for draw in ([0, 1], [1, 2], [999, 1000], [1, 1], [5, 3], [1, 0], [0, 0]):
            jitter_case(f"jitter {base} draw {draw}", base, draw)
    jitter_case("jitter, a share of a half", 1001, [2, 3], share=[1, 2])
    jitter_case("jitter, no share", 1000, [1, 1], share=[0, 1])
    jitter_case("jitter, a share past one", 7, [1, 1], share=[3, 2])

    # Every request, idle.
    for k in KINDS:
        admit_case(f"idle {k}", idle(), k)
    admit_case("idle acquisition, 0 seats", idle(), "queueHeadAcquisition", seats=0)
    cost_case("cost acquisition, tuned", "queueHeadAcquisition",
              table={"queue_head_acquisition": 3})
    # Switches (GA2), each with RETRY-AFTER's base, jittered (retry).
    admit_case("AGENT STOP petition, retry_after with the draw 1/2", idle(agent_stop=True),
               "petition", draw=(1, 2))
    admit_case("AGENT STOP petition, retry_after with no draw", idle(agent_stop=True),
               "petition", draw=None)
    admit_case("AGENT STOP petition, retry_after base 120 with the draw 3/4",
               idle(agent_stop=True, tuning={"retry_after_base": 120}), "petition", draw=(3, 4))
    for k in KINDS:
        admit_case(f"AGENT STOP {k}", idle(agent_stop=True), k)
        admit_case(f"SUSPENDED {k}", idle(suspended=True), k)
    admit_case("AGENT STOP and SUSPENDED", idle(agent_stop=True, suspended=True), "petition")
    admit_case("AGENT STOP and SUSPENDED, STATUS", idle(agent_stop=True, suspended=True),
               "status")

    # The rate (GA5), at the boundary. Sponsor burst 30, agent burst 20: seats 2.
    u = 3600
    for kind in ("petition", "volunteer", "status", "structureTestOp", "proposeProvision"):
        c = default_seats(kind)
        admit_case(f"{kind}: agent exactly full", idle(agent_seats=[(20 - c) * u, 10000]), kind)
        admit_case(f"{kind}: agent one unit over", idle(agent_seats=[(20 - c) * u + 1, 10000]),
                   kind)
        admit_case(f"{kind}: sponsor exactly full",
                   idle(sponsor_seats=[(30 - c) * u, 10000]), kind)
        admit_case(f"{kind}: sponsor one unit over",
                   idle(sponsor_seats=[(30 - c) * u + 1, 10000]), kind)
    # Draining over time: 120 seats an hour drain 120 units a second.
    for elapsed in (0, 1, 29, 30, 31, 60, 600, 3600):
        admit_case(f"agent drained {elapsed} s", idle(agent_seats=[20 * u, 10000 - elapsed]),
                   "petition")
        admit_case(f"sponsor drained {elapsed} s",
                   idle(sponsor_seats=[30 * u, 10000 - elapsed]), "petition")
    # Both over: the later of the two waits, the sponsor named.
    admit_case("both over, the agent's wait longer",
               idle(sponsor_seats=[30 * u + 1, 10000], agent_seats=[25 * u, 10000]), "petition")
    admit_case("both over, the sponsor's wait longer",
               idle(sponsor_seats=[40 * u, 10000], agent_seats=[19 * u, 10000]), "petition")
    admit_case("agent over, sponsor fine", idle(agent_seats=[30 * u, 9000]), "petition")
    # Lane 2: debited and never refused.
    for kind in ("push", "workReturn", "heartbeat", "pollByHeadOrHolder", "releaseOp",
                 "inquire", "queueHeadAcquisition"):
        admit_case(f"lane 2 deep in debt: {kind}",
                   idle(agent_seats=[10 ** 9, 9990], sponsor_seats=[10 ** 9, 9990]), kind)
    admit_case("lane 2 push of 1000 records", idle(), "push", seats=1004)
    admit_case("after a push of 1000 records, a petition", idle(
        agent_seats=[1004 * u, 10000], sponsor_seats=[1004 * u, 10000]), "petition")
    # More seats than the burst (seats b): conforms on an empty bucket, charged in full.
    admit_case("falcon RETURN of 340 rows, above the agent's burst", idle(),
               "falconReturn", seats=21)
    admit_case("falcon RETURN of 320 rows, the agent's burst", idle(), "falconReturn",
               seats=20)
    admit_case("31 seats, above the sponsor's burst too", idle(), "volunteer", seats=31)
    admit_case("falcon RETURN of 2000 rows, empty buckets", idle(), "falconReturn",
               seats=104)
    admit_case("dear, agent one unit in", idle(agent_seats=[1, 10000]), "falconReturn",
               seats=21)
    admit_case("dear, agent drained to empty now", idle(agent_seats=[120 * 30, 9970]),
               "falconReturn", seats=21)
    admit_case("dear, agent one second short of empty", idle(agent_seats=[120 * 30, 9971]),
               "falconReturn", seats=21)
    admit_case("dear for the agent only, sponsor full", idle(sponsor_seats=[10 * u, 10000]),
               "falconReturn", seats=25)
    admit_case("dear for both, sponsor not empty", idle(sponsor_seats=[u, 10000]),
               "volunteer", seats=40)
    admit_case("dear, clock behind an empty bucket", idle(agent_seats=[0, 10500]),
               "falconReturn", seats=21)
    admit_case("dear, clock behind a bucket in debt", idle(agent_seats=[5 * u, 10500]),
               "falconReturn", seats=21)
    admit_case("after a dear RETURN, its debt", idle(agent_seats=[104 * u, 10000],
                                                     sponsor_seats=[104 * u, 10000]),
               "petition")
    admit_case("dear, rate 0, empty", idle(tuning={"agent_seat_rate": 0}), "falconReturn",
               seats=21)
    admit_case("dear, rate 0, not empty", idle(tuning={"agent_seat_rate": 0},
                                              agent_seats=[1, 0]), "falconReturn", seats=21)
    admit_case("dear, burst 0", idle(tuning={"agent_seat_burst": 0},
                                     agent_seats=[u, 9990]), "status")
    # Zero seats: conforms unless in debt.
    admit_case("zero seats, empty", idle(), "petition", seats=0)
    admit_case("zero seats, in debt", idle(agent_seats=[20 * u + 1, 10000]), "petition",
               seats=0)
    # A clock behind the bucket.
    admit_case("clock behind the agent's bucket, room left",
               idle(agent_seats=[10 * u, 10500]), "petition")
    admit_case("clock behind the agent's bucket, no room",
               idle(agent_seats=[19 * u, 10500]), "petition")
    admit_case("clock behind the sponsor's bucket, exactly full",
               idle(sponsor_seats=[29 * u, 12000]), "status")
    admit_case("clock behind the sponsor's bucket, no room",
               idle(sponsor_seats=[30 * u, 12000]), "status")
    # Tuned rates and bursts.
    admit_case("rate 7 an hour", idle(tuning={"agent_seat_rate": 7},
                                      agent_seats=[20 * u, 9000]), "petition")
    admit_case("rate 0, room left", idle(tuning={"agent_seat_rate": 0},
                                         agent_seats=[10 * u, 0]), "petition")
    admit_case("rate 0, no room", idle(tuning={"agent_seat_rate": 0},
                                       agent_seats=[19 * u, 0]), "petition")
    admit_case("sponsor rate 0, no room", idle(tuning={"sponsor_seat_rate": 0},
                                               sponsor_seats=[29 * u, 0]), "petition")
    # retry: a request that never conforms is refused with RETRY-AFTER's base, jittered.
    never = idle(tuning={"agent_seat_rate": 0}, agent_seats=[19 * u, 0])
    admit_case("rate 0, never conforms, retry_after with the draw 1/2", never, "petition",
               draw=(1, 2))
    admit_case("rate 0, never conforms, retry_after with no draw", never, "petition",
               draw=None)
    admit_case("rate 0, never conforms, retry_after base 120, jitter 1/5, draw 1/1",
               idle(tuning={"agent_seat_rate": 0, "retry_after_base": 120,
                            "retry_after_jitter": [1, 5]}, agent_seats=[19 * u, 0]),
               "petition", draw=(1, 1))
    admit_case("burst 0", idle(tuning={"agent_seat_burst": 0}), "status")
    admit_case("rate 3600 an hour", idle(tuning={"agent_seat_rate": 3600},
                                         agent_seats=[25 * u, 9999]), "petition")
    admit_case("rate 5000 an hour", idle(tuning={"sponsor_seat_rate": 5000},
                                         sponsor_seats=[35 * u, 9999]), "petition")
    # The jitter on a refusal.
    over = idle(agent_seats=[25 * u, 10000])
    for draw in ((0, 1), (1, 2), (999, 1000), (1, 1), (5, 3), (1, 0)):
        admit_case(f"jitter draw {list(draw)}", over, "petition", draw=draw)
    admit_case("jitter share of a half", idle(tuning={"retry_after_jitter": [1, 2]},
                                              agent_seats=[25 * u, 10000]), "petition",
               draw=(1, 1))
    admit_case("jitter share 0", idle(tuning={"retry_after_jitter": [0, 7]},
                                      agent_seats=[25 * u, 10000]), "petition", draw=(1, 1))

    # The slots (GA6).
    for kind in ("push", "petition", "volunteer", "status", "inquire"):
        admit_case(f"agent slot taken: {kind}", idle(agent_in_flight=1), kind)
        admit_case(f"sponsor slots taken: {kind}", idle(sponsor_in_flight=2), kind)
        admit_case(f"sponsor one slot left: {kind}", idle(sponsor_in_flight=1), kind)
        for fin, start in ((0, 4), (1, 4), (2, 3), (3, 3), (6, 0), (5, 0), (2, 4), (0, 5)):
            admit_case(f"pool {fin} + {start}: {kind}",
                       idle(finishing_in_flight=fin, starting_in_flight=start), kind)
    admit_case("tuned slots: two per agent", idle(tuning={"slots_per_agent": 2},
                                                  agent_in_flight=1), "petition")
    admit_case("tuned slots: three per sponsor", idle(tuning={"slots_per_sponsor": 3},
                                                     sponsor_in_flight=2), "petition")
    admit_case("tuned slots: none per agent", idle(tuning={"slots_per_agent": 0}), "push")
    # The slot refusal's Retry-After (slot).
    for draw in ((0, 1), (1, 2), (999, 1000), (1, 1), (5, 3), (1, 0)):
        admit_case(f"slot Retry-After, draw {list(draw)}", idle(agent_in_flight=1), "petition",
                   draw=draw)
    for base in (0, 1, 10, 60, 3600):
        admit_case(f"slot Retry-After tuned to {base}",
                   idle(tuning={"slot_retry_after": base}, sponsor_in_flight=2), "push",
                   draw=(1, 1))
    admit_case("slot Retry-After, a share of a half",
               idle(tuning={"retry_after_jitter": [1, 2], "slot_retry_after": 31},
                    finishing_in_flight=6), "heartbeat", draw=(2, 3))
    # GOVERNOR OFF (off): no rate, no charge; the switches and the slots stay.
    deep = dict(agent_seats=[10 ** 9, 9990], sponsor_seats=[10 ** 9, 9990])
    for k in KINDS:
        admit_case(f"GOVERNOR OFF, deep in debt: {k}", idle(governor_off=True, **deep), k)
    admit_case("GOVERNOR OFF, a dear request", idle(governor_off=True, agent_seats=[u, 10000]),
               "falconReturn", seats=500)
    for k in ("petition", "push", "status", "inquire"):
        admit_case(f"GOVERNOR OFF, AGENT STOP: {k}",
                   idle(governor_off=True, agent_stop=True, **deep), k)
        admit_case(f"GOVERNOR OFF, SUSPENDED: {k}",
                   idle(governor_off=True, suspended=True, **deep), k)
        admit_case(f"GOVERNOR OFF, agent slot taken: {k}",
                   idle(governor_off=True, agent_in_flight=1, **deep), k)
        admit_case(f"GOVERNOR OFF, sponsor slots taken: {k}",
                   idle(governor_off=True, sponsor_in_flight=2, **deep), k)
        admit_case(f"GOVERNOR OFF, pool 2 + 4: {k}",
                   idle(governor_off=True, finishing_in_flight=2, starting_in_flight=4, **deep),
                   k)
    # The order: GA2, then GA5, then GA6.
    full = dict(agent_in_flight=1, sponsor_in_flight=2, finishing_in_flight=6)
    admit_case("switch before rate and slots", idle(agent_stop=True,
                                                    agent_seats=[25 * u, 10000], **full),
               "petition")
    admit_case("rate before slots", idle(agent_seats=[25 * u, 10000], **full), "petition")
    admit_case("lane 2: slots, not rate", idle(agent_seats=[25 * u, 10000], **full), "push")
    admit_case("STATUS under AGENT STOP, rated", idle(agent_stop=True,
                                                      agent_seats=[25 * u, 10000]), "status")
    admit_case("lanes 0, 1, 5, 6 ignore everything", idle(agent_stop=True, suspended=True,
                                                           agent_seats=[10 ** 9, 0], **full),
               "signedInUser")
    # Large numbers.
    big = 1 << 40
    admit_case("large clock and levels", idle(now=big, agent_seats=[10 ** 15, big - 10],
                                              sponsor_seats=[10 ** 15, big - 10]), "petition")
    admit_case("large clock, drained", idle(now=big, agent_seats=[10 ** 6, 0],
                                            sponsor_seats=[10 ** 6, 0]), "petition")
    admit_case("large push", idle(), "push", seats=10 ** 6)

    # A sweep: the parameter space, by a fixed generator.
    g = Lcg(20261015)
    rates = [0, 1, 7, 120, 240, 3599, 3600, 5000]
    bursts = [0, 1, 2, 20, 30]
    for i in range(300):
        tuning = {}
        if g.below(3) == 0:
            tuning["agent_seat_rate"] = g.pick(rates)
            tuning["agent_seat_burst"] = g.pick(bursts)
        if g.below(3) == 0:
            tuning["sponsor_seat_rate"] = g.pick(rates)
            tuning["sponsor_seat_burst"] = g.pick(bursts)
        if g.below(4) == 0:
            tuning["slots_per_agent"] = g.below(3)
            tuning["slots_per_sponsor"] = g.below(4)
        if g.below(4) == 0:
            tuning["retry_after_jitter"] = [g.below(50), 1 + g.below(100)]
        if g.below(4) == 0:
            tuning["slot_retry_after"] = g.pick([0, 1, 5, 7, 60, 3600])
        now = g.below(20000)

        def bucket():
            since = g.below(21000) if g.below(5) else now
            level = g.pick([0, g.below(40 * u), 20 * u - g.below(5), 30 * u + g.below(5),
                            g.below(10 ** 7)])
            return [level, since]
        state = idle(now=now, agent_stop=g.below(10) == 0, suspended=g.below(10) == 0,
                     governor_off=g.below(8) == 0,
                     agent_seats=bucket(), sponsor_seats=bucket(),
                     agent_in_flight=g.below(3) if g.below(3) == 0 else 0,
                     sponsor_in_flight=g.below(4) if g.below(3) == 0 else 0,
                     finishing_in_flight=g.below(7), starting_in_flight=g.below(6))
        if tuning:
            state["tuning"] = tuning
        kind = g.pick(SWEEP_AGENT_KINDS) if g.below(6) else g.pick(SWEEP_KINDS)
        seats = g.below(25) if g.below(4) == 0 else default_seats(kind)
        draw = (g.below(1000), 1 + g.below(1000))
        admit_case(f"sweep {i}", state, kind, seats=seats, draw=draw)

    # The pressure levels (GA4): the level's update.
    def level_case(name, use, prev, external_until=0, now=10000, tuning=None):
        t = dict(TUNING)
        t.update(tuning or {})
        r = ratio(use, t["kappa_m"])
        kept, in_force = level_step(LEVELS.index(prev), r, t, now < external_until)
        c = {"function": "level", "name": name, "use": use, "prev": prev,
             "external_until": external_until, "now": now}
        if tuning:
            c["tuning"] = tuning
        c["expected"] = {"kept": LEVELS[kept], "level": LEVELS[in_force],
                         "ratio": [r.numerator, r.denominator]}
        cases.append(c)

    def hour_use(x, kappa=Fraction(1)):
        """The hour's use, in thousandths of a CPU second, whose ratio is x exactly at
        kappa_M `kappa` (1, tuned, by default: at 1.3 no whole use gives a threshold)."""
        u = x * SIGMA * BUDGET["hour"] * 1000 / kappa
        assert u.denominator == 1
        return {"hour": int(u), "day": 0, "thirty_days": 0}
    k1 = {"kappa_m": [1, 1]}

    def tuned(**kw):
        return dict(k1, **kw)
    # r exactly at and either side of each threshold, and at each exit point.
    points = [Fraction(n, 100) for n in (0, 30, 54, 55, 56, 59, 60, 61, 69, 70, 71, 74, 75,
                                         76, 84, 85, 86, 89, 90, 91, 99, 100, 150)]
    for x in points:
        level_case(f"level from CLEAR at r {x}", hour_use(x), "CLEAR", tuning=k1)
    for prev in ("BUSY", "STRAINED", "OVERLOADED"):
        for x in (Fraction(0), Fraction(54, 100), Fraction(55, 100), Fraction(56, 100),
                  Fraction(69, 100), Fraction(70, 100), Fraction(71, 100), Fraction(84, 100),
                  Fraction(85, 100), Fraction(86, 100)):
            level_case(f"level from {prev} at r {x}", hour_use(x), prev, tuning=k1)
    # Each horizon may be the largest; kappa_M tuned.
    level_case("the day the largest", {"hour": 0, "day": 16774194, "thirty_days": 0}, "CLEAR")
    level_case("thirty days the largest", {"hour": 1000, "day": 1000,
                                           "thirty_days": 450000000}, "CLEAR")
    level_case("every horizon at once", {"hour": 2400000, "day": 15000000,
                                         "thirty_days": 450000000}, "CLEAR")
    # At kappa_M's starting value, 1.3: the whole uses either side of each threshold.
    for x in (Fraction(60, 100), Fraction(75, 100), Fraction(90, 100), Fraction(55, 100)):
        exact = x * SIGMA * BUDGET["hour"] * 1000 / Fraction(13, 10)
        for use in (math.floor(exact), math.ceil(exact)):
            level_case(f"kappa_M 1.3, hour use {use}", {"hour": use, "day": 0,
                                                        "thirty_days": 0}, "CLEAR")
            level_case(f"kappa_M 1.3, hour use {use}, from OVERLOADED",
                       {"hour": use, "day": 0, "thirty_days": 0}, "OVERLOADED")
    level_case("kappa_M 0", hour_use(Fraction(99, 100)), "STRAINED",
               tuning={"kappa_m": [0, 1]})
    level_case("a use of a thousandth", {"hour": 1, "day": 1, "thirty_days": 1}, "CLEAR")
    level_case("a large use", {"hour": 10 ** 30, "day": 0, "thirty_days": 0}, "CLEAR")
    # The external reading: in force while now is before external_until.
    for prev, x in (("CLEAR", Fraction(0)), ("CLEAR", Fraction(60, 100)),
                    ("STRAINED", Fraction(80, 100)), ("OVERLOADED", Fraction(95, 100)),
                    ("STRAINED", Fraction(60, 100)), ("BUSY", Fraction(56, 100))):
        for until, now in ((11800, 10000), (10001, 10000), (10000, 10000), (9000, 10000)):
            level_case(f"external {until} at {now} from {prev}, r {x}", hour_use(x), prev,
                       external_until=until, now=now, tuning=k1)
    # The pressure levels' readings (levels), each away from its default.
    for descent in ("ONE STEP", "BANDS"):
        for prev, x in (("OVERLOADED", Fraction(0)), ("OVERLOADED", Fraction(65, 100)),
                        ("OVERLOADED", Fraction(72, 100)), ("STRAINED", Fraction(30, 100)),
                        ("STRAINED", Fraction(55, 100)), ("BUSY", Fraction(10, 100))):
            level_case(f"descent {descent} from {prev}, r {x}", hour_use(x), prev,
                       tuning=tuned(descent=descent))
    for x in (Fraction(59, 100), Fraction(60, 100), Fraction(75, 100), Fraction(76, 100),
              Fraction(90, 100), Fraction(91, 100)):
        level_case(f"ABOVE THRESHOLD from CLEAR, r {x}", hour_use(x), "CLEAR",
                   tuning=tuned(threshold_rule="ABOVE THRESHOLD"))
    for prev, x in (("STRAINED", Fraction(70, 100)), ("OVERLOADED", Fraction(85, 100)),
                    ("BUSY", Fraction(55, 100)), ("STRAINED", Fraction(69, 100))):
        level_case(f"ABOVE THRESHOLD from {prev}, r {x}", hour_use(x), prev,
                   tuning=tuned(threshold_rule="ABOVE THRESHOLD"))
    for prev, x in (("CLEAR", Fraction(0)), ("STRAINED", Fraction(65, 100)),
                    ("STRAINED", Fraction(50, 100)), ("OVERLOADED", Fraction(95, 100)),
                    ("BUSY", Fraction(76, 100))):
        level_case(f"RAISE BEFORE from {prev}, r {x}", hour_use(x), prev,
                   external_until=11800, tuning=tuned(external_order="RAISE BEFORE"))
    level_case("RAISE BEFORE, the reading lapsed", hour_use(Fraction(65, 100)), "STRAINED",
               external_until=9000, tuning=tuned(external_order="RAISE BEFORE"))

    # GA4 in the admission: every request at every level passed.
    for lv in LEVELS:
        for k in KINDS:
            admit_case(f"{lv} {k}", idle(pressure=lv), k)
    # The order: GA2 before GA4, GA4 before GA5 and GA6.
    for lv in ("STRAINED", "OVERLOADED"):
        admit_case(f"{lv}: switch before pressure", idle(pressure=lv, agent_stop=True),
                   "petition")
        admit_case(f"{lv}: STATUS under AGENT STOP meets pressure",
                   idle(pressure=lv, agent_stop=True), "status")
        admit_case(f"{lv}: pressure before rate and slots",
                   idle(pressure=lv, agent_seats=[25 * u, 10000], **full), "petition")
        admit_case(f"{lv}: lane 2 deep in debt, slots full",
                   idle(pressure=lv, agent_seats=[25 * u, 10000], **full), "push")
    admit_case("BUSY: lane 3 passes GA4, then the rate", idle(
        pressure="BUSY", agent_seats=[25 * u, 10000]), "petition")
    admit_case("BUSY: lane 4 refused before the rate", idle(
        pressure="BUSY", agent_seats=[25 * u, 10000]), "volunteer")
    # GOVERNOR OFF skips GA4.
    for lv in ("BUSY", "OVERLOADED"):
        for k in ("petition", "volunteer", "deferrableJob", "anonymousRead", "push"):
            admit_case(f"GOVERNOR OFF at {lv}: {k}", idle(pressure=lv, governor_off=True), k)
    # GA4's Retry-After by reading (b), jittered.
    for retry in ("SLOT", "PSEUDO LAG", "BASE"):
        for lv in ("BUSY", "STRAINED", "OVERLOADED"):
            admit_case(f"Retry-After {retry} at {lv}",
                       idle(pressure=lv, tuning={"pressure_retry_after": retry}),
                       "volunteer", draw=(1, 1))
    admit_case("Retry-After tuned SLOT 31, share of a half",
               idle(pressure="STRAINED", tuning={"slot_retry_after": 31,
                                                 "retry_after_jitter": [1, 2]}),
               "deferrableJob", draw=(2, 3))
    admit_case("Retry-After PSEUDO LAG tuned", idle(
        pressure="OVERLOADED", tuning={"pressure_retry_after": "PSEUDO LAG",
                                       "pseudo_lag": [1, 2, 3, 400]}), "petition",
        draw=(999, 1000))
    admit_case("Retry-After BASE tuned", idle(
        pressure="STRAINED", tuning={"pressure_retry_after": "BASE",
                                     "retry_after_base": 120}), "petition", draw=(1, 2))
    # Lane 6 under its slots by level (7.2.24, X3), cached at OVERLOADED.
    for lv, cap in zip(LEVELS, (6, 3, 1, 0)):
        for n in sorted({0, max(cap - 1, 0), cap, cap + 1}):
            admit_case(f"lane 6 at {lv}, {n} in flight", idle(pressure=lv,
                                                              anonymous_in_flight=n),
                       "anonymousRead")
            admit_case(f"lane 6 at {lv}, {n} in flight, SLOTS", idle(
                pressure=lv, anonymous_in_flight=n, tuning={"anonymous_full": "SLOTS"}),
                "anonymousRead", draw=(1, 2))
    admit_case("lane 6, slots tuned", idle(pressure="BUSY", anonymous_in_flight=4,
                                           tuning={"anonymous_slots": [9, 5, 2, 1]}),
               "anonymousRead")
    admit_case("lane 6, slots tuned, OVERLOADED still cached", idle(
        pressure="OVERLOADED", tuning={"anonymous_slots": [9, 5, 2, 1]}), "anonymousRead")
    # The level computed from the uses inside the admission.
    for prev, x, until in (("CLEAR", Fraction(60, 100), 0), ("CLEAR", Fraction(75, 100), 0),
                           ("CLEAR", Fraction(90, 100), 0), ("OVERLOADED", Fraction(86, 100), 0),
                           ("OVERLOADED", Fraction(84, 100), 0), ("STRAINED", Fraction(70, 100), 0),
                           ("STRAINED", Fraction(69, 100), 0), ("BUSY", Fraction(56, 100), 0),
                           ("BUSY", Fraction(54, 100), 0), ("CLEAR", Fraction(0), 11800),
                           ("CLEAR", Fraction(60, 100), 11800),
                           ("STRAINED", Fraction(80, 100), 11800),
                           ("STRAINED", Fraction(80, 100), 10000)):
        for k in ("petition", "volunteer", "deferrableJob", "anonymousRead", "push"):
            admit_case(f"use r {x} from {prev}, external {until}: {k}",
                       idle(pressure=prev, use=hour_use(x), external_until=until, tuning=k1),
                       k)
    admit_case("use, ABOVE THRESHOLD at 0.75", idle(
        use=hour_use(Fraction(75, 100)), tuning=tuned(threshold_rule="ABOVE THRESHOLD")),
        "petition")
    admit_case("use, ONE STEP down from OVERLOADED", idle(
        pressure="OVERLOADED", use=hour_use(Fraction(0)), tuning=tuned(descent="ONE STEP")),
        "petition")
    admit_case("use, RAISE BEFORE", idle(
        pressure="BUSY", use=hour_use(Fraction(50, 100)), external_until=11800,
        tuning=tuned(external_order="RAISE BEFORE")), "volunteer")
    admit_case("use at kappa_M 1.3, OVERLOADED", idle(
        use={"hour": 2215385, "day": 0, "thirty_days": 0}), "petition")

    # The traffic stages (GA3): one event or one request's end.
    T0 = 100000

    def rec(**kw):
        r = fresh()
        r.update(kw)
        return r

    def tuned_t(tuning):
        t = dict(TUNING)
        t.update(tuning or {})
        return t

    def step_case(name, traffic, now, event=None, end=None, tuning=None):
        t = tuned_t(tuning)
        c = {"function": "traffic_step", "name": name, "traffic": traffic, "now": now}
        if event is not None:
            c["event"] = event
            after, raised = event_(traffic, t, event, now), False
        else:
            c["end"] = end
            after, raised = end_of(traffic, t, end, now)
        if tuning:
            c["tuning"] = tuning
        c["expected"] = {"raises": raised, "traffic": after}
        cases.append(c)
        return after

    def event_(traffic, t, e, now):
        return event(traffic, t, e, now)

    def end(kind, ending, retry_after=None):
        return {"kind": kind, "ending": ending, "retry_after": retry_after}

    def stage_case(name, traffic, now, kind, tuning=None):
        t = tuned_t(tuning)
        tr = in_force(traffic, t, now)
        c = {"function": "traffic_stage", "name": name, "traffic": traffic, "now": now,
             "kind": kind}
        if tuning:
            c["tuning"] = tuning
        c["expected"] = {"stage": tr["stage"], "breaker": breaker_wait(tr, t, now),
                         "flood": flood_wait(tr, t, kind, now),
                         "served_retry_after": served_wait(tr, t, now),
                         "backoff_violation": now < traffic["backoff_until"]}
        cases.append(c)

    EVENTS = ["REPEAT", "ERROR STREAK", "BACKOFF VIOLATION", "CAP OVERRUN"]
    # Each event from NORMAL, THROTTLED, PENALIZED and CONTAINED.
    throttled = rec(stage="THROTTLED", breaker_until=T0 + 60, trial_pending=True,
                    retry_after=60, throttled_times=[T0], last_event=T0)
    penalized = rec(stage="PENALIZED", breaker_until=T0 + 60, trial_pending=True,
                    retry_after=60, throttled_times=[T0, T0 - 100], penalized_times=[T0],
                    last_event=T0)
    contained_ = rec(stage="CONTAINED", penalized_times=[T0, T0 - 5000, T0 - 9000],
                     last_event=T0)
    for e in EVENTS:
        step_case(f"{e} from NORMAL", fresh(), T0, event=e)
        for at in (10, 3599, 3600, 7200):
            step_case(f"{e} from THROTTLED, {at} s on", throttled, T0 + at, event=e)
            step_case(f"{e} from PENALIZED, {at} s on", penalized, T0 + at, event=e)
        step_case(f"{e} on CONTAINED", contained_, T0 + 10, event=e)
    # TE3 counted: three in an hour PENALIZE, ten in 24 hours CONTAIN.
    tr = fresh()
    for i in range(12):
        tr = step_case(f"TE3 number {i + 1}, 25 minutes apart", tr, T0 + 1500 * i,
                       event="BACKOFF VIOLATION")
    tr = fresh()
    for i in range(4):
        tr = step_case(f"TE3 number {i + 1}, 31 minutes apart", tr, T0 + 1860 * i,
                       event="BACKOFF VIOLATION")
    tr = fresh()
    for i in range(11):
        tr = step_case(f"TE3 number {i + 1}, 2.5 hours apart", tr, T0 + 9000 * i,
                       event="BACKOFF VIOLATION")
    step_case("ten TE3 inside 24 hours, the oldest just out", rec(
        te3_times=[T0 - 100 * i for i in range(8)] + [T0 - 86399, T0 - 86400]), T0 + 1,
        event="BACKOFF VIOLATION")
    step_case("ten TE3 inside 24 hours exactly", rec(
        te3_times=[T0 - 100 * i for i in range(8)] + [T0 - 86398]), T0 + 1,
        event="BACKOFF VIOLATION")
    # THROTTLED twice in an hour, and the hour's edge.
    for gap in (1, 3599, 3600, 3601):
        tr = step_case(f"TE1, then TE2 {gap} s on: first", fresh(), T0, event="REPEAT")
        step_case(f"TE1, then TE2 {gap} s on: second", tr, T0 + gap, event="ERROR STREAK")
    # A third PENALIZED in 24 hours.
    for olds in ([T0 - 4000, T0 - 8000], [T0 - 4000, T0 - 86400], [T0 - 86399, T0 - 50000]):
        step_case(f"a PENALIZED after two at {[T0 - x for x in olds]} s ago",
                  rec(stage="THROTTLED", breaker_until=T0 - 100, trial_pending=True,
                      retry_after=60, throttled_times=[T0 - 200], penalized_times=olds,
                      last_event=T0 - 200), T0, event="REPEAT")
    # PENALIZED ends PENALTY HOUR after the last event.
    for at in (3599, 3600):
        step_case(f"CAP OVERRUN {at} s after PENALIZED's last event", penalized, T0 + at,
                  event="CAP OVERRUN")
        stage_case(f"PENALIZED, {at} s after the last event", penalized, T0 + at, "petition")
    step_case("PENALTY HOUR tuned to 600 s", penalized, T0 + 600, event="REPEAT",
              tuning={"penalty_hour": 600})
    # PER EVENT doubling (stages b), to the cap.
    tr = penalized
    for i in range(8):
        tr = step_case(f"PER EVENT: TE1 number {i + 1} while PENALIZED", tr, T0 + 10 * (i + 1),
                       event="REPEAT", tuning={"doubling": "PER EVENT"})
    step_case("PER EVENT: CAP OVERRUN while PENALIZED doubles", penalized, T0 + 5,
              event="CAP OVERRUN", tuning={"doubling": "PER EVENT"})
    step_case("RETRY-AFTER base above its cap", fresh(), T0, event="REPEAT",
              tuning={"retry_after_base": 5000})
    # The end of a request: the streak (TE2) and the seats GA5 never debits for a request GA6 refuses.
    for streak in (0, 18, 19):
        for ending in ("SWITCH", "TRAFFIC", "PRESSURE", "RATE", "SLOTS", "SHAPE", "FAILED",
                       "SUCCEEDED"):
            step_case(f"streak {streak}, ending {ending}", rec(streak=streak), T0,
                      end=end("petition", ending))
    for ending in ("PRESSURE", "SLOTS"):
        step_case(f"WITH FLEET: streak 19, ending {ending}", rec(streak=19), T0,
                  end=end("push", ending), tuning={"te2_causes": "WITH FLEET"})
    step_case("ERROR STREAK tuned to 1", fresh(), T0, end=end("petition", "RATE"),
              tuning={"error_streak": 1})
    step_case("ERROR STREAK tuned to 0", fresh(), T0, end=end("petition", "SUCCEEDED"),
              tuning={"error_streak": 0})
    # The trial: after the breaker's time, the next end decides.
    for ending in ("SWITCH", "TRAFFIC", "PRESSURE", "RATE", "SLOTS", "SHAPE", "FAILED",
                   "SUCCEEDED"):
        step_case(f"THROTTLED trial: {ending}", throttled, T0 + 60, end=end("petition", ending))
        step_case(f"PENALIZED trial: {ending}", penalized, T0 + 61, end=end("push", ending))
        step_case(f"THROTTLED trial, PASSED TRAFFIC: {ending}", throttled, T0 + 61,
                  end=end("petition", ending), tuning={"trial_success": "PASSED TRAFFIC"})
        step_case(f"PENALIZED trial, PER EVENT: {ending}", penalized, T0 + 61,
                  end=end("push", ending), tuning={"doubling": "PER EVENT"})
    # Inside the breaker's time: PER REFUSAL doubles at each refusal, to the cap.
    tr = penalized
    for i in range(8):
        tr = step_case(f"PER REFUSAL: refusal number {i + 1}", tr, T0 + 1 + i,
                       end=end("petition", "TRAFFIC", tr["retry_after"]))
    step_case("THROTTLED: a refusal inside the breaker keeps it", throttled, T0 + 30,
              end=end("petition", "TRAFFIC", 30))
    step_case("PENALIZED, PER EVENT: a refusal keeps the breaker", penalized, T0 + 30,
              end=end("petition", "TRAFFIC", 30), tuning={"doubling": "PER EVENT"})
    step_case("RETRY-AFTER cap tuned to 100", rec(
        stage="PENALIZED", breaker_until=T0 + 80, trial_pending=True, retry_after=80,
        penalized_times=[T0], last_event=T0), T0 + 1, end=end("petition", "TRAFFIC", 80),
        tuning={"retry_after_cap": 100})
    # The Retry-After given recorded; a CONTAINED account's answers recorded.
    for ra in (None, 0, 5, 60, 3600):
        step_case(f"a Retry-After of {ra} recorded", fresh(), T0,
                  end=end("petition", "RATE", ra))
    for kind in ("inquire", "releaseOp", "status", "heartbeat"):
        for ending in ("SUCCEEDED", "FAILED", "TRAFFIC"):
            step_case(f"CONTAINED {kind} {ending}", contained_, T0 + 100,
                      end=end(kind, ending, 60))
    # A sequence, by a fixed generator: events and ends in turn.
    g = Lcg(20261022)
    ends = ["SWITCH", "TRAFFIC", "PRESSURE", "RATE", "SLOTS", "SHAPE", "FAILED", "SUCCEEDED"]
    for run in range(4):
        tr, now = fresh(), T0
        tuning = [None, {"doubling": "PER EVENT"}, {"trial_success": "PASSED TRAFFIC",
                                                      "te2_causes": "WITH FLEET"},
                  {"error_streak": 3, "retry_after_base": 7}][run]
        for i in range(30):
            now += g.pick([0, 1, 5, 30, 61, 300, 1800, 3700])
            name = f"sequence {run} step {i}"
            if g.below(3) == 0:
                tr = step_case(name, tr, now, event=g.pick(EVENTS), tuning=tuning)
            else:
                kind = g.pick(["petition", "push", "inquire", "releaseOp", "status", "heartbeat"])
                ra = g.pick([None, None, 0, 5, 60, 120])
                tr = step_case(name, tr, now, end=end(kind, g.pick(ends), ra), tuning=tuning)
    # What GA3 reads, by stage and request.
    flooded = dict(contained_, flood_inquire=T0 + 50, flood_release=T0 - 30)
    for kind in ("petition", "status", "inquire", "releaseOp", "heartbeat"):
        for name_, tr_ in (("NORMAL", fresh()), ("THROTTLED", throttled),
                           ("PENALIZED", penalized), ("CONTAINED", flooded)):
            for at in (0, 30, 60, 100):
                stage_case(f"{name_} at +{at}: {kind}", tr_, T0 + at, kind)
    stage_case("PENALIZED, PER EVENT", penalized, T0 + 10, "petition",
               tuning={"doubling": "PER EVENT"})
    stage_case("FLOOD INTERVAL tuned to 10", flooded, T0 + 55, "inquire",
               tuning={"flood_interval": 10})
    stage_case("a TE3 at the Retry-After's last second", rec(backoff_until=T0 + 10), T0 + 9,
               "petition")
    stage_case("no TE3 at the Retry-After's end", rec(backoff_until=T0 + 10), T0 + 10,
               "petition")

    # GA3 in the admission.
    breaker_closed = dict(throttled, trial_pending=False, breaker_until=0)
    for name_, tr_ in (("NORMAL", fresh()), ("THROTTLED", throttled),
                       ("PENALIZED", penalized), ("CONTAINED", flooded),
                       ("THROTTLED, closed", breaker_closed)):
        for k in KINDS:
            admit_case(f"{name_} {k}", idle(now=T0 + 10, traffic=tr_), k, draw=(1, 2))
    for at in (59, 60, 61):
        admit_case(f"THROTTLED breaker at +{at}", idle(now=T0 + at, traffic=throttled),
                   "petition")
    for at in (3599, 3600):
        admit_case(f"PENALIZED at +{at}, halved rate", idle(
            now=T0 + at, traffic=penalized, agent_seats=[25 * u, T0 + at - 120]), "petition")
    for k in ("inquire", "releaseOp", "status"):
        for at in (49, 50, 109, 110):
            admit_case(f"CONTAINED {k} at +{at}", idle(now=T0 + at, traffic=flooded), k)
    # The order: GA2 before GA3, GA3 before GA4, GA5 and GA6.
    admit_case("AGENT STOP before CONTAINED", idle(now=T0, agent_stop=True, traffic=flooded),
               "petition")
    admit_case("CONTAINED before SUSPENDED", idle(now=T0, suspended=True, traffic=flooded),
               "petition")
    admit_case("SUSPENDED before the breaker", idle(now=T0 + 10, suspended=True,
                                                    traffic=throttled), "petition")
    admit_case("the breaker before pressure, rate and slots", idle(
        now=T0 + 10, traffic=throttled, pressure="OVERLOADED", agent_seats=[25 * u, T0], **full),
        "volunteer")
    admit_case("lane 2 under the breaker: HEARTBEAT", idle(now=T0 + 10, traffic=penalized),
               "heartbeat")
    admit_case("lane 2 under CONTAINED: HEARTBEAT", idle(now=T0 + 10, traffic=flooded),
               "heartbeat")
    # GOVERNOR OFF skips GA3; the switches stay.
    for k in ("petition", "heartbeat", "inquire", "status"):
        admit_case(f"GOVERNOR OFF, THROTTLED: {k}", idle(now=T0 + 10, governor_off=True,
                                                         traffic=throttled), k)
        admit_case(f"GOVERNOR OFF, CONTAINED: {k}", idle(now=T0 + 60, governor_off=True,
                                                         traffic=flooded), k)
    # The halved rate (stages a), the breaker closed so GA5 decides.
    pen_closed = dict(penalized, trial_pending=False, breaker_until=0)
    for payer in ("AGENT", "AGENT AND SPONSOR"):
        for el in (0, 30, 60, 120):
            admit_case(f"PENALIZED {payer}: agent full, {el} s drained", idle(
                now=T0 + 100, traffic=pen_closed, tuning={"penalized_payer": payer},
                agent_seats=[20 * u, T0 + 100 - el]), "petition")
            admit_case(f"PENALIZED {payer}: sponsor full, {el} s drained", idle(
                now=T0 + 100, traffic=pen_closed, tuning={"penalized_payer": payer},
                sponsor_seats=[30 * u, T0 + 100 - el]), "petition")
        admit_case(f"PENALIZED {payer}: a push charged at the halved rates", idle(
            now=T0 + 100, traffic=pen_closed, tuning={"penalized_payer": payer},
            agent_seats=[10 * u, T0], sponsor_seats=[10 * u, T0]), "push")
    admit_case("PENALIZED, an odd rate rounded up", idle(
        now=T0 + 100, traffic=pen_closed, tuning={"agent_seat_rate": 7},
        agent_seats=[20 * u, T0]), "petition")
    admit_case("PENALIZED, rate 1 stays 1", idle(
        now=T0 + 100, traffic=pen_closed, tuning={"agent_seat_rate": 1},
        agent_seats=[20 * u, T0 + 98]), "petition")
    # The breaker's Retry-After by reading (b), jittered.
    for doubling in ("PER REFUSAL", "PER EVENT"):
        for ra in (60, 120, 1920, 3600):
            admit_case(f"PENALIZED {doubling}, Retry-After {ra}", idle(
                now=T0 + 7, traffic=dict(penalized, retry_after=ra, breaker_until=T0 + ra),
                tuning={"doubling": doubling}), "petition", draw=(999, 1000))
    return cases


def render(cases):
    return "[\n" + ",\n".join(json.dumps(c, ensure_ascii=False) for c in cases) + "\n]\n"


def main():
    text = render(build())
    if "--check" in sys.argv[1:]:
        if OUT.read_text(encoding="utf-8") != text:
            print(f"{OUT.relative_to(ROOT)} differs from what the rules give")
            return 1
        print(f"{OUT.relative_to(ROOT)}: as the rules give")
        return 0
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
