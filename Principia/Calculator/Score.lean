import Principia.Calculator.Interface
import Principia.Score.Bounded

/-!
# Family `score`: the reliability score, the Beta layer and the user score's evidence

v1's `tpc_score` 0.1.0 (`Principia.Score`) and `tpc_beta` 0.1.0 (`Principia.Beta`), one
function each, named as v1 named it, its arguments named as v1's `run_case` names them;
`params`, which v1 read with `args.get`, may be absent or `null`, and a function v1 gave no
`params` takes none:

* the Beta layer: `beta_mean {"a", "b"}`, `beta_interval {"a", "b", "level"}`,
  `betainc {"a", "b", "x"}`, `betainc_inv {"a", "b", "p"}`, `lgamma {"x"}`, `canon {"x"}`;
* the score: `diversity_quota {"window", "counterpart", "g", "c_max"}`,
  `evidence {"events", "idle", "params"?}`, `score_interval {"S", "E", "lo", "hi"}`,
  `standing {"x", "y"}`, `rank {"accounts", "params"?}`,
  `prime_select {"accounts", "override", "params"?}`, `pending_level {"items", "now",
  "params"?}`, `state_step {"prev", "level", "event", "params"?}`,
  `peer_activity {"events", "params"?}`, `score_update {"role", "S", "E", "S_P", "a",
  "params"?}`, `violation_cut {"S", "m_class", "standing", "params"?}`,
  `trip {"S", "in_tier", "prior_ages", "params"?}`, `inquire {"state", "block", "S",
  "params"?}`, `override_check {"decl", "facts", "params"?}`, `override_effective
  {"decl_time", "now", "cancelled", "params"?}`, `override_mark {"grant", "now",
  "params"?}`, `pad_check {"decl", "facts", "params"?}`, `pad_weight {"P", "age",
  "params"?}`, `tier_gate_release {"reproducer"}`, `inherit {"F_old", "facts",
  "params"?}`, `sponsor_cut {"S", "m_class", "params"?}`;
* the user score: `user_aggregate {"agents", "sponsor", "params"?}` and
  `user_score_evidence {"agents", "conduct", "sponsor", "params"?}`, the latter ending in
  the sponsor's user evidence.

The answer is v1's text of the result (v1's `render_*` line or lines), every number in it
the exact value correctly rounded to twelve significant digits. A request v1 refused is
refused with v1's word as the detail (`BAD_ARGUMENT`), the checks made in v1's order; one
whose exact values would cross the bound on an exact value's size is refused alike, "exact
value too large" (`Principia.Score.Bounded`, each of whose answers is proved to be the plain
function's). A number whose bounds up to 4096 bits settle neither its twelve digits nor its
comparison with another (one lying on a rounding boundary, or too small for the bounds to
hold) is owed (`OWED`).

## Bounds, measured

Measured on the built binary, one request at a time, with the slowest requests found; each
bound's own comment gives its times:

* `maxWindow` window entries for the quota, `maxAccounts` accounts for RANK and the Prime
  (an insertion sort), `maxItems` pending items, `maxActivityEvents` events for the peer
  activity, `maxPriorAges` prior ages for the trip, and `maxFacts` entries in each list of
  an override's or a pad's facts.
* `maxEvents` events for `evidence`, whose sums F and A hold at most `maxTerms` powers of 2
  together: each is a term the Beta layer's bounds evaluate at every precision they try.
* `maxAgents` agents, holding `maxPooled` events in all, for the user aggregate and the
  user evidence, and `maxConduct` CONDUCT EVENTS, the user evidence's sums held to
  `maxTerms` powers of 2: each FOR event's quota is a sum over the events before it,
  compared with 0 and 1 by bounds.
* The Beta layer's incomplete function and its quantile (`betainc`, `betainc_inv`,
  `beta_interval`, and the interval of `evidence` and `user_score_evidence`): shapes from
  `minShape` to `maxShape`, a quantile's tail (`p` and `1 - p`, or `(1 - level) / 2`) at
  least `minTail`, and every number given them, and every coefficient of a shape, of at
  most `maxBetaBits` bits above and below its fraction line. Outside them the quantile's
  search can run through every precision before it is owed, for seconds or minutes; inside
  them the values the Beta layer's methods form stay well within the bound on an exact
  value. The mean, `lgamma` and `canon` take any number the reader takes.

An owed answer is given only once bounds at every precision up to 4096 bits have failed to
settle it, which takes longer than an answer: within the bounds, 8.8 s for a quantile on a
rounding boundary, and up to 6 s for an incomplete function whose exponential falls below
what the bounds hold.
-/

namespace Principia.Calculator.Score

open Principia.Canonical
open Principia.Beta
open Principia.Score

/-! ## The family's bounds, measured -/

/-- The most entries a quota's window holds: 10,000 take 0.12 s, and 0.79 s with weights of
80 digits whose exponents spread over 90 powers of ten, the sums exact. -/
def maxWindow : Nat := 10000

/-- The most accounts RANK and the Prime take: v1's insertion sort and its check that no
two accounts share a name grow with the square of their number; 2,000 in the slowest order
take 0.18 s for RANK and 0.28 s for the Prime, and 0.61 s for RANK with names of 400
characters that differ only at their ends. -/
def maxAccounts : Nat := 2000

/-- The most pending items: each counterpart is checked against those seen; 5,000 take
0.48 s, and 0.58 s with counterparts' names of 110 characters. -/
def maxItems : Nat := 5000

/-- The most events the peer activity counts: each counterpart is checked against those
seen; 5,000 take 0.15 s, and 0.22 s with names of 150 characters. -/
def maxActivityEvents : Nat := 5000

/-- The most prior ages a trip takes: 100,000 take 0.23 s. -/
def maxPriorAges : Nat := 100000

/-- The most entries each list of an override's or a pad's facts holds: the most that fit
in a request, 7,000 certified accounts and 7,000 nonces, take 0.09 s. -/
def maxFacts : Nat := 10000

/-- The most events `evidence` takes: 10,000 whose sums hold `maxTerms` powers of 2 take
1.7 s. -/
def maxEvents : Nat := 10000

/-- The most powers of 2 the sums F and A hold together once the events are aged and
summed (events aged alike share one): each is a term the Beta layer's bounds evaluate at
every precision they try. At 64, with shapes near `maxShape`, 3.0 s, the slowest found. -/
def maxTerms : Nat := 64

/-- The most agents the user aggregate and the user evidence take: each name is checked
against those before it; 1,000 take 0.03 s, and 0.12 s with names of 900 characters. -/
def maxAgents : Nat := 1000

/-- The most events the agents hold in all: each FOR event's quota sums the events before
it within a half-life and is compared with 0 and 1 by bounds, so the work grows with the
cube of their number; 30 events in the slowest arrangement found take 1.9 s for the
aggregate and 2.2 s for the user evidence (40 took 3.3 s, and 300 took 69 s). -/
def maxPooled : Nat := 30

/-- The most CONDUCT EVENTS the user evidence takes: 10,000 beside 30 pooled events, with
shapes near `maxShape`, take 3.8 s, the slowest found. -/
def maxConduct : Nat := 10000

/-- The least shape the Beta layer's incomplete function and quantile take: below it a
quantile can lie so near 0 that its search halves its bracket thousands of times, and runs
out of steps (a shape of 1/100,000 took 164 s to be owed). -/
def minShape : Rat := 1 / 10

/-- The greatest shape: above it the series grows long and the exponential of a point the
quantile's search tries far from the mean falls below what the bounds hold, so the search
runs through every precision before it is owed (shapes 30,000 and 1 took 152 s). Within
the box from `minShape` to `maxShape`, with tails of at least `minTail`, the slowest
quantile found takes 0.94 s. -/
def maxShape : Rat := 10000

/-- The least tail of a quantile: `p` and `1 - p` at least this (a tail of `10^-12` beside
a shape of 100 or more took 24 s to 34 s to be owed). -/
def minTail : Rat := 1 / 1000000

/-- The most bits of each number given to the Beta layer's incomplete function and
quantile, above and below its fraction line, and of each coefficient of a shape. -/
def maxBetaBits : Nat := 4096

/-- Refuse a list of more than `n` entries. -/
def within (what : String) (n : Nat) (len : Nat) : Except Refusal Unit :=
  if n < len then badArgument s!"{what} holds more than {n} entries (the Calculator's bound)"
  else .ok ()

/-- The number of entries of a list, `0` for anything else. -/
def entries : Value → Nat
  | .arr xs => xs.length
  | _ => 0

/-- The member `k` of an object, `null` when absent or for anything else. -/
def memberOf (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => (ms.lookup k).getD .null
  | _ => .null

/-- The events the agents of a request hold in all. -/
def pooledEvents (agents : Value) : Nat :=
  match agents with
  | .arr xs => (xs.map fun a => entries (memberOf a "events")).sum
  | _ => 0

/-- At most `maxPooled` events in all among the agents. -/
def pooledWithin (agents : Value) : Except Refusal Unit :=
  if maxPooled < pooledEvents agents then
    badArgument s!"the agents hold more than {maxPooled} events in all (the Calculator's bound)"
  else .ok ()

/-! ## Answers and refusals -/

/-- The refusal of a number the Calculator's bounds do not settle. -/
def unsettled : Refusal :=
  ⟨.owed, "a number whose bounds up to 4096 bits settle neither its twelve digits nor its comparison with another: how the Calculator answers such a number is an open choice"⟩

/-- v1's word as a refusal. -/
def lift {α : Type} : Except String α → Except Refusal α
  | .ok a => .ok a
  | .error w => badArgument w

/-- v1's word as a refusal, or owed. -/
def liftStop {α : Type} : Except Stop α → Except Refusal α
  | .ok a => .ok a
  | .error (.refused w) => badArgument w
  | .error .unsettled => .error unsettled

/-- The twelve digits of numbers, or owed. -/
def settled (qs : List Quantity) : Except Refusal (List String) :=
  match qs.mapM Quantity.twelve? with
  | some ts => .ok ts
  | none => .error unsettled

/-- A text answer. -/
def text (t : String) : Except Refusal Value := .ok (.str t)

/-- The request's members as v1's `run_case` read them: those in `needed'` must be present,
the others may be absent (`null`). -/
def read (needed' optional' : List String) (v : Value) : Except Refusal (String → Value) := do
  let ms ← membersOf (needed' ++ optional') v
  for n in needed' do
    let _ ← needed ms n
  pure fun k => (ms.lookup k).getD .null

/-! ## The Beta layer's bounds -/

/-- A number of at most `maxBetaBits` bits above and below its fraction line. -/
def bitsWithin (what : String) (q : Rat) : Except Refusal Unit :=
  if maxBetaBits < ValueBound.numBits q || maxBetaBits < ValueBound.denBits q then
    badArgument s!"{what} has more than {maxBetaBits} bits above or below its fraction line (the Calculator's bound)"
  else .ok ()

/-- Two shapes given exactly, each from `minShape` to `maxShape`. -/
def shapesWithin (a b : Rat) : Except Refusal Unit := do
  for (what, x) in [("the shape a", a), ("the shape b", b)] do
    if x < minShape || maxShape < x then
      badArgument s!"{what} lies outside 0.1 to 10000 (the Calculator's bound)"
    bitsWithin what x

/-- A quantile's tail, `p` and `1 - p` each at least `minTail`. -/
def tailWithin (what : String) (p : Rat) : Except Refusal Unit :=
  if p < minTail || 1 - minTail < p then
    badArgument s!"{what} lies within 0.000001 of 0 or 1 (the Calculator's bound)"
  else .ok ()

/-- A shape given as a sum of powers of 2 (the evidence's `a0 + F`), from `minShape` to
`maxShape`, each coefficient of at most `maxBetaBits` bits; the comparisons are owed when
bounds do not settle them. -/
def shapeWithin (what : String) (x : PowSum) : Except Refusal Unit := do
  let (nb, db) := x.bits
  if maxBetaBits < nb || maxBetaBits < db then
    badArgument s!"{what} has a coefficient of more than {maxBetaBits} bits above or below its fraction line (the Calculator's bound)"
  let lo ← lift (Score.Bounded.PowSum.sub x (PowSum.ofRat minShape))
  let hi ← lift (Score.Bounded.PowSum.sub (PowSum.ofRat maxShape) x)
  match lo.sign?, hi.sign? with
  | some s, some t =>
    if s < 0 || t < 0 then badArgument s!"{what} lies outside 0.1 to 10000 (the Calculator's bound)"
  | _, _ => .error unsettled

/-- The sums F and A of at most `maxTerms` powers of 2 together. -/
def termsWithin (what : String) (f a : PowSum) : Except Refusal Unit :=
  if maxTerms < f.terms.length + a.terms.length then
    badArgument s!"{what} hold more than {maxTerms} powers of 2 together (the Calculator's bound)"
  else .ok ()

/-- A number argument v1's checks have taken. -/
def numberOf (v : Value) : Rat := (numberOf? v).getD 0

/-! ## v1's text -/

/-- v1's `_esc`: `|` and `\` escaped with a backslash, control characters as `\xHH`. -/
def esc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '|' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      "\\x" ++ String.ofList [Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
    else c.toString)

/-- v1's `_b`. -/
def bool (b : Bool) : String := if b then "true" else "false"

/-- A wire word. -/
def wire {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a

/-- A rational's twelve-digit form. -/
def rat (q : Rat) : String := Quantity.ratText q

/-- v1's `render_rank`. -/
def rankText (r : Rank) : String :=
  "\n".intercalate (s!"rank|{r.count}|{r.cut}" :: r.rows.map fun row =>
    match row.place with
    | none => s!"row|{esc row.name}|-|-|false"
    | some (pos, pct) => s!"row|{esc row.name}|{pos}|{rat pct}|{bool row.tier}")

/-- A declared grant refused, as v1 writes it. -/
def refusalText (r : DeclRefusal) : String := "REFUSED|" ++ wire r

/-- v1's `render_gate`. -/
def gateText : GateAnswer → String
  | .pass => "PASS|TIER"
  | .notInTier => "REFUSED|NOT IN TIER"
  | .overrideMark => "REFUSED|OVERRIDE MARK"

/-- v1's `render_evidence` and `render_user_evidence`: F, A, n, E and its interval. -/
def posteriorText (f a : PowSum) (n : Nat) (e lo hi : Quantity) : Except Refusal (List String) := do
  match ← settled [f.toQuantity, a.toQuantity, e, lo, hi] with
  | [f, a, e, lo, hi] => pure [f, a, toString n, e, lo, hi]
  | _ => .error unsettled

/-! ## The functions -/

/-- The family's functions. -/
def calls : Family := [
  ("beta_interval", fun v => do
    let g ← read ["a", "b", "level"] [] v
    let (a, b, l) ← lift (betaIntervalArgs (g "a") (g "b") (g "level"))
    shapesWithin a b
    bitsWithin "the level" l
    if (1 - l) / 2 < minTail then
      badArgument "the level lies above 0.999998 (the Calculator's bound)"
    let (lo, hi) ← lift (Score.Bounded.betaInterval (g "a") (g "b") (g "level"))
    text ("|".intercalate (← settled [lo, hi]))),
  ("beta_mean", fun v => do
    let g ← read ["a", "b"] [] v
    text (rat (← lift (Score.Bounded.betaMean (g "a") (g "b"))))),
  ("betainc", fun v => do
    let g ← read ["a", "b", "x"] [] v
    let q ← lift (betaincOf (g "a") (g "b") (g "x"))
    if let .bounds _ := q then
      shapesWithin (numberOf (g "a")) (numberOf (g "b"))
      bitsWithin "x" (numberOf (g "x"))
    text (String.join (← settled [q]))),
  ("betainc_inv", fun v => do
    let g ← read ["a", "b", "p"] [] v
    let q ← lift (betaincInv (g "a") (g "b") (g "p"))
    if let .bounds _ := q then
      shapesWithin (numberOf (g "a")) (numberOf (g "b"))
      bitsWithin "p" (numberOf (g "p"))
      tailWithin "p" (numberOf (g "p"))
    text (String.join (← settled [q]))),
  ("canon", fun v => do
    let g ← read ["x"] [] v
    text (rat (← lift (canonOf (g "x"))))),
  ("diversity_quota", fun v => do
    let g ← read ["window", "counterpart", "g", "c_max"] [] v
    within "window" maxWindow (entries (g "window"))
    let r ← lift (Score.Bounded.diversityQuota (g "window") (g "counterpart") (g "g") (g "c_max"))
    text ("|".intercalate [rat r.q, rat r.w, rat r.wc, rat r.admitted])),
  ("evidence", fun v => do
    let g ← read ["events", "idle"] ["params"] v
    within "events" maxEvents (entries (g "events"))
    let (r, sa, sb) ← lift (Score.Bounded.evidence (g "events") (g "idle") (g "params"))
    termsWithin "F and A" r.f r.a
    shapeWithin "a0 + F" sa
    shapeWithin "b0 + A" sb
    text ("|".intercalate ((← posteriorText r.f r.a r.n r.e r.lo r.hi) ++ [rat r.factor]))),
  ("inherit", fun v => do
    let g ← read ["F_old", "facts"] ["params"] v
    let (f, s, c) ← lift (Score.Bounded.inherit (g "F_old") (g "facts") (g "params"))
    text s!"{rat f}|{rat s}|{bool c}"),
  ("inquire", fun v => do
    let g ← read ["state", "block", "S"] ["params"] v
    let r ← lift (Score.Bounded.inquire (g "state") (g "block") (g "S") (g "params"))
    text ("|".intercalate [(match r.cost with | none => "inf" | some c => rat c), rat r.s,
      toString r.k, bool r.inside, toString r.last, toString r.k])),
  ("lgamma", fun v => do
    let g ← read ["x"] [] v
    text (String.join (← settled [← lift (lgammaOf (g "x"))]))),
  ("override_check", fun v => do
    let g ← read ["decl", "facts"] ["params"] v
    for k in ["certified", "suspended", "nonces"] do
      within k maxFacts (entries (memberOf (g "facts") k))
    match ← lift (overrideCheck (g "decl") (g "facts") (g "params")) with
    | .error why => text (refusalText why)
    | .ok o => text (s!"OK|{rat o.value}|{o.effective}|{o.sunset}|" ++ o.replaces.getD "-")),
  ("override_effective", fun v => do
    let g ← read ["decl_time", "now", "cancelled"] ["params"] v
    text (wire (← lift (overrideEffective (g "decl_time") (g "now") (g "cancelled") (g "params"))))),
  ("override_mark", fun v => do
    let g ← read ["grant", "now"] ["params"] v
    let (f, n) ← lift (overrideMark (g "grant") (g "now") (g "params"))
    text s!"{bool f}|{n}"),
  ("pad_check", fun v => do
    let g ← read ["decl", "facts"] ["params"] v
    for k in ["certified", "suspended", "nonces"] do
      within k maxFacts (entries (memberOf (g "facts") k))
    match ← lift (padCheck (g "decl") (g "facts") (g "params")) with
    | .error why => text (refusalText why)
    | .ok o =>
      text (s!"OK|{o.value}|{o.effective}|{bool o.mark}|" ++
        (match o.sunset with | none => "-" | some n => toString n))),
  ("pad_weight", fun v => do
    let g ← read ["P", "age"] ["params"] v
    let w ← lift (Score.Bounded.padWeight (g "P") (g "age") (g "params"))
    text (String.join (← settled [w.toQuantity]))),
  ("peer_activity", fun v => do
    let g ← read ["events"] ["params"] v
    within "events" maxActivityEvents (entries (g "events"))
    let (n, x) ← lift (peerActivity (g "events") (g "params"))
    text s!"{n}|{rat x}"),
  ("pending_level", fun v => do
    let g ← read ["items", "now"] ["params"] v
    within "items" maxItems (entries (g "items"))
    let r ← lift (pendingLevel (g "items") (g "now") (g "params"))
    text ("|".intercalate [wire r.level, toString r.h, toString r.i, toString r.sim,
      toString r.low, toString r.counted, toString r.expired])),
  ("prime_select", fun v => do
    let g ← read ["accounts", "override"] ["params"] v
    within "accounts" maxAccounts (entries (g "accounts"))
    let (p, why) ← lift (Score.Bounded.primeSelect (g "accounts") (g "override") (g "params"))
    text ((match p with | none => "-" | some n => esc n) ++ "|" ++ wire why)),
  ("rank", fun v => do
    let g ← read ["accounts"] ["params"] v
    within "accounts" maxAccounts (entries (g "accounts"))
    text (rankText (← lift (Score.Bounded.rank (g "accounts") (g "params"))))),
  ("score_interval", fun v => do
    let g ← read ["S", "E", "lo", "hi"] [] v
    let (l, h) ← lift (Score.Bounded.scoreInterval (g "S") (g "E") (g "lo") (g "hi"))
    text (rat l ++ "|" ++ rat h)),
  ("score_update", fun v => do
    let g ← read ["role", "S", "E", "S_P", "a"] ["params"] v
    let r ← lift (Score.Bounded.scoreUpdate (g "role") (g "S") (g "E") (g "S_P") (g "a") (g "params"))
    text ("|".intercalate [rat r.s, rat r.target, rat r.k, rat r.step, bool r.clipped])),
  ("sponsor_cut", fun v => do
    let g ← read ["S", "m_class"] ["params"] v
    text (rat (← lift (Score.Bounded.sponsorCut (g "S") (g "m_class") (g "params"))))),
  ("standing", fun v => do
    let g ← read ["x", "y"] [] v
    text (wire (← lift (standing (g "x") (g "y"))))),
  ("state_step", fun v => do
    let g ← read ["prev", "level", "event"] ["params"] v
    let r ← lift (stateStep (g "prev") (g "level") (g "event") (g "params"))
    text s!"{wire r.state}|{r.passes}|{wire r.change}"),
  ("tier_gate_release", fun v => do
    let g ← read ["reproducer"] [] v
    text (gateText (← lift (tierGateRelease (g "reproducer"))))),
  ("trip", fun v => do
    let g ← read ["S", "in_tier", "prior_ages"] ["params"] v
    within "prior_ages" maxPriorAges (entries (g "prior_ages"))
    let (t, why) ← lift (trip (g "S") (g "in_tier") (g "prior_ages") (g "params"))
    text ((if t then "TRIP" else "PICKUP") ++ "|" ++ wire why)),
  ("user_aggregate", fun v => do
    let g ← read ["agents", "sponsor"] ["params"] v
    within "agents" maxAgents (entries (g "agents"))
    pooledWithin (g "agents")
    match ← liftStop (Score.Bounded.userAggregate (g "agents") (g "sponsor") (g "params")) with
    | .none => text "aggregate|NONE"
    | .pooled evs =>
      let ts ← settled (evs.map (·.weight.toQuantity))
      text ("\n".intercalate ("aggregate|OK" :: (evs.zip ts).map fun (e, t) =>
        s!"event|{wire e.side}|{t}|{e.age}"))),
  ("user_score_evidence", fun v => do
    let g ← read ["agents", "conduct", "sponsor"] ["params"] v
    within "agents" maxAgents (entries (g "agents"))
    pooledWithin (g "agents")
    within "conduct" maxConduct (entries (g "conduct"))
    match ← liftStop (Score.Bounded.scoreUserEvidence (g "agents") (g "conduct") (g "sponsor")
        (g "params")) with
    | none => text "NONE"
    | some (r, sa, sb) =>
      termsWithin "F_u and A_u" r.f r.a
      shapeWithin "a0 + F_u" sa
      shapeWithin "b0 + A_u" sb
      text ("|".intercalate ("OK" :: (← posteriorText r.f r.a r.n r.e r.lo r.hi)))),
  ("violation_cut", fun v => do
    let g ← read ["S", "m_class", "standing"] ["params"] v
    let r ← lift (Score.Bounded.violationCut (g "S") (g "m_class") (g "standing") (g "params"))
    text ("|".intercalate [rat r.s, rat r.m, rat r.aInc])),
]

end Principia.Calculator.Score
