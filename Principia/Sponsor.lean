import Principia.Score

/-!
# The sponsor: its conduct events, the user evidence and the whitewash count

v1's `tpc_sponsor` 0.1.0 (DRAFT; the identity speculation 0.1.0 SM-1 to SM-3
and section 8; PMP-TPM 0.12.0 AI CERTIFICATION CR12; the tuning
options `g_C`, `h_C` and SUCCESSION WINDOW): the sponsor's CONDUCT EVENTS, the user
evidence `E_u` with its interval and `n_u`, and the WHITEWASH count. Each function is v1's,
with its argument checks, its refusal words and their order, and its rules as v1's
docstring states them (CR-F1, CR-F2, the five audit and removal rules; UE1 to UE4; the whitewash rules WC1, WC2).

* `conductResolve(event, facts)`: a CONDUCT EVENT's resolution, FOR, AGAINST, NEUTRAL or
  PENDING, with its reason, from the counted facts or the audit's finding its kind needs
  "Each is a counted fact or an audit finding; none resolves AGAINST on a
  statistic"; "a PENDING item updates nothing". The 100-block windows are the rule's own
  figures (`windowBlocks`), not parameters.
* `userEvidence(events, ages, g, h, a0, b0, half_life)`: the resolved events of both parts
  (the sponsor's CONDUCT EVENTS, weighted by `g` or `h`, and the pooled agent events with
  their own weights), each aged by `2^(-age / half_life)` (UE1), summed into `F_u` and `A_u`
  (UE2), counted into `n_u` (UE3), and the mean and the 95 per cent equal-tailed interval of
  `Beta(a0 + F_u, b0 + A_u)` (UE4).
* `whitewashCount(admissions, retirements, states, window)`: the admissions that count as
  WHITEWASH events (WC1, WC2).

**Numbers** (the Declarer's choice of exact values): every number is the exact value. The weights are read as
the decimals they spell, each aged weight `w 2^(-age / half_life)` is an exact sum of
rational multiples of powers of 2 (`Principia.Score.PowSum`), and so are `F_u` and `A_u`;
the mean and the interval are the Beta layer's (`Principia.Beta`), the mean exactly when it
is rational and otherwise, with the interval's ends, between bounds narrowed until twelve
digits settle. v1 computed in doubles and printed twelve digits; on its corpus and on the
score's `user_evidence` cases no printed number differs from the exact value's.

**The user score's evidence.** v1's `tpc_score.user_score_evidence` pools its agents'
events and hands them, with the sponsor's CONDUCT EVENTS, to `user_evidence`
(`Principia.Score.userScoreEvidence` gives that call's input, `SponsorInput`);
`evidenceOfInput` makes the call and `scoreUserEvidence` is v1's function whole.

Nothing here needs SHA-256 or Unicode's tables: v1 compares agent names byte for byte and
puts no text in NFC.

Corpus: the sponsor corpus (83 cases), run by the sponsor vector tests; and the 20
`user_evidence` cases of the score corpus, run by the score vector tests.
-/

namespace Principia.Sponsor

open Principia.Canonical
open Principia.Beta
open Principia.Score

/-! ## Words -/

/-- A CONDUCT EVENT's kind: two FOR kinds and five AGAINST kinds. -/
inductive ConductKind where
  /-- CE-F1, PROACTIVE SUCCESSION. -/
  | f1
  /-- CE-F2, DECLARED CHANGE KEPT CLEAN. -/
  | f2
  /-- UNDECLARED PROMPT CHANGE, found by audit. -/
  | a1
  /-- UNDECLARED MODEL OR FAMILY CHANGE, found by audit. -/
  | a2
  /-- FALSE DECLARATION, found by audit. -/
  | a3
  /-- WHITEWASH. -/
  | a4
  /-- REMOVAL FOR CAUSE. -/
  | a5
  deriving DecidableEq, Repr, Inhabited

instance : WireWord ConductKind where
  members := [.f1, .f2, .a1, .a2, .a3, .a4, .a5]
  toWire
    | .f1 => "CE-F1"
    | .f2 => "CE-F2"
    | .a1 => "CE-A1"
    | .a2 => "CE-A2"
    | .a3 => "CE-A3"
    | .a4 => "CE-A4"
    | .a5 => "CE-A5"
  read_toWire a := by cases a <;> decide

/-- v1's `FOR_KINDS`. -/
def forKinds : List ConductKind := [.f1, .f2]

/-- v1's `AGAINST_KINDS`. -/
def againstKinds : List ConductKind := [.a1, .a2, .a3, .a4, .a5]

/-- The side a resolved event of the kind falls on: FOR for CE-F1 and CE-F2, AGAINST for
the others. -/
def ConductKind.side : ConductKind → Side
  | .f1 | .f2 => .supporting
  | _ => .opposing

/-- A CONDUCT EVENT's resolution. -/
inductive Resolution where
  /-- FOR -/
  | supporting
  /-- AGAINST -/
  | opposing
  /-- NEUTRAL: resolved, carrying no evidence. -/
  | neutral
  /-- PENDING: not resolved yet; it updates nothing. -/
  | pending
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Resolution where
  members := [.supporting, .opposing, .neutral, .pending]
  toWire
    | .supporting => "FOR"
    | .opposing => "AGAINST"
    | .neutral => "NEUTRAL"
    | .pending => "PENDING"
  read_toWire a := by cases a <;> decide

/-- Why a CONDUCT EVENT resolved as it did. -/
inductive Reason where
  | clean
  | window
  | notNamed
  | predecessor
  | period
  | violation
  | notDeclared
  | canary
  | audit
  | dismissed
  | outsideWindow
  | green
  | whitewash
  | trip
  | decisionItem
  | notForCause
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Reason where
  members := [.clean, .window, .notNamed, .predecessor, .period, .violation, .notDeclared,
    .canary, .audit, .dismissed, .outsideWindow, .green, .whitewash, .trip, .decisionItem,
    .notForCause]
  toWire
    | .clean => "CLEAN"
    | .window => "WINDOW"
    | .notNamed => "NOT NAMED"
    | .predecessor => "PREDECESSOR"
    | .period => "PERIOD"
    | .violation => "VIOLATION"
    | .notDeclared => "NOT DECLARED"
    | .canary => "CANARY"
    | .audit => "AUDIT"
    | .dismissed => "DISMISSED"
    | .outsideWindow => "OUTSIDE WINDOW"
    | .green => "GREEN"
    | .whitewash => "WHITEWASH"
    | .trip => "TRIP"
    | .decisionItem => "DECISION ITEM"
    | .notForCause => "NOT FOR CAUSE"
  read_toWire a := by cases a <;> decide

/-- The state of an audit block (the three audit kinds). -/
inductive AuditState where
  /-- OPEN -/
  | opened
  /-- CONFIRMED -/
  | confirmed
  /-- DISMISSED -/
  | dismissed
  deriving DecidableEq, Repr, Inhabited

instance : WireWord AuditState where
  members := [.opened, .confirmed, .dismissed]
  toWire
    | .opened => "OPEN"
    | .confirmed => "CONFIRMED"
    | .dismissed => "DISMISSED"
  read_toWire a := by cases a <;> decide

/-- The cause of an agent's removal (REMOVAL FOR CAUSE). -/
inductive RemovalCause where
  | canary
  | trip
  | other
  deriving DecidableEq, Repr, Inhabited

instance : WireWord RemovalCause where
  members := [.canary, .trip, .other]
  toWire
    | .canary => "CANARY"
    | .trip => "TRIP"
    | .other => "OTHER"
  read_toWire a := by cases a <;> decide

/-! ## Shared rules -/

/-- The 100-block windows of CE-F1 and CE-F2, the rule's own figure. -/
def windowBlocks : Nat := 100

/-- An agent's standing at a retirement, a lapse or an admission: its state and its count
of PENDING items. -/
structure AgentStatus where
  state : AlertState
  pending : Nat
  deriving DecidableEq, Repr

/-- Not GREEN, or with a PENDING item: the condition CE-F1 refuses in a predecessor and
WHITEWASH counts in the agent that left. -/
def AgentStatus.troubled (s : AgentStatus) : Bool := !(s.state == .green && s.pending == 0)

/-- `|a - b|`, two times in seconds. -/
def gap (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- The whitewash test: the admission and the exit lie within the window of each other, on either
side, the window closed at both ends (PD-OC-9). -/
def within (admission exit window : Nat) : Bool := gap admission exit ≤ window

/-! ## conduct_resolve -/

/-- What a resolution says: the resolution and its reason. -/
abbrev Resolved := Resolution × Reason

/-- CR-F1, PROACTIVE SUCCESSION: not named, a predecessor not GREEN or with a PENDING item,
or the RATING PERIOD's CE-F1 taken: NEUTRAL; a confirmed violation at a block up to and
including 100: NEUTRAL; at least 100 blocks with none: FOR; otherwise PENDING. -/
def successionOf (named : Bool) (predecessor : Option AgentStatus) (blocks : Nat)
    (violation : Option Nat) (periodTaken : Bool) : Resolved :=
  if !named then (.neutral, .notNamed)
  else if predecessor.any (·.troubled) then (.neutral, .predecessor)
  else if periodTaken then (.neutral, .period)
  else if violation.any (· ≤ windowBlocks) then (.neutral, .violation)
  else if windowBlocks ≤ blocks then (.supporting, .clean)
  else (.pending, .window)

/-- CR-F2, DECLARED CHANGE KEPT CLEAN: not declared: NEUTRAL (an undeclared change is
the matter of UNDECLARED PROMPT CHANGE); a canary failure or a confirmed violation at a block up to 100: NEUTRAL;
at least 100 blocks with neither: FOR; otherwise PENDING. -/
def changeOf (declared : Bool) (blocks : Nat) (violation canary : Option Nat) : Resolved :=
  if !declared then (.neutral, .notDeclared)
  else if canary.any (· ≤ windowBlocks) then (.neutral, .canary)
  else if violation.any (· ≤ windowBlocks) then (.neutral, .violation)
  else if windowBlocks ≤ blocks then (.supporting, .clean)
  else (.pending, .window)

/-- The three audit kinds: the audit block's state; no statistic enters. -/
def auditOf : AuditState → Resolved
  | .confirmed => (.opposing, .audit)
  | .opened => (.pending, .audit)
  | .dismissed => (.neutral, .dismissed)

/-- WHITEWASH: admitted within the window of the retirement or lapse of another agent
of the sponsor that was then not GREEN or had a PENDING item: AGAINST, counted at the
admission; otherwise NEUTRAL; never PENDING. -/
def whitewashOf (admission exit : Nat) (left : AgentStatus) (window : Nat) : Resolved :=
  if !within admission exit window then (.neutral, .outsideWindow)
  else if !left.troubled then (.neutral, .green)
  else (.opposing, .whitewash)

/-- REMOVAL FOR CAUSE: removed after a canary failure or a trip: AGAINST (the SPONSOR
CUT is applied at once by TPX, outside this function); removed otherwise: NEUTRAL; not
removed: PENDING (the decision item open). -/
def removalOf (removed : Bool) (cause : Option RemovalCause) : Resolved :=
  if !removed then (.pending, .decisionItem)
  else match cause with
    | some .canary => (.opposing, .canary)
    | some .trip => (.opposing, .trip)
    | _ => (.neutral, .notForCause)

/-- v1 `_opt_block`: `null`, or a 1-based block number up to COUNT_MAX. -/
def optBlock? : Canonical.Value → Option (Option Nat)
  | .null => some none
  | v => (intIn? v 1 countMax).map (some ∘ natOf)

/-- v1 `_state_ok`: `{state, pending}`, a state of CR11's and a count. -/
def statusOf? (v : Canonical.Value) : Option AgentStatus := do
  let ms ← keysAre? v ["state", "pending"]
  let s ← match member ms "state" with
    | .str s => WireWord.ofWire? s
    | _ => none
  let p ← intIn? (member ms "pending") 0 countMax
  return ⟨s, natOf p⟩

/-- A word of an enumeration, `none` for anything else. -/
def word? (α : Type) [WireWord α] : Canonical.Value → Option α
  | .str s => WireWord.ofWire? s
  | _ => none

/-- v1 `conduct_resolve(event, facts)`. -/
def conductResolve (event facts : Canonical.Value) : Except String Resolved := do
  let ems ← need (keysAre? event ["kind"]) "event"
  let kind ← need (word? ConductKind (member ems "kind")) "event"
  match kind with
  | .f1 =>
    let ms ← need (keysAre? facts ["named", "predecessor", "blocks", "first_violation_block",
      "period_taken"]) "facts"
    let named ← need (boolOf? (member ms "named")) "facts"
    let taken ← need (boolOf? (member ms "period_taken")) "facts"
    let blocks ← need (intIn? (member ms "blocks") 0 countMax) "facts"
    let v ← need (optBlock? (member ms "first_violation_block")) "facts"
    let pred ← match member ms "predecessor" with
      | .null => pure none
      | p => some <$> need (statusOf? p) "facts"
    return successionOf named pred (natOf blocks) v taken
  | .f2 =>
    let ms ← need (keysAre? facts ["declared", "blocks", "first_violation_block",
      "first_canary_failure_block"]) "facts"
    let declared ← need (boolOf? (member ms "declared")) "facts"
    let blocks ← need (intIn? (member ms "blocks") 0 countMax) "facts"
    let v ← need (optBlock? (member ms "first_violation_block")) "facts"
    let c ← need (optBlock? (member ms "first_canary_failure_block")) "facts"
    return changeOf declared (natOf blocks) v c
  | .a1 | .a2 | .a3 =>
    let ms ← need (keysAre? facts ["audit"]) "facts"
    return auditOf (← need (word? AuditState (member ms "audit")) "facts")
  | .a4 =>
    let ms ← need (keysAre? facts ["admission", "exit", "state", "pending", "window"]) "facts"
    let adm ← need (intIn? (member ms "admission") 0 timeMax) "facts"
    let exit ← need (intIn? (member ms "exit") 0 timeMax) "facts"
    let st ← need (word? AlertState (member ms "state")) "facts"
    let pending ← need (intIn? (member ms "pending") 0 countMax) "facts"
    let window ← need (intIn? (member ms "window") 0 timeMax) "facts"
    return whitewashOf (natOf adm) (natOf exit) ⟨st, natOf pending⟩ (natOf window)
  | .a5 =>
    let ms ← need (keysAre? facts ["removed", "cause"]) "facts"
    let removed ← need (boolOf? (member ms "removed")) "facts"
    let cause ← match member ms "cause" with
      | .null => pure none
      | c => some <$> need (word? RemovalCause c) "facts"
    return removalOf removed cause

/-! ## user_evidence -/

/-- A resolved event as UE1 to UE3 take it: its side (none for NEUTRAL), its base weight
and its age in the sponsor's agents' landed blocks. -/
structure Weighed where
  side : Option Side
  weight : PowSum
  age : Nat
  deriving Repr

/-- UE1: the event's weight aged by `2^(-age / half_life)`, exactly. -/
def Weighed.aged (halfLife : Rat) (x : Weighed) : PowSum :=
  PowSum.mulPow2 (-(x.age : Rat) / halfLife) x.weight

/-- UE2: the sum of the aged weights of the events on one side. -/
def sideSum (events : List Weighed) (s : Side) (halfLife : Rat) : PowSum :=
  (events.filter (·.side == some s)).foldl (fun acc x => PowSum.add acc (x.aged halfLife))
    PowSum.zero

/-- UE3: the FOR and AGAINST events; a NEUTRAL event is resolved but not counted
(PD-OC-10). -/
def counted (events : List Weighed) : Nat := (events.filter (·.side.isSome)).length

/-- The user evidence: `F_u`, `A_u`, `n_u`, `E_u` and its interval. -/
structure Posterior where
  f : PowSum
  a : PowSum
  n : Nat
  e : Quantity
  lo : Quantity
  hi : Quantity

/-- UE1 to UE4. -/
def posteriorOf (events : List Weighed) (a0 b0 halfLife : Rat) : Posterior :=
  let f := sideSum events .supporting halfLife
  let a := sideSum events .opposing halfLife
  let sa := PowSum.add (PowSum.ofRat a0) f
  let sb := PowSum.add (PowSum.ofRat b0) a
  let (lo, hi) := interval sa.toQuantity sb.toQuantity (95 / 100)
  ⟨f, a, counted events, PowSum.ratio sa (PowSum.add sa sb), lo, hi⟩

/-- An event's weight as given: absent (`none`), or present, with its value when it is a
number at least 0 (v1 `_num`) and `none` when it is not. -/
abbrev WeightIn := Option (Option PowSum)

/-- One event's side and base weight (v1's loop past the age): an agent event (kind
`AGENT`) FOR or AGAINST with its own weight at least 0; a CONDUCT EVENT with no weight,
resolved on its kind's side or NEUTRAL, weighted by `g` or `h` (`weightOf`). Anything else,
a PENDING event among them, is refused (`events`). -/
def weigh (weightOf : ConductKind → Rat) (kind resolution : Canonical.Value) (weight : WeightIn) :
    Except String (Option Side × PowSum) :=
  match kind with
  | .str "AGENT" =>
    match word? Side resolution, weight with
    | some s, some (some w) => .ok (some s, w)
    | _, _ => .error "events"
  | k =>
    match word? ConductKind k, word? Resolution resolution, weight with
    | some c, some .neutral, none => .ok (none, PowSum.ofRat (weightOf c))
    | some c, some .supporting, none =>
      if c.side == .supporting then .ok (some .supporting, PowSum.ofRat (weightOf c)) else .error "events"
    | some c, some .opposing, none =>
      if c.side == .opposing then .ok (some .opposing, PowSum.ofRat (weightOf c)) else .error "events"
    | _, _, _ => .error "events"

/-- v1 `_check_weights`: an object with exactly the kinds as keys, each a number at least
0 (`weights`). -/
def readWeights (v : Canonical.Value) (kinds : List ConductKind) :
    Except String (List (ConductKind × Rat)) := do
  let ms ← need (keysAre? v (kinds.map WireWord.toWire)) "weights"
  kinds.mapM fun k => do
    let w ← need (numberOf? (member ms (WireWord.toWire k))) "weights"
    check (0 ≤ w) "weights"
    return (k, w)

/-- The weight table `g` and `h` give a kind. -/
def weightTable (g h : List (ConductKind × Rat)) (k : ConductKind) : Rat :=
  ((g ++ h).lookup k).getD 0

/-- PRIOR `a0, b0 > 0` (`prior`) and `half_life > 0` (`half_life`). -/
def readPriorOf (a0 b0 halfLife : Option Rat) : Except String (Rat × Rat × Rat) := do
  let a ← need a0 "prior"
  let b ← need b0 "prior"
  check (0 < a && 0 < b) "prior"
  let hl ← need halfLife "half_life"
  check (0 < hl) "half_life"
  return (a, b, hl)

/-- Version 1's `user_evidence`'s checks of its arguments, in its order: the events, each
weighed but not yet aged, and `a0`, `b0` and the half-life. -/
def readEvidence (events ages g h a0 b0 halfLife : Canonical.Value) :
    Except String (List Weighed × Rat × Rat × Rat) := do
  let es ← listOf events "events"
  let as ← listOf ages "events"
  check (es.length == as.length) "events"
  let gw ← readWeights g forKinds
  let hw ← readWeights h againstKinds
  let (a0, b0, hl) ← readPriorOf (numberOf? a0) (numberOf? b0) (numberOf? halfLife)
  let ws ← (es.zip as).mapM fun (e, age) => do
    let ms ← need (keysAre? e ["kind", "resolution"] ["weight"]) "events"
    let age ← need (intIn? age 0 countMax) "ages"
    let weight : WeightIn := (ms.lookup "weight").map fun w =>
      (numberOf? w).bind fun q => if 0 ≤ q then some (PowSum.ofRat q) else none
    let (side, w) ← weigh (weightTable gw hw) (member ms "kind") (member ms "resolution") weight
    return (⟨side, w, natOf age⟩ : Weighed)
  return (ws, a0, b0, hl)

/-- v1 `user_evidence(events, ages, g, h, a0, b0, half_life)`. -/
def userEvidence (events ages g h a0 b0 halfLife : Canonical.Value) : Except String Posterior := do
  let (ws, a0, b0, hl) ← readEvidence events ages g h a0 b0 halfLife
  return posteriorOf ws a0 b0 hl

/-- v1's call `user_evidence(events, ages, g_C, h_C, a0, b0, HALF-LIFE)` at the end of
`tpc_score.user_score_evidence`, on the input the score's port gives: the pooled agent
events (kind `AGENT`, each with its weight), then the CONDUCT EVENTS as given (`kind`,
`resolution`, no weight), with their ages, which the score has checked. -/
def evidenceOfInput (input : SponsorInput) : Except String Posterior := do
  let gw ← readWeights input.gC forKinds
  let hw ← readWeights input.hC againstKinds
  let (a0, b0, hl) ← readPriorOf (some input.a0) (some input.b0) (some input.halfLife)
  let agents := input.agentEvents.map fun e =>
    ((Canonical.Value.str "AGENT", Canonical.Value.str (WireWord.toWire e.side),
      (some (some e.weight) : WeightIn)), e.age)
  let conduct := input.conduct.map fun (k, r, age) => ((k, r, (none : WeightIn)), age)
  let ws ← (agents ++ conduct).mapM fun ((k, r, w), age) => do
    let (side, w) ← weigh (weightTable gw hw) k r w
    return (⟨side, w, age⟩ : Weighed)
  return posteriorOf ws a0 b0 hl

/-- v1 `tpc_score.user_score_evidence(agents, conduct, sponsor, params)`, whole: NONE
(`none`) when the user aggregate is; otherwise the user evidence of the pooled events and
the CONDUCT EVENTS. -/
def scoreUserEvidence (agents conduct sponsor params : Canonical.Value) :
    Except Stop (Option Posterior) := do
  match ← userScoreEvidence agents conduct sponsor params with
  | .none => return none
  | .sponsor input => some <$> (evidenceOfInput input).mapError Stop.refused

/-! ## whitewash_count -/

/-- A retirement or lapse of one of the sponsor's agents, with that agent's standing then. -/
structure Retired where
  agent : String
  time : Nat
  status : AgentStatus
  deriving Repr

/-- WC1: the first retirement in list order of ANOTHER agent within the window of the
admission whose agent was then not GREEN or had a PENDING item (the whitewash test). -/
def firstMatch (admission : String × Nat) (retirements : List Retired) (window : Nat) :
    Option Retired :=
  retirements.find? fun r =>
    r.agent != admission.1 && within admission.2 r.time window && r.status.troubled

/-- WC1 and WC2: each admission that counts, once, with the retirement it is matched to. -/
def whitewashMatches (admissions : List (String × Nat)) (retirements : List Retired)
    (window : Nat) : List (String × String) :=
  admissions.filterMap fun adm => (firstMatch adm retirements window).map fun r => (adm.1, r.agent)

/-- `{agent, time}`, a nonempty name and a time (`lists`). -/
def readAgentTime (v : Canonical.Value) : Except String (String × Nat) := do
  let ms ← need (keysAre? v ["agent", "time"]) "lists"
  let a ← need (nameOf? (member ms "agent")) "lists"
  let t ← need (intIn? (member ms "time") 0 timeMax) "lists"
  return (a, natOf t)

/-- v1 `whitewash_count(admissions, retirements, states, window)`: the count and the
matches. -/
def whitewashCount (admissions retirements states window : Canonical.Value) :
    Except String (List (String × String)) := do
  let adms ← listOf admissions "lists"
  let rets ← listOf retirements "lists"
  let adms ← adms.mapM readAgentTime
  let rets ← rets.mapM readAgentTime
  let sts ← match states with
    | .obj ms => pure ms
    | _ => throw "states"
  let table ← sts.mapM fun (k, v) => do
    check (!k.isEmpty) "states"
    return (k, ← need (statusOf? v) "states")
  let retired ← rets.mapM fun (a, t) => do
    return (⟨a, t, ← need (table.lookup a) "states"⟩ : Retired)
  let w ← need (intIn? window 0 timeMax) "window"
  return whitewashMatches adms retired (natOf w)

/-! ## What Lean proves

Each statement is the text's, about the exact values, on every input. -/

/-- A FOR kind never resolves AGAINST: CE-F1 ... -/
theorem successionOf_ne_opposing (named : Bool) (p : Option AgentStatus) (blocks : Nat)
    (v : Option Nat) (taken : Bool) : (successionOf named p blocks v taken).1 ≠ .opposing := by
  unfold successionOf; repeat (first | split | decide)

/-- ... and CE-F2. -/
theorem changeOf_ne_opposing (declared : Bool) (blocks : Nat) (v c : Option Nat) :
    (changeOf declared blocks v c).1 ≠ .opposing := by
  unfold changeOf; repeat (first | split | decide)

/-- An AGAINST kind never resolves FOR: the three audit kinds ... -/
theorem auditOf_ne_supporting (a : AuditState) : (auditOf a).1 ≠ .supporting := by
  cases a <;> decide

/-- ... WHITEWASH ... -/
theorem whitewashOf_ne_supporting (adm exit : Nat) (s : AgentStatus) (w : Nat) :
    (whitewashOf adm exit s w).1 ≠ .supporting := by
  unfold whitewashOf; repeat (first | split | decide)

/-- ... and REMOVAL FOR CAUSE. -/
theorem removalOf_ne_supporting (removed : Bool) (c : Option RemovalCause) :
    (removalOf removed c).1 ≠ .supporting := by
  unfold removalOf; repeat (first | split | decide)

/-- WHITEWASH is never PENDING. -/
theorem whitewashOf_ne_pending (adm exit : Nat) (s : AgentStatus) (w : Nat) :
    (whitewashOf adm exit s w).1 ≠ .pending := by
  unfold whitewashOf; repeat (first | split | decide)

/-- The whitewash window lies on either side of the exit: the admission before the exit and after
it are judged alike. -/
theorem whitewashOf_symm (adm exit : Nat) (s : AgentStatus) (w : Nat) :
    whitewashOf adm exit s w = whitewashOf exit adm s w := by
  have : gap adm exit = gap exit adm := by unfold gap; split <;> split <;> omega
  unfold whitewashOf within
  rw [this]

/-- CR-F1: at most one CE-F1 per RATING PERIOD: with the period's taken, none resolves FOR. -/
theorem successionOf_period (named : Bool) (p : Option AgentStatus) (blocks : Nat) (v : Option Nat) :
    (successionOf named p blocks v true).1 ≠ .supporting := by
  unfold successionOf
  split
  · decide
  · split
    · decide
    · simp

/-- CR-F1: FOR only after 100 blocks, named, with no troubled predecessor. -/
theorem successionOf_for {named : Bool} {p : Option AgentStatus} {blocks : Nat} {v : Option Nat}
    {taken : Bool} (h : (successionOf named p blocks v taken).1 = .supporting) :
    named = true ∧ windowBlocks ≤ blocks ∧ p.any (·.troubled) = false := by
  unfold successionOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i h1 h2 _ _ h5; simp_all
          · cases h

/-- CR-F2: FOR only after 100 blocks of a declared change. -/
theorem changeOf_for {declared : Bool} {blocks : Nat} {v c : Option Nat}
    (h : (changeOf declared blocks v c).1 = .supporting) :
    declared = true ∧ windowBlocks ≤ blocks := by
  unfold changeOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i h1 _ _ h4; simp_all
        · cases h

/-- UE3: `n_u` never exceeds the events given. -/
theorem counted_le (events : List Weighed) : counted events ≤ events.length :=
  List.length_filter_le _ _

/-- PD-OC-10: a NEUTRAL event carries no evidence and is not counted: `F_u`, `A_u` and
`n_u` are those of the events without it. -/
theorem neutral_adds_nothing (events : List Weighed) (x : Weighed) (hx : x.side = none)
    (s : Side) (halfLife : Rat) :
    sideSum (events ++ [x]) s halfLife = sideSum events s halfLife ∧
      counted (events ++ [x]) = counted events := by
  simp [sideSum, counted, List.filter_append, hx]

/-- WC2: each admission counts at most once. -/
theorem whitewash_count_le (admissions : List (String × Nat)) (retirements : List Retired)
    (window : Nat) : (whitewashMatches admissions retirements window).length ≤ admissions.length :=
  List.length_filterMap_le _ _

/-- WC1: a match is a retirement of ANOTHER agent, within the window, of an agent then not
GREEN or with a PENDING item: the whitewash test resolves the pair AGAINST. -/
theorem firstMatch_whitewash {adm : String × Nat} {rs : List Retired} {w : Nat} {r : Retired}
    (h : firstMatch adm rs w = some r) :
    r.agent ≠ adm.1 ∧ r ∈ rs ∧ whitewashOf adm.2 r.time r.status w = (.opposing, .whitewash) := by
  unfold firstMatch at h
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
  refine ⟨hp.1.1, hm, ?_⟩
  simp [whitewashOf, hp.1.2, hp.2]

end Principia.Sponsor
