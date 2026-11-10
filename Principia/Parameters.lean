/-!
# Parameters

Every declared parameter and tuning option TPM v1 declares, carried into PMA
(the first phase of the rewrite). The inventory, with each value's source, unit and
kind, the values the sources leave open and where they disagree, is the parameters
inventory of the design notes.

v1 sorted its numbers in two kinds (TPS 5.3.30, 7.2.20; VOCABULARY "TUNING
OPTION"):

* a **declared parameter** fixes what; it is the Declarer's, and changing it is a
  revision of the specification (TPS 7.2.6). Each is one definition below.
* a **tuning option** fixes how fast; it is the Operator's, set in configuration
  and chained on every change. They are the fields of `TuningOptions`, whose default
  value is v1's set of starting values, so a tuned set is a value of that
  structure. `TuningOptions.Admissible` collects the constraints the specification
  states on any tuned set, and the bounds a value's own definition implies (a share
  is at most 1); `TuningOptions.SanityChecks` holds the few further checks this
  file's author adds, which the specification does not state. The per-user and
  per-UWC options are `UserTuning` and `UwcTuning`, whose defaults are the
  declared fleet defaults (TPS 7.2.1).

A few numbers fixed in the rule text of other sections, outside TPS 7.2, are here
too, marked "rule constant"; changing one is likewise a revision of the
specification.

Sources: "TPS 7.2.x" is section 7.2 of the TPS, its declared parameters; every other
"TPS N.M.x" is section N.M of TPS 0.5.0.

No floating point (the Lean rules): a non-integer value is an exact rational pair,
`Ratio`. Durations, block counts, CPU time, sizes and calendar months carry their
unit in their type; a rate or a cap per hour or per day is a plain count whose
period its doc comment states. Every period, window, age and half-life counts
landed blocks unless v1 marks it wall-clock (TPS 7.2.20).

This file holds values and tables only. It adds no `pcalc` subcommand, so it has no
vector corpus; its checks are the theorems below.
-/

namespace Principia.Parameters

/-! ## Exact values and units -/

/-- A non-negative exact rational `num / den`, `den > 0`. Values are compared by
cross-multiplication and never normalized, so `decide` evaluates every comparison
below. -/
structure Ratio where
  /-- The numerator. -/
  num : Nat
  /-- The denominator, positive. -/
  den : Nat
  /-- The denominator is positive. -/
  den_pos : 0 < den := by decide
  deriving Repr

/-- The `Ratio` `n / d`; the positivity of `d` is checked when the value is written. -/
def ratio (n d : Nat) (h : 0 < d := by decide) : Ratio := ⟨n, d, h⟩

namespace Ratio

instance : OfNat Ratio n := ⟨⟨n, 1, Nat.one_pos⟩⟩

/-- A whole number as a `Ratio`. -/
def ofWhole (n : Nat) : Ratio := ⟨n, 1, Nat.one_pos⟩

/-- `a ≤ b` as values. -/
protected def Le (a b : Ratio) : Prop := a.num * b.den ≤ b.num * a.den

/-- `a < b` as values. -/
protected def Lt (a b : Ratio) : Prop := a.num * b.den < b.num * a.den

instance : LE Ratio := ⟨Ratio.Le⟩
instance : LT Ratio := ⟨Ratio.Lt⟩

instance (a b : Ratio) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

instance (a b : Ratio) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

/-- Equal as values: `a` and `b` name the same rational. -/
def SameValue (a b : Ratio) : Prop := a.num * b.den = b.num * a.den

instance (a b : Ratio) : Decidable (SameValue a b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

/-- The sum, unnormalized. Used by the theorems of this file. -/
protected def add (a b : Ratio) : Ratio :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- The product, unnormalized. Used by the theorems of this file. -/
protected def mul (a b : Ratio) : Ratio :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

instance : Add Ratio := ⟨Ratio.add⟩
instance : Mul Ratio := ⟨Ratio.mul⟩

/-- The sum of a list, unnormalized. Used by the theorems of this file. -/
def sum (l : List Ratio) : Ratio := l.foldl (· + ·) 0

end Ratio

/-- A closed interval `[lo, hi]` of `Ratio`s: v1's `U[lo, hi]`. -/
structure RatioInterval where
  /-- The lower end. -/
  lo : Ratio
  /-- The upper end. -/
  hi : Ratio
  deriving Repr

/-- An inclusive range of block counts: v1's `U{lo..hi}`. -/
structure BlockRange where
  /-- The least count. -/
  lo : Nat
  /-- The greatest count. -/
  hi : Nat
  deriving Repr, DecidableEq

/-- A count of landed work blocks, the clock of every period, window, age and
half-life v1 does not mark wall-clock (TPS 7.2.20). -/
structure LandedBlocks where
  /-- The number of landed blocks. -/
  count : Nat
  deriving Repr, DecidableEq

/-- Wall-clock seconds, for the values v1 marks "(wall-clock)". -/
structure WallSeconds where
  /-- The number of seconds. -/
  count : Nat
  deriving Repr, DecidableEq

/-- CPU seconds: the host's and the meter's unit (TPS 5.3.32). -/
structure CpuSeconds where
  /-- The number of CPU seconds. -/
  count : Nat
  deriving Repr, DecidableEq

/-- A count of megabytes. Whether v1's megabyte is 10^6 or 2^20 bytes is not
stated (inventory U3), so the byte count is left open. -/
structure Megabytes where
  /-- The number of megabytes. -/
  count : Nat
  deriving Repr, DecidableEq

/-- A count of calendar months, not a fixed number of seconds. -/
structure CalendarMonths where
  /-- The number of months. -/
  count : Nat
  deriving Repr, DecidableEq

/-! ## Enumerations -/

/-- COMMUNITY PARROTS (TPS 5.16.11, VOCABULARY): whether a UWC's records may be
parrot targets for other UWCs' accounts. -/
inductive CommunityParrots
  /-- ACCEPT -/
  | accept
  /-- DECLINE -/
  | decline
  deriving Repr, DecidableEq

/-- AUDIT TRIGGER (TPS 5.16.11, 4.1.6). -/
inductive AuditTrigger
  /-- AUTOMATIC: an audit block opens at DISPUTE COUNT. -/
  | automatic
  /-- ON REQUEST -/
  | onRequest
  deriving Repr, DecidableEq

/-- CROSS-CORROBORATION (TPS 5.14 CR12): whether two agents of one sponsor may
corroborate each other. -/
inductive CrossCorroboration
  /-- GRANTED, by the Operator's explicit setting on that user. -/
  | granted
  /-- INHERITED, when both agents are in the TRUST TIER at the match. -/
  | inherited
  /-- RESTRICTED, never. -/
  | restricted
  deriving Repr, DecidableEq

/-- DOSSIER READ (TPS 5.18.10): a user's own read of its restricted pages. -/
inductive DossierRead
  /-- USER ONLY -/
  | userOnly
  /-- USER AND AGENT -/
  | userAndAgent
  /-- NEITHER -/
  | neither
  deriving Repr, DecidableEq

/-- RELIABILITY BASIS (TPS 7.2.19): AGENT only; SPONSORED was removed. -/
inductive ReliabilityBasis
  /-- AGENT: every comparison reads the agent's own score. -/
  | agent
  deriving Repr, DecidableEq

/-- PRIME AI PHASE (TPS 7.2.19, 5.13.5). -/
inductive PrimeAiPhase
  /-- REFERENCE -/
  | reference
  /-- ACTIVE, by a later declaration. -/
  | active
  deriving Repr, DecidableEq

/-- The challenge v1's CAPTCHA MODULE names (TPS 7.2.19, 5.3.27):
MediaWiki ConfirmEdit's challenge on badlogin. -/
inductive CaptchaKind
  /-- Turnstile -/
  | turnstile
  /-- QuestyCaptcha, the local fallback. -/
  | questyCaptcha
  deriving Repr, DecidableEq

/-- RATIO EPOCH SCOPE (TPS 5.17.13, VOCABULARY): whose clock the PARROT RATIO's
epoch runs on. -/
inductive RatioEpochScope
  /-- PER ACCOUNT -/
  | perAccount
  /-- FLEET -/
  | fleet
  deriving Repr, DecidableEq

/-- VOLUNTEER TIER (TPS 5.9.14, 7.2.20): which accounts in GOOD STANDING may
volunteer. -/
inductive VolunteerTier
  /-- ANY GREEN -/
  | anyGreen
  /-- TRUST TIER -/
  | trustTier
  deriving Repr, DecidableEq

/-- BIBLIOGRAPHY SETTING (TPS 5.21.1). -/
inductive BibliographySetting
  /-- OFF -/
  | off
  /-- ON -/
  | on
  /-- CLOSED -/
  | closed
  deriving Repr, DecidableEq

/-- SESSION LOG RETENTION (TPS 7.2.28): how long a sponsor keeps every SESSION LOG. -/
inductive SessionLogRetention
  /-- The certificate's life, as for the PROMPT and its salt. -/
  | certificateLife
  deriving Repr, DecidableEq

/-- IC2_POLICY (TPS 2.4.5, 2.4.7, 2.3.6): a Criteria Set parameter. -/
inductive Ic2Policy
  /-- GAP -/
  | gap
  /-- REJECT -/
  | reject
  deriving Repr, DecidableEq

/-- PROMOTION_FLOOR (TPS 2.4.5, 2.4.7, 3.2.12): a Criteria Set parameter. -/
inductive PromotionFloor
  /-- F1 -/
  | f1
  /-- F2 -/
  | f2
  /-- F3 -/
  | f3
  deriving Repr, DecidableEq

/-- STRUCTURE_CHECK (TPS 2.4.5, 2.4.7, 2.2.20): a Criteria Set parameter. -/
inductive StructureCheck
  /-- ON -/
  | on
  /-- OFF -/
  | off
  deriving Repr, DecidableEq

/-- PRESSURE LEVEL (TPS 5.3.34). -/
inductive PressureLevel
  /-- CLEAR -/
  | clear
  /-- BUSY -/
  | busy
  /-- STRAINED -/
  | strained
  /-- OVERLOADED -/
  | overloaded
  deriving Repr, DecidableEq

/-- A value for each PRESSURE LEVEL. -/
structure ByLevel (α : Type) where
  /-- At CLEAR. -/
  clear : α
  /-- At BUSY. -/
  busy : α
  /-- At STRAINED. -/
  strained : α
  /-- At OVERLOADED. -/
  overloaded : α
  deriving Repr

/-- The LANES (TPS 5.3.33), LANE 0 to LANE 6. -/
inductive Lane
  /-- LANE 0 OPERATOR: the Declarer, the Operator and W1's essential jobs. -/
  | operator
  /-- LANE 1 PEOPLE: USER accounts signed in. -/
  | people
  /-- LANE 2 FINISHING: work under way. -/
  | finishing
  /-- LANE 3 STARTING: work asked for. -/
  | starting
  /-- LANE 4 OPTIONAL: VOLUNTEER and a falcon RETURN. -/
  | optional
  /-- LANE 5 BACKGROUND: deferrable jobs. -/
  | background
  /-- LANE 6 ANONYMOUS: readers and crawlers. -/
  | anonymous
  deriving Repr, DecidableEq

/-- A lane's number, 0 to 6 (TPS 5.3.33). -/
def Lane.number : Lane → Nat
  | .operator => 0
  | .people => 1
  | .finishing => 2
  | .starting => 3
  | .optional => 4
  | .background => 5
  | .anonymous => 6

/-- What a PRESSURE LEVEL does to a lane (TPS 5.3.34). -/
inductive LaneAdmission
  /-- yes -/
  | admitted
  /-- no -/
  | refused
  /-- lane 6's anonymous expensive actions, under the slot cap for the level
  (the tuning option `GovernorTuning.anonymousSlots`) -/
  | anonymousSlots
  /-- cached pages only -/
  | cachedOnly
  deriving Repr, DecidableEq

/-- The governed requests as the LANE TABLE sorts them (TPS 5.3.33, as amended in
7.2.30). The lane of an AGENT account's core API write is not stated
(inventory U10). The Provision proposal op is the member `proposeProvision`, in LANE 4
beside VOLUNTEER, as the Declarer chose. -/
inductive GovernedRequest
  /-- A request by the Declarer or the Operator. -/
  | declarerOrOperator
  /-- W1's essential jobs: the switch's ping, expiry work, the integrity check,
  the budget roll-up, the weekly exception check, and the HOLD and RELEASE
  records and withdrawals when they run as jobs. -/
  | essentialJob
  /-- A request of a signed-in USER account. -/
  | signedInUser
  /-- The control panel's STRUCTURE TEST button, a signed-in USER's request. -/
  | structureTestButton
  /-- The queue head's acquisition inside its ACQUISITION WINDOW. -/
  | queueHeadAcquisition
  /-- POLL by the queue head or a holder. -/
  | pollByHeadOrHolder
  /-- HEARTBEAT -/
  | heartbeat
  /-- PUSH, the bibliography's landing lookups and EOM-0's settlement check
  inside it. -/
  | push
  /-- RETURN of a work block. -/
  | workReturn
  /-- RELEASE, the op. -/
  | releaseOp
  /-- INQUIRE -/
  | inquire
  /-- PETITION -/
  | petition
  /-- POLL by any other account. -/
  | pollOther
  /-- STATUS -/
  | status
  /-- A core API read by an AGENT account. -/
  | agentCoreRead
  /-- The op STRUCTURE_TEST. -/
  | structureTestOp
  /-- VOLUNTEER -/
  | volunteer
  /-- A falcon's RETURN. -/
  | falconReturn
  /-- The Provision proposal op, `PROPOSE_PROVISION`: any agent-group account proposes the
  text of a Provision. -/
  | proposeProvision
  /-- W1's deferrable jobs. -/
  | deferrableJob
  /-- TPX's falcon jobs. -/
  | falconJob
  /-- The bibliography recheck job (TPS 5.21.18). -/
  | bibliographyRecheckJob
  /-- The structure-test job (TPS 5.3.47). -/
  | structureTestJob
  /-- The configuration-strata job (TPS 5.18.17). -/
  | configurationStrataJob
  /-- An anonymous reader or crawler. -/
  | anonymousRead
  deriving Repr, DecidableEq

/-! ## The lock, the queue and the volumes -/

/-- ACQUISITION WINDOW: 5 minutes, server time (TPS 7.2.2, 5.8.5). When the
lock is let go, the queue head acquires; if it has not within the window, the next
waiter may. -/
def acquisitionWindow : WallSeconds := ⟨5 * 60⟩

/-- The agents' polling interval is at most 2.5 minutes, since the
ACQUISITION WINDOW is not less than twice it (TPS 7.2.2, 5.8.5). -/
def pollingIntervalMax : WallSeconds := ⟨150⟩

/-- Rule constant: each agent polls at most 24 times an hour (TPS 5.2.5). -/
def pollsPerHourMax : Nat := 24

/-- The lock ceiling: a heartbeat never extends a lock past 24 hours from grant
(TPS 7.2.21 NO-PROGRESS RULE, 5.7.1, 5.7.3; AC-4.9). -/
def lockCeiling : WallSeconds := ⟨24 * 3600⟩

/-- Rule constant: a lease is a whole number of volumes, at most 1,000
identifiers (TPS 3.1.13, 5.7.11). -/
def leaseMax : Nat := 1000

/-- Rule constant: one WAITING petition per account per UWC (TPS 5.8.9). -/
def waitingPetitionsPerUwc : Nat := 1

/-- Rule constant: three WAITING petitions per account across the fleet
(TPS 5.8.9). -/
def waitingPetitionsFleet : Nat := 3

/-- VOLUME SIZE: 10 records per register volume, for every UWC, never varied
(TPS 7.2.21, 3.1.12). -/
def volumeSize : Nat := 10

/-- VOLUME SIZE: 10 entries per APPEND VOLUME, for every UWC, never varied
(TPS 7.2.21, 5.3.42). -/
def appendVolumeSize : Nat := 10

/-- BIBLIO VOLUME SIZE: 5 entries per BIBLIOGRAPHY VOLUME, for every UWC, never
varied (TPS 7.2.25, 5.21.22). -/
def biblioVolumeSize : Nat := 5

/-! ## Certification, canaries and parrots -/

/-- The probe types of the certification suite as recorded: six (TPS 7.2.3, CR4).
A new probe type moves N. -/
def recordedSuiteProbeTypes : Nat := 6

/-- One REPRODUCTION operation in the supervised trial (TPS 7.2.3, CR4). -/
def trialReproductions : Nat := 1

/-- N: one operation per probe type in the suite in force, plus one REPRODUCTION
operation; a definition, not a value (TPS 7.2.3). -/
def trialOperations : Nat := recordedSuiteProbeTypes + trialReproductions

/-- CANARY SCHEDULE: tier 1 is blocks 1 to 100 under the current certificate
(TPS 7.2.4, 5.17.12). -/
def canaryTierOneEnd : LandedBlocks := ⟨100⟩

/-- CANARY SCHEDULE: tier 2 is blocks 101 to 1,000 (TPS 7.2.4). -/
def canaryTierTwoEnd : LandedBlocks := ⟨1000⟩

/-- CANARY SCHEDULE: 1 probe in 5 blocks in tier 1 (TPS 7.2.4). -/
def canaryRateTierOne : Ratio := ratio 1 5

/-- CANARY SCHEDULE: 1 in 10 in tier 2 (TPS 7.2.4). -/
def canaryRateTierTwo : Ratio := ratio 1 10

/-- CANARY SCHEDULE: 1 in 20 by default from block 1,001 (TPS 7.2.4). -/
def canaryRateTierThree : Ratio := ratio 1 20

/-- CANARY SCHEDULE: a burst runs at 1 in 5 or 1 in 10 (TPS 7.2.4). -/
def burstRates : List Ratio := [ratio 1 5, ratio 1 10]

/-- CANARY SCHEDULE: the burst rates are drawn at even odds (TPS 7.2.4). -/
def burstRateOdds : Ratio := ratio 1 2

/-- CANARY SCHEDULE: a burst lasts U{50..200} blocks (TPS 7.2.4). -/
def burstDuration : BlockRange := ⟨50, 200⟩

/-- CANARY SCHEDULE: U{200..500} blocks from the end of one burst to the start
of the next (TPS 7.2.4). -/
def burstGap : BlockRange := ⟨200, 500⟩

/-- CANARY SCHEDULE: bursts after block 1,000 only (TPS 7.2.4). -/
def burstsAfter : LandedBlocks := ⟨1000⟩

/-- LOOKBACK PASSES: 2. After a failed canary the hold reaches back to the
account's second most recent passed canary, block inclusive (TPS 7.2.17, CR6,
5.14.3). -/
def lookbackPasses : Nat := 2

/-- LOOKBACK PASSES below 1 is refused (TPS 7.2.17, 5.14.3). -/
def lookbackPassesMin : Nat := 1

/-- PARROT RATIO: k parrots per canary, k drawn from {1/2, 1/3, 1/5, 1/7}
(TPS 7.2.18, 5.17.13). -/
def parrotRatioChoices : List Ratio := [ratio 1 2, ratio 1 3, ratio 1 5, ratio 1 7]

/-- PARROT RATIO: the weights 0.30 / 0.50 / 0.15 / 0.05 of the choices, in order
(TPS 7.2.18). -/
def parrotRatioWeights : List Ratio := [ratio 3 10, ratio 1 2, ratio 3 20, ratio 1 20]

/-- PARROT RATIO: k is drawn per epoch of U{50..100} work blocks (TPS 7.2.18). -/
def parrotRatioEpoch : BlockRange := ⟨50, 100⟩

/-- The expected parrot share of probes as stated: 0.26 (TPS 7.2.18, 5.17.13). -/
def statedParrotShare : Ratio := ratio 26 100

/-- The share of probes that are parrots when k parrots ride per canary:
k / (k + 1), for k = n / d that is n / (n + d) (TPS 7.2.18: "k parrots per canary,
k : 1"). -/
def parrotShareOf (k : Ratio) : Ratio :=
  ⟨k.num, k.num + k.den, Nat.lt_of_lt_of_le k.den_pos (Nat.le_add_left _ _)⟩

/-- The expected parrot share the declared PARROT RATIO gives: each choice's share
weighted by its weight (TPS 7.2.18). -/
def expectedParrotShare : Ratio :=
  Ratio.sum ((parrotRatioWeights.zip parrotRatioChoices).map
    fun (w, k) => w * parrotShareOf k)

/-- RESET RULE: after a non-corroboration the reproducer's probe rate is 1 in 5
(TPS 7.2.18, 5.17.14). -/
def resetRate : Ratio := ratio 1 5

/-- COMMUNITY PARROTS, the fleet default: ACCEPT. Per UWC it is a tuning option,
`UwcTuning.communityParrots` (TPS 7.2.18, 5.16.11). -/
def communityParrotsDefault : CommunityParrots := .accept

/-- AUDIT TRIGGER, the fleet default: AUTOMATIC; per UWC it is selected at the
new-UWC form and declared in UWC STATE (TPS 7.2.18, 5.16.11). -/
def auditTriggerDefault : AuditTrigger := .automatic

/-- CONFORMANCE RATE: 1 in 50 work blocks, drawn per block, on top of the CANARY
SCHEDULE and outside its budget; an ESTIMATE (TPS 7.2.28, 5.17.18). -/
def conformanceRate : Ratio := ratio 1 50

/-! ## The gradient, the sequential test and the review point -/

/-- GRADIENT ARMS: STEEP theta_1 ~ Uniform[3.0, 4.0]; interim values until the
refit (TPS 7.2.11, 5.17.6). -/
def steepTheta : RatioInterval := ⟨3, 4⟩

/-- GRADIENT ARMS: SHALLOW theta_2 ~ Uniform[1.0, 2.0], gapped from steep by
(2.0, 3.0) (TPS 7.2.11). -/
def shallowTheta : RatioInterval := ⟨1, 2⟩

/-- GRADIENT ARMS: HYPERBOLIC kappa ~ Uniform[2.0, 4.0] (TPS 7.2.11). -/
def hyperbolicKappa : RatioInterval := ⟨2, 4⟩

/-- GRADIENT ARMS: HYPERBOLIC alpha ~ Uniform[1.5, 3.0] (TPS 7.2.11). -/
def hyperbolicAlpha : RatioInterval := ⟨ratio 3 2, 3⟩

/-- ARM WEIGHTS: fixed at 1/3 each (TPS 7.2.11). -/
def armWeight : Ratio := ratio 1 3

/-- ARM CLOCKS: each arm's epoch ends with probability 0.10 per probe that arm
delivered, so its length is Geometric with mean 10 probes (TPS 7.2.12, 5.17.7). -/
def armClockEnd : Ratio := ratio 1 10

/-- SEQUENTIAL TEST: alpha = 0.10 (TPS 7.2.7). -/
def sequentialAlpha : Ratio := ratio 1 10

/-- SEQUENTIAL TEST: beta = 0.01 (TPS 7.2.7). -/
def sequentialBeta : Ratio := ratio 1 100

/-- SEQUENTIAL TEST: H0 p = 0.99 over the removal rate (TPS 7.2.7). -/
def sequentialNullRate : Ratio := ratio 99 100

/-- SEQUENTIAL TEST: H1 p = 0.95 (TPS 7.2.7). -/
def sequentialAltRate : Ratio := ratio 95 100

/-- REVIEW POINT: when 200 probes have been delivered fleet-wide, the gradient,
the CANARY SCHEDULE and the sequential test's hypotheses are revisited
(TPS 7.2.16). -/
def reviewPointProbes : Nat := 200

/-! ## The scorecard and the alert channel -/

/-- SCORECARD CADENCE: an exception check every week (TPS 7.2.13, 5.18.5). -/
def scorecardExceptionPeriod : WallSeconds := ⟨7 * 86400⟩

/-- SCORECARD CADENCE: a full report every month regardless (TPS 7.2.13). -/
def scorecardFullReportPeriod : CalendarMonths := ⟨1⟩

/-- ALERT CHANNEL, the secondary: a dead-man's switch with period one week
(TPS 7.2.15, 5.18.12). The service is VERIFY. -/
def alertSwitchPeriod : WallSeconds := ⟨7 * 86400⟩

/-- ALERT CHANNEL, the secondary: grace one day (TPS 7.2.15, 5.18.12). -/
def alertSwitchGrace : WallSeconds := ⟨86400⟩

/-- FLEET CELL FLOOR: a configuration-strata cell with fewer than 3 accounts is
shown only as a count of suppressed cells; an ESTIMATE (TPS 7.2.28, 5.18.17). -/
def fleetCellFloor : Nat := 3

/-- Rule constant: every interval the scorecard and the score show is the
95 per cent interval, equal-tailed for E (TPS 5.14 CR8, CR11, 5.18.17). -/
def intervalLevel : Ratio := ratio 95 100

/-! ## Reliability and identity (TPS 5.14 CR11, CR12) -/

/-- PRIOR a0 (TPS 7.2.19). -/
def priorA0 : Ratio := 1

/-- PRIOR b0 (TPS 7.2.19). -/
def priorB0 : Ratio := 1

/-- THIN FILE START: every account after the first starts at 0.5 (TPS 7.2.19, CR11). -/
def thinFileStart : Ratio := ratio 1 2

/-- PRIME SEED: the first certified account is Prime at 0.8 (TPS 7.2.19, CR11). -/
def primeSeed : Ratio := ratio 4 5

/-- PRIME CEILING: 1 (TPS 7.2.19, CR11). -/
def primeCeiling : Ratio := 1

/-- WARN COUNT: 3 (TPS 7.2.19, CR11). -/
def warnCount : Nat := 3

/-- SUSPEND COUNT: 2 (TPS 7.2.19, CR11). -/
def suspendCount : Nat := 2

/-- ORANGE PASSES: ORANGE ends after 3 consecutive canary passes (TPS 7.2.19,
CR11, 5.17.14). -/
def orangePasses : Nat := 3

/-- PRIME AI PHASE: REFERENCE; ACTIVE by a later declaration (TPS 7.2.19, 5.13.5). -/
def primeAiPhase : PrimeAiPhase := .reference

/-- KEY ROTATION: 365 days (wall-clock), fleet; on the schedule or on suspicion
(TPS 7.2.19, 5.3.27). -/
def keyRotation : WallSeconds := ⟨365 * 86400⟩

/-- CAPTCHA MODULE: ConfirmEdit with Turnstile on badlogin; no createaccount
trigger, since no visitor creates an account (TPS 7.2.19, 5.3.27). -/
def captchaChallenge : CaptchaKind := .turnstile

/-- CAPTCHA MODULE: QuestyCaptcha the local fallback (TPS 7.2.19). -/
def captchaFallback : CaptchaKind := .questyCaptcha

/-- AGENTS PER SPONSOR, the fleet default: 5; per user it is a tuning option,
`UserTuning.agentsPerSponsor` (TPS 7.2.19, CR12). -/
def agentsPerSponsorDefault : Nat := 5

/-- CROSS-CORROBORATION, the fleet default: INHERITED; per user a tuning option
(TPS 7.2.19, CR12). -/
def crossCorroborationDefault : CrossCorroboration := .inherited

/-- DOSSIER READ, the fleet default: NEITHER; per user a tuning option
(TPS 7.2.19, 5.18.10). -/
def dossierReadDefault : DossierRead := .neither

/-- RELIABILITY BASIS: AGENT only; SPONSORED removed and SPONSOR WEIGHT retired
(TPS 7.2.19). -/
def reliabilityBasis : ReliabilityBasis := .agent

/-- SPONSOR CUT: an agent's confirmed violation cuts its sponsor's score by
m_class x 0.5 (TPS 7.2.19, CR12). -/
def sponsorCut : Ratio := ratio 1 2

/-- Rule constant: a CE-F1 or CE-F2 conduct event resolves FOR when the 100 landed
blocks after it pass clean (TPS 5.14 CR12). -/
def conductWindow : LandedBlocks := ⟨100⟩

/-- Rule constant: at most one CE-F1 per RATING PERIOD of the sponsor's blocks
(TPS 5.14 CR12). -/
def proactiveSuccessionPerPeriod : Nat := 1

/-! ## The governor -/

/-- HOST CAPS: 4,000 CPU seconds an hour; VERIFY until read from Site Tools
(TPS 7.2.21, 5.2.5). -/
def hostCpuHour : CpuSeconds := ⟨4000⟩

/-- HOST CAPS: 40,000 CPU seconds a day (TPS 7.2.21). -/
def hostCpuDay : CpuSeconds := ⟨40000⟩

/-- HOST CAPS: 800,000 CPU seconds a month (TPS 7.2.21); TPS 5.2.5 reads the
horizon as 30 days. -/
def hostCpuMonth : CpuSeconds := ⟨800000⟩

/-- HOST CAPS: 30 simultaneous processes (TPS 7.2.21). -/
def hostProcesses : Nat := 30

/-- HOST CAPS: 20 connections per IP (TPS 7.2.21). -/
def hostConnectionsPerIp : Nat := 20

/-- HOST CAPS: a 1,000 MB database (TPS 7.2.21). -/
def hostDatabase : Megabytes := ⟨1000⟩

/-- HOST CAPS: 600,000 inodes (TPS 7.2.21). -/
def hostInodes : Nat := 600000

/-- Rule constant: the host runs up to 10 Node.js projects; VERIFY until read from
Site Tools (TPS 5.2.5). -/
def hostNodeProjects : Nat := 10

/-- Rule constant: W1's cron entry runs at most twice an hour, if HC2 confirms the
host's 30-minute spacing (TPS 5.2.5). -/
def w1RunsPerHourMax : Nat := 2

/-- BUDGET RULE: B_H1 = 4,000 CPU seconds (TPS 7.2.21, 5.3.32). -/
def budgetHour : Ratio := 4000

/-- BUDGET RULE: B_H24 = min(40,000, 800,000 / 31) = 800,000 / 31 CPU seconds,
which paces the month even in a 31-day month (TPS 7.2.21, 5.3.32). Not an
integer (inventory U5). -/
def budgetDay : Ratio := ratio 800000 31

/-- BUDGET RULE: B_H30 = 800,000 CPU seconds over a sliding 30 days (TPS 7.2.21,
5.3.32). -/
def budgetThirtyDays : Ratio := 800000

/-- SIGMA: 0.8; r = max over the horizons of kappa_M x U_T / (sigma x B_T) is
kept below 1 (TPS 7.2.21, 5.3.32). -/
def sigma : Ratio := ratio 4 5

/-- PRESSURE LEVELS: BUSY from r = 0.60 (TPS 7.2.21, 5.3.34). A level is entered
at its threshold (inventory X1). -/
def pressureBusy : Ratio := ratio 60 100

/-- PRESSURE LEVELS: STRAINED from r = 0.75 (TPS 7.2.21, 5.3.34). -/
def pressureStrained : Ratio := ratio 75 100

/-- PRESSURE LEVELS: OVERLOADED from r = 0.90 (TPS 7.2.21, 5.3.34). -/
def pressureOverloaded : Ratio := ratio 90 100

/-- PRESSURE LEVELS: a level is left only when r falls 0.05 below its entry
threshold (TPS 7.2.21, 5.3.34). -/
def pressureHysteresis : Ratio := ratio 5 100

/-- PRESSURE LEVELS: admission by level and lane (TPS 7.2.21, 5.3.34). -/
def pressureAdmission : PressureLevel → Lane → LaneAdmission
  | _, .operator => .admitted
  | _, .people => .admitted
  | _, .finishing => .admitted
  | .clear, .starting => .admitted
  | .busy, .starting => .admitted
  | _, .starting => .refused
  | .clear, .optional => .admitted
  | _, .optional => .refused
  | .clear, .background => .admitted
  | .busy, .background => .admitted
  | _, .background => .refused
  | .overloaded, .anonymous => .cachedOnly
  | _, .anonymous => .anonymousSlots

/-- LANE TABLE: the lane of every governed request (TPS 7.2.21, 5.3.33; as amended
in 7.2.30). -/
def laneOf : GovernedRequest → Lane
  | .declarerOrOperator => .operator
  | .essentialJob => .operator
  | .signedInUser => .people
  | .structureTestButton => .people
  | .queueHeadAcquisition => .finishing
  | .pollByHeadOrHolder => .finishing
  | .heartbeat => .finishing
  | .push => .finishing
  | .workReturn => .finishing
  | .releaseOp => .finishing
  | .inquire => .finishing
  | .petition => .starting
  | .pollOther => .starting
  | .status => .starting
  | .agentCoreRead => .starting
  | .structureTestOp => .starting
  | .volunteer => .optional
  | .falconReturn => .optional
  | .proposeProvision => .optional
  | .deferrableJob => .background
  | .falconJob => .background
  | .bibliographyRecheckJob => .background
  | .structureTestJob => .background
  | .configurationStrataJob => .background
  | .anonymousRead => .anonymous

/-- LANE TABLE: the agent lanes together hold six slots (TPS 7.2.21, 5.3.33). Declared, as 7.2.21 states it (inventory X2). -/
def agentLaneSlots : Nat := 6

/-- LANE TABLE: two of the six agent slots are kept for lane 2 (TPS 7.2.21,
5.3.33). Declared, as 7.2.21 states it (inventory X2). -/
def slotsKeptForFinishing : Nat := 2

/-- Rule constant: an EXTERNAL READING that shows the host limiting the site
raises the PRESSURE LEVEL one step for 30 minutes (TPS 5.3.31). -/
def externalReadingStep : WallSeconds := ⟨30 * 60⟩

/-- TRAFFIC STAGE RULES: PENALIZED after three TE3 in an hour (TPS 7.2.21,
5.3.37). -/
def penalizedTe3Count : Nat := 3

/-- TRAFFIC STAGE RULES: PENALIZED after a second THROTTLED in an hour
(TPS 7.2.21). -/
def penalizedThrottledCount : Nat := 2

/-- TRAFFIC STAGE RULES: PENALIZED's counting window, an hour (TPS 7.2.21). -/
def penalizedWindow : WallSeconds := ⟨3600⟩

/-- TRAFFIC STAGE RULES: CONTAINED after ten TE3 in 24 hours (TPS 7.2.21). -/
def containedTe3Count : Nat := 10

/-- TRAFFIC STAGE RULES: CONTAINED after a third PENALIZED in 24 hours
(TPS 7.2.21). -/
def containedPenalizedCount : Nat := 3

/-- TRAFFIC STAGE RULES: CONTAINED's counting window, 24 hours (TPS 7.2.21). -/
def containedWindow : WallSeconds := ⟨24 * 3600⟩

/-- Rule constant: PENALIZED halves the seat rate (TPS 5.3.37). -/
def penalizedSeatRateFactor : Ratio := ratio 1 2

/-- Rule constant: inodes are counted by W1, 80 per cent flagged (TPS 5.3.39). -/
def inodeFlag : Ratio := ratio 80 100

/-- Rule constant: the REVISIT MARK is set when anonymous load passes half of the
paced day budget (TPS 5.3.40). -/
def revisitMarkShare : Ratio := ratio 1 2

/-- Rule constant: the REVISIT MARK counts 7 such days ... (TPS 5.3.40). -/
def revisitMarkDays : Nat := 7

/-- Rule constant: ... in 30 (TPS 5.3.40). -/
def revisitMarkWindowDays : Nat := 30

/-! ## The cluster and the falcons -/

/-- IN MAX: 2.5 spacings (TPS 7.2.22, 5.19.8). -/
def clusterInMax : Ratio := ratio 5 2

/-- CUSP MAX: 3.5 spacings (TPS 7.2.22, 5.19.8). -/
def clusterCuspMax : Ratio := ratio 7 2

/-- Z: 1.645 (TPS 7.2.22, 5.19.8). -/
def clusterZ : Ratio := ratio 1645 1000

/-- HISTORY MIN: 100 landed blocks, for the gate's cusp path (TPS 7.2.22, 5.19.14). -/
def historyMin : LandedBlocks := ⟨100⟩

/-- Rule constant: a fetch follows a redirect to a declared host at most 3 hops
(TPS 5.19.3). -/
def fetchRedirectHops : Nat := 3

/-- Rule constant: a fetch's timeout, 30 s (TPS 5.19.3). -/
def fetchTimeout : WallSeconds := ⟨30⟩

/-- Rule constant: a fetch's download cap, 20 MB (TPS 5.19.3). -/
def fetchDownloadCap : Megabytes := ⟨20⟩

/-- Rule constant: each declared archive member is decompressed under a 50 MB cap
(TPS 5.19.3). -/
def fetchMemberCap : Megabytes := ⟨50⟩

/-- Rule constant: at most 256 entries in an archive (TPS 5.19.3). -/
def fetchArchiveEntries : Nat := 256

/-- FALCON FLOOR: two distinct assignees; a falcon waits rather than run on one
(TPS 7.2.22, 5.20.6). -/
def falconFloor : Nat := 2

/-- FALCON CANARY RATE: 1 in 10 of an account's falcon assignments, an ESTIMATE
between the schedule's 1 in 5 and 1 in 20 (TPS 7.2.22, 5.20.17). -/
def falconCanaryRate : Ratio := ratio 1 10

/-- Rule constant: one falcon in flight per account (TPS 5.20.18). -/
def falconsInFlight : Nat := 1

/-- Rule constant: LADDER 2 adds one more blind assignee and takes a strict
majority of three per field (TPS 5.20.10). -/
def ladderAssignees : Nat := 3

/-- GRADUATION BLOCKS: 10 landed blocks (TPS 7.2.22, 5.14.9). -/
def graduationBlocks : LandedBlocks := ⟨10⟩

/-- GRADUATION DATES: 5 distinct UTC dates (TPS 7.2.22, 5.14.9). -/
def graduationDates : Nat := 5

/-- GRADUATION SPAN: 14 days (wall-clock) from the first landed block to the latest
(TPS 7.2.22, 5.14.9). -/
def graduationSpan : WallSeconds := ⟨14 * 86400⟩

/-! ## The bibliography, the prompt and the Research Client -/

/-- BIBLIOGRAPHY SETTING, the default: OFF (TPS 7.2.25, 5.21.1). -/
def bibliographySettingDefault : BibliographySetting := .off

/-- ENTRY CAPS: a title, 1,000 code points after NFC (TPS 7.2.25, 5.21.7). -/
def entryCapTitle : Nat := 1000

/-- ENTRY CAPS: every other text, 500 code points after NFC (TPS 7.2.25). -/
def entryCapText : Nat := 500

/-- ENTRY CAPS: each name part, 200 code points after NFC (TPS 7.2.25). -/
def entryCapNamePart : Nat := 200

/-- ENTRY CAPS: a URL, 2,000 code points after NFC (TPS 7.2.25). -/
def entryCapUrl : Nat := 2000

/-- ENTRY CAPS: at most 100 names per role (TPS 7.2.25). -/
def entryCapNamesPerRole : Nat := 100

/-- ENTRY CAPS: at most one identifier per kind (TPS 7.2.25). -/
def entryCapIdentifiersPerKind : Nat := 1

/-- SPONSOR ZONE CAP: 8,000 code points after NFC; an ESTIMATE (TPS 7.2.28,
5.14.5, 5.4.16). -/
def sponsorZoneCap : Nat := 8000

/-- SESSION LOG RETENTION: the certificate's life (TPS 7.2.28, 5.4.18). -/
def sessionLogRetention : SessionLogRetention := .certificateLife

/-- Rule constant: the Research Client sends maxlag=5 on every call (TPS 5.4.13). -/
def clientMaxlag : WallSeconds := ⟨5⟩

/-- Rule constant: the Research Client throttles adaptively with K_AT = 2 ...
(TPS 5.4.13). -/
def clientAdaptiveK : Nat := 2

/-- Rule constant: ... over two minutes (TPS 5.4.13). -/
def clientAdaptiveWindow : WallSeconds := ⟨2 * 60⟩

/-- Rule constant: the Research Client keeps a retry budget of 10 per cent of its
requests (TPS 5.4.13). -/
def clientRetryBudget : Ratio := ratio 10 100

/-- Rule constant: the Research Client sends serial requests, one in flight per
agent (TPS 5.4.13). -/
def clientInFlight : Nat := 1

/-! ## The declared-form grammar's bounds -/

/-- Rule constant: a declared form is at most 4,096 code points of its text after
line-ending normalization and NFC, whitespace counted (TPS 2.2 BOUNDS). -/
def formMaxLength : Nat := 4096

/-- Rule constant: a declared form is at most 64 parentheses deep (TPS 2.2 BOUNDS). -/
def formMaxDepth : Nat := 64

/-- Rule constant: an integer of the form grammar is at most four digits as
written, so at most 9999, the bound of a DIMENSION exponent (TPS 2.2 BOUNDS,
2.5.12). -/
def grammarIntegerMax : Nat := 9999

/-- Rule constant: a DIMENSION exponent, and every exponent the analysis computes,
lies within -9999..9999 (TPS 2.5.12, 2.2). -/
def exponentBound : Nat := 9999

/-! ## The strike rule and the Criteria Set's bounds -/

/-- Rule constant: SR8 applies when N ≥ 2 standing M records of one quantity
disagree (TPS 4.4 SR8). -/
def sr8MinGroup : Nat := 2

/-- Rule constant: SR8's scale factor applies when chi^2 / (N - 1) > 1
(TPS 4.4 SR8). -/
def sr8Threshold : Ratio := 1

/-- Rule constant: SR8 computes S over the records with
delta_i < 3 N^(1/2) delta_mean (TPS 4.4 SR8). -/
def sr8OutlierFactor : Nat := 3

/-- The least N_X a Criteria Set may declare: 2 (TPS 2.4.7, 4.4 SR6). -/
def nXMin : Nat := 2

/-- The greatest N_X a Criteria Set may declare: 1,000,000 (TPS 2.4.7). -/
def nXMax : Nat := 1000000

/-- The least S_MAX, the T3 depth, a Criteria Set may declare: 1 (TPS 2.4.7). -/
def sMaxMin : Nat := 1

/-- The greatest S_MAX a Criteria Set may declare: 1,000,000 (TPS 2.4.7). -/
def sMaxMax : Nat := 1000000

/-- IC2_POLICY when absent: GAP (TPS 2.4.5, 2.4.7). -/
def ic2PolicyDefault : Ic2Policy := .gap

/-- PROMOTION_FLOOR when absent: F2 (TPS 2.4.5, 2.4.7, 3.2.12). -/
def promotionFloorDefault : PromotionFloor := .f2

/-- STRUCTURE_CHECK when absent: ON (TPS 2.4.5, 2.4.7). -/
def structureCheckDefault : StructureCheck := .on

/-! ## The tuning options -/

/-- The reliability score's tuning options (TPS 7.2.20, 5.14 CR11). -/
structure ScoreTuning where
  /-- HALF-LIFE: evidence weighs 2^(-age / HALF-LIFE). -/
  halfLife : LandedBlocks := ⟨500⟩
  /-- RATING PERIOD. -/
  ratingPeriod : LandedBlocks := ⟨50⟩
  /-- k_base, the leader-following gain. -/
  kBase : Ratio := ratio 2 10
  /-- k_min, the least follower gain. -/
  kMin : Ratio := ratio 1 100
  /-- k_max, the greatest follower gain. -/
  kMax : Ratio := ratio 5 10
  /-- eps_P, the factor on Prime's own rate. -/
  epsP : Ratio := ratio 1 10
  /-- delta_max, the greatest change of S per period. -/
  deltaMax : Ratio := ratio 5 100
  /-- g_F, the weight a MATCH adds to F. -/
  gF : Ratio := 1
  /-- m_1, the cut for a record struck on reproduction. -/
  m1 : Ratio := ratio 25 100
  /-- m_2, the cut for a false corroboration, the largest. -/
  m2 : Ratio := ratio 5 10
  /-- m_3, the cut for a consistency mismatch. -/
  m3 : Ratio := ratio 15 100
  /-- h for a CLEARLY LOWER counterpart. -/
  hClearlyLower : Ratio := 1
  /-- h for a SIMILAR counterpart. -/
  hSimilar : Ratio := 2
  /-- h for a CLEARLY HIGHER counterpart. -/
  hClearlyHigher : Ratio := 3
  /-- TRIP LEVEL. -/
  tripLevel : Ratio := ratio 4 10
  /-- TRIP WINDOW. -/
  tripWindow : LandedBlocks := ⟨500⟩
  /-- w_I, the cost of the first INQUIRE. -/
  wI : Ratio := ratio 1 100
  /-- COOL-OFF, the INQUIRE window. -/
  coolOff : LandedBlocks := ⟨200⟩
  /-- T_idle (wall-clock): 90 days. -/
  tIdle : WallSeconds := ⟨90 * 86400⟩
  /-- P_max, the most pending items. -/
  pMax : Nat := 5
  /-- c_max, the DIVERSITY QUOTA. -/
  cMax : Ratio := ratio 25 100
  /-- DISPUTE COUNT (also TPS 5.9.12). -/
  disputeCount : Nat := 2
  /-- TRUST TIER on. -/
  trustTierOn : Bool := true
  /-- TRUST TIER: the top 0.25 of RANK. -/
  trustTierTop : Ratio := ratio 25 100
  /-- OVERTAKE off. -/
  overtake : Bool := false
  /-- INHERITANCE on. -/
  inheritanceOn : Bool := true
  /-- INHERITANCE: 0.25 of the old F. -/
  inheritanceShare : Ratio := ratio 25 100
  /-- OVERRIDE DELAY (wall-clock): 24 h (also TPS 5.6.9). -/
  overrideDelay : WallSeconds := ⟨24 * 3600⟩
  /-- OVERRIDE SUNSET. -/
  overrideSunset : LandedBlocks := ⟨500⟩
  /-- PRIME PAD: synthetic FOR events. -/
  primePad : Nat := 20
  /-- PAD MAX. -/
  padMax : Nat := 40
  /-- PAD NON-REFERENCE off. -/
  padNonReference : Bool := false
  deriving Repr

/-- The sponsor's conduct events' tuning options; ESTIMATES (TPS 7.2.24, 5.14 CR12). -/
structure ConductTuning where
  /-- g_C for CE-F1 PROACTIVE SUCCESSION. -/
  gCProactiveSuccession : Ratio := 1
  /-- g_C for CE-F2 DECLARED CHANGE KEPT CLEAN. -/
  gCDeclaredChangeKept : Ratio := 1
  /-- h_C for the UNDECLARED PROMPT CHANGE conduct event. -/
  hCUndeclaredPrompt : Ratio := 2
  /-- h_C for the WHITEWASH conduct event. -/
  hCWhitewash : Ratio := 2
  /-- h_C for the UNDECLARED MODEL OR FAMILY CHANGE conduct event. -/
  hCUndeclaredModel : Ratio := 3
  /-- h_C for the FALSE DECLARATION conduct event. -/
  hCFalseDeclaration : Ratio := 3
  /-- h_C for the REMOVAL FOR CAUSE conduct event. -/
  hCRemovalForCause : Ratio := 3
  /-- SUCCESSION WINDOW (wall-clock): 30 days. -/
  successionWindow : WallSeconds := ⟨30 * 86400⟩
  deriving Repr

/-- The probes' tuning options (TPS 7.2.20, 5.17.13). -/
structure ProbeTuning where
  /-- RATIO EPOCH SCOPE. -/
  ratioEpochScope : RatioEpochScope := .perAccount
  /-- CONSISTENCY SHARE: the fraction of parrots that are consistency parrots. -/
  consistencyShare : Ratio := ratio 10 100
  deriving Repr

/-- The volunteer channel's tuning options (TPS 7.2.20, 5.9.14-5.9.17). -/
structure VolunteerTuning where
  /-- EARLY CALL LIMIT: refused volunteer calls per RATING PERIOD. -/
  earlyCallLimit : Nat := 3
  /-- VOLUNTEER COOL-OFF. -/
  volunteerCoolOff : LandedBlocks := ⟨200⟩
  /-- VOLUNTEER TIER. -/
  volunteerTier : VolunteerTier := .anyGreen
  /-- P_V BOUNDS: p_v is drawn per epoch from U[0.25, 0.50]. -/
  pVBounds : RatioInterval := ⟨ratio 25 100, ratio 50 100⟩
  /-- P_V ROTATION: the epoch ends with probability 0.10 per volunteer call,
  fleet-wide. -/
  pVRotation : Ratio := ratio 10 100
  /-- VOLUNTEER RATE (wall-clock): tokens per hour. -/
  volunteerRate : Nat := 2
  /-- VOLUNTEER BURST: tokens. -/
  volunteerBurst : Nat := 3
  /-- BACKOFF BASE (wall-clock): 5 minutes. -/
  backoffBase : WallSeconds := ⟨5 * 60⟩
  /-- BACKOFF CAP (wall-clock): 4 hours. -/
  backoffCap : WallSeconds := ⟨4 * 3600⟩
  /-- INTAKE w_q, the EWMA weight. -/
  intakeWq : Ratio := ratio 2 10
  /-- INTAKE MIN, of landed blocks in the period. -/
  intakeMin : Ratio := ratio 25 100
  /-- INTAKE MAX, of landed blocks in the period. -/
  intakeMax : Ratio := ratio 50 100
  /-- INTAKE MAX_P. -/
  intakeMaxP : Ratio := ratio 9 10
  /-- VOLUNTEER SHARE, v_max. -/
  volunteerShare : Ratio := ratio 25 100
  deriving Repr

/-- The control panel's tuning options (TPS 7.2.20, 7.2.24, 5.3.29). -/
structure PanelTuning where
  /-- PANEL HEARTBEAT (wall-clock): 5 minutes. -/
  panelHeartbeat : WallSeconds := ⟨5 * 60⟩
  /-- PANEL GRACE (wall-clock): 10 minutes. -/
  panelGrace : WallSeconds := ⟨10 * 60⟩
  /-- W2 READING (wall-clock): every 60 s. -/
  w2Reading : WallSeconds := ⟨60⟩
  deriving Repr

/-- SEATS: the declared cost of each op, never measured cost (TPS 7.2.24, 7.2.30,
5.3.36). -/
structure SeatTable where
  /-- STATUS -/
  status : Nat := 1
  /-- POLL -/
  poll : Nat := 1
  /-- HEARTBEAT -/
  heartbeat : Nat := 1
  /-- INQUIRE -/
  inquire : Nat := 1
  /-- PETITION -/
  petition : Nat := 2
  /-- RELEASE, the op. -/
  releaseOp : Nat := 2
  /-- VOLUNTEER -/
  volunteer : Nat := 2
  /-- RETURN: 4 ... -/
  returnBase : Nat := 4
  /-- ... + 1 per record. -/
  returnPerRecord : Nat := 1
  /-- PUSH: 4 ... -/
  pushBase : Nat := 4
  /-- ... + 1 per record. -/
  pushPerRecord : Nat := 1
  /-- A core API read by an AGENT account. -/
  coreRead : Nat := 1
  /-- A core API write by an AGENT account. -/
  coreWrite : Nat := 4
  /-- A falcon RETURN: 4 ... -/
  falconReturnBase : Nat := 4
  /-- ... + 1 per started group of this many result rows: the rows round up, as the
  Declarer chose (inventory U4). -/
  falconReturnRowsPerSeat : Nat := 20
  /-- The Provision proposal op: 4, as the Declarer chose. -/
  proposeProvision : Nat := 4
  /-- STRUCTURE_TEST: 2, an ESTIMATE (TPS 7.2.30). -/
  structureTest : Nat := 2
  /-- The queue head's acquisition (lane 2): 1, as POLL and HEARTBEAT, as the Declarer chose. -/
  queueHeadAcquisition : Nat := 1
  deriving Repr

/-- The governor's tuning options (TPS 7.2.24, 5.3.31-5.3.40). -/
structure GovernorTuning where
  /-- kappa_M: 1.3 until the Operator's first monthly reading. -/
  kappaM : Ratio := ratio 13 10
  /-- SAMPLE PERIOD (wall-clock). -/
  samplePeriod : WallSeconds := ⟨60⟩
  /-- METER SAMPLE: anonymous requests sampled 1 in q. -/
  meterSample : Nat := 1
  /-- SEATS. -/
  seats : SeatTable := {}
  /-- SEAT RATES (wall-clock): agent, seats an hour. -/
  agentSeatRate : Nat := 120
  /-- SEAT RATES: agent burst. -/
  agentSeatBurst : Nat := 20
  /-- SEAT RATES (wall-clock): sponsor, seats an hour. -/
  sponsorSeatRate : Nat := 240
  /-- SEAT RATES: sponsor burst. -/
  sponsorSeatBurst : Nat := 30
  /-- SLOTS: per sponsor. -/
  slotsPerSponsor : Nat := 2
  /-- SLOTS: per agent. -/
  slotsPerAgent : Nat := 1
  /-- SLOTS: anonymous expensive actions by PRESSURE LEVEL (inventory X3). -/
  anonymousSlots : ByLevel Nat := ⟨6, 3, 1, 0⟩
  /-- REPEAT LIMIT: one REQUEST DIGEST more than 5 times ... -/
  repeatLimit : Nat := 5
  /-- ... in 10 minutes (wall-clock). -/
  repeatWindow : WallSeconds := ⟨10 * 60⟩
  /-- ERROR STREAK. -/
  errorStreak : Nat := 20
  /-- PENALTY HOUR (wall-clock). -/
  penaltyHour : WallSeconds := ⟨3600⟩
  /-- RETRY-AFTER base (wall-clock). -/
  retryAfterBase : WallSeconds := ⟨60⟩
  /-- RETRY-AFTER cap (wall-clock). -/
  retryAfterCap : WallSeconds := ⟨3600⟩
  /-- RETRY-AFTER jitter: up to 10 per cent. -/
  retryAfterJitter : Ratio := ratio 10 100
  /-- SLOT RETRY-AFTER (wall-clock): the wait a slot refusal (503) tells, before its
  jitter; 5 seconds, an ESTIMATE tuned in the sandboxes, as the Declarer chose. -/
  slotRetryAfter : WallSeconds := ⟨5⟩
  /-- FLOOD INTERVAL (wall-clock). -/
  floodInterval : WallSeconds := ⟨60⟩
  /-- NO-PROGRESS LIMIT (wall-clock): 6 hours, never above the 24-hour ceiling. -/
  noProgressLimit : WallSeconds := ⟨6 * 3600⟩
  /-- LANDED BYTES (wall-clock): per account a day. -/
  landedBytesAccountDay : Megabytes := ⟨5⟩
  /-- LANDED BYTES (wall-clock): the fleet a day. -/
  landedBytesFleetDay : Megabytes := ⟨20⟩
  /-- DATABASE LEVELS: the first, 70 per cent of the cap. -/
  databaseLevelFirst : Ratio := ratio 70 100
  /-- DATABASE LEVELS: the second, 85 per cent. -/
  databaseLevelSecond : Ratio := ratio 85 100
  /-- DATABASE LEVELS: the third, 95 per cent. -/
  databaseLevelThird : Ratio := ratio 95 100
  /-- CACHE LIFETIME (wall-clock). -/
  cacheLifetime : WallSeconds := ⟨300⟩
  /-- PSEUDO-LAG (wall-clock) by PRESSURE LEVEL. -/
  pseudoLag : ByLevel WallSeconds := ⟨⟨0⟩, ⟨3⟩, ⟨6⟩, ⟨30⟩⟩
  /-- ANONYMOUS NETWORK CAP: CPU seconds an hour. -/
  anonymousNetworkCap : CpuSeconds := ⟨300⟩
  /-- ANONYMOUS NETWORK CAP: the network listed for one hour (wall-clock). -/
  anonymousNetworkListing : WallSeconds := ⟨3600⟩
  /-- MANIFEST FANOUT (v1's word; the Index tree's fanout in PMA's terms). -/
  indexFanout : Nat := 20
  /-- EXPIRY STEP (wall-clock): 30 minutes. -/
  expiryStep : WallSeconds := ⟨30 * 60⟩
  deriving Repr

/-- The cluster's tuning options (TPS 7.2.24, 5.19.4, 5.19.10). -/
structure ClusterTuning where
  /-- UNLISTED GRACE (wall-clock): 2 months. -/
  unlistedGrace : CalendarMonths := ⟨2⟩
  /-- SOURCE RETRY (wall-clock): 7 days. -/
  sourceRetry : WallSeconds := ⟨7 * 86400⟩
  /-- SOURCE LOST: cycles. -/
  sourceLost : Nat := 2
  deriving Repr

/-- The falcons' tuning options; ESTIMATES (TPS 7.2.24, 5.20). -/
structure FalconTuning where
  /-- FALCON TRIAL: a new kind's first 10 falcons ... -/
  trialFalcons : Nat := 10
  /-- ... are issued to three assignees each. -/
  trialAssignees : Nat := 3
  /-- FALCON BREAKER: issuing stops when DECLINED plus UNRESOLVED exceed 0.3 ... -/
  breakerShare : Ratio := ratio 3 10
  /-- ... of the last 20 falcons. -/
  breakerSpan : Nat := 20
  /-- FALCON WAIT (wall-clock): 24 h. -/
  falconWait : WallSeconds := ⟨24 * 3600⟩
  /-- FALCON WINDOW: no starting value, set in the sandboxes; its unit is not
  stated (inventory U2). -/
  falconWindow : Option Nat := none
  /-- FALCON LEASE (wall-clock): 72 h. -/
  falconLease : WallSeconds := ⟨72 * 3600⟩
  /-- FALCON SHARE: 0.25 of an account's seats ... -/
  falconShare : Ratio := ratio 25 100
  /-- ... in 24 h (wall-clock). -/
  falconShareWindow : WallSeconds := ⟨24 * 3600⟩
  /-- FALCON RATE CAP (wall-clock): one save per 10 s at application, never above
  the cap the FALCON KIND DECLARATION states. -/
  rateCapInterval : WallSeconds := ⟨10⟩
  deriving Repr

/-- The bibliography's tuning options; ESTIMATES (TPS 7.2.27, 5.21.18, 5.21.21). -/
structure BibliographyTuning where
  /-- BIBLIO ENTRY MAX: bytes of an entry's canonical serialization. -/
  entryMax : Nat := 16384
  /-- BIBLIO RECHECK (wall-clock): 30 days. -/
  recheck : WallSeconds := ⟨30 * 86400⟩
  /-- BIBLIO LOOKUP CAP (wall-clock): lookups a day for the fleet, landings first. -/
  lookupCap : Nat := 2000
  /-- BIBLIO LOOKUP TIME (wall-clock): per landing job and per recheck run. -/
  lookupTime : WallSeconds := ⟨120⟩
  /-- BIBLIO RECHECK BATCH: identifiers per run. -/
  recheckBatch : Nat := 50
  deriving Repr

/-- The prompt's tuning options, published in STATUS for the Research Client
(TPS 7.2.29, 5.3.45). -/
structure PromptTuning where
  /-- SESSION BLOCK CAP. -/
  sessionBlockCap : Nat := 1
  /-- SESSION TURN CAP: an ESTIMATE. -/
  sessionTurnCap : Nat := 40
  /-- RE-ANCHOR on. -/
  reAnchor : Bool := true
  /-- CONFORMANCE WEIGHTS: CP1, an ESTIMATE. -/
  conformanceWeightCp1 : Ratio := ratio 5 10
  /-- CONFORMANCE WEIGHTS: CP2, 0 until its scorer exists (C-37). -/
  conformanceWeightCp2 : Ratio := 0
  /-- CONFORMANCE WEIGHTS: CP3, an ESTIMATE. -/
  conformanceWeightCp3 : Ratio := ratio 5 10
  deriving Repr

/-- The fleet's tuning options: the Operator's values, set in configuration,
displayed on the control panel and chained on every change (TPS 5.3.30, 7.2.20).
The default value is v1's set of starting values for the synthetic UWC and the
sandboxes; a tuned set is a value of this structure. -/
structure TuningOptions where
  /-- The reliability score. -/
  score : ScoreTuning := {}
  /-- The sponsor's conduct events. -/
  conduct : ConductTuning := {}
  /-- The probes. -/
  probe : ProbeTuning := {}
  /-- The volunteer channel. -/
  volunteer : VolunteerTuning := {}
  /-- The control panel. -/
  panel : PanelTuning := {}
  /-- The governor. -/
  governor : GovernorTuning := {}
  /-- The cluster. -/
  cluster : ClusterTuning := {}
  /-- The falcons. -/
  falcon : FalconTuning := {}
  /-- The bibliography. -/
  bibliography : BibliographyTuning := {}
  /-- The prompt. -/
  prompt : PromptTuning := {}
  deriving Repr

/-- v1's starting values (TPS 7.2.20, 7.2.24, 7.2.27, 7.2.29, 7.2.30). -/
def TuningOptions.starting : TuningOptions := {}

/-- The per-user tuning options; their defaults are the declared fleet defaults
(TPS 7.2.1, 7.2.19, 7.2.20). -/
structure UserTuning where
  /-- AGENTS PER SPONSOR. -/
  agentsPerSponsor : Nat := agentsPerSponsorDefault
  /-- CROSS-CORROBORATION, set by the Operator on that user. -/
  crossCorroboration : CrossCorroboration := crossCorroborationDefault
  /-- DOSSIER READ. -/
  dossierRead : DossierRead := dossierReadDefault
  deriving Repr

/-- The per-UWC tuning options; their defaults are the declared fleet defaults
(TPS 7.2.1, 7.2.18, 5.16.11). -/
structure UwcTuning where
  /-- COMMUNITY PARROTS, set by the Operator for that UWC. -/
  communityParrots : CommunityParrots := communityParrotsDefault
  deriving Repr

/-- The constraints on any tuned set: those the specification states, and the bounds
a value's own definition implies (a share or a probability lies in [0, 1]; a
Geometric epoch's end probability is above 0). Each field's doc says which, and
cites its source. A change the Operator makes is admissible only when the new set
satisfies every one. Checks the specification neither states nor implies are
`TuningOptions.SanityChecks`, which refuses nothing. -/
structure TuningOptions.Admissible (t : TuningOptions) : Prop where
  /-- Stated: the NO-PROGRESS LIMIT is never above the 24-hour ceiling (TPS 5.7.8,
  7.2.21, 7.2.24). -/
  noProgress_le_ceiling : t.governor.noProgressLimit.count ≤ lockCeiling.count
  /-- Implied: clip(·, k_min, k_max) needs k_min ≤ k_max (TPS 5.14 CR11). -/
  kMin_le_kMax : t.score.kMin ≤ t.score.kMax
  /-- Implied: a first-order lag S <- S + k x (T - S) moves S toward T and no
  further only with k ≤ 1 (TPS 5.14 CR11). -/
  kMax_le_one : t.score.kMax ≤ 1
  /-- Stated: m_2 is the largest cut (TPS 5.14 CR11: "m_2 (largest)"). -/
  m1_lt_m2 : t.score.m1 < t.score.m2
  /-- Stated: m_2 is the largest cut. -/
  m3_lt_m2 : t.score.m3 < t.score.m2
  /-- Implied: a cut S <- S x (1 - m_class) leaves S in [0, 1] (TPS 5.14 CR11). -/
  m2_le_one : t.score.m2 ≤ 1
  /-- Implied: TRIP LEVEL is a score, and S lies in [0, 1] (TPS 5.14 CR11). -/
  tripLevel_le_one : t.score.tripLevel ≤ 1
  /-- Implied: c_max is a share of an account's FOR weight (TPS 5.14 CR11). -/
  cMax_le_one : t.score.cMax ≤ 1
  /-- Implied: the TRUST TIER is a top fraction of RANK (TPS 5.14 CR11). -/
  trustTierTop_le_one : t.score.trustTierTop ≤ 1
  /-- Implied: INHERITANCE carries a share of the old F (TPS 5.14 CR11). -/
  inheritanceShare_le_one : t.score.inheritanceShare ≤ 1
  /-- Stated: the PAD is bounded by PAD MAX (TPS 5.14 CR11). -/
  primePad_le_padMax : t.score.primePad ≤ t.score.padMax
  /-- Implied: CONSISTENCY SHARE is a fraction of parrots (TPS 5.17.13). -/
  consistencyShare_le_one : t.probe.consistencyShare ≤ 1
  /-- Stated: p_v's interval has interior endpoints (TPS 5.9.16, 5.17.16): above
  0 ... -/
  pV_lo_pos : 0 < t.volunteer.pVBounds.lo
  /-- ... in order ... -/
  pV_lo_lt_hi : t.volunteer.pVBounds.lo < t.volunteer.pVBounds.hi
  /-- ... and below 1. -/
  pV_hi_lt_one : t.volunteer.pVBounds.hi < 1
  /-- Implied: P_V ROTATION is the probability per call that the Geometric epoch
  ends; above 0, or the epoch never ends (TPS 5.9.16) ... -/
  pVRotation_pos : 0 < t.volunteer.pVRotation
  /-- ... and at most 1. -/
  pVRotation_le_one : t.volunteer.pVRotation ≤ 1
  /-- Implied: p_nw is 0 below INTAKE MIN and rises linearly to INTAKE MAX_P at
  INTAKE MAX, which needs INTAKE MIN below INTAKE MAX (TPS 5.9.16). -/
  intakeMin_lt_intakeMax : t.volunteer.intakeMin < t.volunteer.intakeMax
  /-- Implied: INTAKE MAX_P is a probability (TPS 5.9.16). -/
  intakeMaxP_le_one : t.volunteer.intakeMaxP ≤ 1
  /-- Implied: VOLUNTEER SHARE is a share of an account's FOR weight (TPS 5.9.17). -/
  volunteerShare_le_one : t.volunteer.volunteerShare ≤ 1
  /-- Implied: anonymous requests are sampled 1 in q, so q is at least 1
  (TPS 5.3.32). -/
  meterSample_pos : 1 ≤ t.governor.meterSample
  /-- Stated: OVERLOADED serves anonymous readers cached pages only (TPS 5.3.34). -/
  anonymousSlots_overloaded : t.governor.anonymousSlots.overloaded = 0
  /-- Implied: the DATABASE LEVELS are the first, second and third, each a per cent
  of the cap (TPS 5.3.39). -/
  databaseLevels_ordered : t.governor.databaseLevelFirst < t.governor.databaseLevelSecond ∧
    t.governor.databaseLevelSecond < t.governor.databaseLevelThird ∧
    t.governor.databaseLevelThird ≤ 1
  /-- Stated: a falcon is never worked by fewer than two accounts (TPS 5.20.1,
  5.20.6). -/
  falconTrial_ge_floor : falconFloor ≤ t.falcon.trialAssignees
  /-- Implied: FALCON BREAKER is a share of the last falcons (TPS 5.20.4). -/
  breakerShare_le_one : t.falcon.breakerShare ≤ 1
  /-- Implied: FALCON SHARE is a share of an account's seats (TPS 5.20.18). -/
  falconShare_le_one : t.falcon.falconShare ≤ 1
  /-- Stated: CP2's weight is 0 until its scorer exists (TPS 7.2.29, 5.17.18; C-37).
  Lifting this field when C-37 closes is a change to this file, reviewed as such,
  not an Operator act. -/
  cp2_zero : t.prompt.conformanceWeightCp2.num = 0
  /-- Implied: the conformance kinds are drawn by CONFORMANCE WEIGHTS (TPS 5.17.18),
  so the weights sum to 1. -/
  conformanceWeights_sum : Ratio.SameValue
    (t.prompt.conformanceWeightCp1 + t.prompt.conformanceWeightCp2 +
      t.prompt.conformanceWeightCp3) 1

/-- Checks this file's author adds, which the specification neither states nor
implies; a tuned set may fail one and still be admissible (the parameters inventory,
section 8). -/
structure TuningOptions.SanityChecks (t : TuningOptions) : Prop where
  /-- The backoff's base does not pass its cap. TPS 5.9.16 computes
  min(BACKOFF CAP, BACKOFF BASE x 2^attempt), well defined either way. -/
  backoff_base_le_cap : t.volunteer.backoffBase.count ≤ t.volunteer.backoffCap.count
  /-- RETRY-AFTER's base does not pass its cap (TPS 5.3.37 doubles it from the one
  toward the other). -/
  retryAfter_base_le_cap : t.governor.retryAfterBase.count ≤ t.governor.retryAfterCap.count
  /-- PANEL HEARTBEAT is no longer than PANEL GRACE. TPS 5.3.29 says only that W2
  pings "at PANEL HEARTBEAT within PANEL GRACE". -/
  panelHeartbeat_le_grace : t.panel.panelHeartbeat.count ≤ t.panel.panelGrace.count

/-! ## Theorems: the constraints the specification states -/

/-- The starting values satisfy every constraint on a tuned set. -/
theorem starting_admissible : TuningOptions.starting.Admissible := by
  constructor <;> decide

/-- The starting values pass the author's sanity checks. -/
theorem starting_sane : TuningOptions.starting.SanityChecks := by
  constructor <;> decide

/-- The ACQUISITION WINDOW is not less than twice the agents' polling interval
(TPS 7.2.2, 5.8.5). -/
theorem pollingInterval_within_window :
    2 * pollingIntervalMax.count ≤ acquisitionWindow.count := by decide

/-- TPS 7.2.2's polling interval and TPS 5.2.5's polls an hour agree: at the
longest interval 7.2.2 allows, an agent polls exactly the most times 5.2.5
allows (inventory U11). -/
theorem pollsPerHour_agrees : pollsPerHourMax * pollingIntervalMax.count = 3600 := by
  decide

/-- N as the suite stands: six probe operations and one reproduction (TPS 7.2.3). -/
theorem trialOperations_eq : trialOperations = 7 := by decide

/-- A lease is a whole number of volumes, so the lease cap is one (TPS 3.1.13). -/
theorem leaseMax_whole_volumes : leaseMax % volumeSize = 0 := by decide

/-- A WAITING petition per UWC is within the fleet cap (TPS 5.8.9). -/
theorem waitingPetitions_ordered : waitingPetitionsPerUwc ≤ waitingPetitionsFleet := by
  decide

/-- The CANARY SCHEDULE's tiers are in order and its rates fall with tenure
(TPS 7.2.4). -/
theorem canarySchedule_ordered :
    canaryTierOneEnd.count < canaryTierTwoEnd.count ∧
      canaryRateTierThree < canaryRateTierTwo ∧ canaryRateTierTwo < canaryRateTierOne := by
  decide

/-- Bursts run after tier 2 only, faster than tier 3, and their ranges are
proper (TPS 7.2.4). -/
theorem bursts_well_formed :
    burstsAfter = canaryTierTwoEnd ∧
      (∀ r ∈ burstRates, canaryRateTierThree < r) ∧
      burstDuration.lo ≤ burstDuration.hi ∧ burstGap.lo ≤ burstGap.hi := by
  refine ⟨rfl, ?_, by decide, by decide⟩
  intro r hr
  simp only [burstRates, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

/-- FALCON CANARY RATE lies between the schedule's 1 in 20 and 1 in 5
(TPS 7.2.22). -/
theorem falconCanaryRate_between :
    canaryRateTierThree ≤ falconCanaryRate ∧ falconCanaryRate ≤ canaryRateTierOne := by
  decide

/-- LOOKBACK PASSES is not below 1 (TPS 7.2.17). -/
theorem lookbackPasses_admissible : lookbackPassesMin ≤ lookbackPasses := by decide

/-- The PARROT RATIO has one weight per choice, and its weights sum to 1
(TPS 7.2.18). -/
theorem parrotRatioWeights_sum :
    parrotRatioWeights.length = parrotRatioChoices.length ∧
      Ratio.SameValue (Ratio.sum parrotRatioWeights) 1 := by decide

/-- The exact expected parrot share of probes: the declared choices and weights give
0.30 x 1/3 + 0.50 x 1/4 + 0.15 x 1/6 + 0.05 x 1/8 = 41/160 (TPS 7.2.18). -/
theorem parrotShare_exact : Ratio.SameValue expectedParrotShare (ratio 41 160) := by
  decide

/-- The stated 0.26 is the expected share to two places: 0.255 ≤ 41/160 < 0.265
(TPS 7.2.18, 5.17.13; inventory X7). -/
theorem parrotShare_rounds_to_stated :
    statedParrotShare ≤ expectedParrotShare + ratio 1 200 ∧
      expectedParrotShare < statedParrotShare + ratio 1 200 := by decide

/-- Every gradient interval is proper and strictly interior, so no arm is flat
(TPS 7.2.11, 5.17.8). -/
theorem gradientArms_interior :
    0 < steepTheta.lo ∧ steepTheta.lo < steepTheta.hi ∧
      0 < shallowTheta.lo ∧ shallowTheta.lo < shallowTheta.hi ∧
      0 < hyperbolicKappa.lo ∧ hyperbolicKappa.lo < hyperbolicKappa.hi ∧
      0 < hyperbolicAlpha.lo ∧ hyperbolicAlpha.lo < hyperbolicAlpha.hi := by decide

/-- SHALLOW is gapped from STEEP, so the arms stay distinguishable
(TPS 7.2.11). -/
theorem shallow_gapped_from_steep : shallowTheta.hi < steepTheta.lo := by decide

/-- The three ARM WEIGHTS sum to 1 (TPS 7.2.11). -/
theorem armWeights_sum : Ratio.SameValue (armWeight + armWeight + armWeight) 1 := by
  decide

/-- An arm's epoch is Geometric with mean 10 probes: 1 / p = 10 (TPS 7.2.12). -/
theorem armClock_mean_ten : Ratio.SameValue (armClockEnd * 10) 1 := by decide

/-- The sequential test's hypotheses and rates are proper: H1 below H0, both
probabilities, alpha and beta in (0, 1) (TPS 7.2.7). -/
theorem sequentialTest_proper :
    sequentialAltRate < sequentialNullRate ∧ sequentialNullRate < 1 ∧
      0 < sequentialAlpha ∧ sequentialAlpha < 1 ∧ 0 < sequentialBeta ∧ sequentialBeta < 1 := by
  decide

/-- The Beta prior is proper: a0 and b0 positive (TPS 7.2.19, CR11). -/
theorem prior_proper : 0 < priorA0 ∧ 0 < priorB0 := by decide

/-- The score's anchors in order, within [0, 1]: an override sets S within
[THIN FILE START, PRIME CEILING] and S lies in [0, 1] (TPS 7.2.19, CR11). -/
theorem scoreAnchors_ordered :
    thinFileStart ≤ primeSeed ∧ primeSeed ≤ primeCeiling ∧ primeCeiling ≤ 1 := by decide

/-- Every pending set falls under exactly one state (TPS 5.14 CR11): with exactly
one CLEARLY HIGHER counterpart an account is YELLOW, which needs SUSPEND COUNT at
least 2. -/
theorem suspendCount_ge_two : 2 ≤ suspendCount := by decide

/-- B_H24 = min(40,000, 800,000 / 31): it is the month cap paced over 31 days,
exactly, and that lies below the day cap, so the min takes it; B_H1 and B_H30 are
the hour and month caps (TPS 7.2.21, 5.3.32). -/
theorem budget_paces_month :
    Ratio.SameValue (budgetDay * 31) (Ratio.ofWhole hostCpuMonth.count) ∧
      budgetDay ≤ Ratio.ofWhole hostCpuDay.count ∧
      Ratio.SameValue budgetHour (Ratio.ofWhole hostCpuHour.count) ∧
      Ratio.SameValue budgetThirtyDays (Ratio.ofWhole hostCpuMonth.count) := by decide

/-- SIGMA is a proper safety factor (TPS 7.2.21, 5.3.32). -/
theorem sigma_proper : 0 < sigma ∧ sigma < 1 := by decide

/-- The PRESSURE LEVELS' thresholds rise below 1 (r is kept below 1), and the
hysteresis is smaller than every gap between them, so each level's exit point lies
above the next threshold down (TPS 7.2.21, 5.3.34). A sudden drop of r can still
pass more than one level. -/
theorem pressureLevels_ordered :
    pressureBusy < pressureStrained ∧ pressureStrained < pressureOverloaded ∧
      pressureOverloaded < 1 ∧ pressureHysteresis < pressureBusy ∧
      pressureHysteresis + pressureBusy < pressureStrained ∧
      pressureHysteresis + pressureStrained < pressureOverloaded := by decide

/-- Lanes 0 to 2 are admitted at every PRESSURE LEVEL: LANE 0 and LANE 1 are never
refused on budget, and LANE 2 is never refused on budget, rate, pressure or share
(TPS 5.3.33, 5.3.34). -/
theorem pressureAdmission_lanes_zero_to_two (p : PressureLevel) (l : Lane)
    (h : l.number ≤ 2) : pressureAdmission p l = .admitted := by
  cases p <;> cases l <;> simp_all [Lane.number, pressureAdmission]

/-- Lane 6 serves cached pages only when OVERLOADED, and runs under its slot cap
otherwise (TPS 5.3.34). -/
theorem pressureAdmission_anonymous (p : PressureLevel) :
    pressureAdmission p .anonymous =
      if p = .overloaded then .cachedOnly else .anonymousSlots := by
  cases p <;> rfl

/-- The work under way is in LANE 2: the queue head's acquisition, POLL by the head
or a holder, HEARTBEAT, PUSH, RETURN, RELEASE and INQUIRE (TPS 5.3.33). -/
theorem laneOf_finishing :
    laneOf .queueHeadAcquisition = .finishing ∧ laneOf .pollByHeadOrHolder = .finishing ∧
      laneOf .heartbeat = .finishing ∧ laneOf .push = .finishing ∧
      laneOf .workReturn = .finishing ∧ laneOf .releaseOp = .finishing ∧
      laneOf .inquire = .finishing := by decide

/-- A falcon RETURN runs in LANE 4 and TPX's falcon jobs in LANE 5, never in
LANE 2 (TPS 5.20.18). -/
theorem laneOf_falcon_not_finishing :
    laneOf .falconReturn = .optional ∧ laneOf .falconJob = .background ∧
      laneOf .falconReturn ≠ .finishing ∧ laneOf .falconJob ≠ .finishing := by
  decide

/-- The Provision proposal op runs in LANE 4 beside VOLUNTEER, outside lanes 0 to 2, so
it is shed first under pressure and refused on budget. -/
theorem laneOf_proposeProvision :
    laneOf .proposeProvision = .optional ∧ laneOf .proposeProvision = laneOf .volunteer ∧
      ¬ (laneOf .proposeProvision).number ≤ 2 := by decide

/-- The agent lanes less the slots kept for lane 2: "so lanes 3 and 4 together hold
at most four" (TPS 5.3.33). -/
theorem startingOptionalSlots : agentLaneSlots - slotsKeptForFinishing = 4 ∧
    slotsKeptForFinishing ≤ agentLaneSlots := by decide

/-- CUSP MAX lies above IN MAX, so the CUSP band is not empty, and Z is positive
(TPS 7.2.22, 5.19.8). -/
theorem cluster_bands_ordered : clusterInMax < clusterCuspMax ∧ 0 < clusterZ := by
  decide

/-- The graduation thresholds can be met together. SG1 to SG3 are floors (TPS
5.14.9: "at least"): each distinct date needs a landed block, and a span above zero
needs two blocks (TPS 7.2.22, 5.14.9). -/
theorem graduation_satisfiable :
    graduationDates ≤ graduationBlocks.count ∧ 2 ≤ graduationBlocks.count ∧
      0 < graduationSpan.count := by decide

/-- The Criteria Set's bounds are proper, and N_X's least is SR6's "at least 2"
(TPS 2.4.7, 4.4 SR6). -/
theorem criteriaBounds_proper :
    nXMin ≤ nXMax ∧ sMaxMin ≤ sMaxMax ∧ nXMin = 2 := by decide

/-- SR8 applies from two records of one quantity: "N >= 2" (TPS 4.4 SR8). -/
theorem sr8MinGroup_eq : sr8MinGroup = 2 := by decide

/-- A four-digit integer of the grammar fits the DIMENSION exponent's bound
(TPS 2.2 BOUNDS: "the bound of a DIMENSION exponent"). -/
theorem grammarInteger_within_exponent :
    grammarIntegerMax = 10 ^ 4 - 1 ∧ grammarIntegerMax ≤ exponentBound := by decide

/-- The per-user and per-UWC options start at the declared fleet defaults
(TPS 7.2.1). -/
theorem perScope_defaults :
    ({} : UserTuning).agentsPerSponsor = agentsPerSponsorDefault ∧
      ({} : UserTuning).crossCorroboration = crossCorroborationDefault ∧
      ({} : UserTuning).dossierRead = dossierReadDefault ∧
      ({} : UwcTuning).communityParrots = communityParrotsDefault := by decide

end Principia.Parameters
