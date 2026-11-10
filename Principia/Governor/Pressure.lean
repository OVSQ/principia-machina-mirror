import Principia.Parameters

/-!
# The governor's pressure levels

GA4 of version 1's admission (TPS 5.3.31, 5.3.32, 5.3.34; 7.2.21, 7.2.24): the budget
ratio over three horizons, the PRESSURE LEVEL it names, the hysteresis that keeps a level
until the ratio falls 0.05 below its entry threshold, and the EXTERNAL READING that raises
the level one step for 30 minutes. The admission (`Principia.Governor.admit`) reads the
level this file computes; its table by level and lane is `Parameters.pressureAdmission`.
Vectors: the governor corpus's `level` cases, their expectations computed by
a script of hand-written vectors, a transcription written apart from this file.

## The ratio

r = max over the horizons T of kappa_M x U_T / (sigma x B_T) (TPS 5.3.32): U_T the metered
CPU use over the hour, the day and 30 days, B_T the budgets (`Parameters.budgetHour`,
`budgetDay`, `budgetThirtyDays`), sigma 0.8 and kappa_M the tuning option (1.3 until the
Operator's first monthly reading). The use is given in thousandths of a CPU second, so a
meter that reads CPU time to the millisecond passes it exactly; r is an exact fraction.

## The readings

Four points TPS 0.5.0 leaves unstated or states twice differently are the Declarer's
(selected by the Declarer: the first of each). Each is a field of `PressureReadings`, the
selected reading its default, so that another answer changes a default and its vectors,
not the mechanism:

* `descent`: when the ratio falls past a level's exit point, the level falls straight to
  the level the ratio names (`straight`); or one level per update (`oneStep`); or to the
  highest level whose own exit point the ratio has not passed (`bands`).
* `retry` (GA4's 503 Retry-After, which 5.3.35 does not state): SLOT RETRY-AFTER, the slots' own
  5 seconds, with the jitter (`slot`); or the level's pseudo-lag (`pseudoLag`); or
  RETRY-AFTER's base (`base`). Read by `Principia.Governor`.
* `threshold` (inventory X1): a level is entered at its threshold, as 5.3.34 states ("BUSY
  from 0.60", so r = 0.90 is OVERLOADED; `atThreshold`); or as 7.2.21's "BUSY to 0.75,
  STRAINED to 0.90, OVERLOADED above" (`aboveThreshold`: BUSY from 0.60, STRAINED above
  0.75, OVERLOADED above 0.90).
* `external`: the external reading raises the level the hysteresis step gives, one step,
  capped at OVERLOADED (`raiseAfter`); or the raised level is what the hysteresis steps
  toward (`raiseBefore`).

A fifth point the brief did not name is read here too, with its own field and default
(`anonymousFull`, read by `Principia.Governor`): what a lane 6 request meets below
OVERLOADED when the anonymous slots are full (TPS 5.3.40 ER3: they "run under lane-6
slots and are answered 503 with Retry-After in OVERLOADED only"). The default serves it
cached pages (`cached`), so that no lane 6 request is answered 503 below OVERLOADED; the
other answers 503 with SLOT RETRY-AFTER as a full agent pool does (`slots`).

## The step

`levelStep` is the GOVERNOR's lazy update (TPS 5.3.31): from the level in force, the
ratio now, and the time the last external reading's raised step runs until. A level is
entered as soon as the ratio names it (or one above it); a level is left only when the
ratio falls 0.05 below the level's entry threshold (`levelStep_hysteresis`). The external
reading is in force while `now` is before `externalUntil`; Custos sets `externalUntil` to
the reading's time plus `Parameters.externalReadingStep` (30 minutes) when W1's reading
shows the host limiting the site, and an absent or stale reading changes nothing.
-/

namespace Principia.Governor

open Principia.Parameters

/-! ## Levels -/

/-- A level's place, CLEAR 0 to OVERLOADED 3. -/
def _root_.Principia.Parameters.PressureLevel.rank : PressureLevel → Nat
  | .clear => 0
  | .busy => 1
  | .strained => 2
  | .overloaded => 3

/-- The level one step up, OVERLOADED staying OVERLOADED. -/
def _root_.Principia.Parameters.PressureLevel.up : PressureLevel → PressureLevel
  | .clear => .busy
  | .busy => .strained
  | .strained => .overloaded
  | .overloaded => .overloaded

/-- The level one step down, CLEAR staying CLEAR. -/
def _root_.Principia.Parameters.PressureLevel.down : PressureLevel → PressureLevel
  | .clear => .clear
  | .busy => .clear
  | .strained => .busy
  | .overloaded => .strained

/-- A value for a level. -/
def _root_.Principia.Parameters.ByLevel.at {α : Type} (b : ByLevel α) : PressureLevel → α
  | .clear => b.clear
  | .busy => b.busy
  | .strained => b.strained
  | .overloaded => b.overloaded

/-- A `Parameters.Ratio` as an exact fraction. -/
def ratioRat (r : Ratio) : Rat := (r.num : Rat) / (r.den : Rat)

/-- A level's entry threshold (TPS 5.3.34): CLEAR 0, BUSY 0.60, STRAINED 0.75,
OVERLOADED 0.90. -/
def entry : PressureLevel → Rat
  | .clear => 0
  | .busy => ratioRat pressureBusy
  | .strained => ratioRat pressureStrained
  | .overloaded => ratioRat pressureOverloaded

/-- The hysteresis, 0.05 (TPS 5.3.34). -/
def hysteresis : Rat := ratioRat pressureHysteresis

/-! ## The ratio -/

/-- A value for each budget horizon: the hour, the day and 30 days (TPS 5.3.32). -/
structure ByHorizon (α : Type) where
  /-- The hour. -/
  hour : α
  /-- The day. -/
  day : α
  /-- 30 days. -/
  thirtyDays : α
  deriving Repr, DecidableEq

/-- One horizon's term, kappa_M x U_T / (sigma x B_T), the use in thousandths of a CPU
second. -/
def horizonTerm (kappa : Ratio) (use : Nat) (budget : Ratio) : Rat :=
  ratioRat kappa * ((use : Rat) / 1000) / (ratioRat sigma * ratioRat budget)

/-- The ratio r: the largest of the three horizons' terms (TPS 5.3.32). -/
def pressureRatio (use : ByHorizon Nat) (t : GovernorTuning) : Rat :=
  max (max (horizonTerm t.kappaM use.hour budgetHour) (horizonTerm t.kappaM use.day budgetDay))
    (horizonTerm t.kappaM use.thirtyDays budgetThirtyDays)

/-! ## The readings -/

/-- The descent under hysteresis, reading (a). -/
inductive Descent where
  /-- Straight to the level the ratio names (the Declarer's selection). -/
  | straight
  /-- One level per update. -/
  | oneStep
  /-- To the highest level whose own exit point the ratio has not passed. -/
  | bands
  deriving Repr, DecidableEq

/-- GA4's Retry-After, reading (b). -/
inductive PressureRetry where
  /-- SLOT RETRY-AFTER, the slots' own 5 seconds, with the jitter (the Declarer's selection). -/
  | slot
  /-- The level's pseudo-lag, with the jitter. -/
  | pseudoLag
  /-- RETRY-AFTER's base, with the jitter. -/
  | base
  deriving Repr, DecidableEq

/-- A threshold's own value, reading (c) (inventory X1). -/
inductive ThresholdRule where
  /-- Entered at its threshold, as 5.3.34 (the Declarer's selection). -/
  | atThreshold
  /-- As 7.2.21: BUSY from 0.60, STRAINED above 0.75, OVERLOADED above 0.90. -/
  | aboveThreshold
  deriving Repr, DecidableEq

/-- The external reading's order, reading (d). -/
inductive ExternalOrder where
  /-- The hysteresis step's level, then raised one step, capped (the Declarer's selection). -/
  | raiseAfter
  /-- The raised level, then the hysteresis step toward it. -/
  | raiseBefore
  deriving Repr, DecidableEq

/-- A lane 6 request below OVERLOADED with the anonymous slots full. -/
inductive AnonymousFull where
  /-- Served cached pages only: no 503 below OVERLOADED (TPS 5.3.40 ER3). -/
  | cached
  /-- Refused 503 with SLOT RETRY-AFTER, as a full agent pool is. -/
  | slots
  deriving Repr, DecidableEq

/-- The readings in force, each defaulting to the Declarer's selection. -/
structure PressureReadings where
  /-- (a) -/
  descent : Descent := .straight
  /-- (b) -/
  retry : PressureRetry := .slot
  /-- (c) -/
  threshold : ThresholdRule := .atThreshold
  /-- (d) -/
  external : ExternalOrder := .raiseAfter
  /-- A full lane 6 below OVERLOADED. -/
  anonymousFull : AnonymousFull := .cached
  deriving Repr, DecidableEq

/-! ## The level -/

/-- Whether a level's region includes its threshold: always under `atThreshold` (5.3.34,
"BUSY from 0.60"); under `aboveThreshold` only BUSY's (7.2.21: "CLEAR below 0.60, BUSY to
0.75, STRAINED to 0.90, OVERLOADED above"). -/
def inclusive (rule : ThresholdRule) (l : PressureLevel) : Bool :=
  rule == .atThreshold || l == .busy

/-- The ratio `r` lies in level `l`'s region or above it: at or past its threshold when the
region includes it, past it otherwise. -/
def reaches (rule : ThresholdRule) (l : PressureLevel) (r : Rat) : Bool :=
  if inclusive rule l then decide (entry l ≤ r) else decide (entry l < r)

/-- The level the ratio names (TPS 5.3.34; 7.2.21 under `aboveThreshold`): the highest whose
region the ratio reaches. -/
def levelOf (rule : ThresholdRule) (r : Rat) : PressureLevel :=
  if reaches rule .overloaded r then .overloaded
  else if reaches rule .strained r then .strained
  else if reaches rule .busy r then .busy
  else .clear

/-- The level reached when the ratio has passed the exit point of `prev`, by reading (a);
under `bands`, the highest level below `prev` whose region, widened 0.05 downward, the ratio
still reaches. -/
def descend (rd : PressureReadings) (prev : PressureLevel) (r : Rat) : PressureLevel :=
  match rd.descent with
  | .straight => levelOf rd.threshold r
  | .oneStep => prev.down
  | .bands =>
    match prev with
    | .overloaded =>
      if reaches rd.threshold .strained (r + hysteresis) then .strained
      else if reaches rd.threshold .busy (r + hysteresis) then .busy
      else .clear
    | .strained => if reaches rd.threshold .busy (r + hysteresis) then .busy else .clear
    | _ => .clear

/-- The hysteresis step from `prev` (TPS 5.3.34): the level `lift` makes of the named level
when it is not below `prev`; else `prev` is kept while the ratio, raised 0.05, still reaches
it (its region widened 0.05 downward, the threshold rule's boundary kept), and left for what
`lift` makes of the descent's level once the ratio falls 0.05 below its entry threshold. -/
def hysteresisStep (rd : PressureReadings) (lift : PressureLevel → PressureLevel)
    (prev : PressureLevel) (r : Rat) : PressureLevel :=
  let named := lift (levelOf rd.threshold r)
  if prev.rank ≤ named.rank then named
  else if reaches rd.threshold prev (r + hysteresis) then prev
  else lift (descend rd prev r)

/-- A level's update: the level the hysteresis keeps (`base`), which Custos keeps as the
next update's `prev`, and the level in force, which admission reads and STATUS publishes. -/
structure LevelStep where
  /-- The level the hysteresis keeps. -/
  base : PressureLevel
  /-- The level in force. -/
  inForce : PressureLevel
  deriving Repr, DecidableEq

/-- The level's update (TPS 5.3.31, 5.3.34): from the hysteresis's level `prev`, the ratio
`r`, and the external reading's raised step, in force while `now < externalUntil`. Under
`raiseAfter` the hysteresis keeps the computed level and the step raises only the level in
force, so a raised step ends when the reading's 30 minutes do; under `raiseBefore` the
hysteresis steps toward the raised level and keeps it, leaving it as any level is left. -/
def levelStep (rd : PressureReadings) (prev : PressureLevel) (r : Rat)
    (externalUntil now : Nat) : LevelStep :=
  let raised := decide (now < externalUntil)
  match rd.external with
  | .raiseAfter =>
    let b := hysteresisStep rd id prev r
    ⟨b, if raised then b.up else b⟩
  | .raiseBefore =>
    let b := hysteresisStep rd (fun l => if raised then l.up else l) prev r
    ⟨b, b⟩

/-! ## Theorems -/

/-- The hysteresis step leaves `prev` downward only when the ratio has fallen 0.05 below
its entry threshold. -/
theorem hysteresisStep_hysteresis (rd : PressureReadings) (lift : PressureLevel → PressureLevel)
    (prev : PressureLevel) (r : Rat)
    (h : (hysteresisStep rd lift prev r).rank < prev.rank) :
    reaches rd.threshold prev (r + hysteresis) = false := by
  unfold hysteresisStep at h
  simp only at h
  split at h
  · omega
  · split at h
    · omega
    · rename_i hr; simpa using hr

/-- TPS 5.3.34: a level is left only when the ratio falls 0.05 below its entry threshold,
under every reading. -/
theorem levelStep_hysteresis (rd : PressureReadings) (prev : PressureLevel) (r : Rat)
    (externalUntil now : Nat)
    (h : (levelStep rd prev r externalUntil now).base.rank < prev.rank) :
    reaches rd.threshold prev (r + hysteresis) = false := by
  unfold levelStep at h
  split at h <;> dsimp only at h
  · exact hysteresisStep_hysteresis rd id prev r h
  · exact hysteresisStep_hysteresis rd _ prev r h

/-- Under the selected threshold rule, a level is left only when the ratio falls more
than 0.05 below its entry threshold: kept at exactly 0.05 below, as it is entered at exactly
its threshold. -/
theorem levelStep_hysteresis_atThreshold (rd : PressureReadings) (prev : PressureLevel)
    (r : Rat) (externalUntil now : Nat) (hr : rd.threshold = .atThreshold)
    (h : (levelStep rd prev r externalUntil now).base.rank < prev.rank) :
    r + hysteresis < entry prev := by
  have := levelStep_hysteresis rd prev r externalUntil now h
  simp [reaches, inclusive, hr] at this
  exact Rat.not_le.mp this

/-- A step up never lowers a level. -/
theorem _root_.Principia.Parameters.PressureLevel.rank_le_up (l : PressureLevel) :
    l.rank ≤ l.up.rank := by
  cases l <;> decide

/-- The external reading only tightens (TPS 5.3.31): the level in force is never below the
level the hysteresis keeps, and without a reading in force the two are the same. -/
theorem levelStep_external (rd : PressureReadings) (prev : PressureLevel) (r : Rat)
    (externalUntil now : Nat) :
    (levelStep rd prev r externalUntil now).base.rank ≤
        (levelStep rd prev r externalUntil now).inForce.rank ∧
      (externalUntil ≤ now →
        (levelStep rd prev r externalUntil now).inForce =
          (levelStep rd prev r externalUntil now).base) := by
  unfold levelStep
  simp only
  split
  · by_cases hn : now < externalUntil
    · simp only [hn, decide_true, ite_true]
      exact ⟨PressureLevel.rank_le_up _, fun h => absurd hn (by omega)⟩
    · simp only [hn, decide_false]
      exact ⟨Nat.le_refl _, fun _ => rfl⟩
  · exact ⟨Nat.le_refl _, fun _ => rfl⟩

end Principia.Governor
