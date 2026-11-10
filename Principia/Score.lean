import Principia.Wire
import Principia.Beta
import Principia.Score.PowSum

/-!
# The reliability score

v1's `tpc_score` 0.1.0: the machinery of the reliability score (CR11, CR12, as PMP-TPM 0.12.0 words them): the evidence posterior with the diversity
quota and idle widening, the standing comparison, RANK and the TRUST TIER, the Prime
selection, the state function with its caps and hysteresis, the score update under the
leader-following law, the confirmed-violation cut, the trip, the inquiry cost, the override
and the pad, the trust-tier gate on a held record's release, the inheritance on a declared continuation,
the user-score aggregation and the sponsor cut. Each function is v1's, with its argument
checks, its refusal words and their order, and its rules as v1's docstring states them
(DQ1 to DQ3, EV1 to EV4, ST1, RK1 to RK3, PS1 to PS3, PL1 to PL3, SS1 to SS3, PA1, SU1 to
SU2, TR1, IQ1 to IQ2, OV1 to OV2, PD1 to PD2, IN1, UA1 to UA3).

**Numbers** (the Declarer's choice of exact values): every number is the exact value. Inputs are read as the
decimals they spell; sums, products, clips and comparisons are exact on rationals; the
event weights `2^(-age / HALF-LIFE)` are exact sums of powers of 2 (`PowSum`); the mean and
the interval of the evidence posterior are the Beta layer's (`Principia.Beta`). v1 computed
in doubles and printed twelve digits; on v1's 487 cases no printed number differs from the
exact value's (the score vector tests). Where v1 wrote a rule against the double type, the rule
is kept as v1's text states it: the inquiry cost is infinite past `k' > 1024` (IQ2). Where
v1 added a guard against its own rounding, the exact rule is used: RANK's tier cut is
`⌈fraction × N⌉` (RK3), where v1 took `⌈fraction × N - 10^-12⌉`; the two differ only when
`fraction × N` lies within `10^-12` above a whole number, which no case of the corpus does.

**The sponsor's part.** `user_score_evidence` hands its pooled events to
`tpc_sponsor.user_evidence`, which v1's `tpc_score` imports; here the order is
turned: this file checks and pools what v1 checked and pooled before that call and gives
the call's input (`UserEvidence.sponsor`), and the sponsor's port, which imports this one,
makes the call (`Principia.Sponsor.evidenceOfInput`, and v1's function whole as
`Principia.Sponsor.scoreUserEvidence`).

**The bound on an exact value.** The functions here form their values unchecked; the same
functions within the bound on an exact value's size, each refused "exact value too large"
where a value could cross it and each answer proved to be the one given here, are
`Principia.Score.Bounded`'s, which the Calculator calls. No case of v1's corpora comes near
the bound.

Corpus: the score corpus (487 cases), run by the score vector tests.
-/

namespace Principia.Score

open Principia.Canonical
open Principia.Beta

/-! ## Words -/

/-- A counterpart's standing relative to an account. -/
inductive Standing where
  | clearlyLower
  | similar
  | clearlyHigher
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Standing where
  members := [.clearlyLower, .similar, .clearlyHigher]
  toWire
    | .clearlyLower => "CLEARLY LOWER"
    | .similar => "SIMILAR"
    | .clearlyHigher => "CLEARLY HIGHER"
  read_toWire a := by cases a <;> decide

/-- An account's state (CR11 STATES), in rising order. -/
inductive AlertState where
  | green
  | yellow
  | orange
  | suspended
  deriving DecidableEq, Repr, Inhabited

instance : WireWord AlertState where
  members := [.green, .yellow, .orange, .suspended]
  toWire
    | .green => "GREEN"
    | .yellow => "YELLOW"
    | .orange => "ORANGE"
    | .suspended => "SUSPENDED"
  read_toWire a := by cases a <;> decide

/-- The state's place in `GREEN < YELLOW < ORANGE < SUSPENDED`. -/
def AlertState.rank : AlertState → Nat
  | .green => 0
  | .yellow => 1
  | .orange => 2
  | .suspended => 3

/-- What moves the state (CR11 hysteresis). -/
inductive StateEvent where
  | landing
  | canaryPass
  | canaryFail
  | auditFinding
  deriving DecidableEq, Repr, Inhabited

instance : WireWord StateEvent where
  members := [.landing, .canaryPass, .canaryFail, .auditFinding]
  toWire
    | .landing => "LANDING"
    | .canaryPass => "CANARY PASS"
    | .canaryFail => "CANARY FAIL"
    | .auditFinding => "AUDIT FINDING"
  read_toWire a := by cases a <;> decide

/-- How a state step moved the state. -/
inductive StateChange where
  | up
  | same
  | down
  | wait
  | reset
  | held
  | audit
  deriving DecidableEq, Repr, Inhabited

instance : WireWord StateChange where
  members := [.up, .same, .down, .wait, .reset, .held, .audit]
  toWire
    | .up => "UP"
    | .same => "SAME"
    | .down => "DOWN"
    | .wait => "WAIT"
    | .reset => "RESET"
    | .held => "HELD"
    | .audit => "AUDIT"
  read_toWire a := by cases a <;> decide

/-- Whose score a step updates (CR11, CR12). -/
inductive UpdateRole where
  | follower
  | prime
  | user
  | userPrime
  deriving DecidableEq, Repr, Inhabited

instance : WireWord UpdateRole where
  members := [.follower, .prime, .user, .userPrime]
  toWire
    | .follower => "FOLLOWER"
    | .prime => "PRIME"
    | .user => "USER"
    | .userPrime => "USER PRIME"
  read_toWire a := by cases a <;> decide

/-- Why an account was re-certified. -/
inductive ChangeCause where
  | dis
  | suite
  | family
  | promptNewAgent
  | model
  deriving DecidableEq, Repr, Inhabited

instance : WireWord ChangeCause where
  members := [.dis, .suite, .family, .promptNewAgent, .model]
  toWire
    | .dis => "DIS"
    | .suite => "SUITE"
    | .family => "FAMILY"
    | .promptNewAgent => "PROMPT NEW AGENT"
    | .model => "MODEL"
  read_toWire a := by cases a <;> decide

/-- A resolved event's side: a match (`FOR`) or a finding against (`AGAINST`). -/
inductive Side where
  | supporting
  | opposing
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Side where
  members := [.supporting, .opposing]
  toWire
    | .supporting => "FOR"
    | .opposing => "AGAINST"
  read_toWire a := by cases a <;> decide

/-- Why the Prime is the one named (PS1 to PS3). -/
inductive PrimeReason where
  | override
  | none
  | topRank
  | highestInTier
  deriving DecidableEq, Repr, Inhabited

instance : WireWord PrimeReason where
  members := [.override, .none, .topRank, .highestInTier]
  toWire
    | .override => "OVERRIDE"
    | .none => "NONE"
    | .topRank => "TOP RANK"
    | .highestInTier => "HIGHEST S IN TIER"
  read_toWire a := by cases a <;> decide

/-- A trip's verdict and reason (TR1). -/
inductive TripReason where
  | first
  | level
  | window
  | above
  deriving DecidableEq, Repr, Inhabited

instance : WireWord TripReason where
  members := [.first, .level, .window, .above]
  toWire
    | .first => "FIRST"
    | .level => "LEVEL"
    | .window => "WINDOW"
    | .above => "ABOVE"
  read_toWire a := by cases a <;> decide

/-- Why an override's or a pad's declared grant is refused (OV1, PD1). -/
inductive DeclRefusal where
  | fingerprint
  | notCertified
  | suspended
  | nonceForm
  | nonce
  | reason
  | bounds
  | value
  | padMax
  | nonReference
  deriving DecidableEq, Repr, Inhabited

instance : WireWord DeclRefusal where
  members := [.fingerprint, .notCertified, .suspended, .nonceForm, .nonce, .reason, .bounds,
    .value, .padMax, .nonReference]
  toWire
    | .fingerprint => "FINGERPRINT"
    | .notCertified => "NOT CERTIFIED"
    | .suspended => "SUSPENDED"
    | .nonceForm => "NONCE FORM"
    | .nonce => "NONCE"
    | .reason => "REASON"
    | .bounds => "BOUNDS"
    | .value => "VALUE"
    | .padMax => "PAD MAX"
    | .nonReference => "NON-REFERENCE"
  read_toWire a := by cases a <;> decide

/-- Where an override stands in time. -/
inductive OverrideStatus where
  | cancelled
  | pending
  | effective
  deriving DecidableEq, Repr, Inhabited

instance : WireWord OverrideStatus where
  members := [.cancelled, .pending, .effective]
  toWire
    | .cancelled => "CANCELLED"
    | .pending => "PENDING"
    | .effective => "EFFECTIVE"
  read_toWire a := by cases a <;> decide

/-- The trust-tier gate's answer. -/
inductive GateAnswer where
  | pass
  | notInTier
  | overrideMark
  deriving DecidableEq, Repr, Inhabited

/-! ## Shared readers and bounds -/

/-- v1's `TIME_MAX`, the last second of the year 9999. -/
def timeMax : Int := 253402300799

/-- v1's `COUNT_MAX`. -/
def countMax : Int := 1000000000

/-- A word of an enumeration, or v1's refusal. -/
def wordOf (α : Type) [WireWord α] (v : Canonical.Value) (refusal : String) : Except String α :=
  match v with
  | .str s => need (WireWord.ofWire? s) refusal
  | _ => .error refusal

/-- A list, or v1's refusal. -/
def listOf (v : Canonical.Value) (refusal : String) : Except String (List Canonical.Value) :=
  match v with
  | .arr xs => .ok xs
  | _ => .error refusal

/-- `max lo (min x hi)` as v1's `_clip`: below `lo` gives `lo`, above `hi` gives `hi`. -/
def clip (x lo hi : Rat) : Rat := if x < lo then lo else if hi < x then hi else x

/-- A number in `[0, 1]`, or v1's refusal. -/
def unitNumber (v : Canonical.Value) (refusal : String) : Except String Rat := do
  let x ← need (numberOf? v) refusal
  check (0 ≤ x && x ≤ 1) refusal
  return x

/-- A string of exactly `n` lowercase hexadecimal digits (v1 `_is_hex`). -/
def isHex (s : String) (n : Nat) : Bool :=
  s.length == n && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Only spaces, tabs, line feeds and carriage returns (v1 `_blank`). -/
def blank (s : String) : Bool := s.all fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The integer `n` as a natural number (`n ≥ 0` checked before). -/
def natOf (n : Int) : Nat := n.toNat

/-! ## diversity_quota (DQ1 to DQ3) -/

/-- DQ2: the fraction of a match of base weight `g` admitted, the window's FOR weight being
`w` and the counterpart's part of it `wc`. -/
def quotaFraction (w wc g cMax : Rat) : Rat := clip ((cMax * (w + g) - wc) / g) 0 1

/-- The quota's answer: `q`, the window's weight `W`, the counterpart's `W_c`, the
admitted weight `g q`. -/
structure Quota where
  q : Rat
  w : Rat
  wc : Rat
  admitted : Rat
  deriving Repr

/-- DQ1 to DQ3 over a window of `(counterpart, weight)`. -/
def quotaOf (window : List (Option String × Rat)) (counterpart : String) (g cMax : Rat) : Quota :=
  let w := window.foldl (fun s e => s + e.2) 0
  let wc := window.foldl (fun s e => if e.1 == some counterpart then s + e.2 else s) 0
  let q := quotaFraction w wc g cMax
  ⟨q, w, wc, g * q⟩

/-- The arguments of v1 `diversity_quota`, checked in v1's order: the window's entries, the
counterpart, `g` and `c_max`. -/
def quotaArgs (window counterpart g cMax : Canonical.Value) :
    Except String (List (Option String × Rat) × String × Rat × Rat) := do
  let xs ← listOf window "window"
  let cp ← need (nameOf? counterpart) "counterpart"
  let gf ← need (numberOf? g) "g"
  check (0 < gf) "g"
  let cm ← need (numberOf? cMax) "c_max"
  check (0 < cm && cm < 1) "c_max"
  let entries ← xs.mapM fun e => do
    let ms ← need (keysAre? e ["counterpart", "weight"]) "window"
    let c ← match member ms "counterpart" with
      | .null => pure none
      | v => some <$> need (nameOf? v) "window"
    let w ← need (numberOf? (member ms "weight")) "window"
    check (0 ≤ w) "window"
    return (c, w)
  return (entries, cp, gf, cm)

/-- v1 `diversity_quota(window, counterpart, g, c_max)`. -/
def diversityQuota (window counterpart g cMax : Canonical.Value) : Except String Quota := do
  let (entries, cp, gf, cm) ← quotaArgs window counterpart g cMax
  return quotaOf entries cp gf cm

/-- The quota over exact sums of powers of 2 (the user aggregate's window, UA2): the same
rule, the clip decided exactly or from bounds; `none` when a comparison is not settled. -/
def quotaPow (window : List (Option String × PowSum)) (counterpart : String) (g cMax : Rat) :
    Option PowSum :=
  let w := window.foldl (fun s e => PowSum.add s e.2) PowSum.zero
  let wc := window.foldl (fun s e => if e.1 == some counterpart then PowSum.add s e.2 else s)
    PowSum.zero
  let v := PowSum.scale (1 / g) (PowSum.sub (PowSum.scale cMax (PowSum.add w (PowSum.ofRat g))) wc)
  v.clip01

/-! ## evidence (EV1 to EV4) -/

/-- A resolved event as the evidence layer takes it. -/
structure EvidenceEvent where
  side : Side
  weight : Rat
  age : Nat
  pad : Bool
  deriving Repr

/-- PRIOR, HALF-LIFE and T_idle. -/
structure Prior where
  a0 : Rat
  b0 : Rat
  halfLife : Rat
  tIdle : Rat
  deriving Repr

/-- EV1: an event's weight aged by `2^(-age / HALF-LIFE)`, exactly. -/
def aged (halfLife w : Rat) (age : Nat) : PowSum :=
  PowSum.scale w (PowSum.pow2 (-(age : Rat) / halfLife))

/-- The evidence: F, A, n, E with its interval, and the idle factor. -/
structure Evidence where
  f : PowSum
  a : PowSum
  n : Nat
  e : Quantity
  lo : Quantity
  hi : Quantity
  factor : Rat

/-- EV3: the idle factor, `1 / (1 + (days - T_idle) / T_idle)` past T_idle, else 1. -/
def idleFactor (days tIdle : Rat) : Rat :=
  if tIdle < days then 1 / (1 + (days - tIdle) / tIdle) else 1

/-- EV1 to EV4. -/
def evidenceOf (events : List EvidenceEvent) (days : Rat) (p : Prior) : Evidence :=
  let sum (s : Side) := events.foldl (fun acc e =>
    if e.side == s then PowSum.add acc (aged p.halfLife e.weight e.age) else acc) PowSum.zero
  let n := (events.filter (!·.pad)).length
  let factor := idleFactor days p.tIdle
  let f := PowSum.scale factor (sum .supporting)
  let a := PowSum.scale factor (sum .opposing)
  let sa := PowSum.add (PowSum.ofRat p.a0) f
  let sb := PowSum.add (PowSum.ofRat p.b0) a
  let (lo, hi) := interval sa.toQuantity sb.toQuantity (95 / 100)
  ⟨f, a, n, PowSum.ratio sa (PowSum.add sa sb), lo, hi, factor⟩

/-- PRIOR, HALF-LIFE and T_idle from the params, in v1's order. -/
def readPrior (params : Canonical.Value) : Except String Prior := do
  let a0 ← paramNumber params "a0" 0 1000000000 true
  let b0 ← paramNumber params "b0" 0 1000000000 true
  let hl ← paramNumber params "HALF-LIFE" 0 1000000000 true
  let t ← paramNumber params "T_idle" 0 1000000000 true
  return ⟨a0, b0, hl, t⟩

/-- The arguments of v1 `evidence`, checked in v1's order: the events, the idle days and
PRIOR, HALF-LIFE and T_idle. -/
def evidenceArgs (events idle params : Canonical.Value) :
    Except String (List EvidenceEvent × Rat × Prior) := do
  let xs ← listOf events "events"
  let ims ← need (keysAre? idle ["days"]) "idle"
  let days ← need (numberOf? (member ims "days")) "idle"
  check (0 ≤ days) "idle"
  let p ← readPrior params
  let evs ← xs.mapM fun e => do
    let ms ← need (keysAre? e ["kind", "weight", "age"] ["pad"]) "events"
    let side ← wordOf Side (member ms "kind") "events"
    let w ← need (numberOf? (member ms "weight")) "events"
    let age ← need (intIn? (member ms "age") 0 countMax) "events"
    check (0 ≤ w) "events"
    let pad ← match ms.lookup "pad" with
      | none => pure false
      | some v => need (boolOf? v) "events"
    return (⟨side, w, natOf age, pad⟩ : EvidenceEvent)
  return (evs, days, p)

/-- v1 `evidence(events, idle, params)`. -/
def evidence (events idle params : Canonical.Value) : Except String Evidence := do
  let (evs, days, p) ← evidenceArgs events idle params
  return evidenceOf evs days p

/-! ## score_interval -/

/-- `[S - (E - lo), S + (hi - E)]`, each clipped to `[0, 1]`. -/
def scoreIntervalOf (s e lo hi : Rat) : Rat × Rat :=
  (clip (s - (e - lo)) 0 1, clip (s + (hi - e)) 0 1)

/-- The arguments of v1 `score_interval`, checked in v1's order. -/
def intervalArgs (s e lo hi : Canonical.Value) : Except String (Rat × Rat × Rat × Rat) := do
  let s ← unitNumber s "S"
  let e ← need (numberOf? e) "interval"
  let l ← need (numberOf? lo) "interval"
  let h ← need (numberOf? hi) "interval"
  check (0 ≤ l && l ≤ e && e ≤ h && h ≤ 1) "interval"
  return (s, e, l, h)

/-- v1 `score_interval(S, E, lo, hi)`. -/
def scoreInterval (s e lo hi : Canonical.Value) : Except String (Rat × Rat) := do
  let (s, e, l, h) ← intervalArgs s e lo hi
  return scoreIntervalOf s e l h

/-! ## standing (ST1) -/

/-- An interval with its OVERRIDE mark. -/
structure Placed where
  lo : Rat
  hi : Rat
  override : Bool
  deriving Repr

/-- ST1: `y` relative to `x`. -/
def standingOf (x y : Placed) : Standing :=
  if x.hi < y.lo && !y.override then .clearlyHigher
  else if y.hi < x.lo then .clearlyLower
  else .similar

/-- An interval `{lo, hi, override?}`, `0 ≤ lo ≤ hi ≤ 1` (v1 `_iv`). -/
def readPlaced (v : Canonical.Value) : Except String Placed := do
  let ms ← need (keysAre? v ["lo", "hi"] ["override"]) "interval"
  let lo ← need (numberOf? (member ms "lo")) "interval"
  let hi ← need (numberOf? (member ms "hi")) "interval"
  check (0 ≤ lo && lo ≤ hi && hi ≤ 1) "interval"
  let ov ← match ms.lookup "override" with
    | none => pure false
    | some b => need (boolOf? b) "interval"
  return ⟨lo, hi, ov⟩

/-- v1 `standing(x, y)`. -/
def standing (x y : Canonical.Value) : Except String Standing := do
  let x ← readPlaced x
  let y ← readPlaced y
  return standingOf x y

/-! ## rank (RK1 to RK3) and prime_select (PS1 to PS3) -/

/-- An account as RANK takes it. -/
structure Account where
  name : String
  s : Rat
  lo : Rat
  hi : Rat
  n : Nat
  active : Bool
  deriving Repr

/-- The interval's width. -/
def Account.width (a : Account) : Rat := a.hi - a.lo

/-- v1's insertion of `x` before the first element that `cmp` puts after it. -/
def insertBy {α : Type} (cmp : α → α → Ordering) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if cmp y x == .gt then x :: y :: ys else y :: insertBy cmp x ys

/-- v1's `_sort`: insertion sort by a comparator, stable. -/
def sortBy {α : Type} (cmp : α → α → Ordering) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy cmp x acc) []

/-- Larger first. -/
def descending (a b : Rat) : Ordering := if b < a then .lt else if a < b then .gt else .eq

/-- Smaller first. -/
def ascending (a b : Rat) : Ordering := descending b a

/-- RK1: `S_lo` descending, width ascending, `n` descending, name ascending. -/
def rankOrder (a b : Account) : Ordering :=
  (descending a.lo b.lo).then <| (ascending a.width b.width).then <|
    (descending a.n b.n).then (compare a.name b.name)

/-- PS2: `S` descending, then as RK1. -/
def primeOrder (a b : Account) : Ordering :=
  (descending a.s b.s).then <| (ascending a.width b.width).then <|
    (descending a.n b.n).then (compare a.name b.name)

/-- A row of RANK: the account, and for an active account its position, percentile and
whether it is in the TRUST TIER. -/
structure RankRow where
  name : String
  place : Option (Nat × Rat)
  tier : Bool
  deriving Repr

/-- RANK's answer: N, the tier's cut, the rows. -/
structure Rank where
  count : Nat
  cut : Nat
  rows : List RankRow
  deriving Repr

/-- RK3: the TRUST TIER's size, `⌈fraction × N⌉`. -/
def tierCut (fraction : Rat) (count : Nat) : Nat :=
  if count = 0 then 0 else (fraction * count).ceil.toNat

/-- RK1 to RK3. -/
def rankOf (accounts : List Account) (on : Bool) (fraction : Rat) : Rank :=
  let ordered := sortBy rankOrder (accounts.filter (·.active))
  let count := ordered.length
  let cut := tierCut fraction count
  let rows := ordered.zipIdx.map fun (a, i) =>
    ⟨a.name, some (i + 1, 1 - (i : Rat) / count), on && decide (i + 1 ≤ cut)⟩
  ⟨count, if on then cut else 0, rows ++ (accounts.filter (!·.active)).map fun a => ⟨a.name, none, false⟩⟩

/-- The accounts (v1 `_accounts`): names unique; `0 ≤ S_lo ≤ S_hi ≤ 1`, `0 ≤ S ≤ 1`. -/
def readAccounts (v : Canonical.Value) : Except String (List Account) := do
  let xs ← listOf v "accounts"
  let (out, _) ← xs.foldlM (fun (acc : List Account × List String) a => do
    let ms ← need (keysAre? a ["account", "S", "S_lo", "S_hi", "n", "active"]) "accounts"
    let name ← need (nameOf? (member ms "account")) "accounts"
    check (!acc.2.contains name) "accounts"
    let s ← need (numberOf? (member ms "S")) "accounts"
    let lo ← need (numberOf? (member ms "S_lo")) "accounts"
    let hi ← need (numberOf? (member ms "S_hi")) "accounts"
    let n ← need (intIn? (member ms "n") 0 countMax) "accounts"
    let active ← need (boolOf? (member ms "active")) "accounts"
    check (0 ≤ lo && lo ≤ hi && hi ≤ 1 && 0 ≤ s && s ≤ 1) "accounts"
    return (acc.1 ++ [⟨name, s, lo, hi, natOf n, active⟩], name :: acc.2)) ([], [])
  return out

/-- The arguments of v1 `rank`: the accounts and the TRUST TIER. -/
def rankArgs (accounts params : Canonical.Value) : Except String (List Account × Bool × Rat) := do
  let acc ← readAccounts accounts
  let (on, fraction) ← paramFlag params "TRUST TIER"
  return (acc, on, fraction)

/-- v1 `rank(accounts, params)`. -/
def rank (accounts params : Canonical.Value) : Except String Rank := do
  let (acc, on, fraction) ← rankArgs accounts params
  return rankOf acc on fraction

/-- PS1 to PS3: the Prime and why. -/
def primeOf (accounts : List Account) (override : Option String) (overtake on : Bool)
    (fraction : Rat) : Option String × PrimeReason :=
  match override with
  | some o => (some o, .override)
  | none =>
    let active := accounts.filter (·.active)
    if active.isEmpty then (none, .none)
    else
      let rk := rankOf accounts on fraction
      if overtake then ((rk.rows.head?.map (·.name)), .topRank)
      else
        let tier := (rk.rows.filter (·.tier)).map (·.name)
        match sortBy primeOrder (active.filter fun a => tier.contains a.name) with
        | [] => (none, .none)
        | p :: _ => (some p.name, .highestInTier)

/-- The arguments of v1 `prime_select`, checked in v1's order: the accounts, OVERTAKE, the
TRUST TIER and the override. -/
def primeArgs (accounts override params : Canonical.Value) :
    Except String (List Account × Option String × Bool × Bool × Rat) := do
  let acc ← readAccounts accounts
  let overtake ← paramBool params "OVERTAKE"
  let (on, fraction) ← paramFlag params "TRUST TIER"
  let ov ← match override with
    | .null => pure none
    | v =>
      let o ← need (nameOf? v) "override"
      check (acc.any fun a => a.name == o && a.active) "override"
      pure (some o)
  return (acc, ov, overtake, on, fraction)

/-- v1 `prime_select(accounts, override, params)`. -/
def primeSelect (accounts override params : Canonical.Value) :
    Except String (Option String × PrimeReason) := do
  let (acc, ov, overtake, on, fraction) ← primeArgs accounts override params
  return primeOf acc ov overtake on fraction

/-! ## pending_level (PL1 to PL3) -/

/-- A pending non-corroboration. -/
structure Pending where
  counterpart : String
  snapshot : String
  standing : Standing
  eta : Int
  independent : Bool
  deriving Repr

/-- The level and its counts: H, I, SIM, LOW, counted, expired. -/
structure PendingLevel where
  level : AlertState
  h : Nat
  i : Nat
  sim : Nat
  low : Nat
  counted : Nat
  expired : Nat
  deriving Repr

/-- PL1 to PL3. -/
def pendingLevelOf (items : List Pending) (now : Int) (pMax warn susp : Nat) : PendingLevel :=
  let step := fun (st : List String × List Pending × Nat) (it : Pending) =>
    let (seen, counted, expired) := st
    if it.eta < now then (seen, counted, expired + 1)
    else if seen.contains it.counterpart then st
    else (it.counterpart :: seen, if counted.length < pMax then counted ++ [it] else counted, expired)
  let (_, counted, expired) := items.foldl step ([], [], 0)
  let high := counted.filter (·.standing == .clearlyHigher)
  let h := high.length
  let i := ((high.filter (·.independent)).map (·.snapshot)).eraseDups.length
  let sim := (counted.filter (·.standing == .similar)).length
  let low := (counted.filter (·.standing == .clearlyLower)).length
  let level : AlertState :=
    if counted.isEmpty then .green
    else if susp ≤ i then .suspended
    else if (2 ≤ h && i < susp) || warn ≤ sim then .orange
    else .yellow
  ⟨level, h, i, sim, low, counted.length, expired⟩

/-- v1 `pending_level(items, now, params)`. -/
def pendingLevel (items now params : Canonical.Value) : Except String PendingLevel := do
  let xs ← listOf items "items"
  let t ← need (intIn? now 0 timeMax) "items"
  let pMax ← paramInt params "P_max" 1 countMax
  let warn ← paramInt params "WARN COUNT" 1 countMax
  let susp ← paramInt params "SUSPEND COUNT" 1 countMax
  let its ← xs.mapM fun it => do
    let ms ← need (keysAre? it ["counterpart", "snapshot", "standing", "eta"] ["independent"]) "items"
    let cp ← need (nameOf? (member ms "counterpart")) "items"
    let snap ← need (nameOf? (member ms "snapshot")) "items"
    let st ← wordOf Standing (member ms "standing") "items"
    let eta ← need (intIn? (member ms "eta") 0 timeMax) "items"
    let ind ← match ms.lookup "independent" with
      | none => pure true
      | some v => need (boolOf? v) "items"
    return (⟨cp, snap, st, eta, ind⟩ : Pending)
  return pendingLevelOf its t (natOf pMax) (natOf warn) (natOf susp)

/-! ## state_step (SS1 to SS3) -/

/-- The state after a step, the passes counted and the change. -/
structure StateStep where
  state : AlertState
  passes : Nat
  change : StateChange
  deriving Repr, DecidableEq

/-- SS1 to SS3. -/
def stateStepOf (st : AlertState) (passes : Nat) (level : AlertState) (ev : StateEvent)
    (orangePasses : Nat) : StateStep :=
  if st == .suspended then
    if ev == .auditFinding then ⟨level, 0, .audit⟩ else ⟨st, 0, .held⟩
  else if st.rank < level.rank then ⟨level, 0, .up⟩
  else if st.rank == level.rank then ⟨st, 0, .same⟩
  else if ev == .canaryFail then ⟨st, 0, .reset⟩
  else if ev != .canaryPass then ⟨st, passes, .wait⟩
  else
    let need := if st == .orange then orangePasses else 1
    if need ≤ passes + 1 then ⟨level, 0, .down⟩ else ⟨st, passes + 1, .wait⟩

/-- v1 `state_step(prev, level, event, params)`. -/
def stateStep (prev level event params : Canonical.Value) : Except String StateStep := do
  let ms ← need (keysAre? prev ["state", "passes"]) "prev"
  let st ← wordOf AlertState (member ms "state") "prev"
  let passes ← need (intIn? (member ms "passes") 0 countMax) "prev"
  let lv ← wordOf AlertState level "level"
  let ev ← wordOf StateEvent event "event"
  let orange ← paramInt params "ORANGE PASSES" 1 countMax
  return stateStepOf st (natOf passes) lv ev (natOf orange)

/-! ## peer_activity (PA1) -/

/-- PA1: the distinct counterparts among the independent events, and `min(1, count /
RATING PERIOD)`. -/
def activityOf (events : List (String × Bool)) (period : Nat) : Nat × Rat :=
  let count := ((events.filter (·.2)).map (·.1)).eraseDups.length
  let a : Rat := (count : Rat) / period
  (count, if 1 < a then 1 else a)

/-- The arguments of v1 `peer_activity`: the events and the RATING PERIOD. -/
def activityArgs (events params : Canonical.Value) : Except String (List (String × Bool) × Nat) := do
  let xs ← listOf events "events"
  let period ← paramInt params "RATING PERIOD" 1 countMax
  let evs ← xs.mapM fun e => do
    let ms ← need (keysAre? e ["counterpart", "independent"]) "events"
    let cp ← need (nameOf? (member ms "counterpart")) "events"
    let ind ← need (boolOf? (member ms "independent")) "events"
    return (cp, ind)
  return (evs, natOf period)

/-- v1 `peer_activity(events, params)`. -/
def peerActivity (events params : Canonical.Value) : Except String (Nat × Rat) := do
  let (evs, period) ← activityArgs events params
  return activityOf evs period

/-! ## score_update (SU1, SU2) -/

/-- The law's declared parameters. -/
structure UpdateParams where
  ceiling : Rat
  kBase : Rat
  kMin : Rat
  kMax : Rat
  eps : Rat
  deltaMax : Rat
  overtake : Bool
  deriving Repr

/-- The new score, the target, the gain, the step and whether the step was bounded. -/
structure Update where
  s : Rat
  target : Rat
  k : Rat
  step : Rat
  clipped : Bool
  deriving Repr

/-- The step bounded by `delta_max` on both sides, and whether it was. -/
def boundStep (step dmax : Rat) : Rat × Bool :=
  if dmax < step then (dmax, true) else if step < -dmax then (-dmax, true) else (step, false)

/-- The leader-following law (CR11; 27): a follower moves toward `min(E, S_P)`
(OVERTAKE off) or `min(E, PRIME CEILING)` (on) at gain
`clip(k_base ((S_P - S) / S_P) a, k_min, k_max)`; the Prime climbs toward PRIME CEILING at
`k_base (PRIME CEILING - S_P) a eps_P`; the step at most `delta_max`, the result in
`[0, PRIME CEILING]`. -/
def updateOf (role : UpdateRole) (s e sp a : Rat) (u : UpdateParams) : Update :=
  if role == .prime || role == .userPrime then
    let k := u.kBase * (u.ceiling - sp) * a * u.eps
    let (step, cl) := boundStep (k * (u.ceiling - sp)) u.deltaMax
    ⟨clip (sp + step) 0 u.ceiling, u.ceiling, k, step, cl⟩
  else
    let t0 := if e < u.ceiling then e else u.ceiling
    let t := if !u.overtake && sp < t0 then sp else t0
    let k := clip (u.kBase * ((sp - s) / sp) * a) u.kMin u.kMax
    let (step, cl) := boundStep (k * (t - s)) u.deltaMax
    ⟨clip (s + step) 0 u.ceiling, t, k, step, cl⟩

/-- The arguments of v1 `score_update`, checked in v1's order: the role, the law's declared
parameters, `S`, `E`, `S_P` and `a`. -/
def updateArgs (role s e sp a params : Canonical.Value) :
    Except String (UpdateRole × Rat × Rat × Rat × Rat × UpdateParams) := do
  let r ← wordOf UpdateRole role "role"
  let ceil ← paramNumber params "PRIME CEILING" 0 1 true
  let kb ← paramNumber params "k_base" 0 1000000000
  let kmin ← paramNumber params "k_min" 0 1000000000
  let kmax ← paramNumber params "k_max" 0 1000000000
  let eps ← paramNumber params "eps_P" 0 1000000000
  let dmax ← paramNumber params "delta_max" 0 1000000000
  let ov ← paramBool params "OVERTAKE"
  check (kmin ≤ kmax) "params:k_min"
  let s ← unitNumber s "S"
  let e ← unitNumber e "E"
  let sp ← need (numberOf? sp) "S_P"
  check (0 < sp && sp ≤ 1) "S_P"
  let a ← unitNumber a "a"
  return (r, s, e, sp, a, ⟨ceil, kb, kmin, kmax, eps, dmax, ov⟩)

/-- v1 `score_update(role, S, E, S_P, a, params)`. -/
def scoreUpdate (role s e sp a params : Canonical.Value) : Except String Update := do
  let (r, s, e, sp, a, u) ← updateArgs role s e sp a params
  return updateOf r s e sp a u

/-! ## violation_cut, trip, inquire (CR11; 28.1 to 28.3) -/

/-- The cut score, `m` and the AGAINST weight `h(standing)` added. -/
structure Cut where
  s : Rat
  m : Rat
  aInc : Rat
  deriving Repr

/-- `h`, an object of the three standings' AGAINST weights, each `≥ 0` (v1 `_ph`). -/
def readH (params : Canonical.Value) : Except String (Standing → Rat) := do
  let ms ← need (keysAre? (← param params "h") ["CLEARLY LOWER", "SIMILAR", "CLEARLY HIGHER"])
    "params:h"
  let get := fun (k : String) => do
    let x ← need (numberOf? (member ms k)) "params:h"
    check (0 ≤ x) "params:h"
    return x
  let lo ← get "CLEARLY LOWER"
  let si ← get "SIMILAR"
  let hi ← get "CLEARLY HIGHER"
  return fun | .clearlyLower => lo | .similar => si | .clearlyHigher => hi

/-- A confirmed violation's cut, `S (1 - m)`. -/
def cutOf (s m : Rat) : Rat := s * (1 - m)

/-- The arguments of v1 `violation_cut`, checked in v1's order: `S`, `m` of the class and
`h(standing)`. -/
def cutArgs (s mClass standing params : Canonical.Value) : Except String (Rat × Rat × Rat) := do
  let s ← unitNumber s "S"
  let k ← need (intIn? mClass 1 3) "m_class"
  let st ← wordOf Standing standing "standing"
  let m ← paramNumber params s!"m_{k}" 0 1
  let h ← readH params
  return (s, m, h st)

/-- v1 `violation_cut(S, m_class, standing, params)`: `S (1 - m)`, and `h(standing)`. -/
def violationCut (s mClass standing params : Canonical.Value) : Except String Cut := do
  let (s, m, aInc) ← cutArgs s mClass standing params
  return ⟨cutOf s m, m, aInc⟩

/-- TR1: the trip's verdict (`true` for TRIP) and reason. -/
def tripOf (s : Rat) (inTier : Bool) (priorAges : List Nat) (level : Rat) (window : Nat) :
    Bool × TripReason :=
  if !inTier then (true, .first)
  else if s < level then (true, .level)
  else if priorAges.any (· ≤ window) then (true, .window)
  else (false, .above)

/-- v1 `trip(S_after, in_tier, prior_ages, params)`. -/
def trip (s inTier priorAges params : Canonical.Value) : Except String (Bool × TripReason) := do
  let s ← unitNumber s "S"
  let it ← need (boolOf? inTier) "in_tier"
  let xs ← listOf priorAges "prior_ages"
  let ages ← xs.mapM fun x => need (intIn? x 0 countMax) "prior_ages"
  let level ← paramNumber params "TRIP LEVEL" 0 1
  let window ← paramInt params "TRIP WINDOW" 1 countMax
  return tripOf s it (ages.map natOf) level (natOf window)

/-- The inquiry: its cost (`none`: infinite), the new score, `k'`, whether it fell inside
the COOL-OFF window, and the new state `{last, k}`. -/
structure Inquiry where
  cost : Option Rat
  s : Rat
  k : Nat
  inside : Bool
  last : Nat
  deriving Repr

/-- IQ2: the `k'`-th inquiry's cost, `w_I 2^(k' - 1)`, infinite (`none`) past `k' > 1024`
as v1's text states. -/
def inquiryCost (k' : Nat) (wI : Rat) : Option Rat :=
  if 1023 < k' - 1 then none else some (wI * (2 : Rat) ^ (k' - 1))

/-- The score after a cost, floored at 0; an infinite cost leaves 0. -/
def afterCost (s : Rat) : Option Rat → Rat
  | none => 0
  | some c => if s - c < 0 then 0 else s - c

/-- IQ1, IQ2: inside the COOL-OFF window when the last inquiry was fewer than COOL-OFF blocks
before; the cost doubles inside it and restarts at `w_I` outside. -/
def inquireOf (last : Option Nat) (k block : Nat) (s wI : Rat) (cool : Nat) : Inquiry :=
  let inside := match last with
    | some l => decide (block - l < cool)
    | none => false
  let k' := if inside then k + 1 else 1
  ⟨inquiryCost k' wI, afterCost s (inquiryCost k' wI), k', inside, block⟩

/-- The arguments of v1 `inquire`, checked in v1's order: the state, the block, `S`, `w_I`
and COOL-OFF. -/
def inquireArgs (state block s params : Canonical.Value) :
    Except String (Option Nat × Nat × Nat × Rat × Rat × Nat) := do
  let ms ← need (keysAre? state ["last", "k"]) "state"
  let last ← match member ms "last" with
    | .null => pure none
    | v => some <$> need (intIn? v 0 countMax) "state"
  let k ← need (intIn? (member ms "k") 0 countMax) "state"
  let b ← need (intIn? block 0 countMax) "block"
  check (match last with | some l => l ≤ b | none => true) "block"
  let s ← unitNumber s "S"
  let wI ← paramNumber params "w_I" 0 1
  let cool ← paramInt params "COOL-OFF" 1 countMax
  return (last.map natOf, natOf k, natOf b, s, wI, natOf cool)

/-- v1 `inquire(state, block, S, params)`. -/
def inquire (state block s params : Canonical.Value) : Except String Inquiry := do
  let (last, k, b, s, wI, cool) ← inquireArgs state block s params
  return inquireOf last k b s wI cool

/-! ## The override and the pad (OV1, OV2, PD1, PD2) -/

/-- An override's or a pad's declared grant (v1's `decl`), with the facts it is checked
against. -/
structure DeclaredGrant where
  fingerprint : String
  value : Canonical.Value
  nonce : String
  time : Int
  reason : String
  certified : List String
  suspendedList : List String
  nonces : List String
  prime : Option String
  deriving Repr

/-- A list of strings, or v1's refusal. -/
def stringsOf (v : Canonical.Value) (refusal : String) : Except String (List String) := do
  let xs ← listOf v refusal
  xs.mapM fun x => match x with
    | .str s => pure s
    | _ => .error refusal

/-- v1 `_decl`: the declared grant and the facts read, `extra` the facts' further keys. -/
def readGrant (decl facts : Canonical.Value) (extra : List String := []) :
    Except String (DeclaredGrant × List (String × Canonical.Value)) := do
  let dm ← need (keysAre? decl ["fingerprint", "value", "nonce", "time", "reason"]) "decl"
  let fm ← need (keysAre? facts (["certified", "suspended", "nonces", "prime"] ++ extra)) "facts"
  let cert ← stringsOf (member fm "certified") "facts"
  let susp ← stringsOf (member fm "suspended") "facts"
  let nonces ← stringsOf (member fm "nonces") "facts"
  let prime ← match member fm "prime" with
    | .null => pure none
    | .str s => if isHex s 64 then pure (some s) else .error "facts"
    | _ => .error "facts"
  let time ← need (intIn? (member dm "time") 0 timeMax) "decl"
  let reason ← match member dm "reason" with
    | .str s => pure s
    | _ => .error "decl"
  let nonce ← match member dm "nonce" with
    | .str s => pure s
    | _ => .error "decl"
  let fp ← match member dm "fingerprint" with
    | .str s => pure s
    | _ => .error "decl"
  return (⟨fp, member dm "value", nonce, time, reason, cert, susp, nonces, prime⟩, fm)

/-- OV1's refusals common to the override and the pad, in v1's order. -/
def declRefusal (d : DeclaredGrant) : Option DeclRefusal :=
  if !isHex d.fingerprint 64 then some .fingerprint
  else if !d.certified.contains d.fingerprint then some .notCertified
  else if d.suspendedList.contains d.fingerprint then some .suspended
  else if !isHex d.nonce 32 then some .nonceForm
  else if d.nonces.contains d.nonce then some .nonce
  else if blank d.reason then some .reason
  else none

/-- An override accepted: its value, when it takes effect, its sunset and the Prime it
replaces. -/
structure OverrideOk where
  value : Rat
  effective : Int
  sunset : Int
  replaces : Option String
  deriving Repr

/-- v1 `override_check(decl, facts, params)`. -/
def overrideCheck (decl facts params : Canonical.Value) :
    Except String (Except DeclRefusal OverrideOk) := do
  let (d, _) ← readGrant decl facts
  let lo ← paramNumber params "THIN FILE START" 0 1
  let hi ← paramNumber params "PRIME CEILING" 0 1 true
  let delay ← paramInt params "OVERRIDE DELAY" 0 timeMax
  let sunset ← paramInt params "OVERRIDE SUNSET" 1 countMax
  let v ← need (numberOf? d.value) "decl"
  match declRefusal d with
  | some r => return .error r
  | none =>
    if v < lo || hi < v then return .error .bounds
    return .ok ⟨v, d.time + delay, sunset, d.prime⟩

/-- v1 `override_effective(decl_time, now, cancelled, params)`. -/
def overrideEffective (declTime now cancelled params : Canonical.Value) :
    Except String OverrideStatus := do
  let t ← need (intIn? declTime 0 timeMax) "time"
  let n ← need (intIn? now 0 timeMax) "time"
  let c ← need (boolOf? cancelled) "cancelled"
  let delay ← paramInt params "OVERRIDE DELAY" 0 timeMax
  return if c then .cancelled else if n < t + delay then .pending else .effective

/-- v1 `override_mark(grant_block, now_block, params)`: in force while fewer than OVERRIDE
SUNSET blocks have passed, and the blocks left. -/
def overrideMark (grant now params : Canonical.Value) : Except String (Bool × Nat) := do
  let g ← need (intIn? grant 0 countMax) "block"
  let n ← need (intIn? now 0 countMax) "block"
  check (g ≤ n) "block"
  let sunset ← paramInt params "OVERRIDE SUNSET" 1 countMax
  let elapsed := n - g
  return (elapsed < sunset, natOf (sunset - elapsed))

/-- A pad accepted: P, when it takes effect, whether it carries the OVERRIDE mark, and the
mark's sunset when it does. -/
structure PadOk where
  value : Nat
  effective : Int
  mark : Bool
  sunset : Option Int
  deriving Repr

/-- v1 `pad_check(decl, facts, params)`. -/
def padCheck (decl facts params : Canonical.Value) :
    Except String (Except DeclRefusal PadOk) := do
  let (d, fm) ← readGrant decl facts ["reference"]
  let ref ← match member fm "reference" with
    | .null => pure none
    | .str s => if isHex s 64 then pure (some s) else .error "facts"
    | _ => .error "facts"
  let padMax ← paramInt params "PAD MAX" 1 countMax
  let nonRef ← paramBool params "PAD NON-REFERENCE"
  let delay ← paramInt params "OVERRIDE DELAY" 0 timeMax
  let sunset ← paramInt params "OVERRIDE SUNSET" 1 countMax
  let p ← need (intIn? d.value 0 countMax) "decl"
  let mark := some d.fingerprint != ref
  match declRefusal d with
  | some r => return .error r
  | none =>
    if p < 1 then return .error .value
    if padMax < p then return .error .padMax
    if mark && !nonRef then return .error .nonReference
    return .ok ⟨natOf p, d.time + delay, mark, if mark then some sunset else none⟩

/-- `P 2^(-age / HALF-LIFE)`, exactly. -/
def padWeightOf (p age : Nat) (halfLife : Rat) : PowSum := aged halfLife p age

/-- The arguments of v1 `pad_weight`: `P`, the age and HALF-LIFE. -/
def padWeightArgs (p age params : Canonical.Value) : Except String (Nat × Nat × Rat) := do
  let p ← need (intIn? p 1 countMax) "pad"
  let a ← need (intIn? age 0 countMax) "pad"
  let hl ← paramNumber params "HALF-LIFE" 0 1000000000 true
  return (natOf p, natOf a, hl)

/-- v1 `pad_weight(P, age, params)`. -/
def padWeight (p age params : Canonical.Value) : Except String PowSum := do
  let (p, a, hl) ← padWeightArgs p age params
  return padWeightOf p a hl

/-- The gate: a TRUST TIER member, and under the OVERRIDE mark a second independent
match. -/
def gateOf (inTier override : Bool) (count : Nat) : GateAnswer :=
  if !inTier then .notInTier else if override && count < 2 then .overrideMark else .pass

/-- v1 `tier_gate_release(reproducer)`. -/
def tierGateRelease (reproducer : Canonical.Value) : Except String GateAnswer := do
  let ms ← need (keysAre? reproducer ["in_tier", "override_in_force", "independent_matches"])
    "reproducer"
  let it ← need (boolOf? (member ms "in_tier")) "reproducer"
  let ov ← need (boolOf? (member ms "override_in_force")) "reproducer"
  let m ← need (intIn? (member ms "independent_matches") 0 countMax) "reproducer"
  return gateOf it ov (natOf m)

/-! ## inherit (IN1) -/

/-- IN1: F inherited and whether the succession continues; S starts at THIN FILE START. -/
def inheritOf (fOld : Rat) (continuation sameAccount sameIdentity : Bool) (cause : ChangeCause)
    (on : Bool) (fraction : Rat) : Rat × Bool :=
  let valid := on && continuation && sameAccount && sameIdentity &&
    (cause == .dis || cause == .suite)
  (if valid then fraction * fOld else 0, valid)

/-- The arguments of v1 `inherit`, checked in v1's order: `F_old`, the facts, INHERITANCE
and THIN FILE START. -/
def inheritArgs (fOld facts params : Canonical.Value) :
    Except String (Rat × Bool × Bool × Bool × ChangeCause × Bool × Rat × Rat) := do
  let f ← need (numberOf? fOld) "F_old"
  check (0 ≤ f) "F_old"
  let ms ← need (keysAre? facts ["continuation", "same_account", "same_identity", "cause"]) "facts"
  let c ← need (boolOf? (member ms "continuation")) "facts"
  let sa ← need (boolOf? (member ms "same_account")) "facts"
  let si ← need (boolOf? (member ms "same_identity")) "facts"
  let cause ← wordOf ChangeCause (member ms "cause") "facts"
  let (on, fraction) ← paramFlag params "INHERITANCE"
  let start ← paramNumber params "THIN FILE START" 0 1
  return (f, c, sa, si, cause, on, fraction, start)

/-- v1 `inherit(F_old, facts, params)`: F, S and whether the succession continues. -/
def inherit (fOld facts params : Canonical.Value) : Except String (Rat × Rat × Bool) := do
  let (f, c, sa, si, cause, on, fraction, start) ← inheritArgs fOld facts params
  let (fNew, valid) := inheritOf f c sa si cause on fraction
  return (fNew, start, valid)

/-! ## user_aggregate (UA1 to UA3) -/

/-- An agent's event as the user layer pools it. -/
structure PooledEvent where
  side : Side
  base : Rat
  age : Nat
  counterpart : Option String
  counterpartSponsor : Option String
  agent : Nat
  index : Nat
  deriving Repr

/-- The pooled order (UA2): age descending, then agent order, then event order. -/
def landingOrder (a b : PooledEvent) : Ordering :=
  (compare b.age a.age).then <| (compare a.agent b.agent).then (compare a.index b.index)

/-- An event of the result: its side, its weight for the user and its age. -/
structure UserEvent where
  side : Side
  weight : PowSum
  age : Nat
  deriving Repr

/-- An event's weight for the user, the FOR events admitted before it given with their ages,
counterparts and weights; `none` when its quota's clip is not settled. -/
def poolWeight (admitted : List (Nat × Option String × PowSum)) (e : PooledEvent)
    (sponsor : String) (halfLife cMax : Rat) : Option PowSum :=
  if e.side == .opposing then some (PowSum.ofRat e.base)
  else if e.counterpart.isSome && e.counterpartSponsor == some sponsor then some PowSum.zero
  else match e.counterpart with
    | none => some (PowSum.ofRat e.base)
    | some cp =>
      if e.base = 0 then some (PowSum.ofRat e.base)
      else
        let window := (admitted.filter fun x => ((x.1 - e.age : Nat) : Rat) ≤ halfLife).map
          fun x => (x.2.1, PowSum.mulPow2 (-((x.1 - e.age : Nat) : Rat) / halfLife) x.2.2)
        (quotaPow window cp e.base cMax).map (PowSum.scale e.base)

/-- One event pooled, after the FOR events admitted and the events weighed before it. -/
def poolStep (sponsor : String) (halfLife cMax : Rat)
    (st : List (Nat × Option String × PowSum) × List UserEvent) (e : PooledEvent) :
    Option (List (Nat × Option String × PowSum) × List UserEvent) :=
  (poolWeight st.1 e sponsor halfLife cMax).map fun w =>
    ((if e.side == .supporting then st.1 ++ [(e.age, e.counterpart, w)] else st.1),
      st.2 ++ [⟨e.side, w, e.age⟩])

/-- UA2: the pooled events, each weighed in landing order; `none` when a quota's clip is not
settled. -/
def poolOf (pool : List PooledEvent) (sponsor : String) (halfLife cMax : Rat) :
    Option (List UserEvent) := do
  let (_, out) ← (sortBy landingOrder pool).foldlM (poolStep sponsor halfLife cMax) ([], [])
  return out

/-- The aggregate: NONE with no certified agent, else the pooled events. -/
inductive Aggregate where
  | none
  | pooled (events : List UserEvent)
  deriving Repr

/-- The agents and the sponsor read, the parameters HALF-LIFE and c_max, and the pool. -/
def readAgents (agents sponsor params : Canonical.Value) :
    Except String (String × Rat × Rat × Nat × List PooledEvent) := do
  let xs ← listOf agents "agents"
  let sp ← need (nameOf? sponsor) "agents"
  let hl ← paramNumber params "HALF-LIFE" 0 1000000000 true
  let cm ← paramNumber params "c_max" 0 1 true true
  let (certified, pool, _) ← xs.zipIdx.foldlM (fun (st : Nat × List PooledEvent × List String) (ag, ai) => do
    let ms ← need (keysAre? ag ["account", "certified", "removed", "events"]) "agents"
    let name ← need (nameOf? (member ms "account")) "agents"
    check (!st.2.2.contains name) "agents"
    let cert ← need (boolOf? (member ms "certified")) "agents"
    let _ ← need (boolOf? (member ms "removed")) "agents"
    let evs ← listOf (member ms "events") "agents"
    let pooled ← evs.zipIdx.mapM fun (e, ei) => do
      let em ← need (keysAre? e ["kind", "base", "age", "counterpart", "counterpart_sponsor"]) "agents"
      let base ← need (numberOf? (member em "base")) "agents"
      let side ← wordOf Side (member em "kind") "agents"
      check (0 ≤ base) "agents"
      let age ← need (intIn? (member em "age") 0 countMax) "agents"
      let cp ← match member em "counterpart" with
        | .null => pure none
        | v => some <$> need (nameOf? v) "agents"
      let cs ← match member em "counterpart_sponsor" with
        | .null => pure none
        | v => some <$> need (nameOf? v) "agents"
      return (⟨side, base, natOf age, cp, cs, ai, ei⟩ : PooledEvent)
    return (st.1 + (if cert then 1 else 0), st.2.1 ++ pooled, name :: st.2.2)) (0, [], [])
  return (sp, hl, cm, certified, pool)

/-- What stops an answer: v1's refusal word, or a comparison bounds did not settle. -/
inductive Stop where
  | refused (word : String)
  | unsettled
  deriving Repr, DecidableEq

/-- v1 `user_aggregate(agents, sponsor, params)`. -/
def userAggregate (agents sponsor params : Canonical.Value) : Except Stop Aggregate := do
  let (sp, hl, cm, certified, pool) ← (readAgents agents sponsor params).mapError .refused
  if certified = 0 then return .none
  match poolOf pool sp hl cm with
  | some evs => return .pooled evs
  | none => throw .unsettled

/-! ## user_score_evidence and sponsor_cut -/

/-- What `tpc_sponsor.user_evidence` takes: the pooled agent events, the conduct events as
given (`kind`, `resolution`, `age`), the conduct weights `g_C` and `h_C`, PRIOR and
HALF-LIFE. -/
structure SponsorInput where
  agentEvents : List UserEvent
  conduct : List (Canonical.Value × Canonical.Value × Nat)
  gC : Canonical.Value
  hC : Canonical.Value
  a0 : Rat
  b0 : Rat
  halfLife : Rat
  deriving Repr

/-- The user's evidence: NONE, or the sponsor's computation on its input, which the
sponsor's port makes (`Principia.Sponsor.evidenceOfInput`). -/
inductive UserEvidence where
  | none
  | sponsor (input : SponsorInput)
  deriving Repr

/-- The input of v1's call of `tpc_sponsor.user_evidence` past the pooled events: the
CONDUCT EVENTS, PRIOR, HALF-LIFE, `g_C` and `h_C`, checked in v1's order. -/
def sponsorInputOf (evs : List UserEvent) (conduct params : Canonical.Value) :
    Except String SponsorInput := do
  let xs ← listOf conduct "conduct"
  let a0 ← paramNumber params "a0" 0 1000000000 true
  let b0 ← paramNumber params "b0" 0 1000000000 true
  let hl ← paramNumber params "HALF-LIFE" 0 1000000000 true
  let gC ← param params "g_C" |>.mapError fun _ => "params:g_C"
  let hC ← param params "h_C" |>.mapError fun _ => "params:g_C"
  match gC, hC with
  | .obj _, .obj _ => pure ()
  | _, _ => throw "params:g_C"
  let cs ← xs.mapM fun c => do
    let ms ← need (keysAre? c ["kind", "resolution", "age"]) "conduct"
    let age ← need (intIn? (member ms "age") 0 countMax) "conduct"
    return (member ms "kind", member ms "resolution", natOf age)
  return ⟨evs, cs, gC, hC, a0, b0, hl⟩

/-- v1 `user_score_evidence(agents, conduct, sponsor, params)`, up to its call of
`tpc_sponsor.user_evidence`. -/
def userScoreEvidence (agents conduct sponsor params : Canonical.Value) :
    Except Stop UserEvidence := do
  match ← userAggregate agents sponsor params with
  | .none => return .none
  | .pooled evs => return .sponsor (← (sponsorInputOf evs conduct params).mapError Stop.refused)

/-- The sponsor cut: `S_u (1 - m SPONSOR CUT)`. -/
def sponsorCutOf (s m cut : Rat) : Rat := s * (1 - m * cut)

/-- The arguments of v1 `sponsor_cut`, checked in v1's order: `S_u`, `m` of the class and
SPONSOR CUT. -/
def sponsorCutArgs (s mClass params : Canonical.Value) : Except String (Rat × Rat × Rat) := do
  let s ← unitNumber s "S"
  let k ← need (intIn? mClass 1 3) "m_class"
  let m ← paramNumber params s!"m_{k}" 0 1
  let cut ← paramNumber params "SPONSOR CUT" 0 1
  return (s, m, cut)

/-- v1 `sponsor_cut(S_u, m_class, params)`. -/
def sponsorCut (s mClass params : Canonical.Value) : Except String Rat := do
  let (s, m, cut) ← sponsorCutArgs s mClass params
  return sponsorCutOf s m cut

/-! ## What Lean proves

Each statement is the text's, about the exact values, on every input. -/

theorem clip_mem {x lo hi : Rat} (h : lo ≤ hi) : lo ≤ clip x lo hi ∧ clip x lo hi ≤ hi := by
  unfold clip
  split
  · exact ⟨Rat.le_refl, h⟩
  · split
    · exact ⟨h, Rat.le_refl⟩
    · constructor <;> grind

/-- DQ2: the admitted fraction lies in `[0, 1]`. -/
theorem quotaFraction_mem (w wc g cMax : Rat) :
    0 ≤ quotaFraction w wc g cMax ∧ quotaFraction w wc g cMax ≤ 1 :=
  clip_mem (by decide)

/-- DQ3: a match is never admitted above its base weight. -/
theorem quota_admitted_le (window : List (Option String × Rat)) (cp : String) {g : Rat}
    (cMax : Rat) (hg : 0 ≤ g) : (quotaOf window cp g cMax).admitted ≤ g := by
  have h := (quotaFraction_mem (window.foldl (fun s e => s + e.2) 0)
    (window.foldl (fun s e => if e.1 == some cp then s + e.2 else s) 0) g cMax).2
  have := Rat.mul_le_mul_of_nonneg_left h hg
  simp only [quotaOf]
  grind

/-- DQ2: whatever fraction is admitted keeps the counterpart at or under `c_max` of the
window's FOR weight with the match: with `q > 0`, `W_c + g q ≤ c_max (W + g)`. -/
theorem quota_keeps_share {w wc g cMax : Rat} (hg : 0 < g) (hq : 0 < quotaFraction w wc g cMax) :
    wc + g * quotaFraction w wc g cMax ≤ cMax * (w + g) := by
  unfold quotaFraction clip at *
  have e : g * ((cMax * (w + g) - wc) / g) = cMax * (w + g) - wc := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel (Rat.ne_of_gt hg)
  by_cases h1 : (cMax * (w + g) - wc) / g < 0
  · simp only [h1, ↓reduceIte] at hq; exact absurd hq (by decide)
  · simp only [h1, ↓reduceIte] at hq ⊢
    by_cases h2 : 1 < (cMax * (w + g) - wc) / g
    · simp only [h2, ↓reduceIte]
      have := (Rat.lt_div_iff hg).mp h2
      grind
    · simp only [h2, ↓reduceIte]; grind

/-- The score's interval holds the score, within `[0, 1]`. -/
theorem scoreInterval_holds {s e lo hi : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hle : lo ≤ e)
    (heh : e ≤ hi) :
    let r := scoreIntervalOf s e lo hi
    0 ≤ r.1 ∧ r.1 ≤ s ∧ s ≤ r.2 ∧ r.2 ≤ 1 := by
  simp only [scoreIntervalOf, clip]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split <;> (try split) <;> grind

/-- ST1: CLEARLY HIGHER and CLEARLY LOWER are each other's mirror: when `y` is CLEARLY HIGHER
than `x`, `x` is CLEARLY LOWER than `y`. -/
theorem standing_higher_mirror {x y : Placed} (hx : x.lo ≤ x.hi) (hy : y.lo ≤ y.hi)
    (h : standingOf x y = .clearlyHigher) : standingOf y x = .clearlyLower := by
  unfold standingOf at *
  by_cases hc : x.hi < y.lo
  · have h1 : ¬ y.hi < x.lo := by grind
    simp [h1, hc]
  · simp only [hc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> simp at h

/-- ST1: when `y` is CLEARLY LOWER than `x` and `x` is not under the OVERRIDE mark, `x` is
CLEARLY HIGHER than `y`. -/
theorem standing_lower_mirror {x y : Placed} (hov : x.override = false)
    (h : standingOf x y = .clearlyLower) : standingOf y x = .clearlyHigher := by
  unfold standingOf at *
  by_cases hc : y.hi < x.lo
  · simp [hc, hov]
  · simp only [hc, ↓reduceIte] at h
    split at h <;> simp at h

/-- An overridden account is never CLEARLY HIGHER. -/
theorem standing_override_never_higher {x y : Placed} (hov : y.override = true) :
    standingOf x y ≠ .clearlyHigher := by
  unfold standingOf
  simp [hov]
  split <;> simp

/-- SU2 and the step's bound: the new score lies in `[0, PRIME CEILING]` and no step exceeds
`delta_max`. -/
theorem update_bounded (role : UpdateRole) (s e sp a : Rat) (u : UpdateParams)
    (hc : 0 ≤ u.ceiling) (hd : 0 ≤ u.deltaMax) :
    let r := updateOf role s e sp a u
    0 ≤ r.s ∧ r.s ≤ u.ceiling ∧ -u.deltaMax ≤ r.step ∧ r.step ≤ u.deltaMax := by
  simp only [updateOf, boundStep]
  split <;> (refine ⟨(clip_mem hc).1, (clip_mem hc).2, ?_, ?_⟩) <;> split <;> (try split) <;>
    simp <;> grind

/-- A follower's gain lies in `[k_min, k_max]`. -/
theorem update_follower_gain (role : UpdateRole) (s e sp a : Rat) (u : UpdateParams)
    (hr : role = .follower ∨ role = .user) (hk : u.kMin ≤ u.kMax) :
    u.kMin ≤ (updateOf role s e sp a u).k ∧ (updateOf role s e sp a u).k ≤ u.kMax := by
  rcases hr with hr | hr <;> subst hr <;> simp only [updateOf] <;> exact clip_mem hk

/-- CR11: a confirmed violation never raises the score, and leaves it nonnegative. -/
theorem cut_lowers {s m : Rat} (hs : 0 ≤ s) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    0 ≤ s * (1 - m) ∧ s * (1 - m) ≤ s := by
  constructor
  · exact Rat.mul_nonneg hs (by grind)
  · have := Rat.mul_le_mul_of_nonneg_left (show 1 - m ≤ 1 by grind) hs
    grind

/-- The sponsor cut never raises the user's score, and leaves it nonnegative. -/
theorem sponsorCut_lowers {s m cut : Rat} (hs : 0 ≤ s) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hc0 : 0 ≤ cut) (hc1 : cut ≤ 1) :
    0 ≤ sponsorCutOf s m cut ∧ sponsorCutOf s m cut ≤ s := by
  have h0 : 0 ≤ m * cut := Rat.mul_nonneg hm0 hc0
  have h1 : m * cut ≤ 1 := by
    have := Rat.mul_le_mul_of_nonneg_left hc1 hm0
    grind
  exact cut_lowers hs h0 h1

/-- IQ2: an inquiry never raises the score, and never takes it below 0. -/
theorem inquire_lowers (last : Option Nat) (k block : Nat) {s wI : Rat} (cool : Nat)
    (hs : 0 ≤ s) (hw : 0 ≤ wI) :
    0 ≤ (inquireOf last k block s wI cool).s ∧ (inquireOf last k block s wI cool).s ≤ s := by
  simp only [inquireOf]
  generalize hk : (if (match last with
    | some l => decide (block - l < cool)
    | none => false) = true then k + 1 else 1) = k'
  unfold afterCost inquiryCost
  split
  · simp; exact hs
  · have : 0 ≤ wI * (2 : Rat) ^ (k' - 1) := Rat.mul_nonneg hw (Rat.pow_nonneg (by decide))
    split <;> grind

/-- TR1: an account below the tier trips on its first confirmed violation. -/
theorem trip_below_tier (s : Rat) (ages : List Nat) (level : Rat) (window : Nat) :
    tripOf s false ages level window = (true, .first) := by
  simp [tripOf]

/-- SS1: a SUSPENDED account leaves SUSPENDED only by an AUDIT FINDING. -/
theorem suspended_held (passes : Nat) (level : AlertState) (ev : StateEvent) (o : Nat)
    (h : ev ≠ .auditFinding) : (stateStepOf .suspended passes level ev o).state = .suspended := by
  simp [stateStepOf, h]

/-- PL3: GREEN exactly when nothing is counted. -/
theorem pending_green_iff (items : List Pending) (now : Int) (pMax warn susp : Nat) :
    (pendingLevelOf items now pMax warn susp).level = .green ↔
      (pendingLevelOf items now pMax warn susp).counted = 0 := by
  simp only [pendingLevelOf]
  split
  · next h => simp_all
  · next h =>
    have : ¬ _ := h
    simp only [List.isEmpty_iff] at this
    constructor
    · intro hg
      split at hg
      · simp at hg
      · split at hg <;> simp at hg
    · intro h0
      exact absurd (List.eq_nil_of_length_eq_zero h0) this

/-- The gate passes only a TRUST TIER member. -/
theorem gate_pass_in_tier {inTier override : Bool} {m : Nat}
    (h : gateOf inTier override m = .pass) : inTier = true := by
  unfold gateOf at h
  cases inTier <;> simp_all

/-- IN1: an inherited F is never more than the old one, and nothing is inherited without a
declared continuation. -/
theorem inherit_le {fOld fraction : Rat} (c sa si : Bool) (cause : ChangeCause) (on : Bool)
    (hf : 0 ≤ fOld) (h1 : fraction ≤ 1) :
    (inheritOf fOld c sa si cause on fraction).1 ≤ fOld := by
  simp only [inheritOf]
  split
  · have := Rat.mul_le_mul_of_nonneg_right h1 hf
    grind
  · exact hf

theorem inherit_needs_continuation (fOld fraction : Rat) (sa si : Bool) (cause : ChangeCause)
    (on : Bool) : inheritOf fOld false sa si cause on fraction = (0, false) := by
  simp [inheritOf]

/-- PA1: peer activity is at most 1. -/
theorem activity_le_one (events : List (String × Bool)) (period : Nat) :
    (activityOf events period).2 ≤ 1 := by
  simp only [activityOf]
  split <;> grind

end Principia.Score
