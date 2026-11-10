import Principia.Strike
import Principia.Wire

/-!
# SR9: the compliance checks of a Criteria Set entry

The mechanical part of SR9 (TPS 0.5.0, 4.4 SR9; 4.5.2 and 4.5.3), ported from v1's program
`tpc_sr9` (TPC-PY 0.3.0, `tpc_sr9` 0.1.1). An entry of the Criteria Set ranks records
(its key) and resolves a contradiction between two of them; the harness runs it over a
synthetic record suite and checks:

* C1: it never ranks a record failing SR1 above one passing it;
* C2: within a regime, adding an ASSUMPTION never improves rank, except in a declared
  limiting case naming its DOMAIN, applied only there;
* C4: it does not let an M contradiction strike an L derivation;

and the gate of TPS 4.5.3: the Criteria Set declares `k`, its STEP CONVENTION and `N_x`.
C3 and C5 are INSPECTION (check-class matrix row 18) and are not here.

A pass on a finite suite is evidence, not proof: an entry can still fail C1, C2 or C4 on
records the suite lacks. The theorems at the end prove C1 and C4 for the skeleton entry on
every suite.

`fixture` holds v1's compliant entry (the strike skeleton) and its deliberately broken
entries, each failing exactly one check, by v1's names; the corpus names them. An entry
compiled from a declared yardstick (v1's `tpc_yardstick`) is an `Entry` too; it is the
yardstick item's.

Vectors: the SR9 corpus, run by the strike vector tests.
-/

namespace Principia.Strike.SR9

open Principia.Strike

/-! ## The synthetic records -/

/-- `REGIME` (TPS 4.4 SR3): `L`, verifiable by re-derivation with no empirical input, or
`M`, a value with its combined standard uncertainty. -/
inductive Regime where
  /-- `L`: a derivation. -/
  | derivation
  /-- `M`: a measurement. -/
  | measurement
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Regime where
  members := [.derivation, .measurement]
  toWire
    | .derivation => "L"
    | .measurement => "M"
  read_toWire a := by cases a <;> decide

/-- A record of the synthetic suite: what the checks read. SR1's verdict is given, since
detecting an SR1 failure needs a derivation oracle and is no function of the Calculator. -/
structure SuiteRecord where
  /-- The record's regime. -/
  regime : Regime
  /-- Its own ASSUMPTIONS. -/
  assumptions : List String
  /-- The records it CITES. -/
  cites : List String
  /-- Its own derivation's step count. -/
  steps : Nat
  /-- The DOMAIN it applies in. -/
  domain : String
  /-- Whether it fails SR1. -/
  sr1Fail : Bool
  /-- The record's row of fields, as a declared yardstick's key reads it (v1
  `tpc_yardstick`'s placed row); empty for the fixtures, whose keys read none. C2's `r+`
  keeps `r`'s row, as v1's `dict(recs[rid])` did. -/
  fields : List (String × String) := []
  deriving Repr, DecidableEq, Inhabited

/-- What SR4 reads of a suite record. -/
def SuiteRecord.toStrikeRecord (r : SuiteRecord) : StrikeRecord :=
  ⟨r.assumptions, r.cites, r.steps⟩

/-- A suite's records, by identifier; the first pair carrying an identifier is that
record. -/
abbrev SuiteRecords := List (String × SuiteRecord)

/-- The synthetic record suite. -/
structure Suite where
  /-- The records. -/
  records : SuiteRecords
  /-- The Research Assembly's own assumptions, excluded from `a(r)`. -/
  assembly : List String
  /-- The contradicting pairs C4 resolves. -/
  contradictions : List (String × String)
  deriving Repr, Inhabited

/-- `a(r)` over a suite's records. -/
def aOf (rid : String) (recs : SuiteRecords) (assembly : List String) : Option Nat :=
  aOfR rid (recs.map fun p => (p.1, p.2.toStrikeRecord)) assembly

/-! ## Entries -/

/-- A key, compared lexicographically; lower is closer. Rational, since a declared
yardstick's key may weigh with decimals (a WSUM weight of 0.5, a U_C field of 0.05). -/
abbrev Key := List Rat

/-- The lexicographic order of keys, as v1 compared tuples: a proper prefix is lower. -/
def keyLt : Key → Key → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (a == b && keyLt as bs)

/-- No key is below itself. -/
theorem keyLt_irrefl (k : Key) : keyLt k k = false := by
  induction k with
  | nil => rfl
  | cons a as ih => simp [keyLt, ih, Rat.lt_irrefl]

/-- No two keys are each below the other. -/
theorem keyLt_asymm (k l : Key) (h : keyLt k l = true) : keyLt l k = false := by
  induction k generalizing l with
  | nil => cases l <;> simp_all [keyLt]
  | cons a as ih =>
    cases l with
    | nil => simp [keyLt] at h
    | cons b bs =>
      simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | ⟨rfl, h⟩
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff,
          beq_eq_false_iff_ne]
        exact ⟨Rat.not_lt.mpr (Rat.le_of_lt h), Or.inl fun he => Rat.lt_irrefl (he ▸ h)⟩
      · simp [Rat.lt_irrefl, ih bs h]

/-- How an entry resolves a contradiction between two records. -/
inductive Resolution where
  /-- v1's `STRIKE:<id>`: that record is struck. -/
  | strike (id : String)
  /-- v1's `AUDIT`: an audit block opens. -/
  | audit
  /-- v1's `GAP:<id>`: a named gap against that L record's ASSUMPTIONS (SR7). -/
  | gap (id : String)
  /-- v1's `DOMAIN:<id>`: a finding against the Research Assembly's DOMAIN (SR7). -/
  | domain (id : String)
  deriving Repr, DecidableEq, Inhabited

/-- v1's words for a resolution. -/
def Resolution.toV1 : Resolution → String
  | .strike i => "STRIKE:" ++ i
  | .audit => "AUDIT"
  | .gap i => "GAP:" ++ i
  | .domain i => "DOMAIN:" ++ i

/-- An entry's key of record `rid`, given the suite's records and the assembly's
assumptions; `none` when the suite lacks a record it reads. -/
abbrev KeyFn := String → SuiteRecords → List String → Option Key

/-- v1's executable entry interface: a key, a resolver of a contradicting pair, and the
DOMAINs where it declares a C2 limiting case. -/
structure Entry where
  /-- The key: lower is closer. -/
  key : KeyFn
  /-- The resolution of a contradiction between two records. -/
  resolve : String → String → SuiteRecords → List String → Option Resolution
  /-- The DOMAINs of its declared limiting cases. -/
  limiting : List String

/-- SR1's place in a key: 1 for a record failing SR1, 0 for one passing it. -/
def sr1Rank (r : SuiteRecord) : Rat := if r.sr1Fail then 1 else 0

/-- The skeleton's key, (i) and (iii) of the strike skeleton: a record failing SR1 sorts
after every passing one, then `d(r) = (a(r), s(r))`. -/
def skeletonKey : KeyFn := fun rid recs tfk => do
  let r ← recs.lookup rid
  let a ← aOf rid recs tfk
  pure [sr1Rank r, (a : Rat), (r.steps : Rat)]

/-- Broken for C1: plain `d(r)`, SR1 ignored. -/
def naiveKey : KeyFn := fun rid recs tfk => do
  let r ← recs.lookup rid
  let a ← aOf rid recs tfk
  pure [(a : Rat), (r.steps : Rat)]

/-- Broken for C2: more assumptions rank closer. -/
def moreIsBetterKey : KeyFn := fun rid recs tfk => do
  let r ← recs.lookup rid
  let a ← aOf rid recs tfk
  pure [sr1Rank r, -(a : Rat), (r.steps : Rat)]

/-- The skeleton's key with the assumption count inverted inside one DOMAIN only: a
limiting case. -/
def invertedInKey (dom : String) : KeyFn := fun rid recs tfk => do
  let r ← recs.lookup rid
  let a ← aOf rid recs tfk
  pure [sr1Rank r, if r.domain == dom then -(a : Rat) else (a : Rat), (r.steps : Rat)]

/-- SR5 on a key: the record with the lower key stands and the other is struck; equal
keys open an audit block. -/
def resolveByKey (key : KeyFn) (id1 id2 : String) (recs : SuiteRecords) (tfk : List String) :
    Option Resolution := do
  let k1 ← key id1 recs tfk
  let k2 ← key id2 recs tfk
  pure (if keyLt k1 k2 then .strike id2 else if keyLt k2 k1 then .strike id1 else .audit)

/-- SR7 for an L-M pair, SR5 on the key otherwise: an M contradiction never strikes the L
derivation; it is a named gap when `a(L) > 0`, a DOMAIN finding when `a(L) = 0`. -/
def resolveRegimeAware (key : KeyFn) (id1 id2 : String) (recs : SuiteRecords)
    (tfk : List String) : Option Resolution := do
  let r1 ← recs.lookup id1
  let r2 ← recs.lookup id2
  if r1.regime ≠ r2.regime then
    let lid := if r1.regime = .derivation then id1 else id2
    let a ← aOf lid recs tfk
    pure (if 0 < a then .gap lid else .domain lid)
  else resolveByKey key id1 id2 recs tfk

/-- The compliant entry: the strike skeleton. -/
def skeleton : Entry := ⟨skeletonKey, resolveRegimeAware skeletonKey, []⟩

/-- v1's fixtures by name: the skeleton, and entries each broken for one check. -/
def fixture : String → Option Entry
  | "skeleton" => some skeleton
  | "naive_d" => some ⟨naiveKey, resolveRegimeAware naiveKey, []⟩
  | "more_is_better" => some ⟨moreIsBetterKey, resolveRegimeAware moreIsBetterKey, []⟩
  | "ignores_regime" => some ⟨skeletonKey, resolveByKey skeletonKey, []⟩
  | "limiting_declared" =>
    some ⟨invertedInKey "LIM", resolveRegimeAware (invertedInKey "LIM"), ["LIM"]⟩
  | "limiting_undeclared" =>
    some ⟨invertedInKey "LIM", resolveRegimeAware (invertedInKey "LIM"), []⟩
  | "limiting_leak" =>
    some ⟨invertedInKey "OTHER", resolveRegimeAware (invertedInKey "OTHER"), ["LIM"]⟩
  | _ => none

/-! ## The checks -/

/-- The suite's record identifiers, each once, in code point order. -/
def Suite.ids (s : Suite) : List String :=
  (s.records.map (·.1)).eraseDups.mergeSort idLe

/-- Whether the suite's record `rid` fails SR1. -/
def Suite.fails (s : Suite) (rid : String) : Bool :=
  (s.records.lookup rid).any (·.sr1Fail)

/-- C1's witnesses `f>p` for one failing record `f`, of key `kf`, against `passes`. -/
def c1Against (key : String → Option Key) (f : String) (kf : Key) :
    List String → Option (List String)
  | [] => some []
  | p :: ps => do
    let kp ← key p
    let rest ← c1Against key f kf ps
    pure (if keyLt kf kp then (f ++ ">" ++ p) :: rest else rest)

/-- C1's witnesses for the failing records `fails` against `passes`. -/
def c1Witnesses (key : String → Option Key) (passes : List String) :
    List String → Option (List String)
  | [] => some []
  | f :: fs => do
    let kf ← key f
    let w ← c1Against key f kf passes
    let rest ← c1Witnesses key passes fs
    pure (w ++ rest)

/-- v1's `sr9_c1`: `(pass, witnesses)`, a witness `f>p` being a record `f` failing SR1
ranked strictly above a record `p` passing it; sorted. `none` when the suite lacks a
record the entry reads (v1 raised). -/
def sr9C1 (e : Entry) (s : Suite) : Option (Bool × List String) := do
  let fails := s.ids.filter s.fails
  let passes := s.ids.filter (!s.fails ·)
  let w ← c1Witnesses (e.key · s.records s.assembly) passes fails
  let w := w.mergeSort idLe
  pure (w.isEmpty, w)

/-- The prefix of the assumption C2's transform adds: `~FRESH~<id>`. -/
def freshPrefix : String := "~FRESH~"

/-- C2's verdict on one record: `some (some true)` a violation, `some (some false)` an
exempt case (the record's DOMAIN is a declared limiting case), `some none` no
improvement. The transform adds the record `<rid>+`, `rid` with one fresh assumption, in
front of the suite's records, and compares the two keys over that set. -/
def c2One (e : Entry) (s : Suite) (rid : String) : Option (Option Bool) := do
  let r ← s.records.lookup rid
  let plus := { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] }
  let recs2 := (rid ++ "+", plus) :: s.records
  let kPlus ← e.key (rid ++ "+") recs2 s.assembly
  let k ← e.key rid recs2 s.assembly
  pure (if keyLt kPlus k then some (!e.limiting.contains r.domain) else none)

/-- v1's `sr9_c2`: `(pass, violations, exempt)`. For each record `r`, `r+` is `r` with one
fresh assumption, in the same regime; `r` is a violation when `r+` ranks strictly closer
than `r` outside a declared limiting DOMAIN, and exempt when inside one. Both lists
sorted. `none` when the suite lacks a record the entry reads. -/
def sr9C2 (e : Entry) (s : Suite) : Option (Bool × List String × List String) := do
  let verdicts ← s.ids.mapM fun rid => do
    let v ← c2One e s rid
    pure (rid, v)
  let viol := (verdicts.filter (·.2 == some true)).map (·.1)
  let exempt := (verdicts.filter (·.2 == some false)).map (·.1)
  pure (viol.isEmpty, viol.mergeSort idLe, exempt.mergeSort idLe)

/-- C4's verdict on one contradicting pair: `some (some w)` a violation `L|M`, `some none`
none (or a pair within one regime, which C4 does not concern). The pair is resolved in
both orders; a violation is any outcome that strikes the L record. -/
def c4One (e : Entry) (s : Suite) (a b : String) : Option (Option String) := do
  let ra ← s.records.lookup a
  let rb ← s.records.lookup b
  if ra.regime = rb.regime then pure none
  else
    let lid := if ra.regime = .derivation then a else b
    let mid := if ra.regime = .derivation then b else a
    let o1 ← e.resolve lid mid s.records s.assembly
    let o2 ← e.resolve mid lid s.records s.assembly
    pure (if o1 = .strike lid ∨ o2 = .strike lid then some (lid ++ "|" ++ mid) else none)

/-- v1's `sr9_c4`: `(pass, witnesses)`, a witness `L|M` being a listed L-M contradiction
the entry resolves by striking the L record, in either order; sorted. `none` when the
suite lacks a record it reads. -/
def sr9C4 (e : Entry) (s : Suite) : Option (Bool × List String) := do
  let vs ← s.contradictions.mapM fun (a, b) => c4One e s a b
  let w := vs.filterMap id |>.mergeSort idLe
  pure (w.isEmpty, w)

/-- v1's `sr9_harness`, the summary for the gate: C1, C2 and C4 passed, and the count of
violations (C1's witnesses, C2's violations, C4's witnesses; C2's exempt cases are not
violations). -/
def sr9Harness (e : Entry) (s : Suite) : Option (Bool × Bool × Bool × Nat) := do
  let c1 ← sr9C1 e s
  let c2 ← sr9C2 e s
  let c4 ← sr9C4 e s
  pure (c1.1, c2.1, c4.1, c1.2.length + c2.2.1.length + c4.2.length)

/-! ## The gate of TPS 4.5.3: the Criteria Set's parameters -/

/-- The parameters the gate reads, as the Criteria Set's reader found them: `none` where
the parameter is absent or not of its type (`k` a number, the STEP CONVENTION a string,
`N_x` an integer). -/
structure TmsParams where
  /-- `k` (SR3). -/
  k : Option Rat := none
  /-- The STEP CONVENTION (SR4). -/
  stepConvention : Option String := none
  /-- `N_x` (SR6). -/
  nX : Option Int := none
  deriving Repr, Inhabited

/-- A white space character as v1's `str.strip` removes it (Python's `str.isspace`). -/
def isPySpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || (0x1C ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xA0 ||
    n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000

/-- v1's `tms_params_ok`: the Criteria Set declares `k > 0`, a STEP CONVENTION that is not
blank, and an integer `N_x` of at least 2 (`Parameters.nXMin`); `(pass, the names missing
or invalid)`, in v1's words and order. -/
def tmsParamsOk (p : TmsParams) : Bool × List String :=
  let missing :=
    (if p.k.any (0 < ·) then [] else ["k"]) ++
    (if p.stepConvention.any (fun s => !s.all isPySpace) then [] else ["step_convention"]) ++
    (if p.nX.any (fun n => (Parameters.nXMin : Int) ≤ n) then [] else ["n_x"])
  (missing.isEmpty, missing)

/-! ## C1 and C4 for the skeleton, on every suite -/

/-- Against records of keys starting with 0, a key starting with 1 has no witness. -/
theorem c1Against_nil {key : String → Option Key} {f : String} {kf : Key}
    {kfs : List Rat} (hkf : kf = 1 :: kfs) :
    ∀ (passes : List String) (w : List String),
      (∀ p ∈ passes, ∀ kp, key p = some kp → ∃ y ys, kp = y :: ys ∧ y = 0) →
      c1Against key f kf passes = some w → w = [] := by
  intro passes
  induction passes with
  | nil => intro w _ h; simp [c1Against] at h; exact h
  | cons p ps ih =>
    intro w hp h
    simp only [c1Against, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨kp, hkp, rest, hrest, hw⟩ := h
    have hr := ih rest (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hrest
    obtain ⟨y, ys, rfl, rfl⟩ := hp p (List.mem_cons_self ..) kp hkp
    subst hkf hr
    simp [keyLt, show ¬ ((1 : Rat) < 0) by decide] at hw
    exact hw

/-- The skeleton's key of a record starts with its SR1 rank. -/
theorem skeletonKey_head {rid : String} {recs : SuiteRecords} {tfk : List String} {k : Key}
    (h : skeletonKey rid recs tfk = some k) :
    ∃ r ks, recs.lookup rid = some r ∧ k = sr1Rank r :: ks := by
  simp only [skeletonKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨r, hr, a, _, rfl⟩ := h
  exact ⟨r, _, hr, rfl⟩

/-- C1's witnesses for the skeleton: none, when the failing records fail SR1 and the
passing ones pass it. -/
theorem c1Witnesses_skeleton (s : Suite) (passes : List String)
    (hp : ∀ p ∈ passes, s.fails p = false) :
    ∀ (fails : List String) (w : List String), (∀ f ∈ fails, s.fails f = true) →
      c1Witnesses (skeleton.key · s.records s.assembly) passes fails = some w → w = [] := by
  intro fails
  induction fails with
  | nil => intro w _ h; simp [c1Witnesses] at h; exact h
  | cons f fs ih =>
    intro w hf h
    simp only [c1Witnesses, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨kf, hkf, wf, hwf, rest, hrest, rfl⟩ := h
    have hr := ih rest (fun q hq => hf q (List.mem_cons_of_mem _ hq)) hrest
    obtain ⟨r, ks, hr1, rfl⟩ := skeletonKey_head hkf
    have hfail : r.sr1Fail = true := by
      have := hf f (List.mem_cons_self ..)
      simp [Suite.fails, hr1] at this
      exact this
    have hw : wf = [] := by
      refine c1Against_nil (kfs := ks) (by simp [sr1Rank, hfail]) passes wf ?_ hwf
      intro p hpm kp hkp
      obtain ⟨rp, kps, hrp, rfl⟩ := skeletonKey_head hkp
      have hpass := hp p hpm
      simp [Suite.fails, hrp] at hpass
      exact ⟨_, _, rfl, by simp [sr1Rank, hpass]⟩
    simp [hw, hr]

/-- SR9 C1 for the skeleton: on every suite it runs on, it ranks no record failing SR1
above one passing it. -/
theorem skeleton_c1 (s : Suite) {r : Bool × List String} (h : sr9C1 skeleton s = some r) :
    r = (true, []) := by
  simp only [sr9C1, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨w, hw, rfl⟩ := h
  have := c1Witnesses_skeleton s _ (fun p hp => by simpa using (List.mem_filter.mp hp).2) _ w
    (fun f hf => (List.mem_filter.mp hf).2) hw
  subst this
  simp

/-- The regime-aware resolver never strikes the L record of an L-M pair, whatever its key. -/
theorem resolveRegimeAware_ne_strike (key : KeyFn) {l m : String} {recs : SuiteRecords}
    {tfk : List String} {rl rm : SuiteRecord} (hl : recs.lookup l = some rl)
    (hm : recs.lookup m = some rm) (hne : rl.regime ≠ rm.regime) {o : Resolution}
    (ho : resolveRegimeAware key l m recs tfk = some o) : o ≠ .strike l ∧ o ≠ .strike m := by
  simp only [resolveRegimeAware, hl, hm, Option.bind_eq_bind, Option.bind_some, ne_eq, hne,
    not_false_eq_true, ite_true, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ho
  obtain ⟨a, _, rfl⟩ := ho
  constructor <;> split <;> simp

/-- Every value `mapM` returns is the value of some member. -/
theorem exists_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs → ∀ v ∈ vs, ∃ x ∈ l, f x = some v
  | [], vs, h, v, hv => by simp at h; subst h; simp at hv
  | x :: xs, vs, h, v, hv => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨x, List.mem_cons_self .., hb⟩
    · obtain ⟨y, hy, hfy⟩ := exists_of_mapM_some hbs v hv
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- C4's verdict on one pair, for an entry with the regime-aware resolver: no violation. -/
theorem c4One_regimeAware (key : KeyFn) (lim : List String) (s : Suite) (a b : String)
    {v : Option String} (h : c4One ⟨key, resolveRegimeAware key, lim⟩ s a b = some v) :
    v = none := by
  simp only [c4One, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ra, hra, rb, hrb, h⟩ := h
  split at h
  · simp at h; exact h.symm
  · rename_i hne
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨o1, h1, o2, h2, rfl⟩ := h
    by_cases hd : ra.regime = .derivation <;> simp only [hd, ite_true, ite_false] at h1 h2
    · have n1 := resolveRegimeAware_ne_strike key hra hrb hne h1
      have n2 := resolveRegimeAware_ne_strike key hrb hra (Ne.symm hne) h2
      simp only [hd, ite_true]
      simp [n1.1, n2.2]
    · have n1 := resolveRegimeAware_ne_strike key hrb hra (Ne.symm hne) h1
      have n2 := resolveRegimeAware_ne_strike key hra hrb hne h2
      simp only [hd, ite_false]
      simp [n1.1, n2.2]

/-- SR9 C4 for every entry with the regime-aware resolver, the skeleton among them: on
every suite it runs on, no M contradiction strikes an L derivation. -/
theorem regimeAware_c4 (key : KeyFn) (lim : List String) (s : Suite)
    {r : Bool × List String} (h : sr9C4 ⟨key, resolveRegimeAware key, lim⟩ s = some r) :
    r = (true, []) := by
  simp only [sr9C4, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨vs, hvs, rfl⟩ := h
  have hnone : ∀ v ∈ vs, v = none := by
    intro v hv
    obtain ⟨⟨a, b⟩, _, hab⟩ := exists_of_mapM_some hvs v hv
    exact c4One_regimeAware key lim s a b hab
  have : vs.filterMap id = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro v hv
    simp [hnone v hv]
  simp [this]

/-- SR9 C4 for the skeleton. -/
theorem skeleton_c4 (s : Suite) {r : Bool × List String} (h : sr9C4 skeleton s = some r) :
    r = (true, []) :=
  regimeAware_c4 skeletonKey [] s h

end Principia.Strike.SR9
