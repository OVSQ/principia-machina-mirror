import Principia.Cluster.TwoRoots
import Principia.Cluster.Rows
import Principia.Cluster.Screen
import Principia.ValueBound

/-!
# The cluster month: the parts composed

The cluster month (TPS 5.19.3 to 5.19.9) is answered by one Calculator call,
`cluster cluster_month` (`Principia.Calculator.Cluster`), which composes the parts in this
order: the EXCLUSION LIST and the MODEL MAP on each source's raw rows (`Screen.screen`); each
ROW's COMPOSITE SCORE, its SE as its exact square and its state (`Rows.rows`); the cluster
rule over the squared SEs (`clusterSq`); the resolving step over the spacing's square and the
representatives' squared SEs (`resolvingStepSq`); the due rule and the page's next state
(`Schedule.step`); and the check that the page's text names no excluded token
(`Screen.textCheck`). This module holds the typed links between the parts; the reading of the
request and the refusals are the Calculator's.

* **A kept raw row's members.** Each source's declaration names the members of a raw row
  that hold the benchmark, the score and the SE (`Members`). A kept row is given to
  `cluster_rows` as `[model, config, benchmark, score, se]` (`entry`): its canonical model
  and configuration, then the three members read by those names, an absent one as `null`,
  which `cluster_rows` refuses with its own word. No layer maps columns.
* **The rows the cluster rule takes.** The LISTED ROWs, each with its COMPOSITE SCORE and its
  `se2` exactly (`fed`, `fed_listed`); an UNLISTED ROW takes no part in the cluster.
* **The resolving step's inputs.** The cluster's spacing square `spacingSq` and the ranked
  representatives' `se2` in rank order (`ses2`), exactly: no root is formed and no value
  rounded, so a month whose SEs or spacing are irrational is answered.
* **The page's text.** v1's text of the cluster result (`renderSq`), a newline, and v1's text
  of the resolving step (`renderResolvingSq`): `page`.

The bound on an exact value. `clusterSq` and `resolvingStepSq` have no walk of their own
within the bound (`Principia.Cluster.Bounded` walks `cluster` and `resolvingStep`). Until they
do, every value fed to them, each row's score and `se2`, IN MAX, CUSP MAX, Z and the SPACING
FLOOR, is held to `capBits` bits in its numerator and its denominator (`fedWithin`), a
month's values being decimals of a few digits; a request beyond it is refused "exact value
too large". The cap only refuses: an answer given is the exact one.
-/

namespace Principia.Cluster.Month

open Principia.Canonical (Value)

/-- A source's declared member names of a raw row: the benchmark, the score and the SE. -/
structure Members where
  /-- The member holding the benchmark. -/
  benchmark : String
  /-- The member holding the score. -/
  score : String
  /-- The member holding the SE. -/
  se : String
  deriving DecidableEq, Repr

/-- A raw row's member by name, `null` when it is absent. -/
def member (r : Screen.Raw) (name : String) : Value := (r.lookup name).getD .null

/-- A kept row as `cluster_rows` reads a component: `[model, config, benchmark, score, se]`,
the model and configuration canonical, the other three read by the declared names. -/
def entry (m : Members) (k : Screen.Kept) : Value :=
  .arr [.str k.model, .str k.config, member k.row m.benchmark, member k.row m.score,
    member k.row m.se]

/-- The rows the cluster rule takes: the LISTED ROWs, each with its COMPOSITE SCORE and its
`se2`, in the ROWs' order. -/
def fed (ms : List Rows.Measure) : List RowSq :=
  ms.filterMap fun m =>
    if m.listed then
      match m.composite, m.se2 with
      | some s, some q => some ⟨m.model, m.config, s, q⟩
      | _, _ => none
    else none

/-- The ranked representatives' `se2`, in rank order. -/
def ses2 (r : ResultSq) : List Rat := r.lines.filterMap fun l => l.rank.map fun _ => l.row.se2

/-- The most bits a value fed to the cluster rule or the resolving step holds in its
numerator, and in its denominator. -/
def capBits : Nat := 1024

/-- A value within `capBits`. -/
def small (q : Rat) : Bool := ValueBound.numBits q ≤ capBits && ValueBound.denBits q ≤ capBits

/-- Every value fed to the cluster rule and the resolving step within `capBits`. -/
def fedWithin (rows : List RowSq) (t : Thresholds) (floor : Rat) : Bool :=
  rows.all (fun r => small r.score && small r.se2) && small t.inMax && small t.cuspMax &&
    small t.z && small floor

/-- The part that refused, by its Calculator name, and its word. -/
abbrev Refused := String × ClusterError

/-- The cluster rule over the rows' squared SEs, then the resolving step over the spacing's
square and the representatives' squared SEs, under ITEM-SAMPLING; a refusal names its part. -/
def clusterMonth (rows : List RowSq) (t : Thresholds) (floor : Rat) :
    Except Refused (ResultSq × Option ResolvingStepSq) :=
  match clusterSq rows t floor none with
  | .error e => .error ("cluster", e)
  | .ok r =>
    match resolvingStepSq r.spacingSq (ses2 r) t none with
    | .error e => .error ("resolving_step", e)
    | .ok d => .ok (r, d)

/-- The page's text: the cluster's, then the resolving step's. -/
def page (r : ResultSq) (d : Option ResolvingStepSq) : String :=
  renderSq r ++ "\n" ++ renderResolvingSq d

/-! ## Its laws -/

/-- Every row the cluster rule takes is a LISTED ROW, with its COMPOSITE SCORE and its `se2`. -/
theorem fed_listed {ms : List Rows.Measure} {r : RowSq} (h : r ∈ fed ms) :
    ∃ m ∈ ms, m.listed = true ∧ m.model = r.model ∧ m.config = r.config ∧
      m.composite = some r.score ∧ m.se2 = some r.se2 := by
  unfold fed at h
  rw [List.mem_filterMap] at h
  obtain ⟨m, hm, hf⟩ := h
  by_cases hl : m.listed = true
  · simp only [hl, ite_true] at hf
    cases hc : m.composite with
    | none => simp [hc] at hf
    | some s =>
      cases hq : m.se2 with
      | none => simp [hc, hq] at hf
      | some q =>
        simp only [hc, hq, Option.some.injEq] at hf
        subst hf
        exact ⟨m, hm, hl, rfl, rfl, hc, hq⟩
  · simp [hl] at hf

/-- An answer of `clusterMonth` is the cluster rule's answer on the rows, then the resolving
step's on that answer's spacing square and its representatives' squared SEs. -/
theorem clusterMonth_ok {rows : List RowSq} {t : Thresholds} {floor : Rat}
    {r : ResultSq} {d : Option ResolvingStepSq} (h : clusterMonth rows t floor = .ok (r, d)) :
    clusterSq rows t floor none = .ok r ∧ resolvingStepSq r.spacingSq (ses2 r) t none = .ok d := by
  unfold clusterMonth at h
  split at h
  · cases h
  · rename_i r' hr
    split at h
    · cases h
    · rename_i d' hd
      cases h
      exact ⟨hr, hd⟩

/-- A refusal of `clusterMonth` is the cluster rule's, or, the cluster answered, the resolving
step's, with that part's word. -/
theorem clusterMonth_error {rows : List RowSq} {t : Thresholds} {floor : Rat} {p : String}
    {e : ClusterError} (h : clusterMonth rows t floor = .error (p, e)) :
    (p = "cluster" ∧ clusterSq rows t floor none = .error e) ∨
      (p = "resolving_step" ∧ ∃ r, clusterSq rows t floor none = .ok r ∧
        resolvingStepSq r.spacingSq (ses2 r) t none = .error e) := by
  unfold clusterMonth at h
  split at h
  · rename_i e' he
    cases h
    exact .inl ⟨rfl, he⟩
  · rename_i r hr
    split at h
    · rename_i e' he
      cases h
      exact .inr ⟨rfl, r, hr, he⟩
    · cases h

end Principia.Cluster.Month
