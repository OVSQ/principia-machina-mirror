import Principia.Falcon.Canon

/-!
# The sponsor-stage predicate

v1's `tpc_falcon` 0.2.0: `sponsor_stage(events, as_of, thresholds)`,
a sponsor's stage, NEW, WORKING or SERIOUS, from the events of its agents (ST1 to ST4 in
v1's text). Events are read in time order, input order among equal times; the predicate
is evaluated after every time that holds a LANDED or an EVALUATED; SERIOUS is one-way;
DORMANT lowers no stage. Only counted events decide: integers throughout, no decision
open.
-/

namespace Principia.Falcon.Stage

open Principia.Canonical (Value)
open Principia.Falcon

/-- Seconds in a UTC day (v1's `DAY`). -/
def day : Nat := 86400

/-- The last second v1 reads (v1's `TIME_MAX`, 9999-12-31T23:59:59Z). -/
def timeMax : Int := 253402300799

/-- Event kinds that name an agent (v1's `_AGENT_KINDS`). -/
def agentKinds : List String := ["LANDED", "SUSPENDED", "RESTORED", "VIOLATION"]

/-- Event kinds that name none (v1's `_PLAIN_KINDS`). -/
def plainKinds : List String := ["EVALUATED", "BLOCKED", "UNBLOCKED"]

/-- One event: its kind, its time, and the agent it names. -/
structure Event where
  kind : String
  time : Nat
  agent : String

/-- An event as v1's `_stage_check` accepts it. -/
def eventOf : Value → Option Event
  | .arr (.str k :: t :: rest) =>
    let agent? : Option String :=
      if agentKinds.contains k then
        match rest with
        | [a] => match a with
          | .str s => if s ≠ "" then some s else none
          | _ => none
        | _ => none
      else if plainKinds.contains k then
        if rest.isEmpty then some "" else none
      else none
    match agent? with
    | some a => if isInt t 0 timeMax then some ⟨k, natOf t, a⟩ else none
    | none => none
  | _ => none

/-- The thresholds: blocks (B), dates (D), span in days (S) and the dormant days. -/
structure Thresholds where
  blocks : Nat
  dates : Nat
  spanDays : Nat
  dormantDays : Nat

/-- v1's `_stage_check` of the thresholds. -/
def thresholdsOf (v : Value) : Option Thresholds :=
  if !keysAreV v ["blocks", "dates", "span_days", "dormant_days"] [] then none
  else
    match members? v with
    | none => none
    | some ms =>
      let get (k : String) (lo : Int) : Option Nat :=
        match field? ms k with
        | some x => if isInt x lo 1000000 then some (natOf x) else none
        | none => none
      return { blocks := ← get "blocks" 1, dates := ← get "dates" 1,
               spanDays := ← get "span_days" 0, dormantDays := ← get "dormant_days" 1 }

/-- The stage's result (v1's dict). -/
structure Stage where
  stage : String
  dormant : Bool
  blocks : Nat
  dates : Nat
  span : Nat
  last : Option Nat
  graduated : Option (Nat × Nat × Nat × Nat)

/-- The running state over the events. -/
structure Run where
  first : Option Nat := none
  last : Option Nat := none
  blocks : Nat := 0
  dates : List Nat := []
  blocked : Bool := false
  violation : Bool := false
  suspended : List String := []
  graduated : Option (Nat × Nat × Nat × Nat) := none

/-- One event applied (v1's inner loop); the flag says it calls for an evaluation. -/
def Run.apply (r : Run) (e : Event) : Run × Bool :=
  match e.kind with
  | "LANDED" =>
    ({ r with blocks := r.blocks + 1,
              dates := if r.dates.contains (e.time / day) then r.dates
                else r.dates ++ [e.time / day],
              first := r.first <|> some e.time, last := some e.time }, true)
  | "EVALUATED" => (r, true)
  | "BLOCKED" => ({ r with blocked := true }, false)
  | "UNBLOCKED" => ({ r with blocked := false }, false)
  | "SUSPENDED" =>
    ({ r with suspended := if r.suspended.contains e.agent then r.suspended
        else r.suspended ++ [e.agent] }, false)
  | "RESTORED" => ({ r with suspended := r.suspended.erase e.agent }, false)
  | _ => ({ r with violation := true }, false)

/-- The span from the first landed block to the latest. -/
def Run.span (r : Run) : Nat :=
  match r.first, r.last with
  | some f, some l => l - f
  | _, _ => 0

/-- The events of one time in order, then the evaluation (v1's outer loop, ST2). -/
def Run.atTime (th : Thresholds) (r : Run) (t : Nat) (es : List Event) : Run :=
  let (r, evaluate) := es.foldl (fun (r, ev) e => let (r', f) := r.apply e; (r', ev || f))
    (r, false)
  if evaluate && r.graduated.isNone && 0 < r.blocks then
    if th.blocks ≤ r.blocks && th.dates ≤ r.dates.length && th.spanDays * day ≤ r.span &&
        !r.blocked && r.suspended.isEmpty && !r.violation then
      { r with graduated := some (t, r.blocks, r.dates.length, r.span) }
    else r
  else r

/-- The events grouped by time, in order (each group's events in input order). -/
def groups : List Event → List (Nat × List Event)
  | [] => []
  | e :: es =>
    match groups es with
    | (t, g) :: rest => if t == e.time then (t, e :: g) :: rest else (e.time, [e]) :: (t, g) :: rest
    | [] => [(e.time, [e])]

/-- v1's `sponsor_stage(events, as_of, thresholds)`. -/
def sponsorStage (events asOf thresholds : Value) : Result Stage := do
  let evs ← match events with
    | .arr es => match es.mapM eventOf with
      | some evs => pure evs
      | none => refuse "events"
    | _ => refuse "events"
  if !isInt asOf 0 timeMax then refuse "as_of"
  let some th := thresholdsOf thresholds | refuse "thresholds"
  let asOf := natOf asOf
  let sorted := (evs.filter (·.time ≤ asOf)).mergeSort (fun a b => a.time ≤ b.time)
  let r := (groups sorted).foldl (fun r (t, es) => Run.atTime th r t es) ({} : Run)
  let stage := if r.graduated.isSome then "SERIOUS" else if 0 < r.blocks then "WORKING" else "NEW"
  let dormant := 0 < r.blocks && th.dormantDays * day ≤ asOf - r.last.getD 0
  return { stage := stage, dormant := dormant, blocks := r.blocks, dates := r.dates.length,
           span := r.span, last := r.last, graduated := r.graduated }

/-- v1's `render_stage`. -/
def renderStage (d : Stage) : String :=
  let last := match d.last with
    | some l => toString l
    | none => "-"
  let grad := match d.graduated with
    | some (t, b, n, s) => s!"graduated|{t}|{b}|{n}|{s}"
    | none => "graduated|-"
  s!"stage|{d.stage}\ndormant|{if d.dormant then "true" else "false"}\n" ++
    s!"counts|{d.blocks}|{d.dates}|{d.span}|{last}\n" ++ grad

end Principia.Falcon.Stage
