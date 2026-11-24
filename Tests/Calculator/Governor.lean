import Tests.Calculator.Common

/-!
The Calculator's runners of the family `governor`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- A governed request's kind from `governor.json`'s Lean name. -/
def governorKind (name : String) : IO Principia.Parameters.GovernedRequest :=
  match Tests.Governor.allKinds.find? (Tests.Governor.kindName · == name) with
  | some k => pure k
  | none => throw (IO.userError s!"governor: unknown kind {name}")

/-- `governor.json`'s Lean names of the admission's words, by member, and their wire words. -/
def governorWords : List (String × String × Value) := [
  ("decision", "admitted", wordValue Principia.Governor.DecisionWord.admitted),
  ("decision", "refused", wordValue Principia.Governor.DecisionWord.refused),
  ("refusal", "switch", wordValue Principia.Governor.RefusalWord.switch),
  ("refusal", "rate", wordValue Principia.Governor.RefusalWord.rate),
  ("refusal", "slots", wordValue Principia.Governor.RefusalWord.slots),
  ("reason", "agentStop", wordValue Principia.Governor.Switch.agentStop),
  ("reason", "suspended", wordValue Principia.Governor.Switch.suspended),
  ("payer", "sponsor", wordValue Principia.Governor.Payer.sponsor),
  ("payer", "agent", wordValue Principia.Governor.Payer.agent),
  ("cap", "agent", wordValue Principia.Governor.SlotCap.agent),
  ("cap", "sponsor", wordValue Principia.Governor.SlotCap.sponsor),
  ("cap", "pool", wordValue Principia.Governor.SlotCap.pool),
  ("cap", "anonymous", wordValue Principia.Governor.SlotCap.anonymous),
  ("decision", "cachedOnly", wordValue Principia.Governor.DecisionWord.cachedOnly),
  ("refusal", "pressure", wordValue Principia.Governor.RefusalWord.pressure),
  ("level", "clear", wordValue Principia.Parameters.PressureLevel.clear),
  ("level", "busy", wordValue Principia.Parameters.PressureLevel.busy),
  ("level", "strained", wordValue Principia.Parameters.PressureLevel.strained),
  ("level", "overloaded", wordValue Principia.Parameters.PressureLevel.overloaded),
  ("refusal", "traffic", wordValue Principia.Governor.RefusalWord.traffic),
  ("reason", "contained", wordValue Principia.Governor.Switch.contained),
  ("stage", "normal", wordValue Principia.Governor.TrafficStage.normal),
  ("stage", "throttled", wordValue Principia.Governor.TrafficStage.throttled),
  ("stage", "penalized", wordValue Principia.Governor.TrafficStage.penalized),
  ("stage", "contained", wordValue Principia.Governor.TrafficStage.contained)]

/-- An expectation of `governor.json` with its Lean names given as wire words. -/
def governorExpectation (e : Value) : IO Value := do
  match e with
  | .obj ms =>
    let ms ← ms.mapM fun (k, x) => do
      match x with
      | .str s =>
        if governorWords.any (·.1 == k) then
          match governorWords.find? (fun w => w.1 == k && w.2.1 == s) with
          | some w => pure (k, w.2.2)
          | none => throw (IO.userError s!"governor: unknown {k} {s}")
        else pure (k, x)
      | _ => pure (k, x)
    pure (.obj ms)
  | _ => throw (IO.userError "governor: an expectation is not an object")

/-- `governor.json`: every case through `governor`, its Lean names given as wire words.
An `admit` case is one check of both calls: `admit`'s answer is the expectation and
`charge`'s its member `charge`. Every seat cost is a number: a falcon RETURN's rows round up
(inventory U4, the Declarer's choice), so a `null` expectation is a defect of the corpus. A
`level` case goes through `pressure_level`,
its expectation the answer. -/
def runGovernorCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases ← match readString (← IO.FS.readFile "vectors/governor.json") with
    | .ok (.arr cs) => pure cs
    | _ => throw (IO.userError "governor.json: not a list of cases")
  for c in cases do
    let fn ← memberStr c "function"
    let name := match member c "name" with
      | some (.str s) => s
      | _ => s!"{fn} {repr ((member c "kind").bind (·.canonicalJson))}"
    let call (f : String) (args : List (String × Value)) := respondTo "governor" f (.obj args)
    match fn with
    | "lane" =>
      let k ← governorKind (← memberStr c "kind")
      let n ← match member c "expected" with
        | some (.int n) => pure n.toNat
        | _ => throw (IO.userError s!"governor {name}: no lane number")
      let some lane := (WireWord.members : List Principia.Parameters.Lane).find? (·.number == n)
        | throw (IO.userError s!"governor {name}: no lane {n}")
      let want := (Value.obj [("lane", wordValue lane), ("number", .int n)]).canonicalJson
      let got := canonOf (call "lane" [("kind", wordValue k)])
      t ← t.check (want.isSome && got == want) s!"governor {name}: expected {repr want}, got {repr got}"
    | "seat_cost" =>
      let k ← governorKind (← memberStr c "kind")
      let table := match member c "seat_table" with
        | some st => [("seat_table", st)]
        | none => []
      let got := call "seat_cost"
        ([("kind", wordValue k), ("records", ← need c "records"), ("rows", ← need c "rows")] ++ table)
      match ← need c "expected" with
      | .null => t ← t.check false s!"governor {name}: a seat cost expected null"
      | e =>
        t ← t.check (canonOf got == e.canonicalJson) s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "jitter" =>
      let share := match member c "share" with
        | some sh => [("share", sh)]
        | none => []
      let got := call "jitter" ([("base", ← need c "base"), ("draw", ← need c "draw")] ++ share)
      let e ← need c "expected"
      t ← t.check (canonOf got == e.canonicalJson) s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "admit" =>
      let rq ← need c "request"
      let rq := withMember rq "kind" (wordValue (← governorKind (← memberStr rq "kind")))
      let args := [("state", ← need c "state"), ("request", rq)]
      let want ← governorExpectation (← need c "expected")
      let wantCharge := (← need want "charge").canonicalJson
      let got := canonOf (call "admit" args)
      let gotCharge := canonOf (call "charge" args)
      t ← t.check (want.canonicalJson.isSome && got == want.canonicalJson && gotCharge == wantCharge)
        s!"governor {name}: expected {repr want.canonicalJson}, got {repr got}, charge {repr gotCharge}"
    | "level" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let got := call "pressure_level" ([("use", ← need c "use"), ("prev", ← need c "prev"),
        ("external_until", ← need c "external_until"), ("now", ← need c "now")] ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "traffic_step" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let which ← match member c "event", member c "end" with
        | some e, none => pure [("event", e)]
        | none, some q =>
          pure [("end", withMember q "kind" (wordValue (← governorKind (← memberStr q "kind"))))]
        | _, _ => throw (IO.userError s!"governor {name}: one of event and end")
      let got := call "traffic_step" ([("traffic", ← need c "traffic"), ("now", ← need c "now")] ++
        which ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | "traffic_stage" =>
      let tuning := match member c "tuning" with
        | some tv => [("tuning", tv)]
        | none => []
      let got := call "traffic_stage" ([("traffic", ← need c "traffic"), ("now", ← need c "now"),
        ("kind", wordValue (← governorKind (← memberStr c "kind")))] ++ tuning)
      let e ← need c "expected"
      t ← t.check (e.canonicalJson.isSome && canonOf got == e.canonicalJson)
        s!"governor {name}: expected {repr e.canonicalJson}, got {repr (canonOf got)}"
    | f => throw (IO.userError s!"governor: unknown function {f}")
  IO.println s!"pcalc governor: {cases.length} cases of governor.json"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Governor

open Tests.Calculator

/-- The family `governor`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc governor (governor)", runGovernorCalls),
]

end Tests.Calculator.Governor
