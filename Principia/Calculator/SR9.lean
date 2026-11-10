import Principia.Calculator.Interface
import Principia.SR9

/-!
# Family `sr9`: the compliance checks of a Criteria Set entry

v1 `tpc_sr9`'s functions, their arguments named as v1's corpus names them.

* `sr9_c1`, `sr9_c2`, `sr9_c4`, `sr9_harness` `{"entry", "suite"}`: `entry` names one of
  v1's fixtures (`skeleton`, `naive_d`, `more_is_better`, `ignores_regime`,
  `limiting_declared`, `limiting_undeclared`, `limiting_leak`); `suite` is
  `{"records": {id: {"regime": "L" | "M", "assumptions"?, "cites"?, "steps", "domain",
  "sr1_fail"}}, "tfk_assumptions"?, "contradictions"?: [[id, id], ...]}` (other members
  are ignored; at most `maxSuiteRecords` records and contradictions, and
  `maxSuiteEntries` assumptions and citations in all). The answers: `[pass, witnesses]` for C1 and C4, `[pass, violations,
  exceptions]` for C2, `[c1, c2, c4, witnesses counted]` for the harness.
* `criteria_set_params_ok {"params": {"k"?, "step_convention"?, "n_x"?}}` (version 1's
  `tms_params_ok`, kept as a second name of the same function): `[pass, names missing or
  invalid]`; a parameter not of its type (`k` a number, the STEP CONVENTION a string,
  `N_x` an integer) counts as missing, as v1's gate read it.
-/

namespace Principia.Calculator.SR9

open Principia.Canonical Principia.Strike.SR9

/-- The most records, and the most contradictions, a suite holds. C2 reruns the entry's
key, which walks the citations, over the suite once per record: 200 records of few
citations take 0.07 s, but 200 records each citing every other took 99 s. A synthetic
suite is small (v1's has a dozen records). -/
def maxSuiteRecords : Nat := 50

/-- The most assumptions and citations a suite's records hold in all; see
`maxSuiteRecords`. -/
def maxSuiteEntries : Nat := 500

/-- One record of the suite. -/
def readRecord (id : String) (v : Value) : Except Refusal (String × SuiteRecord) := do
  let ms ← asObject s!"the record {quote id}" v
  let list (k : String) : Except Refusal (List String) :=
    match optional ms k with
    | some x => asStrings k x
    | none => pure []
  pure (id, { regime := ← asWord Regime "a regime" (← needed ms "regime"),
              assumptions := ← list "assumptions", cites := ← list "cites",
              steps := ← asCount "steps" (← needed ms "steps"),
              domain := ← asString "domain" (← needed ms "domain"),
              sr1Fail := ← asBool "sr1_fail" (← needed ms "sr1_fail") })

/-- The synthetic suite. -/
def readSuite (v : Value) : Except Refusal Suite := do
  let ms ← asObject "suite" v
  let recList ← asObject "records" (← needed ms "records")
  atMost "records" maxSuiteRecords recList
  let recs ← recList.mapM fun (id, r) => readRecord id r
  let entries := (recs.map fun (_, r) => r.assumptions.length + r.cites.length).sum
  if maxSuiteEntries < entries then
    badArgument s!"the suite's records hold more than {maxSuiteEntries} assumptions and citations in all (the Calculator's bound)"
  let assembly ← match optional ms "tfk_assumptions" with
    | some x => asStrings "tfk_assumptions" x
    | none => pure []
  let pairs ← match optional ms "contradictions" with
    | some x => do
      let ps ← asList "contradictions" x
      atMost "contradictions" maxSuiteRecords ps
      ps.mapM fun p => do
        match ← asStrings "a contradiction" p with
        | [a, b] => pure (a, b)
        | _ => badArgument "a contradiction is [id, id]"
    | none => pure []
  pure { records := recs, assembly := assembly, contradictions := pairs }

/-- The fixture entry and the suite. -/
def entryAndSuite (v : Value) : Except Refusal (Entry × Suite) := do
  let (e, s) ← argument2 "entry" "suite" v
  let name ← asString "entry" e
  match fixture name with
  | some entry => pure (entry, ← readSuite s)
  | none => badArgument s!"{quote name} is not one of v1's fixtures"

/-- A check that met a record no record of the suite is. -/
def missing {α : Type} : Except Refusal α := badArgument "a record the suite cites is not in it"

/-- A list of identifiers. -/
def ids (xs : List String) : Value := .arr (xs.map .str)

/-- `criteria_set_params_ok` (version 1's `tms_params_ok`): the Criteria Set's parameters. -/
def paramsOk : Call := fun v => do
  let ms ← asObject "params" (← argument1 "params" v)
  let p : TmsParams := {
    k := match optional ms "k" with
      | some x => (asNumber "k" x).toOption
      | none => none
    stepConvention := match optional ms "step_convention" with
      | some (.str s) => some s
      | _ => none
    nX := match optional ms "n_x" with
      | some (.int n) => some n
      | _ => none }
  let (ok, names) := tmsParamsOk p
  pure (.arr [.bool ok, ids names])

/-- The family's functions. -/
def calls : Family := [
  ("criteria_set_params_ok", paramsOk),
  ("sr9_c1", fun v => do
    let (e, s) ← entryAndSuite v
    match sr9C1 e s with
    | some (p, w) => pure (.arr [.bool p, ids w])
    | none => missing),
  ("sr9_c2", fun v => do
    let (e, s) ← entryAndSuite v
    match sr9C2 e s with
    | some (p, w, x) => pure (.arr [.bool p, ids w, ids x])
    | none => missing),
  ("sr9_c4", fun v => do
    let (e, s) ← entryAndSuite v
    match sr9C4 e s with
    | some (p, w) => pure (.arr [.bool p, ids w])
    | none => missing),
  ("sr9_harness", fun v => do
    let (e, s) ← entryAndSuite v
    match sr9Harness e s with
    | some (a, b, c, n) => pure (.arr [.bool a, .bool b, .bool c, .int n])
    | none => missing),
  ("tms_params_ok", paramsOk)]

end Principia.Calculator.SR9
