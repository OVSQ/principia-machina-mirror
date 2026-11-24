import Tests.Calculator.Common

/-!
The Calculator's runners of the family `score`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The score family: v1's corpora and its bounds -/

/-- v1's names of the score functions in `score_corpus.json` (`run_case`), and the
Calculator's. -/
def scoreFunctions : List (String × String) :=
  [("activity", "peer_activity"), ("aggregate", "user_aggregate"), ("cut", "violation_cut"),
   ("effective", "override_effective"), ("evidence", "evidence"), ("gate", "tier_gate_release"),
   ("inherit", "inherit"), ("inquire", "inquire"), ("interval", "score_interval"),
   ("level", "pending_level"), ("mark", "override_mark"), ("override", "override_check"),
   ("pad", "pad_check"), ("pad_weight", "pad_weight"), ("prime", "prime_select"),
   ("quota", "diversity_quota"), ("rank", "rank"), ("sponsor_cut", "sponsor_cut"),
   ("standing", "standing"), ("state", "state_step"), ("trip", "trip"),
   ("update", "score_update"), ("user_evidence", "user_score_evidence")]

/-- v1's names of the Beta layer's functions in `beta_corpus.json`, and the Calculator's. -/
def betaFunctions : List (String × String) :=
  [("betainc", "betainc"), ("betainc_inv", "betainc_inv"), ("canon", "canon"),
   ("interval", "beta_interval"), ("lgamma", "lgamma"), ("mean", "beta_mean")]

/-- A case's answer through `score <fn>`, as v1's `run_case` text: the text, `ERROR:` and
v1's word, or `none` when it is refused otherwise (`OWED` among them). -/
def scoreText (fn : String) (args : Value) : Option String :=
  match respondTo "score" fn args with
  | .ok (.str text) => some text
  | .error r => if r.code == .badArgument then some ("ERROR:" ++ r.detail) else none
  | _ => none

/-- `score_corpus.json` and `beta_corpus.json`: every case's `args` through
`score <function>`, each giving v1's text, or v1's word as a refusal's detail. A case of
`score_corpus.owed.json` must be answered `OWED`, and no other; a case of
`beta_corpus.divergences.json` gives the Calculator's recorded text where v1's differs, and
each recorded divergence must still be one. -/
def runScoreCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← (← arr (← field (← readJson "vectors/score_corpus.owed.json") "owed")).mapM
    fun o => str o "name"
  for c in ← v1Cases "vectors/score_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := scoreFunctions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let ok := if owed.contains name then
        match respondTo "score" fn args with
        | .error r => r.code == .owed
        | .ok _ => false
      else scoreText fn args == some expected
    t ← t.check ok s!"score {fn} {name}: expected {repr expected}, got {repr (scoreText fn args)}"
  let divs ← (← arr (← field (← readJson "vectors/beta_corpus.divergences.json") "divergences")).mapM
    fun o => do pure ((← str o "name"), (← str o "v1"), (← str o "v2"))
  let mut diverged : List String := []
  for c in ← v1Cases "vectors/beta_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := betaFunctions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := scoreText fn args
    let ok ← match divs.find? (·.1 == name) with
      | some (_, v1, v2) =>
        if v1 == expected && got == some v2 then
          diverged := diverged ++ [name]
          pure true
        else pure false
      | none => pure (got == some expected)
    t ← t.check ok s!"score {fn} {name}: expected {repr expected}, got {repr got}"
  for (name, _, _) in divs do
    t ← t.check (diverged.contains name) s!"score {name}: listed as a divergence but not one"
  return t.pair

/-- `n` events of `evidence`, their ages giving `terms` distinct powers of 2 under a
HALF-LIFE of 500, FOR and AGAINST in turn. -/
def evidenceEvents (n terms : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("kind", .str (if i % 2 == 0 then "FOR" else "AGAINST")),
    ("weight", .int 1), ("age", .int ((i % terms : Nat) : Int))])

/-- The parameters `evidence` reads. -/
def evidenceParams : Value :=
  .obj [("a0", .int 1), ("b0", .int 1), ("HALF-LIFE", .int 500), ("T_idle", .int 90)]

/-- One agent holding `n` AGAINST events. -/
def agentWith (n : Nat) : Value :=
  .arr [.obj [("account", .str "a"), ("certified", .bool true), ("removed", .bool false),
    ("events", valueCopies n (.obj [("kind", .str "AGAINST"), ("base", .int 1), ("age", .int 0),
      ("counterpart", .null), ("counterpart_sponsor", .null)]))]]

/-- An override's facts, `n` entries in each list. -/
def factsOf (n : Nat) : Value :=
  .obj [("certified", valueCopies n (.str hex64a)), ("suspended", .arr []),
    ("nonces", valueCopies n (.str "0123456789abcdef0123456789abcdef")), ("prime", .null)]

/-- The score family's bounds, at each and one past it: a request at a bound is not refused
by it (it may be answered, or refused by v1's checks), one past it is, with the bound
named. Built here, too long for a line of `pcalc.json`. -/
def runScoreBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let quota (n : Nat) : Value := .obj [("window", valueCopies n (.obj [("counterpart", .null),
    ("weight", .int 1)])), ("counterpart", .str "c"), ("g", .int 1), ("c_max", dec 25 (-2))]
  let cases : List (String × String × Value × Bool) := [
    ("window at 10000", "diversity_quota", quota 10000, false),
    ("window past 10000", "diversity_quota", quota 10001, true),
    ("accounts at 2000", "rank", .obj [("accounts", valueCopies 2000 account)], false),
    ("accounts past 2000", "rank", .obj [("accounts", valueCopies 2001 account)], true),
    ("accounts past 2000, the Prime", "prime_select",
      .obj [("accounts", valueCopies 2001 account), ("override", .null)], true),
    ("items at 5000", "pending_level", .obj [("items", valueCopies 5000 .null), ("now", .int 0)], false),
    ("items past 5000", "pending_level", .obj [("items", valueCopies 5001 .null), ("now", .int 0)], true),
    ("activity at 5000", "peer_activity", .obj [("events", valueCopies 5000 .null)], false),
    ("activity past 5000", "peer_activity", .obj [("events", valueCopies 5001 .null)], true),
    ("prior ages at 100000", "trip", .obj [("S", dec 9 (-1)), ("in_tier", .bool true),
      ("prior_ages", valueCopies 100000 (.int 1))], false),
    ("prior ages past 100000", "trip", .obj [("S", dec 9 (-1)), ("in_tier", .bool true),
      ("prior_ages", valueCopies 100001 (.int 1))], true),
    ("facts at 10000", "override_check", .obj [("decl", .null), ("facts", factsOf 10000)], false),
    ("facts past 10000", "override_check", .obj [("decl", .null), ("facts", factsOf 10001)], true),
    ("facts past 10000, the pad", "pad_check",
      .obj [("decl", .null), ("facts", factsOf 10001)], true),
    ("events at 10000", "evidence", .obj [("events", valueCopies 10000 .null),
      ("idle", .obj [("days", .int 0)])], false),
    ("events past 10000", "evidence", .obj [("events", valueCopies 10001 .null),
      ("idle", .obj [("days", .int 0)])], true),
    ("powers of 2 past 64", "evidence", .obj [("events", evidenceEvents 65 65),
      ("idle", .obj [("days", .int 0)]), ("params", evidenceParams)], true),
    ("agents at 1000", "user_aggregate", .obj [("agents", valueCopies 1000 .null),
      ("sponsor", .str "s")], false),
    ("agents past 1000", "user_aggregate", .obj [("agents", valueCopies 1001 .null),
      ("sponsor", .str "s")], true),
    ("pooled events at 30", "user_aggregate", .obj [("agents", agentWith 30),
      ("sponsor", .str "s")], false),
    ("pooled events past 30", "user_aggregate", .obj [("agents", agentWith 31),
      ("sponsor", .str "s")], true),
    ("pooled events past 30, the user evidence", "user_score_evidence",
      .obj [("agents", agentWith 31), ("conduct", .arr []), ("sponsor", .str "s")], true),
    ("conduct at 10000", "user_score_evidence", .obj [("agents", agentWith 1),
      ("conduct", valueCopies 10000 .null), ("sponsor", .str "s")], false),
    ("conduct past 10000", "user_score_evidence", .obj [("agents", agentWith 1),
      ("conduct", valueCopies 10001 .null), ("sponsor", .str "s")], true),
    ("shape at 0.1", "betainc_inv",
      .obj [("a", dec 1 (-1)), ("b", .int 1), ("p", dec 5 (-1))], false),
    ("shape below 0.1", "betainc_inv",
      .obj [("a", dec 9 (-2)), ("b", .int 1), ("p", dec 5 (-1))], true),
    ("shape at 10000", "betainc", .obj [("a", .int 10000), ("b", .int 10000), ("x", dec 5 (-1))], false),
    ("shape past 10000", "betainc", .obj [("a", .int 1), ("b", .int 10001), ("x", dec 5 (-1))], true),
    ("shape past 10000, the interval", "beta_interval",
      .obj [("a", .int 10001), ("b", .int 1), ("level", dec 95 (-2))], true),
    ("tail at 0.000001", "betainc_inv", .obj [("a", .int 1), ("b", .int 1), ("p", dec 1 (-6))], false),
    ("tail below 0.000001", "betainc_inv", .obj [("a", .int 1), ("b", .int 1), ("p", dec 9 (-7))], true),
    ("upper tail at 0.000001", "betainc_inv",
      .obj [("a", .int 1), ("b", .int 1), ("p", dec 999999 (-6))], false),
    ("upper tail below 0.000001", "betainc_inv",
      .obj [("a", .int 1), ("b", .int 1), ("p", dec 9999991 (-7))], true),
    ("level at 0.999998", "beta_interval",
      .obj [("a", .int 1), ("b", .int 1), ("level", dec 999998 (-6))], false),
    ("level past 0.999998", "beta_interval",
      .obj [("a", .int 1), ("b", .int 1), ("level", dec 9999981 (-7))], true),
    ("x of 4096 bits", "betainc", .obj [("a", .int 1), ("b", .int 1), ("x", dec 1 (-1233))], false),
    ("x of more than 4096 bits", "betainc",
      .obj [("a", .int 1), ("b", .int 1), ("x", dec 1 (-1234))], true),
    ("a coefficient of more than 4096 bits", "evidence",
      .obj [("events", .arr [.obj [("kind", .str "FOR"), ("weight", .int 1), ("age", .int 5000)]]),
        ("idle", .obj [("days", .int 0)]), ("params", .obj [("a0", .int 1), ("b0", .int 1),
          ("HALF-LIFE", .int 1), ("T_idle", .int 90)])], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "score" fn request
    t ← t.check (boundRefusal got == refused)
      s!"score {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The bound on powers of 2, at 64: checked on the sums themselves, the request at it being
  -- slow to answer in full.
  let sums (n : Nat) : Principia.Score.PowSum :=
    ⟨(List.range n).map fun (i : Nat) => (((i : Int) : Rat) / 500, 1)⟩
  let atTerms := Principia.Calculator.Score.termsWithin "F and A" (sums 40) (sums 24)
  t ← t.check (atTerms matches .ok ()) "score evidence: 64 powers of 2 refused"
  let pastTerms := Principia.Calculator.Score.termsWithin "F and A" (sums 40) (sums 25)
  t ← t.check (boundRefusal (pastTerms.map fun _ => Value.null)) "score evidence: 65 powers of 2 not refused"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Score

open Tests.Calculator

/-- The family `score`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc score (score, beta)", runScoreCalls),
  ("pcalc score bounds", runScoreBounds),
]

end Tests.Calculator.Score
