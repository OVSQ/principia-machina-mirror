import Principia
import Lean.Data.Json
import Tests.Beta

/-!
The runner of `vectors/score_corpus.json` (v1's `tpc_score` 0.1.0, corpus 0.1.0, 487 cases),
against `Principia.Score`.

Each case is `{name, fn, args, expected}`, `expected` being v1's `run_case` text: the
function's `render_*` line or lines, or `ERROR:<word>`. Each argument is read as the
Calculator reads a request (`Canonical.Value`), `params` included. The Calculator's typed
outcome is written in v1's form here and compared with v1's text line by line and field by
field: each field is a wire word (read back from the typed enumeration), an integer, a
number in the twelve-digit form of the Calculator's exact value rounded once (`inf` for the
inquiry cost v1's text calls infinite), `true`/`false`, or an account name escaped as v1's
`_esc` escapes it (`|`, `\` and control characters), so that equal text is equal fields and
a name holding `|` cannot pass for two fields (the mutation checks below show it).

The 20 `user_evidence` cases end in `tpc_sponsor.user_evidence`, made by the sponsor's port
(`Principia.Sponsor.scoreUserEvidence`), and are compared as the others are. A case whose
number the Calculator's bounds do not settle is owed, listed in
`vectors/score_corpus.owed.json` with its reason (none at present), and every case listed
there must come out owed for that reason.

The runner also measures the size of the exact values: the most bits of a numerator and of
a denominator among each case's arguments and every number of its answer (a sum of powers
of 2 counted by its coefficients), over both v1 corpora of this family, printed with the
case that reaches it.
-/

open Lean
open Principia
open Principia.Beta
open Principia.Score
open Tests.Beta (toValue arg field)

namespace Tests.Score

/-! ## v1's text -/

/-- v1 `_esc`: `|` and `\` escaped with a backslash, control characters as `\xHH`. -/
def esc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '|' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      "\\x" ++ String.ofList [Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
    else c.toString)

/-- v1 `_b`. -/
def bool (b : Bool) : String := if b then "true" else "false"

/-- A wire word. -/
def wire {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a

/-- A rational's twelve-digit form. -/
def rat (q : Rat) : String := Quantity.ratText q

/-- What a case came to: the Calculator's text in v1's form with the exact values it holds,
or owed. -/
inductive Outcome where
  | text (t : String) (values : List Rat)
  | owed (why : String)

/-- Numbers that must settle before the text can be written. -/
def withNumbers (qs : List Quantity) (f : List String → String) (values : List Rat) : Outcome :=
  match qs.mapM Quantity.twelve? with
  | some ts => .text (f ts) values
  | none => .owed Tests.Beta.unsettled

/-- The exact rationals a sum of powers of 2 holds: its exponents and coefficients. -/
def powValues (x : PowSum) : List Rat := x.terms.flatMap fun t => [t.1, t.2]

/-- A refusal or an answer, as v1's `run_case` writes it. -/
def written {α : Type} (r : Except String α) (f : α → Outcome) : Outcome :=
  match r with
  | .error w => .text ("ERROR:" ++ w) []
  | .ok a => f a

/-! ## The functions, written as v1's `render_*` -/

def runQuota (a : String → Canonical.Value) : Outcome :=
  written (diversityQuota (a "window") (a "counterpart") (a "g") (a "c_max")) fun r =>
    .text ("|".intercalate [rat r.q, rat r.w, rat r.wc, rat r.admitted]) [r.q, r.w, r.wc, r.admitted]

def runEvidence (a : String → Canonical.Value) : Outcome :=
  written (evidence (a "events") (a "idle") (a "params")) fun r =>
    withNumbers [r.f.toQuantity, r.a.toQuantity, r.e, r.lo, r.hi] (fun ts =>
      match ts with
      | [f, aa, e, lo, hi] => "|".intercalate [f, aa, toString r.n, e, lo, hi, rat r.factor]
      | _ => "")
      (powValues r.f ++ powValues r.a ++ [r.factor] ++
        (match r.e with | .exact q => [q] | _ => []))

def runInterval (a : String → Canonical.Value) : Outcome :=
  written (scoreInterval (a "S") (a "E") (a "lo") (a "hi")) fun (l, h) =>
    .text (rat l ++ "|" ++ rat h) [l, h]

def runStanding (a : String → Canonical.Value) : Outcome :=
  written (standing (a "x") (a "y")) fun s => .text (wire s) []

def rankText (r : Rank) : String :=
  "\n".intercalate (s!"rank|{r.count}|{r.cut}" :: r.rows.map fun row =>
    match row.place with
    | none => s!"row|{esc row.name}|-|-|false"
    | some (pos, pct) => s!"row|{esc row.name}|{pos}|{rat pct}|{bool row.tier}")

def runRank (a : String → Canonical.Value) : Outcome :=
  written (rank (a "accounts") (a "params")) fun r =>
    .text (rankText r) (r.rows.filterMap fun row => row.place.map (·.2))

def runPrime (a : String → Canonical.Value) : Outcome :=
  written (primeSelect (a "accounts") (a "override") (a "params")) fun (p, why) =>
    .text ((match p with | none => "-" | some n => esc n) ++ "|" ++ wire why) []

def runLevel (a : String → Canonical.Value) : Outcome :=
  written (pendingLevel (a "items") (a "now") (a "params")) fun r =>
    .text ("|".intercalate [wire r.level, toString r.h, toString r.i, toString r.sim,
      toString r.low, toString r.counted, toString r.expired]) []

def runState (a : String → Canonical.Value) : Outcome :=
  written (stateStep (a "prev") (a "level") (a "event") (a "params")) fun r =>
    .text (s!"{wire r.state}|{r.passes}|{wire r.change}") []

def runActivity (a : String → Canonical.Value) : Outcome :=
  written (peerActivity (a "events") (a "params")) fun (n, x) => .text (s!"{n}|{rat x}") [x]

def runUpdate (a : String → Canonical.Value) : Outcome :=
  written (scoreUpdate (a "role") (a "S") (a "E") (a "S_P") (a "a") (a "params")) fun r =>
    .text ("|".intercalate [rat r.s, rat r.target, rat r.k, rat r.step, bool r.clipped])
      [r.s, r.target, r.k, r.step]

def runCut (a : String → Canonical.Value) : Outcome :=
  written (violationCut (a "S") (a "m_class") (a "standing") (a "params")) fun r =>
    .text ("|".intercalate [rat r.s, rat r.m, rat r.aInc]) [r.s, r.m, r.aInc]

def runTrip (a : String → Canonical.Value) : Outcome :=
  written (trip (a "S") (a "in_tier") (a "prior_ages") (a "params")) fun (t, why) =>
    .text ((if t then "TRIP" else "PICKUP") ++ "|" ++ wire why) []

def runInquire (a : String → Canonical.Value) : Outcome :=
  written (inquire (a "state") (a "block") (a "S") (a "params")) fun r =>
    .text ("|".intercalate [(match r.cost with | none => "inf" | some c => rat c), rat r.s,
      toString r.k, bool r.inside, toString r.last, toString r.k])
      (r.s :: r.cost.toList)

def refusalText (r : DeclRefusal) : String := "REFUSED|" ++ wire r

def runOverride (a : String → Canonical.Value) : Outcome :=
  written (overrideCheck (a "decl") (a "facts") (a "params")) fun r =>
    match r with
    | .error why => .text (refusalText why) []
    | .ok o => .text (s!"OK|{rat o.value}|{o.effective}|{o.sunset}|" ++ o.replaces.getD "-") [o.value]

def runEffective (a : String → Canonical.Value) : Outcome :=
  written (overrideEffective (a "decl_time") (a "now") (a "cancelled") (a "params")) fun s =>
    .text (wire s) []

def runMark (a : String → Canonical.Value) : Outcome :=
  written (overrideMark (a "grant") (a "now") (a "params")) fun (f, n) => .text (s!"{bool f}|{n}") []

def runPad (a : String → Canonical.Value) : Outcome :=
  written (padCheck (a "decl") (a "facts") (a "params")) fun r =>
    match r with
    | .error why => .text (refusalText why) []
    | .ok o =>
      .text (s!"OK|{o.value}|{o.effective}|{bool o.mark}|" ++
        (match o.sunset with | none => "-" | some n => toString n)) []

def runPadWeight (a : String → Canonical.Value) : Outcome :=
  written (padWeight (a "P") (a "age") (a "params")) fun w =>
    withNumbers [w.toQuantity] (String.join) (powValues w)

def gateText : GateAnswer → String
  | .pass => "PASS|TIER"
  | .notInTier => "REFUSED|NOT IN TIER"
  | .overrideMark => "REFUSED|OVERRIDE MARK"

def runGate (a : String → Canonical.Value) : Outcome :=
  written (tierGateRelease (a "reproducer")) fun g => .text (gateText g) []

def runInherit (a : String → Canonical.Value) : Outcome :=
  written (inherit (a "F_old") (a "facts") (a "params")) fun (f, s, c) =>
    .text (s!"{rat f}|{rat s}|{bool c}") [f, s]

/-- An answer that may be refused, owed or settled. -/
def stopped {α : Type} (r : Except Stop α) (f : α → Outcome) : Outcome :=
  match r with
  | .error (.refused w) => .text ("ERROR:" ++ w) []
  | .error .unsettled => .owed Tests.Beta.unsettled
  | .ok a => f a

def runAggregate (a : String → Canonical.Value) : Outcome :=
  stopped (userAggregate (a "agents") (a "sponsor") (a "params")) fun r =>
    match r with
    | .none => .text "aggregate|NONE" []
    | .pooled evs =>
      withNumbers (evs.map (·.weight.toQuantity)) (fun ts =>
        "\n".intercalate ("aggregate|OK" :: (evs.zip ts).map fun (e, t) =>
          s!"event|{wire e.side}|{t}|{e.age}"))
        (evs.flatMap (powValues ·.weight))

def runUserEvidence (a : String → Canonical.Value) : Outcome :=
  stopped (Sponsor.scoreUserEvidence (a "agents") (a "conduct") (a "sponsor") (a "params")) fun r =>
    match r with
    | none => .text "NONE" []
    | some r =>
      withNumbers [r.f.toQuantity, r.a.toQuantity, r.e, r.lo, r.hi] (fun ts =>
        match ts with
        | [f, aa, e, lo, hi] => "|".intercalate ["OK", f, aa, toString r.n, e, lo, hi]
        | _ => "")
        (powValues r.f ++ powValues r.a ++ (match r.e with | .exact q => [q] | _ => []))

def runSponsorCut (a : String → Canonical.Value) : Outcome :=
  written (sponsorCut (a "S") (a "m_class") (a "params")) fun x => .text (rat x) [x]

/-- The Calculator's outcome on a case. -/
def run (fn : String) (args : Json) : IO Outcome := do
  let a := arg args
  match fn with
  | "quota" => return runQuota a
  | "evidence" => return runEvidence a
  | "interval" => return runInterval a
  | "standing" => return runStanding a
  | "rank" => return runRank a
  | "prime" => return runPrime a
  | "level" => return runLevel a
  | "state" => return runState a
  | "activity" => return runActivity a
  | "update" => return runUpdate a
  | "cut" => return runCut a
  | "trip" => return runTrip a
  | "inquire" => return runInquire a
  | "override" => return runOverride a
  | "effective" => return runEffective a
  | "mark" => return runMark a
  | "pad" => return runPad a
  | "pad_weight" => return runPadWeight a
  | "gate" => return runGate a
  | "inherit" => return runInherit a
  | "aggregate" => return runAggregate a
  | "user_evidence" => return runUserEvidence a
  | "sponsor_cut" => return runSponsorCut a
  | other => throw (IO.userError s!"score: no runner for {other}")

/-! ## Comparing: line by line, field by field -/

/-- A line's fields: split at each `|` that no backslash escapes, as v1's `_esc` writes
them. -/
def fieldsOf (line : String) : List String :=
  let rec go : List Char → List Char → List String → List String
    | [], cur, acc => acc ++ [String.ofList cur.reverse]
    | '\\' :: c :: rest, cur, acc => go rest (c :: '\\' :: cur) acc
    | '|' :: rest, cur, acc => go rest [] (acc ++ [String.ofList cur.reverse])
    | c :: rest, cur, acc => go rest (c :: cur) acc
  go line.toList [] []

/-- v1's text against the Calculator's: the same lines, each with the same fields. -/
def agrees (expected mine : String) : Bool :=
  let a := expected.splitOn "\n"
  let b := mine.splitOn "\n"
  a.length == b.length && (a.zip b).all fun (x, y) =>
    let fx := fieldsOf x
    let fy := fieldsOf y
    fx.length == fy.length && (fx.zip fy).all fun (p, q) => p == q

/-- Each check is `true` when the comparison does what it must: an account named `a|b`
and one named `a` beside a field `b` are two texts and two field lists; a swapped pair of
numbers is refused. -/
def mutationChecks : List (String × Bool) :=
  let r1 : Rank := ⟨1, 1, [⟨"a|b", some (1, 1), true⟩]⟩
  let t1 := rankText r1
  [("an escaped name is one field", (fieldsOf "row|a\\|b|1|1|true").length == 5),
   ("the rank text as written is accepted", agrees t1 t1),
   ("an unescaped bar in a name is refused", !agrees "rank|1|1\nrow|a|b|1|1|true" t1),
   ("swapped numbers are refused", !agrees "0.5225|0.8|0.075|0.0225|false" "0.8|0.5225|0.075|0.0225|false"),
   ("a missing line is refused", !agrees "rank|1|1" t1)]

/-! ## Sizes -/

/-- The bits of a nonzero natural number. -/
def bitsOf (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Every exact number an argument holds. -/
partial def valueRats : Canonical.Value → List Rat
  | .int n => [n]
  | .num x => [decimalRat x]
  | .arr xs => xs.flatMap valueRats
  | .obj ms => ms.flatMap (valueRats ·.2)
  | _ => []

/-- The largest numerator and denominator met so far, each with its case. -/
structure Sizes where
  num : Nat := 0
  numCase : String := ""
  den : Nat := 0
  denCase : String := ""

def Sizes.add (s : Sizes) (name : String) (qs : List Rat) : Sizes :=
  qs.foldl (fun s q =>
    let n := bitsOf q.num.natAbs
    let d := bitsOf q.den
    let s := if s.num < n then { s with num := n, numCase := name } else s
    if s.den < d then { s with den := d, denCase := name } else s) s

/-! ## The run -/

/-- Run the corpus: passes and failures; owed cases are counted. -/
def runScore : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for (what, ok) in mutationChecks do
    unless ok do
      IO.eprintln s!"FAIL score runner mutation check: {what}"
      fail := fail + 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/score_corpus.json"))
  let cases ← IO.ofExcept ((← field json "cases").getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/score_corpus.owed.json"))
  let listed ← (← IO.ofExcept ((← field owedJson "owed").getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut owed : List (String × String) := []
  let mut sizes : Sizes := {}
  let mut perFn : List (String × Nat) := []
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let args ← field c "args"
    sizes := sizes.add name (valueRats (toValue args))
    match ← run fn args with
    | .owed why => owed := owed ++ [(name, why)]
    | .text mine values =>
      sizes := sizes.add name values
      if agrees expected mine then
        pass := pass + 1
        perFn := match perFn.find? (·.1 == fn) with
          | some _ => perFn.map fun (k, n) => if k == fn then (k, n + 1) else (k, n)
          | none => perFn ++ [(fn, 1)]
      else
        IO.eprintln s!"FAIL score {name} ({fn}):\n  expected {repr expected}\n  got      {repr mine}"
        fail := fail + 1
  for (name, why) in owed do
    unless listed.contains (name, why) do
      IO.eprintln s!"FAIL score {name}: owed ({why}) but not listed so in vectors/score_corpus.owed.json"
      fail := fail + 1
  for (name, why) in listed do
    unless owed.contains (name, why) do
      IO.eprintln s!"FAIL score {name}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  -- The Beta layer's corpus, measured alike: arguments and exact answers.
  let beta ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/beta_corpus.json"))
  for c in ← IO.ofExcept ((← field beta "cases").getArr?) do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let args ← field c "args"
    let a := arg args
    sizes := sizes.add name (valueRats (toValue args))
    match ← IO.ofExcept (c.getObjValAs? String "fn") with
    | "mean" => sizes := sizes.add name ((betaMean (a "a") (a "b")).toOption.toList)
    | "canon" => sizes := sizes.add name ((canonOf (a "x")).toOption.toList)
    | _ => pure ()
  let counts := perFn.map fun (k, n) => s!"{k} {n}"
  IO.println s!"score_corpus: {pass} pass, no divergence, {owed.length} owed; {", ".intercalate counts}"
  IO.println s!"score and beta: the largest exact value has a numerator of {sizes.num} bits ({sizes.numCase}) and a denominator of {sizes.den} bits ({sizes.denCase})"
  return (pass, fail)

end Tests.Score
