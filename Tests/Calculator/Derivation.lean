import Tests.Calculator.Common

/-!
The Calculator's runners of the family `derivation`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The derivation family: the structured checker's corpora through `pcalc derivation`

Every record of `vectors/structured_credit.json` given to `derivation credit_record` as a
RESULT holding its DERIVATION in the wire form, and each STRUCTURED one also to
`derivation credit` as a payload, on the case's `sources` or on sources holding its `laws`:
a LAW of the Starting Set for each law, and for each ASSUMPTION record one of the register
that the record's ASSUMPTIONS name. The answer is the case's verdict and class as wire
words; a KERNEL derivation is refused `OWED`. Every case of `vectors/structured_wire.json`
given to `derivation credit` as the value its text reads to: a payload the reader refuses is
`BAD_ARGUMENT`, its detail ending with the reader's word; one it reads is credited as the
case's `credit` says, or (without one) answered. Then the family's bounds, at each and one
past it. -/

/-- A corpus of the Calculator's own reading. -/
def derivCorpus (path : System.FilePath) : IO Value := do
  match readString (← IO.FS.readFile path) with
  | .ok v => pure v
  | .error f => throw (IO.userError s!"{path}: refused {repr f}")

/-- A member the case needs. -/
def derivNeed (v : Value) (k : String) : IO Value :=
  match member v k with
  | some x => pure x
  | none => throw (IO.userError s!"derivation: no member {k}")

/-- A runner-shaped step in the wire form: its EQUATION, its citation, its SITE (empty when
the case gives none) and FORWARD (false for `"dir": "bwd"`). -/
def derivWireStep (j : Value) : IO Value := do
  let eq ← memberStr j "equation"
  let cite ← match member j "law", member j "assumption", member j "identity" with
    | some (.str n), _, _ => pure ("LAW", Value.str n)
    | _, some (.str r), _ => pure ("ASSUMPTION", Value.str r)
    | _, _, some (.str n) => pure ("IDENTITY", Value.str n)
    | _, _, _ => throw (IO.userError "derivation: a step cites nothing")
  let site := match member j "site" with
    | some (.str s) => s
    | _ => ""
  let fwd := match member j "dir" with
    | some (.str "bwd") => false
    | _ => true
  pure (.obj [("EQUATION", .str eq), cite, ("SITE", .str site), ("FORWARD", .bool fwd)])

/-- A runner-shaped list of steps in the wire form. -/
def derivWireSteps (v : Value) : IO Value := do
  match v with
  | .arr xs => pure (.arr (← xs.mapM derivWireStep))
  | _ => throw (IO.userError "derivation: the steps are not a list")

/-- A runner-shaped start as the payload's START member; none for the left side. -/
def derivWireStart (j : Value) : IO (List (String × Value)) := do
  match member j "start" with
  | none => pure []
  | some s =>
    match member s "law", member s "assumption", member s "refl" with
    | some (.str n), _, _ => pure [("START", .obj [("LAW", .str n)])]
    | _, some (.str r), _ => pure [("START", .obj [("ASSUMPTION", .str r)])]
    | _, _, some (.str e) => pure [("START", .obj [("EXPRESSION", .str e)])]
    | _, _, _ => throw (IO.userError "derivation: not a start")

/-- A runner-shaped derivation in the wire form of the DERIVATION sum. -/
def derivWire (j : Value) : IO Value := do
  match member j "structured", member j "prose", member j "kernelProof" with
  | some s, _, _ => pure (.obj ((← derivWireStart j) ++ [("STEPS", ← derivWireSteps s)]))
  | _, some p, _ =>
    let n ← match member p "steps" with
      | some (.int n) => pure n
      | _ => throw (IO.userError "derivation: PROSE without a step count")
    let att ← match member p "attachment" with
      | some a => pure [("ATTACHMENT", .obj [("STEPS", ← derivWireSteps a)])]
      | none => pure []
    pure (.obj ([("STEPS", .int n), ("TEXT", .str (← memberStr p "text"))] ++ att))
  | _, _, some (.str p) => pure (.obj [("PROOF", .str p)])
  | _, _, _ => throw (IO.userError "derivation: not a derivation")

/-- A case's sources, `(starting_set, register, assumptions)`: its `sources` as written, or
its `laws` as LAWs of the Starting Set and ASSUMPTION records the ASSUMPTIONS name. -/
def derivSources (c : Value) : IO (Value × Value × Value) := do
  match member c "sources", member c "laws" with
  | some s, _ =>
    pure ((member s "startingSet").getD (.obj []), (member s "register").getD (.arr []),
      (member s "assumptions").getD (.arr []))
  | _, some (.arr ls) =>
    let mut laws : List Value := []
    let mut records : List Value := []
    let mut ids : List Value := []
    for l in ls do
      let name ← memberStr l "name"
      let eq ← memberStr l "equation"
      if (← memberStr l "cite") == "law" then
        laws := laws ++ [.obj [("NAME", .str name), ("EQUATION", .str eq)]]
      else
        records := records ++ [.obj [("ID", .str name), ("CLASS", .str "ASSUMPTION"),
          ("EQUATION", .str eq)]]
        ids := ids ++ [.str name]
    pure (.obj [("LAW", .arr laws)], .arr records, .arr ids)
  | _, _ => throw (IO.userError "derivation: a case has neither laws nor sources")

/-- The answer a case expects: its verdict and class as wire words. -/
def derivExpected (expect : Value) (cls : String) : IO Value := do
  let c := ("CLASS", Value.str cls)
  match ← memberStr expect "verdict" with
  | "accepted" => pure (.obj [c, ("VERDICT", .str "ACCEPTED")])
  | "notStructured" => pure (.obj [c, ("VERDICT", .str "NOT_STRUCTURED")])
  | v =>
    let i ← match member expect "step" with
      | some (.int i) => pure i
      | _ => throw (IO.userError "derivation: a verdict without its step")
    let word := if v == "refused" then "REFUSED" else "UNREADABLE"
    pure (.obj [c, ("STEP", .int i), ("VERDICT", .str word), ("WHY", .str (← memberStr expect "why"))])

/-- An answer's canonical JSON, or the refusal's code and detail. -/
def derivShow (r : Except Refusal Value) : String :=
  match r with
  | .ok v => (v.canonicalJson.getD "?")
  | .error f => s!"refused {f.code.word}: {f.detail}"

/-- A `credit` request. -/
def derivCreditRequest (payload : Value) (eq : String) (sources : Value × Value × Value) :
    Value :=
  let (ss, reg, asm) := sources
  .obj [("derivation", payload), ("equation", .str eq), ("assumptions", asm),
    ("starting_set", ss), ("register", reg)]

def runDerivationCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let credit ← derivCorpus "vectors/structured_credit.json"
  let .arr records ← derivNeed credit "records" | throw (IO.userError "derivation: no records")
  for c in records do
    let id ← memberStr c "id"
    let eq ← memberStr c "equation"
    let sources@(ss, reg, asm) ← derivSources c
    let dj ← derivNeed c "derivation"
    let dv ← derivWire dj
    let want := (← derivExpected (← derivNeed c "expect") (← memberStr c "class")).canonicalJson
    let record : Value := .obj [("ASSUMPTIONS", asm), ("CLASS", .str "RESULT"),
      ("DERIVATION", dv), ("EQUATION", .str eq)]
    let gotR := respondTo "derivation" "credit_record"
      (.obj [("record", record), ("starting_set", ss), ("register", reg)])
    let okR := if (member dj "kernelProof").isSome then
        match gotR with
        | .error r => r.code == .owed && r.detail == Derivation.kernelOwed
        | .ok _ => false
      else gotR.toOption.bind (·.canonicalJson) == want
    let gotC := if (member dj "structured").isSome then
        some (respondTo "derivation" "credit" (derivCreditRequest dv eq sources))
      else none
    let okC := match gotC with
      | some g => g.toOption.bind (·.canonicalJson) == want
      | none => true
    t ← t.check (okR && okC)
      s!"derivation {id}: credit_record {derivShow gotR}, credit {(gotC.map derivShow).getD "-"}, expected {repr want}"
  let wire ← derivCorpus "vectors/structured_wire.json"
  let .arr cases ← derivNeed wire "cases" | throw (IO.userError "derivation: no cases")
  for c in cases do
    let id ← memberStr c "id"
    let payload ← match readString (← memberStr c "text") with
      | .ok v => pure v
      | .error f => throw (IO.userError s!"derivation {id}: the text does not read: {repr f}")
    match member c "refused" with
    | some (.str w) =>
      let got := respondTo "derivation" "credit"
        (derivCreditRequest payload "F = m * a" (.obj [], .arr [], .arr []))
      let ok := match got with
        | .error r => r.code == .badArgument &&
            r.detail == s!"the derivation is not a STRUCTURED payload: {w}"
        | .ok _ => false
      t ← t.check ok s!"derivation {id}: {derivShow got}, expected BAD_ARGUMENT {w}"
    | _ =>
      match member c "credit" with
      | some k =>
        let got := respondTo "derivation" "credit"
          (derivCreditRequest payload (← memberStr k "equation") (← derivSources k))
        let want := (← derivExpected (← derivNeed k "expect") (← memberStr k "class")).canonicalJson
        t ← t.check (got.toOption.bind (·.canonicalJson) == want)
          s!"derivation {id}: {derivShow got}, expected {repr want}"
      | none =>
        let got := respondTo "derivation" "credit"
          (derivCreditRequest payload "F = m * a" (.obj [], .arr [], .arr []))
        t ← t.check got.toOption.isSome s!"derivation {id}: {derivShow got}, expected an answer"
  return t.pair

/-- `n` steps from `a + b = a + b`, each commuting the right side, back to it when `n` is
even. -/
def derivCommuting (n : Nat) : Value :=
  .obj [("START", .obj [("EXPRESSION", .str "a + b")]),
    ("STEPS", .arr ((List.range n).map fun i =>
      .obj [("EQUATION", .str (if i % 2 == 0 then "a + b = b + a" else "a + b = a + b")),
        ("IDENTITY", .str "addComm"), ("SITE", .str "rhs"), ("FORWARD", .bool true)]))]

/-- An EQUATION's text of `n` code points: `x = x` and spaces. -/
def derivLongEquation (n : Nat) : String := "x = x" ++ chars (n - 5) ' '

/-- `n` ASSUMPTION records of the register, `A-1` to `A-n`. -/
def derivRegister (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("ID", .str s!"A-{i + 1}"),
    ("CLASS", .str "ASSUMPTION"), ("EQUATION", .str "q = 0")])

/-- `n` identifiers `A-1` to `A-n`. -/
def derivIds (n : Nat) : Value := strs ((List.range n).map fun i => s!"A-{i + 1}")

def runDerivationBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let none3 : Value × Value × Value := (.obj [], .arr [], .arr [])
  let credit (payload : Value) (eq : String) (s : Value × Value × Value) : Value :=
    derivCreditRequest payload eq s
  let plain := derivCommuting 2
  let lawSet (eq : String) : Value := .obj [("LAW", .arr [.obj [("NAME", .str "n"), ("EQUATION", .str eq)]])]
  let record (d : Value) : Value := .obj [("record", .obj [("EQUATION", .str "a + b = a + b"),
    ("DERIVATION", d)]), ("starting_set", .obj []), ("register", .arr [])]
  -- (what, function, request, past the bound)
  let cases : List (String × String × Value × Bool) := [
    ("steps at 1024", "credit", credit (derivCommuting 1024) "a + b = a + b" none3, false),
    ("steps past 1024", "credit", credit (derivCommuting 1025) "a + b = a + b" none3, true),
    ("a record's steps past 1024", "credit_record", record (derivCommuting 1025), true),
    ("the EQUATION at 16384 code points", "credit", credit plain (derivLongEquation 16384) none3, false),
    ("the EQUATION past 16384 code points", "credit", credit plain (derivLongEquation 16385) none3, true),
    ("a step's EQUATION past 16384 code points", "credit",
      credit (.obj [("STEPS", .arr [.obj [("EQUATION", .str (derivLongEquation 16385)),
        ("IDENTITY", .str "addComm"), ("SITE", .str "rhs"), ("FORWARD", .bool true)]])])
        "x = x" none3, true),
    ("a LAW's EQUATION at 16384 code points", "credit",
      credit plain "a + b = a + b" (lawSet (derivLongEquation 16384), .arr [], .arr []), false),
    ("a LAW's EQUATION past 16384 code points", "credit",
      credit plain "a + b = a + b" (lawSet (derivLongEquation 16385), .arr [], .arr []), true),
    ("a Starting Set kind at 64", "credit",
      credit plain "a + b = a + b" (.obj [("DOF", valueCopies 64 (.obj []))], .arr [], .arr []), false),
    ("a Starting Set kind past 64", "credit",
      credit plain "a + b = a + b" (.obj [("DOF", valueCopies 65 (.obj []))], .arr [], .arr []), true),
    ("the register at 1024 records", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 1024, derivIds 1), false),
    ("the register past 1024 records", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 1025, derivIds 1), true),
    ("ASSUMPTIONS at 512", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 512, derivIds 512), false),
    ("ASSUMPTIONS past 512", "credit",
      credit plain "a + b = a + b" (.obj [], derivRegister 513, derivIds 513), true),
    ("ASSUMPTIONS past 512, the law table", "laws",
      .obj [("assumptions", derivIds 513), ("starting_set", .obj []), ("register", .arr [])], true)]
  for (what, fn, request, past) in cases do
    let got := respondTo "derivation" fn request
    let ok := if past then boundRefusal got else got.toOption.isSome
    t ← t.check ok s!"derivation {fn}, {what}: {derivShow got}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Derivation

open Tests.Calculator

/-- The family `derivation`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc derivation (structured_credit, structured_wire)", runDerivationCalls),
  ("pcalc derivation bounds", runDerivationBounds),
]

end Tests.Calculator.Derivation
