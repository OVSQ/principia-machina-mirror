import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/structured_check.json`, written by hand, for the structured
derivation checker's first increment (`Principia.StructuredCheck`).

The corpus has three lists.

* `check`: a derivation and its verdict. A case gives the law table (`laws`: each entry a
  citation, `law` by NAME or `assumption` by record identifier, with its EQUATION's text),
  the start (a citation, or `refl` with an expression's text), the steps and the goal (the
  RESULT's EQUATION). A step gives its side (`lhs` or `rhs`), its path (`l`, `r` and `a`
  joined by dots, empty for the whole side), its rule (`law`, `assumption` or `identity`)
  with the `name` it cites or applies, its direction (`fwd` or `bwd`) and the equation it
  states; with `"instance": true` a law or record is cited by an instance of it (matched,
  not exact). `expect` is `accepted`, or `refused` with the failing step's number and why.
* `match`: first-order matching (`matchExpr`) of a `pattern` against a `target`, both read
  and stripped of their parentheses as the checker reads a law and an equation. `bindings`
  is the substitution matching finds, each identifier of the pattern with the expression
  it stands for, or `null` when the target is no instance of the pattern. Every
  substitution found is also checked to make the pattern exactly the target.
* `eval`: an expression's value under an assignment (rationals written `p` or `p/q`) and
  the runner's interpretation `sample`, whose functions return their argument, whose
  `D(x, s, n)` is worth `n` and whose fractional power is worth its base. The value is
  compared as `Rat`'s text.

Every text in the corpus must read by the declared-form grammar; one that does not is a
defect of the corpus, not a failing case.
-/

open Lean
open Principia
open Principia.Form
open Principia.Record (StepCitation)
open Principia.StructuredCheck

namespace Tests.StructuredCheck

def field (j : Json) (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
def str (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)
def arr (j : Json) (k : String) : IO (List Json) := do
  return (← IO.ofExcept ((← field j k).getArr?)).toList

def corpusError {α : Type} (what : String) : IO α := throw (IO.userError s!"structured_check: {what}")

def equation (text : String) : IO Equation :=
  match Equation.parse text with
  | .ok e => pure e
  | .error r => corpusError s!"the equation {repr text} does not read: {r}"

def expression (text : String) : IO Expr :=
  match parseExpr text with
  | .ok e => pure e
  | .error r => corpusError s!"the expression {repr text} does not read: {r}"

/-- A citation: its kind and name. -/
def citation (kind name : String) : IO StepCitation :=
  match kind with
  | "law" => pure (.law name)
  | "assumption" => pure (.assumption name)
  | w => corpusError s!"not a citation kind: {repr w}"

def dir : String → IO Dir
  | "l" => pure .left
  | "r" => pure .right
  | "a" => pure .arg
  | w => corpusError s!"not a path step: {repr w}"

def path (s : String) : IO (List Dir) :=
  if s.isEmpty then pure [] else (s.splitOn ".").mapM dir

def forward : String → IO Bool
  | "fwd" => pure true
  | "bwd" => pure false
  | w => corpusError s!"not a direction: {repr w}"

def side : String → IO Side
  | "lhs" => pure .lhs
  | "rhs" => pure .rhs
  | w => corpusError s!"not a side: {repr w}"

def rule (j : Json) : IO Rule := do
  let kind ← str j "rule"
  let name ← str j "name"
  let fwd ← forward (← str j "dir")
  let byInstance ← match j.getObjVal? "instance" with
    | .ok v => IO.ofExcept v.getBool?
    | .error _ => pure false
  if kind == "identity" then
    if byInstance then corpusError s!"an identity is not cited by instance: {repr name}"
    match Identity.ofName? name with
    | some i => pure (.identity i fwd)
    | none => corpusError s!"not an identity: {repr name}"
  else if byInstance then
    pure (.citeInstance (← citation kind name) fwd)
  else
    pure (.cite (← citation kind name) fwd)

def step (j : Json) : IO Step := do
  pure { side := ← side (← str j "side"), path := ← path (← str j "path"), rule := ← rule j,
         result := ← equation (← str j "result") }

def start (j : Json) : IO Start := do
  match j.getObjValAs? String "refl" with
  | .ok text => pure (.refl (← expression text))
  | .error _ => pure (.cite (← citation (← str j "cite") (← str j "name")))

def lawEntry (j : Json) : IO (StepCitation × Equation) := do
  pure (← citation (← str j "cite") (← str j "name"), ← equation (← str j "equation"))

def verdictText : Verdict → String
  | .accepted => "accepted"
  | .refused i w => s!"refused {i} {w}"

def expectText (j : Json) : IO String := do
  match ← str j "verdict" with
  | "accepted" => pure "accepted"
  | "refused" =>
    let i ← IO.ofExcept (j.getObjValAs? Nat "step")
    pure s!"refused {i} {← str j "why"}"
  | w => corpusError s!"not a verdict: {repr w}"

/-- The runner's interpretation of the function symbols for `eval`'s cases. -/
def sample : Interp where
  fn := fun _ v => v
  deriv := fun _ _ n => n
  pow := fun b _ _ => b

/-- A rational written `p` or `p/q`. -/
def rational (s : String) : IO Rat :=
  match s.splitOn "/" with
  | [p] => match p.toInt? with
    | some n => pure n
    | none => corpusError s!"not a rational: {repr s}"
  | [p, q] => match p.toInt?, q.toNat? with
    | some n, some d => if d == 0 then corpusError s!"a zero denominator: {repr s}" else pure ((n : Rat) / d)
    | _, _ => corpusError s!"not a rational: {repr s}"
  | _ => corpusError s!"not a rational: {repr s}"

def assignment (j : Json) : IO (String → Rat) := do
  let obj ← IO.ofExcept j.getObj?
  let mut pairs : List (String × Rat) := []
  for ⟨k, v⟩ in obj.toArray do
    pairs := (k, ← rational (← IO.ofExcept v.getStr?)) :: pairs
  let table := pairs
  return fun n => ((table.find? (·.1 == n)).map (·.2)).getD 0

def runStructuredCheck : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/structured_check.json"))
  let mut pass := 0
  let mut fail := 0
  for c in ← arr json "check" do
    let id ← str c "id"
    let laws ← (← arr c "laws").mapM lawEntry
    let st ← start (← field c "start")
    let steps ← (← arr c "steps").mapM step
    let goal ← equation (← str c "goal")
    let got := verdictText (check laws st steps goal)
    let want ← expectText (← field c "expect")
    if got == want then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_check {id}: got {got}, expected {want}"
      fail := fail + 1
  for c in ← arr json "match" do
    let id ← str c "id"
    let pat := unparen (← expression (← str c "pattern"))
    let tgt := unparen (← expression (← str c "target"))
    let got := matchExpr pat tgt []
    let want ← match ← field c "bindings" with
      | .null => pure none
      | j =>
        let obj ← IO.ofExcept j.getObj?
        let mut bs : List (String × Expr) := []
        for ⟨k, v⟩ in obj.toArray do
          bs := bs ++ [(k, unparen (← expression (← IO.ofExcept v.getStr?)))]
        pure (some bs)
    let ok := match got, want with
      | none, none => true
      | some θ, some bs =>
        θ.length == bs.length && bs.all (fun (k, e) => θ.lookup k == some e) &&
          subst θ pat == tgt
      | _, _ => false
    if ok then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_check {id}: got {repr got}, expected {repr want}"
      fail := fail + 1
  for c in ← arr json "eval" do
    let id ← str c "id"
    let e ← expression (← str c "expr")
    let σ ← assignment (← field c "assign")
    let got := toString (eval sample σ e)
    let want ← str c "value"
    if got == want then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_check {id}: got {got}, expected {want}"
      fail := fail + 1
  return (pass, fail)

/-! ## structured_credit.json: a record's STRUCTURED derivation, its verdict and credit -/

/-- A record's step: `equation`, one of `law`, `assumption` or `identity` with its name,
and `site` and `dir` when the record gives them (absent, the defaults of
`StructuredStep`: no site, forward). -/
def recordStep (j : Json) : IO Principia.Record.StructuredStep := do
  let eq ← str j "equation"
  let cites ← match j.getObjValAs? String "law", j.getObjValAs? String "assumption",
      j.getObjValAs? String "identity" with
    | .ok n, _, _ => pure (StepCitation.law n)
    | _, .ok r, _ => pure (StepCitation.assumption r)
    | _, _, .ok n => pure (StepCitation.identity n)
    | _, _, _ => corpusError s!"a step cites nothing: {j.compress}"
  let site := (j.getObjValAs? String "site").toOption.getD ""
  let fwd ← match j.getObjValAs? String "dir" with
    | .ok d => forward d
    | .error _ => pure true
  return { equation := eq, cites, site, forward := fwd }

/-- A record's start: `{"law": name}`, `{"assumption": id}` or `{"refl": expression}`;
absent, the EQUATION's left side. -/
def recordStart (j : Json) : IO Principia.Record.StructuredStart := do
  match j.getObjVal? "start" with
  | .error _ => pure .lhs
  | .ok s =>
    match s.getObjValAs? String "law", s.getObjValAs? String "assumption",
        s.getObjValAs? String "refl" with
    | .ok n, _, _ => pure (.law n)
    | _, .ok r, _ => pure (.assumption r)
    | _, _, .ok e => pure (.refl e)
    | _, _, _ => corpusError s!"not a start: {s.compress}"

/-- A record's derivation: `{"structured": [...], "start"?: ...}`, `{"prose": {"steps",
"text"}}` or `{"kernelProof": "..."}`. -/
def recordDerivation (j : Json) : IO Principia.Record.Derivation := do
  match j.getObjVal? "structured", j.getObjVal? "prose", j.getObjVal? "kernelProof" with
  | .ok s, _, _ =>
    return .structured (← (← IO.ofExcept s.getArr?).toList.mapM recordStep) (← recordStart j)
  | _, .ok p, _ =>
    let n ← IO.ofExcept (p.getObjValAs? Nat "steps")
    let text ← str p "text"
    let att ← match p.getObjVal? "attachment" with
      | .ok a => pure (some (.structured (← (← IO.ofExcept a.getArr?).toList.mapM recordStep) .lhs))
      | .error _ => pure none
    return .prose n text att
  | _, _, .ok (.str e) => return .kernelProof e
  | _, _, _ => corpusError s!"not a derivation: {j.compress}"

def recordVerdictText : RecordVerdict → String
  | .accepted => "accepted"
  | .refused i w => s!"refused {i} {w}"
  | .unreadable i w => s!"unreadable {i} {w}"
  | .notStructured => "notStructured"

def recordExpectText (j : Json) : IO String := do
  match ← str j "verdict" with
  | "accepted" => pure "accepted"
  | "notStructured" => pure "notStructured"
  | v@"refused" | v@"unreadable" =>
    let i ← IO.ofExcept (j.getObjValAs? Nat "step")
    pure s!"{v} {i} {← str j "why"}"
  | w => corpusError s!"not a verdict: {repr w}"

/-- A record's law table: `laws` as written, or assembled by `recordLaws` from
`sources`, its Starting Set, the register's records and the record's ASSUMPTIONS, each
read as v1's JSON reader gives it. -/
def recordTable (c : Json) : IO LawTable := do
  match c.getObjVal? "laws", c.getObjVal? "sources" with
  | .ok _, _ => (← arr c "laws").mapM lawEntry
  | _, .ok s =>
    let ss := Tests.Zone.toValue (← field s "startingSet")
    let register := (← arr s "register").map Tests.Zone.toValue
    let assumptions ← (← arr s "assumptions").mapM fun j => IO.ofExcept j.getStr?
    pure (recordLaws ss register assumptions)
  | _, _ => corpusError s!"a record has neither laws nor sources: {c.compress}"

def runStructuredCredit : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/structured_credit.json"))
  let mut pass := 0
  let mut fail := 0
  -- `lawTables`: the table `recordLaws` assembles, entry by entry, in order.
  for c in ← arr json "lawTables" do
    let id ← str c "id"
    let got ← recordTable (Json.mkObj [("sources", c)])
    let want ← (← arr c "expect").mapM lawEntry
    if got == want then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_credit {id}: got {repr got}, expected {repr want}"
      fail := fail + 1
  for c in ← arr json "records" do
    let id ← str c "id"
    let eq ← str c "equation"
    let laws ← recordTable c
    let d ← recordDerivation (← field c "derivation")
    let got := recordVerdictText (checkRecord laws eq d)
    let want ← recordExpectText (← field c "expect")
    let cls := WireWord.toWire (d.creditedClass (structuredChecker laws eq))
    let wantCls ← str c "class"
    if got == want && cls == wantCls then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_credit {id}: got {got} {cls}, expected {want} {wantCls}"
      fail := fail + 1
  return (pass, fail)

/-! ## structured_wire.json: a STRUCTURED payload's wire form

Each case holds a JSON `text`, read by the Calculator's own reader
(`Principia.Canonical.readString`), never by `Lean.Json`. A case with `canonical`
reads as a payload (`structuredOfValue`); its steps and start are the runner-shaped
`derivation`'s, field by field; the payload is written back (`structuredText`) as
exactly `canonical`, which reads back as the same payload; and, with `credit`, the
payload is checked and credited on the case's laws as a record's derivation. A case with
`refused` does not read as a payload, and the refusal is exactly that text. -/

def runStructuredWire : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/structured_wire.json"))
  let mut pass := 0
  let mut fail := 0
  for c in ← arr json "cases" do
    let id ← str c "id"
    let readText (t : String) : IO Principia.Canonical.Value :=
      match Principia.Canonical.readString t with
      | .ok v => pure v
      | .error e => corpusError s!"{id}: the text does not read as JSON: {repr e}"
    let v ← readText (← str c "text")
    let got := Principia.Record.structuredOfValue v
    let mut problems : List String := []
    match c.getObjValAs? String "refused" with
    | .ok want =>
      match got with
      | .error w => if w != want then problems := problems ++ [s!"refused {repr w}, expected {repr want}"]
      | .ok _ => problems := problems ++ [s!"read, expected refused {repr want}"]
    | .error _ =>
      let canonical ← str c "canonical"
      match got with
      | .error w => problems := problems ++ [s!"refused {repr w}"]
      | .ok (steps, start) =>
        let d := Principia.Record.Derivation.structured steps start
        let want ← recordDerivation (← field c "derivation")
        if d != want then problems := problems ++ [s!"read {repr d}, expected {repr want}"]
        match Principia.Record.structuredText steps start with
        | some t => if t != canonical then problems := problems ++ [s!"wrote {t}, expected {canonical}"]
        | none => problems := problems ++ ["the writer refused it"]
        match Principia.Record.structuredOfValue (← readText canonical) with
        | .ok back => if back != (steps, start) then problems := problems ++ ["the canonical text reads back otherwise"]
        | .error w => problems := problems ++ [s!"the canonical text does not read back: {w}"]
        match c.getObjVal? "credit" with
        | .ok k =>
          let laws ← (← arr k "laws").mapM lawEntry
          let eq ← str k "equation"
          let gotV := recordVerdictText (checkRecord laws eq d)
          let cls := WireWord.toWire (d.creditedClass (structuredChecker laws eq))
          let wantV ← recordExpectText (← field k "expect")
          let wantCls ← str k "class"
          if gotV != wantV || cls != wantCls then
            problems := problems ++ [s!"credited {gotV} {cls}, expected {wantV} {wantCls}"]
        | .error _ => pure ()
    if problems.isEmpty then
      pass := pass + 1
    else
      IO.eprintln s!"FAIL structured_wire {id}: {"; ".intercalate problems}"
      fail := fail + 1
  return (pass, fail)

end Tests.StructuredCheck
