import Principia.StartingSet
import Principia.Units
import Principia.ExactText
import Principia.Form.Evaluation

/-!
# The fundamental tests T2, T3, T5 and their run

v1's `tpc_tests` 0.2.1 (guide 3.6; TPS 2.2.3), the Starting
Set's fundamental tests, mechanical where they read fields only:

* T1 is `Principia.StartingSet.wellFormed`.
* T2, the syntactic part: an ASSUMPTION's PROPOSITION is not a top-level
  conjunction, list or joined pair of claims (`t2Findings`, `t2Atomicity`).
* T3 over the executable fragment: no TARGET both removed and fixed, none fixed at two
  values, the values compared in coherent SI through their twelve-digit form
  (`t3Consistency`); beside it, over the laws with an EQUATION, the ground fragment
  (`Principia.Form.t3Laws`).
* T4's law half and T6's totality, where a LAW carries EQUATION and a BOUNDARY CONDITION
  (`Principia.Form.t4Homogeneity`, `Principia.Form.t6Totality`); without a form they stay
  INSPECTION and are listed (`fundamentalTests`).
* T5 (b) a CONSTRAINT's TARGET is named by some LAW; (c) every DOF is (`t5DofYield`).

The run as the Starting Set is entered: T1, then T2, T5, T4 and T6; a T1 failure stops
it. T3 runs at the final pass (`Principia.ResearchAssembly.finalChecks`).

What the Calculator cannot judge yet is owed (`Owing`), never passed: a zone the zone
checks owe, a form the declared-form grammar owes (a value beyond the Calculator's exact
bounds), or a value whose twelve-digit form the precisions tried do not decide. A
proposition is read after v1's `_text`, its line endings and NFC at Unicode 15.1.0
(`Principia.Zone.textChars`).
-/

namespace Principia.StartingSet.Tests

open Principia.Zone

/-- Why a test is not judged yet. -/
inductive Owing where
  /-- A zone the zone checks owe. -/
  | zone (o : Owed)
  /-- A value's twelve-digit form is not decided at the precisions tried. -/
  | digits
  /-- A form's value has no exact value within the Calculator's bounds: what was met. -/
  | exact (what : String)
  deriving DecidableEq, Repr

/-- The owing's text. -/
def Owing.message : Owing → String
  | .zone o => o.message
  | .digits => "a value's twelve-digit form is not decided at the precisions tried"
  | .exact what => "no exact value within the Calculator's bounds (decision D6): " ++ what

/-- The declared-form grammar's owed reason as the tests': an exact value. -/
def ofForm : Form.Owed → Owing
  | .exact what => .exact what

/-- A form check's answer, its owed reason mapped. -/
def formAnswer {α : Type} (r : Except Form.Owed α) : Except Owing α := r.mapError ofForm

/-- A zone owed for its text or its form fields, as an `Except`. -/
def zoneOwed (z : Value) : Except Owing Unit :=
  match owedOf z with
  | some o => throw (.zone o)
  | none => pure ()

/-! ## Shared readers -/

/-- v1's `_entries_of`: the object entries of a list-valued part of an object. -/
def entriesOf (zone : Value) (key : String) : List Entry :=
  match zone with
  | .obj z => match get? z key with
    | some (.arr xs) => xs.filterMap fun | .obj e => some e | _ => none
    | _ => []
  | _ => []

/-- v1's `_set`: a list of strings, or empty. -/
def setOf (e : Entry) (f : String) : List String :=
  match get? e f with
  | some v => if typeOk "REFS" v then strItems v else []
  | none => []

/-- v1's `_dof_dims`: each DOF NAME, first occurrence, with its DIMENSION normalized. -/
def dofDims (tpk : Value) : List (String × Option String) :=
  (entriesOf tpk "DOF").foldl (fun acc e =>
    match getStr? e "NAME" with
    | some n => if (acc.lookup n).isSome then acc
      else acc ++ [(n, (getStr? e "DIMENSION").bind Dimension.normalize)]
    | none => acc) []

/-- v1's `_law_refs`: every name some LAW's REFS lists. -/
def lawRefs (tpk : Value) : List String := (entriesOf tpk "LAW").flatMap (setOf · "REFS")

/-- Strings sorted by code point, repeats kept (Python's `sorted`). -/
def insertKeep (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else y :: insertKeep x ys

/-- Sort strings by code point, repeats kept. -/
def sortKeep (l : List String) : List String := l.foldl (fun acc p => insertKeep p acc) []

/-- v1's `_removed`: each DOF a REMOVE constraint targets, with those constraints'
names, sorted. -/
def removed (tpk : Value) : List (String × List String) :=
  let pairs := (entriesOf tpk "CONSTRAINT").filterMap fun e =>
    match getStr? e "TARGET", getStr? e "NAME", getStr? e "ACTION" with
    | some t, some n, some "REMOVE" => some (t, n)
    | _, _, _ => none
  (pairs.map (·.1)).eraseDups.map fun t => (t, sortKeep ((pairs.filter (·.1 == t)).map (·.2)))

/-! ## T2, the syntactic part -/

/-- The closed list of top-level joiners of claims. -/
def t2Words : List String := ["and", "but", "whereas"]

/-- An opening bracket's closer. -/
def closerOf? : Char → Option Char
  | '(' => some ')'
  | '[' => some ']'
  | '{' => some '}'
  | _ => none

/-- A closing bracket. -/
def isCloser (c : Char) : Bool := c == ')' || c == ']' || c == '}'

/-- v1's `_top`: where each character lies outside every closed bracket pair and every
closed quotation. A pair counts only once its closer is found; a quotation opens only
outside brackets, `"` closing at the next `"` and U+201C at the next U+201D. -/
def topOf (chars : Array Char) : Array Bool := Id.run do
  let n := chars.size
  let mut inside := Array.replicate n false
  let mut stack : List (Char × Nat) := []
  let mut i := 0
  for _ in [0:n + 1] do
    if i ≥ n then break
    let ch := chars[i]!
    if stack.isEmpty && (ch == '"' || ch == '“') then
      let closer := if ch == '"' then '"' else '”'
      let mut j := i + 1
      for _ in [0:n] do
        if j < n && chars[j]! != closer then j := j + 1 else break
      if j < n then
        for k in [i:j + 1] do
          inside := inside.set! k true
        i := j + 1
        continue
    else if let some c := closerOf? ch then
      stack := (c, i) :: stack
    else if isCloser ch then
      match stack with
      | (c, start) :: rest =>
        if c == ch then
          stack := rest
          for k in [start:i + 1] do
            inside := inside.set! k true
      | [] => pure ()
    i := i + 1
  return inside.map (!·)

/-- v1's `_strip_ws`: White_Space removed at both ends. -/
def stripWs (cs : List Char) : List Char :=
  ((cs.dropWhile whiteSpace).reverse.dropWhile whiteSpace).reverse

/-- The index where the brackets opened at the start first close again, if they do. -/
def firstClose (cs : List Char) : Option Nat := Id.run do
  let mut stack : List Char := []
  let mut i := 0
  for ch in cs do
    if let some c := closerOf? ch then
      stack := c :: stack
    else if isCloser ch then
      match stack with
      | c :: rest =>
        if c == ch then
          stack := rest
          if stack.isEmpty then return some i
      | [] => pure ()
    i := i + 1
  return none

/-- v1's `_strip_enclosing`: bracket pairs enclosing the whole text removed, repeatedly,
so "(A and B)" is still a top-level conjunction. -/
def stripEnclosing (cs : List Char) : List Char := Id.run do
  let mut cs := stripWs cs
  for _ in [0:cs.length] do
    match cs with
    | c :: _ =>
      if cs.length ≥ 2 && (closerOf? c).isSome && firstClose cs == some (cs.length - 1) then
        cs := stripWs ((cs.drop 1).dropLast)
      else break
    | [] => break
  return cs

/-- v1's `_is_word`: an ASCII letter or digit, or `_`. -/
def isWord (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_'

/-- The maximal runs of word characters, lower-cased, each with whether it starts at
top level. -/
def wordsOf (chars : Array Char) (top : Array Bool) : List (String × Bool) := Id.run do
  let n := chars.size
  let mut out : List (String × Bool) := []
  let mut i := 0
  for _ in [0:n + 1] do
    if i ≥ n then break
    if isWord chars[i]! then
      let mut j := i
      for _ in [0:n] do
        if j < n && isWord chars[j]! then j := j + 1 else break
      out := out ++ [(String.ofList ((chars.extract i j).toList.map Char.toLower), top[i]!)]
      i := j
    else
      i := i + 1
  return out

/-- The findings at one character of top level. -/
def charFinding (chars : Array Char) (i : Nat) : Option String :=
  let n := chars.size
  let ch := chars[i]!
  let skip (j : Nat) (p : Char → Bool) : Nat := Id.run do
    let mut j := j
    for _ in [0:n] do
      if j < n && p chars[j]! then j := j + 1 else break
    return j
  if ch == '&' then some "joins claims with \"&\""
  else if ch == '∧' then some "joins claims with U+2227"
  else if ch == ';' then some "has a semicolon"
  else if ch == '.' || ch == '!' || ch == '?' then
    let j := skip (i + 1) whiteSpace
    if j > i + 1 && j < n && 'A' ≤ chars[j]! && chars[j]! ≤ 'Z' then some "has more than one sentence" else none
  else if ch == '\n' then
    let j := skip (i + 1) (fun c => c == ' ' || c == '\t')
    if j < n && "-*+•".toList.contains chars[j]! then some "is a list"
    else if j < n && '0' ≤ chars[j]! && chars[j]! ≤ '9' then
      let k := skip j (fun c => '0' ≤ c && c ≤ '9')
      if k < n && (chars[k]! == '.' || chars[k]! == ')') then some "is a list" else none
    else none
  else none

/-- v1's `t2_findings`: the syntactic findings for one PROPOSITION, sorted, after line
endings and NFC (v1's `_text`). -/
def t2Findings (prop : String) : List String := Id.run do
  let chars := (stripEnclosing (textChars prop)).toArray
  let top := topOf chars
  let words := wordsOf chars top
  let fromWords := (List.range words.length).flatMap fun k =>
    let (w, t) := words[k]!
    let seg := (words.drop k).take 3
    (if t && t2Words.contains w then ["joins claims with \"" ++ w ++ "\""] else []) ++
    (if seg.length == 3 && seg.all (·.2) && seg.map (·.1) == ["as", "well", "as"] then
      ["joins claims with \"as well as\""] else [])
  let fromChars := (List.range chars.size).filterMap fun i => if top[i]! then charFinding chars i else none
  pure ((fromWords ++ fromChars).foldl (fun acc p => insertStr p acc) [])

/-- v1's `t2_atomicity`: T2 over every ASSUMPTION's PROPOSITION; one with a disallowed
code point is T1's to report. The problems, `done`. -/
def t2Atomicity (tpk : Value) : List String :=
  let probs := (entriesOf tpk "ASSUMPTION").map fun e =>
    match getStr? e "PROPOSITION" with
    | none => []
    | some p =>
      if (firstBad p).isSome then []
      else (t2Findings p).map fun f => "ASSUMPTION:" ++ nameOf e ++ ": PROPOSITION " ++ f ++ " (T2)"
  done probs.flatten

/-! ## T3, the executable fragment -/

/-- v1's `_fix_value`: a FIX's VALUE in its UNIT, normalized to coherent SI. -/
def fixValue (e : Entry) : Except String Units.Measurement :=
  match getStr? e "VALUE", getStr? e "UNIT" with
  | some v, some u => Units.normalizeMeasurement v "0" u
  | _, _ => .error "not comparable"

/-- The verdict on two constraints of one TARGET. -/
def pairProblem (t : String) (c1 c2 : String × String × Entry) : Except Owing (Option String) := do
  let (n1, a1, e1) := c1
  let (n2, a2, e2) := c2
  let pair := "CONSTRAINT:" ++ n1 ++ " and CONSTRAINT:" ++ n2
  if a1 != a2 then return some (pair ++ ": " ++ t ++ " is both removed and fixed (T3)")
  if a1 != "FIX" then return none
  match fixValue e1, fixValue e2 with
  | .ok r1, .ok r2 =>
    if r1.kind != r2.kind then
      return some (pair ++ ": the two FIX values of " ++ t ++ " cannot be compared: units of different kind: " ++
        r1.kind ++ " and " ++ r2.kind ++ " (T3)")
    if r1.x == r2.x then return none
    match ExactText.twelveDigits? r1.x, ExactText.twelveDigits? r2.x with
    | some s1, some s2 =>
      if s1 == s2 then return none
      return some (pair ++ ": " ++ t ++ " fixed at " ++ (getStr? e1 "VALUE").getD "" ++ " " ++
        (getStr? e1 "UNIT").getD "" ++ " and at " ++ (getStr? e2 "VALUE").getD "" ++ " " ++
        (getStr? e2 "UNIT").getD "" ++ " (T3)")
    | _, _ => throw .digits
  | _, _ => return some (pair ++ ": the two FIX values of " ++ t ++ " cannot be compared (T3)")

/-- Constraints `(name, action, entry)` sorted by name. -/
def insertCons (x : String × String × Entry) : List (String × String × Entry) → List (String × String × Entry)
  | [] => [x]
  | y :: ys => if x.1 < y.1 then x :: y :: ys else y :: insertCons x ys

/-- Every pair `(cs[i], cs[j])`, `i < j`. -/
def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairsOf xs

/-- v1's `t3_consistency`: S_MAX a declared depth of at least 1, then every pair of
constraints of one TARGET, and beside them the laws' ground fragment
(`Principia.Form.t3Laws`). -/
def t3Consistency (tpk tms : Value) : Except Owing (List String) := do
  let sm : Option Value := match tms with
    | .obj z => match get? z "PARAMETERS" with
      | some (.obj pm) => get? pm "S_MAX"
      | _ => none
    | _ => none
  match sm with
  | some (.int n) => if n < 1 then return done ["T3: S_MAX is not a declared depth of at least 1"]
  | _ => return done ["T3: S_MAX is not a declared depth of at least 1"]
  zoneOwed tpk
  let cons := (entriesOf tpk "CONSTRAINT").filterMap fun e =>
    match getStr? e "TARGET", getStr? e "NAME", getStr? e "ACTION" with
    | some t, some n, some a => if a == "REMOVE" || a == "FIX" then some (t, (n, a, e)) else none
    | _, _, _ => none
  let targets := (cons.map (·.1)).eraseDups.foldl (fun acc p => insertStr p acc) []
  let probs ← targets.mapM fun t => do
    let cs := ((cons.filter (·.1 == t)).map (·.2)).foldl (fun acc c => insertCons c acc) []
    (pairsOf cs).filterMapM fun (c1, c2) => pairProblem t c1 c2
  let laws ← formAnswer (Form.t3Laws tpk)
  pure (done (probs.flatten ++ laws))

/-! ## T5 -/

/-- v1's `t5_dof_yield`: (b) every CONSTRAINT's TARGET that is a DOF is named by some
LAW; (c) every DOF is. -/
def t5DofYield (tpk : Value) : List String := Id.run do
  let named := lawRefs tpk
  let dofs := (dofDims tpk).map (·.1)
  let b := (entriesOf tpk "CONSTRAINT").filterMap fun e =>
    match getStr? e "TARGET" with
    | some t => if dofs.contains t && !named.contains t then
        some ("CONSTRAINT:" ++ nameOf e ++ ": TARGET " ++ t ++ " is named by no LAW, so no law leaves it free (T5 b)")
      else none
    | none => none
  let c := dofs.filterMap fun d => if named.contains d then none else some ("DOF:" ++ d ++ ": named by no LAW (T5 c)")
  pure (done (b ++ c))

/-! ## The run -/

/-- A test's state in the run: passed or not, not reached, or (T4, T6) no form. -/
inductive TestState where
  | ran (pass : Bool)
  | notRun
  | noForm
  deriving DecidableEq, Repr

/-- One row of the run: the test, its state and its problems. -/
structure Row where
  test : String
  state : TestState
  problems : List String
  deriving Repr

/-- The run's result: passed, its rows, and what stays INSPECTION. -/
structure Run where
  pass : Bool
  rows : List Row
  inspections : List String
  deriving Repr

/-- v1's `kernel_tests`: T1, then T2, T5, T4 and T6; a T1 failure stops the run. T4 and
T6 are NO FORM when no LAW carries EQUATION, no BOUNDARY CONDITION; every LAW and
BOUNDARY without its form is listed as INSPECTION. -/
def fundamentalTests (tpk : Value) : Except Owing Run := do
  let t1 ← match StartingSet.wellFormed .calculator tpk with
    | .owed o => throw (.zone o)
    | .checked ps => pure ps
  if !t1.isEmpty then
    return ⟨false, ⟨"T1", .ran false, t1⟩ :: ["T2", "T5", "T4", "T6"].map (fun t => ⟨t, .notRun, []⟩), []⟩
  let t2 := t2Atomicity tpk
  let t5 := t5DofYield tpk
  let t4 ← formAnswer (Form.t4Homogeneity tpk)
  let t6 ← formAnswer (Form.t6Totality tpk)
  let (laws, bnds) := Form.formCoverage tpk
  let allLaws := (entriesOf tpk "LAW").length
  let allBnds := (entriesOf tpk "BOUNDARY").length
  let insp := laws.map (fun n => "LAW:" ++ n ++ ": no EQUATION; T4 and T3 over this law by inspection") ++
    bnds.map (fun n => "BOUNDARY:" ++ n ++ ": no CONDITION; T6 totality by inspection")
  pure ⟨t2.isEmpty && t5.isEmpty && t4.isEmpty && t6.isEmpty,
    [⟨"T1", .ran true, []⟩, ⟨"T2", .ran t2.isEmpty, t2⟩, ⟨"T5", .ran t5.isEmpty, t5⟩,
      ⟨"T4", if laws.length == allLaws then .noForm else .ran t4.isEmpty, t4⟩,
      ⟨"T6", if bnds.length == allBnds then .noForm else .ran t6.isEmpty, t6⟩],
    sortKeep insp⟩

end Principia.StartingSet.Tests
