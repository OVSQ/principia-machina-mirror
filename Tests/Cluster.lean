import Principia
import Lean.Data.Json

/-!
The runner of `vectors/cluster_corpus.json` (v1's `tpc_cluster` 0.3.0, 67 cases):
each case is read into `Principia.Cluster`'s typed inputs and run, and its typed
outcome is compared with the case's `expected` text field by field (below,
"Comparing with the expected text"), not as one rendered string. A case is v1's
`run_case` shape: `fn` (`cluster` when absent, or `resolving`), `params`, and
`rows` and `paired`, or `spacing`, `ses` and `paired`.

A JSON number is read exactly, as the decimal it spells. v1 checked its inputs'
types at run time; a value of the wrong kind where v1 refuses it with a word (an
id that is not a string, a paired entry that is not five fields, a spacing, SE or
paired SE that is not a number) gets that word here, after every check v1 makes
before it. A shape v1 itself could not run is a defect of the corpus and fails
the run.
-/

open Lean
open Principia
open Principia.Cluster

namespace Tests.Cluster

/-- A JSON number, exactly. -/
def rat? : Json → Option Rat
  | .num n => some (mkRat n.mantissa (10 ^ n.exponent))
  | _ => none

/-- A defect of the corpus. -/
def defect (what : String) : Except String α := throw what

def num (j : Json) (k : String) : Except String Rat := do
  match rat? (← j.getObjVal? k) with
  | some q => pure q
  | none => defect s!"{k} is not a number"

def thresholds (p : Json) : Except String Thresholds := do
  pure { inMax := ← num p "in_max", cuspMax := ← num p "cusp_max", z := ← num p "z" }

/-- A row `[model, config, score, se]`; `none` when an id is not a string (v1:
`ids`). -/
def row? (j : Json) : Except String (Option Row) := do
  let arr ← j.getArr?
  unless arr.size == 4 do defect s!"a row of {arr.size} fields"
  let some score := rat? arr[2]! | defect "a score that is not a number"
  let some se := rat? arr[3]! | defect "an SE that is not a number"
  match arr[0]!, arr[1]! with
  | .str m, .str c => pure (some ⟨m, c, score, se⟩)
  | _, _ => pure none

/-- A paired entry `[model, config, model, config, se]`; `none` when it is not
five fields of that kind (v1: `paired`). -/
def pairedSe? (j : Json) : Option PairedSe :=
  match j with
  | .arr #[.str ma, .str ca, .str mb, .str cb, s] =>
    (rat? s).map fun q => ⟨(ma, ca), (mb, cb), q⟩
  | _ => none

/-- An optional list: absent or `null` is `none`. -/
def optList (c : Json) (k : String) : Option (Option (Array Json)) :=
  match c.getObjVal? k with
  | .error _ | .ok .null => some none
  | .ok (.arr a) => some (some a)
  | .ok _ => none

/-! ## Running a case: the typed outcome -/

/-- What a case gives: the cluster rule's result or the resolving step's, each
`Except ClusterError` as the function returns it. -/
inductive Outcome where
  /-- `fn` `cluster`. -/
  | cluster (r : Except ClusterError Result)
  /-- `fn` `resolving`. -/
  | resolving (r : Except ClusterError (Option ResolvingStep))
  /-- A `fn` v1 does not know (v1: `ERROR:fn`). -/
  | unknownFn

def runClusterCase (c : Json) : Except String (Except ClusterError Result) := do
  let p ← c.getObjVal? "params"
  let t ← thresholds p
  let floor ← num p "spacing_floor"
  let rowsJ ← (← c.getObjVal? "rows").getArr?
  let rows? ← rowsJ.toList.mapM row?
  let some rows := rows?.mapM id | return .error .ids
  let paired? : Option (Option (List PairedSe)) :=
    match optList c "paired" with
    | some none => some none
    | some (some a) => (a.toList.mapM pairedSe?).map some
    | none => none
  match paired? with
  | some paired => pure (cluster rows t floor paired)
  -- A malformed paired entry: v1 checks the rows and thresholds first.
  | none => pure (match checkInput rows t floor with
    | .error e => .error e
    | .ok _ => .error .paired)

def runResolvingCase (c : Json) : Except String (Except ClusterError (Option ResolvingStep)) := do
  let p ← c.getObjVal? "params"
  let t ← thresholds p
  let some spacing := rat? (← c.getObjVal? "spacing") | return .error .spacing
  let ses? : Option (List Rat) :=
    match c.getObjVal? "ses" with
    | .ok (.arr a) => a.toList.mapM rat?
    | _ => none
  -- A malformed list of SEs: v1 checks the spacing first.
  let some ses := ses? | return .error (if spacing < 0 then .spacing else .ses)
  let paired? : Option (Option (List Rat)) :=
    match optList c "paired" with
    | some none => some none
    | some (some a) => (a.toList.mapM rat?).map some
    | none => none
  match paired? with
  | some paired => pure (resolvingStep spacing ses t paired)
  -- A malformed paired list: v1 checks the spacing, the SEs and the thresholds first.
  | none => pure (match resolvingStep spacing ses t none with
    | .error e => .error e
    | .ok _ => .error .paired)

/-- One case: what v1's `run_case` would compare, typed. -/
def runCase (c : Json) : Except String Outcome :=
  match c.getObjValAs? String "fn" with
  | .error _ | .ok "cluster" => Outcome.cluster <$> runClusterCase c
  | .ok "resolving" => Outcome.resolving <$> runResolvingCase c
  | .ok _ => pure .unknownFn

/-! ## Comparing with the expected text, field by field

v1's text joins a row's fields with `|` and the rows with a newline, unescaped, so
two different results can print alike (a model `a|b` with configuration `c`, and a
model `a` with configuration `b|c`). The expected text is therefore read back
field by field against the typed outcome: every line must split into exactly the
fields its kind has, each id is compared with the typed id, each word is read into
its enumeration and compared as a value, a rank as a number, and each number as v1's
six-decimal text of the typed exact value (`fmt`, the format under test). An id
holding `|` or a newline cannot pass: its line splits into too many fields, or the
text into too many lines. -/

/-- v1's error word, read into the typed error. -/
def errorOfWord? (w : String) : Option ClusterError :=
  [ClusterError.ids, .scoreOrSe, .parameters, .paired, .spacing, .ses].find? (·.message == w)

/-- The typed error against an expected `ERROR:<word>` text. -/
def errorMatches (expected : String) (e : ClusterError) : Bool :=
  match expected.splitOn "ERROR:" with
  | ["", w] => errorOfWord? w == some e
  | _ => false

/-- A rank field: `-` for a row with no rank, else the rank's digits. -/
def rankMatches (field : String) (rank : Option Nat) : Bool :=
  if field == "-" then rank.isNone else field.toNat?.isSome && field.toNat? == rank

/-- One row line, `rank|model|config|score|se|step|spacings|CLASS`, against the typed
line: exactly eight fields. -/
def lineMatches (txt : String) (l : Line) : Bool :=
  match txt.splitOn "|" with
  | [rank, model, config, score, se, step, spacings, cls] =>
    rankMatches rank l.rank && model == l.row.model && config == l.row.config &&
      score == fmt (some (.ofRat l.row.score)) && se == fmt (some (.ofRat l.row.se)) &&
      step == fmt (l.step.map .ofRat) && spacings == fmt l.spacings &&
      (WireWord.ofWire? cls : Option ClusterClass) == some l.cls
  | _ => false

/-- The cluster rule's outcome against the expected text: the mismatches, none when
it agrees. -/
def clusterMismatches (expected : String) : Except ClusterError Result → List String
  | .error e => if errorMatches expected e then [] else [s!"refused with {e.message}"]
  | .ok r =>
    match expected.splitOn "\n" with
    | head :: rest =>
      let headOk := match head.splitOn "|" with
        | ["spacing", u, src] =>
          u == r.spacing.fixed6 && (WireWord.ofWire? src : Option SpacingSource) == some r.source
        | _ => false
      (if headOk then [] else [s!"the spacing line {repr head}"]) ++
      (if rest.length == r.lines.length then []
       else [s!"{rest.length} row lines expected, {r.lines.length} computed"]) ++
      ((rest.zip r.lines).filter (fun (t, l) => !lineMatches t l)).map
        fun (t, l) => s!"the line {repr t} against {repr l}"
    | [] => ["an empty expected text"]

/-- One number field: v1's six-decimal text of the exact value. -/
def numMatches (field : String) (x : Surd) : Bool := field == x.fixed6

/-- The resolving step's outcome against the expected text. -/
def resolvingMismatches (expected : String) : Except ClusterError (Option ResolvingStep) → List String
  | .error e => if errorMatches expected e then [] else [s!"refused with {e.message}"]
  | .ok none =>
    if expected.splitOn "\n" == ["resolving|NONE"] then [] else ["NONE computed"]
  | .ok (some d) =>
    match expected.splitOn "\n" with
    | first :: second :: ranks =>
      let firstOk := match first.splitOn "|" with
        | ["resolving", o, os, c, cs] =>
          numMatches o d.out && os == fmt d.outSpacings && numMatches c d.cusp &&
            cs == fmt d.cuspSpacings
        | _ => false
      let secondOk := match second.splitOn "|" with
        | ["greatest", o, c] => numMatches o d.outMost && numMatches c d.cuspMost
        | _ => false
      let rankOk (t : String) (x : Nat × Surd × Surd) : Bool :=
        match t.splitOn "|" with
        | ["rank", k, o, c] => k.toNat? == some x.1 && numMatches o x.2.1 && numMatches c x.2.2
        | _ => false
      (if firstOk then [] else [s!"the resolving line {repr first}"]) ++
      (if secondOk then [] else [s!"the greatest line {repr second}"]) ++
      (if ranks.length == d.ranks.length then []
       else [s!"{ranks.length} rank lines expected, {d.ranks.length} computed"]) ++
      ((ranks.zip d.ranks).filter (fun (t, x) => !rankOk t x)).map fun (t, _) => s!"the line {repr t}"
    | _ => ["a resolving text of fewer than two lines"]

/-- A case's outcome against its expected text. -/
def mismatches (expected : String) : Outcome → List String
  | .cluster r => clusterMismatches expected r
  | .resolving r => resolvingMismatches expected r
  | .unknownFn => if expected == "ERROR:fn" then [] else ["an unknown fn"]

/-! ## The mutation checks: the comparison refuses what it must -/

/-- A line `l` as v1 prints it (`render`'s row line). -/
def lineText (l : Line) : String :=
  match (render ⟨0, .notSet, [l]⟩).splitOn "\n" with
  | [_, t] => t
  | _ => ""

/-- Swap two `|` fields of a line. -/
def swapFields (t : String) (i j : Nat) : String :=
  let fs := t.splitOn "|"
  "|".intercalate ((fs.set i (fs.getD j "")).set j (fs.getD i ""))

/-- Each check is `true` when the comparison refuses the mutated text: a swapped
pair of fields, a swapped class word, and the ambiguous ids, which print alike. -/
def mutationChecks : List (String × Bool) :=
  let row : Row := ⟨"A1", "default", 10, 1/2⟩
  let l : Line := ⟨some 3, row, some 2, some ⟨0, 4, 1⟩, .inside⟩
  let t := lineText l
  let ambA : Line := { l with row := { row with model := "a|b", config := "c" } }
  let ambB : Line := { l with row := { row with model := "a", config := "b|c" } }
  [("the line as printed is accepted", lineMatches t l),
   ("model and config swapped", !lineMatches (swapFields t 1 2) l),
   ("score and se swapped", !lineMatches (swapFields t 3 4) l),
   ("step and spacings swapped", !lineMatches (swapFields t 5 6) l),
   ("the class word changed", !lineMatches (t.replace "|IN" "|CUSP") l),
   ("ids holding | print alike", lineText ambA == lineText ambB),
   ("an id holding | is refused", !lineMatches (lineText ambA) ambA && !lineMatches (lineText ambA) ambB)]

/-! ## The run -/

/-- Run the corpus: the counts of cases passed and failed, each failure reported
on stderr with what disagreed. The mutation checks run first; one that fails is a
failure of the runner and counts as a failed case. -/
def runCluster : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for (what, ok) in mutationChecks do
    unless ok do
      IO.eprintln s!"FAIL cluster runner mutation check: {what}"
      fail := fail + 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/cluster_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let got ← IO.ofExcept (runCase c)
    match mismatches expected got with
    | [] => pass := pass + 1
    | ms =>
      IO.eprintln s!"FAIL cluster {name}: expected {repr expected}\n  {"\n  ".intercalate ms}"
      fail := fail + 1
  return (pass, fail)

/-! ## `vectors/cluster_rows.json`: the ROW's measure

Each case's `request` goes through `cluster cluster_rows`, read with the Calculator's own
reader (it keeps a number as it is spelled). An `expected` answer is compared as canonical
JSON; a `refused` case must be refused with that code and, for `BAD_ARGUMENT`, that detail.
A case `vectors/cluster_rows.owed.json` names must be refused `OWED`, and no other case may
be. -/

/-- A member of a value read by the Calculator's reader. -/
def rowsMember (v : Canonical.Value) (k : String) : Option Canonical.Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

/-- A file read by the Calculator's reader. -/
def readValue (path : System.FilePath) : IO Canonical.Value := do
  match Canonical.readString (← IO.FS.readFile path) with
  | .ok v => pure v
  | .error _ => throw (IO.userError s!"{path}: refused by the reader")

/-- Run `cluster_rows.json`: the counts of cases passed and failed. -/
def runRows : IO (Nat × Nat) := do
  let owed ← match rowsMember (← readValue "vectors/cluster_rows.owed.json") "owed" with
    | some (.arr os) => pure (os.filterMap fun o => match rowsMember o "name" with
        | some (.str n) => some n | _ => none)
    | _ => throw (IO.userError "cluster_rows.owed.json: no owed list")
  let cases ← match rowsMember (← readValue "vectors/cluster_rows.json") "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError "cluster_rows.json: no cases")
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let some (.str name) := rowsMember c "name" | throw (IO.userError "a case without a name")
    let some request := rowsMember c "request" | throw (IO.userError s!"{name}: no request")
    let got := Calculator.respondTo "cluster" "cluster_rows" request
    let ok : Bool := match got, rowsMember c "expected", rowsMember c "refused" with
      | .ok v, some e, none => !owed.contains name && v.canonicalJson.isSome && v.canonicalJson == e.canonicalJson
      | .error r, none, some (.str "OWED") => owed.contains name && r.code == .owed
      | .error r, none, some (.str w) =>
        !owed.contains name && r.code.word == w && (match rowsMember c "detail" with | some (.str d) => d == r.detail | _ => false)
      | _, _, _ => false
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL cluster_rows {name}: got {repr (match got with | .ok v => v.canonicalJson | .error r => some r.detail)}"
      fail := fail + 1
  if cases.isEmpty then
    IO.eprintln "FAIL cluster_rows: the corpus checked nothing"
    fail := fail + 1
  return (pass, fail)

/-! ## `vectors/cluster_screen.json`: the EXCLUSION LIST, the MODEL MAP and the page check

Each case names its `function` (`cluster_screen` or `cluster_text_check`); its `request` goes
through `cluster <function>`, read with the Calculator's own reader. An `expected` answer is
compared as canonical JSON; a `refused` case must be refused with that code and that detail.
No case is owed. -/

/-- Run `cluster_screen.json`: the counts of cases passed and failed. -/
def runScreen : IO (Nat × Nat) := do
  let cases ← match rowsMember (← readValue "vectors/cluster_screen.json") "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError "cluster_screen.json: no cases")
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let some (.str name) := rowsMember c "name" | throw (IO.userError "a case without a name")
    let some (.str fn) := rowsMember c "function" | throw (IO.userError s!"{name}: no function")
    let some request := rowsMember c "request" | throw (IO.userError s!"{name}: no request")
    let known := fn == "cluster_screen" || fn == "cluster_text_check"
    let got := Calculator.respondTo "cluster" fn request
    let ok : Bool := known && match got, rowsMember c "expected", rowsMember c "refused" with
      | .ok v, some e, none => v.canonicalJson.isSome && v.canonicalJson == e.canonicalJson
      | .error r, none, some (.str w) =>
        r.code.word == w && (match rowsMember c "detail" with | some (.str d) => d == r.detail | _ => false)
      | _, _, _ => false
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL cluster_screen {name}: got {repr (match got with | .ok v => v.canonicalJson | .error r => some r.detail)}"
      fail := fail + 1
  if cases.isEmpty then
    IO.eprintln "FAIL cluster_screen: the corpus checked nothing"
    fail := fail + 1
  return (pass, fail)

/-! ## `vectors/cluster_schedule.json`: the cluster month's due rule and the page's state

Each case's `request` goes through `cluster cluster_schedule`, read with the Calculator's own
reader. An `expected` answer is compared as canonical JSON; a `refused` case must be refused
with that code and that detail. A case `vectors/cluster_schedule.owed.json` names must be
refused `OWED`, and no other case may be. -/

/-- Run `cluster_schedule.json`: the counts of cases passed and failed. -/
def runSchedule : IO (Nat × Nat) := do
  let owed ← match rowsMember (← readValue "vectors/cluster_schedule.owed.json") "owed" with
    | some (.arr os) => pure (os.filterMap fun o => match rowsMember o "name" with
        | some (.str n) => some n | _ => none)
    | _ => throw (IO.userError "cluster_schedule.owed.json: no owed list")
  let cases ← match rowsMember (← readValue "vectors/cluster_schedule.json") "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError "cluster_schedule.json: no cases")
  let mut pass := 0
  let mut fail := 0
  for c in cases do
    let some (.str name) := rowsMember c "name" | throw (IO.userError "a case without a name")
    let some request := rowsMember c "request" | throw (IO.userError s!"{name}: no request")
    let got := Calculator.respondTo "cluster" "cluster_schedule" request
    let ok : Bool := match got, rowsMember c "expected", rowsMember c "refused" with
      | .ok v, some e, none => !owed.contains name && v.canonicalJson.isSome && v.canonicalJson == e.canonicalJson
      | .error r, none, some (.str "OWED") => owed.contains name && r.code == .owed
      | .error r, none, some (.str w) =>
        !owed.contains name && r.code.word == w && (match rowsMember c "detail" with | some (.str d) => d == r.detail | _ => false)
      | _, _, _ => false
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL cluster_schedule {name}: got {repr (match got with | .ok v => v.canonicalJson | .error r => some r.detail)}"
      fail := fail + 1
  if cases.isEmpty then
    IO.eprintln "FAIL cluster_schedule: the corpus checked nothing"
    fail := fail + 1
  return (pass, fail)

end Tests.Cluster
