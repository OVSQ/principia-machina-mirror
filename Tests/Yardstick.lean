import Principia
import Lean.Data.Json
import Tests.Strike
import Tests.Zone

/-!
The yardstick family's runner: v1's `yardstick_corpus.json` (46 cases: `yardstick_key` 25,
`yardstick_harness` 17, `yardstick_checks` 4), run against `Principia.Yardstick`.

A case is `{"id", "fn", "input", "expect"}`, its `expect` v1's `canon` text of the result.
The text is read back into typed values and compared with the Calculator's typed result:
a key's values as exact numbers (v1's decimal text read exactly, against the exact key), the
harness's flags and count, the checks' flags and record lists, a refusal's reason as a
string. v1's text writes a word unquoted, so a record list is compared only when its
identifiers hold no comma, bracket or empty word (`Tests.Strike.plainWords`); otherwise the
case fails. A Criteria Set is read as `Tests.Zone.toValue` reads a zone; a suite as
`Tests.Strike.suite` reads one; the field table is placed on the records as v1's `_placed`
places it.

An owed result is neither a pass nor a fail, and none is expected: every case of this
corpus is in the tables the Calculator carries, so an owed case is counted as failing. A
case that differs is reported on stderr and counted as failing; v2 divergences would be
listed in `vectors/README.md`, and this corpus has none.
-/

namespace Tests.Yardstick

open Lean
open Principia
open Principia.Strike.SR9
open Principia.Yardstick
open Tests.Strike (field str strs loadV1Cases canonBool plainWords)

/-! ## Reading the input -/

/-- v1's field table: each record's row, as the string-valued members of an object; a
table or a row that is not an object holds nothing (v1 finds no U_C there). -/
def fieldTable (j : Json) : List (String × List (String × String)) :=
  match j with
  | .obj kvs => kvs.foldl (fun acc rid row => acc ++ [(rid, match row with
      | .obj cells => cells.foldl (fun cs k v => match v with
          | .str s => cs ++ [(k, s)]
          | _ => cs) []
      | _ => [])]) []
  | _ => []

/-- The table of a case, absent meaning none. -/
def tableOf (j : Json) : List (String × List (String × String)) :=
  match j.getObjVal? "fields" with
  | .ok t => fieldTable t
  | .error _ => []

/-! ## v1's text of a result, read back -/

/-- v1's `canon` text: a word, or a bracketed list of texts separated by commas. -/
inductive Tree where
  | leaf (w : String)
  | node (ts : List Tree)
  deriving Inhabited

/-- One text from `cs`, and the rest; `none` when malformed. Words hold no comma or
bracket (checked by the caller for the words compared). -/
partial def readTree (cs : List Char) : Option (Tree × List Char) :=
  match cs with
  | '[' :: ']' :: rest => some (.node [], rest)
  | '[' :: rest =>
    let rec items (cs : List Char) (acc : List Tree) : Option (List Tree × List Char) := do
      let (t, r) ← readTree cs
      match r with
      | ',' :: r' => items r' (acc ++ [t])
      | ']' :: r' => some (acc ++ [t], r')
      | _ => none
    (items rest []).map fun (ts, r) => (.node ts, r)
  | _ =>
    let w := cs.takeWhile fun c => c != ',' && c != ']' && c != '['
    some (.leaf (String.ofList w), cs.drop w.length)

/-- The whole text, read. -/
def tree (s : String) : Option Tree :=
  match readTree s.toList with
  | some (t, []) => some t
  | _ => none

def leafBool : Tree → Option Bool
  | .leaf "true" => some true
  | .leaf "false" => some false
  | _ => none

def leafWords : Tree → Option (List String)
  | .node ts => ts.mapM fun | .leaf w => some w | _ => none
  | _ => none

/-- A number of v1's text, exactly: v1 wrote a double as Python's shortest decimal (`2.5`,
`-1`, `1.0005`), read here as the exact decimal it spells. -/
def leafNumber : Tree → Option Rat
  | .leaf w => Decimal.value w
  | _ => none

/-! ## Running -/

/-- The outcome compared with v1's text: `(ok, what was got)`. A refusal is compared by its
reason; an `OK` result by `ok`, given the tree's items after `OK`. -/
def judge {α : Type} (expect : String) (got : Option (Outcome α)) (render : α → String)
    (ok : α → List Tree → Bool) : Bool × String :=
  match got with
  | none => (false, "v1 raised")
  | some (.owed why) => (false, "owed: " ++ why.message)
  | some (.refused r) => ("[REFUSED," ++ r ++ "]" == expect, "[REFUSED," ++ r ++ "]")
  | some (.ok a) =>
    match tree expect with
    | some (.node (.leaf "OK" :: items)) => (ok a items, "[OK," ++ render a ++ "]")
    | _ => (false, "[OK," ++ render a ++ "]")

def showKey (k : List Rat) : String := "[" ++ ",".intercalate (k.map Exact.renderRat) ++ "]"

def keyMatches (k : List Rat) : List Tree → Bool
  | [.node vs] => match vs.mapM leafNumber with
    | some ws => ws == k
    | none => false
  | _ => false

def showHarness (h : Bool × Bool × Bool × Nat) : String :=
  canonBool h.1 ++ "," ++ canonBool h.2.1 ++ "," ++ canonBool h.2.2.1 ++ "," ++ toString h.2.2.2

def harnessMatches (h : Bool × Bool × Bool × Nat) : List Tree → Bool
  | [a, b, c, .leaf n] =>
    leafBool a == some h.1 && leafBool b == some h.2.1 && leafBool c == some h.2.2.1 &&
      n.toNat? == some h.2.2.2
  | _ => false

def words (ws : List String) : String := "[" ++ ",".intercalate ws ++ "]"

def showChecks (c : Checks) : String :=
  let (c1, c2, c4) := c
  words [canonBool c1.1, words c1.2] ++ "," ++ words [canonBool c2.1, words c2.2.1, words c2.2.2] ++
    "," ++ words [canonBool c4.1, words c4.2]

def checksMatches (c : Checks) : List Tree → Bool
  | [.node [p1, w1], .node [p2, v2, x2], .node [p4, w4]] =>
    let (c1, c2, c4) := c
    plainWords (c1.2 ++ c2.2.1 ++ c2.2.2 ++ c4.2) &&
      leafBool p1 == some c1.1 && leafWords w1 == some c1.2 &&
      leafBool p2 == some c2.1 && leafWords v2 == some c2.2.1 && leafWords x2 == some c2.2.2 &&
      leafBool p4 == some c4.1 && leafWords w4 == some c4.2
  | _ => false

/-- The units are never consulted by a Criteria Set (`Principia.Yardstick.compile`). -/
def noUnits : Zone.UnitHook := ⟨fun _ => .error "a Criteria Set has no UNIT"⟩

/-- One case: `(ok, what was got)`. -/
def runCase (fn : String) (input : Json) (expect : String) : IO (Bool × String) := do
  let tms := Tests.Zone.toValue (← field input "tms")
  let name ← str (← field input "name")
  match fn with
  | "yardstick_key" =>
    let s ← Tests.Strike.suite (Json.mkObj [("records", ← field input "records")])
    let got := yardstickKey noUnits tms name (← str (← field input "rid")) s.records s.assembly
      (tableOf input)
    return judge expect got showKey keyMatches
  | "yardstick_checks" =>
    let sj ← field input "suite"
    let s ← Tests.Strike.suite sj
    return judge expect (yardstickChecks noUnits tms name s (tableOf sj)) showChecks checksMatches
  | "yardstick_harness" =>
    let sj ← field input "suite"
    let s ← Tests.Strike.suite sj
    return judge expect (yardstickHarness noUnits tms name s (tableOf sj)) showHarness harnessMatches
  | other => throw (IO.userError s!"unknown function {other}")

/-- Run the corpus: `(pass, fail)`. -/
def runYardstick : IO (Nat × Nat) := do
  let path : System.FilePath := "vectors/yardstick_corpus.json"
  let mut pass := 0
  let mut fail := 0
  for c in ← loadV1Cases path do
    let id ← str (← field c "id")
    let expect ← str (← field c "expect")
    let (ok, got) ← runCase (← str (← field c "fn")) (← field c "input") expect
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL {path} {id}: expected {expect}, got {got}"
      fail := fail + 1
  return (pass, fail)

/-! ## The bound on an exact value (`Principia.Yardstick.Bounded`) -/

/-- The corpus through the checked functions: each answers, and answers as the plain one does
(no case of the corpus is near the bound). -/
def runBoundedCorpus : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in ← loadV1Cases "vectors/yardstick_corpus.json" do
    let id ← str (← field c "id")
    let fn ← str (← field c "fn")
    let input ← field c "input"
    let tms := Tests.Zone.toValue (← field input "tms")
    let name ← str (← field input "name")
    let ok ← match fn with
      | "yardstick_key" => do
        let s ← Tests.Strike.suite (Json.mkObj [("records", ← field input "records")])
        let rid ← str (← field input "rid")
        let t := tableOf input
        pure (match Bounded.yardstickKey noUnits tms name rid s.records s.assembly t with
          | .ok r => toString (repr r) == toString (repr (yardstickKey noUnits tms name rid s.records s.assembly t))
          | .error _ => false)
      | "yardstick_checks" => do
        let sj ← field input "suite"
        let s ← Tests.Strike.suite sj
        pure (match Bounded.yardstickChecks noUnits tms name s (tableOf sj) with
          | .ok r => toString (repr r) == toString (repr (yardstickChecks noUnits tms name s (tableOf sj)))
          | .error _ => false)
      | _ => do
        let sj ← field input "suite"
        let s ← Tests.Strike.suite sj
        pure (match Bounded.yardstickHarness noUnits tms name s (tableOf sj) with
          | .ok r => toString (repr r) == toString (repr (yardstickHarness noUnits tms name s (tableOf sj)))
          | .error _ => false)
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL yardstick_bound {id}: the checked function refused or answered otherwise"
      fail := fail + 1
  return (pass, fail)

/-- A Criteria Set of one constant `w` of value `v` and the yardsticks `ws` (`SR1`,
`WSUM:w*S`) and `uc` (`SR1`, `WSUM:w*FIELD:U_C`). -/
def boundTms (v : String) : Zone.Value :=
  .obj [("PARAMETERS", .obj [("STEP_CONVENTION", .str "one inference rule is one step"),
      ("K", .str "2"), ("N_X", .int 2), ("S_MAX", .int 10)]),
    ("CONSTANTS", .arr [.obj [("NAME", .str "w"), ("VALUE", .str v)]]),
    ("YARDSTICKS", .arr [
      .obj [("NAME", .str "ws"), ("KEY", .arr [.str "SR1", .str "WSUM:w*S"]), ("LIMITING", .arr [])],
      .obj [("NAME", .str "uc"), ("KEY", .arr [.str "SR1", .str "WSUM:w*FIELD:U_C"]),
        ("LIMITING", .arr [])]])]

/-- One record `R1` of `steps` steps. -/
def boundRecords (steps : Nat) : SuiteRecords :=
  [("R1", { regime := .derivation, assumptions := [], cites := [], steps, domain := "MAIN",
            sr1Fail := false })]

/-- `1` followed by `n` zeros, as a decimal text. -/
def tenPow (n : Nat) : String := "1" ++ String.ofList (List.replicate n '0')

/-- `10^n + 1`, a canonical decimal text (no trailing zero, no exponent): a U_C cell must be
its own canonical spelling, whose exponent has at most four digits. -/
def tenPowOne (n : Nat) : String := "1" ++ String.ofList (List.replicate (n - 1) '0') ++ "1"

/-- The bound's hand cases: at it answered, past it refused "exact value too large". -/
def runBoundCases : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let tooLarge (r : ValueBound.Bounded (Option (Outcome (List Rat)))) : Bool :=
    match r with
    | .error e => e == ValueBound.tooLarge
    | .ok _ => false
  -- Answered or refused by version 1's own checks, but not by the bound.
  let answered (r : ValueBound.Bounded (Option (Outcome (List Rat)))) : Bool :=
    match r with
    | .ok _ => true
    | .error _ => false
  -- A decimal's exponent has at most four digits, so a value past the bound is written with
  -- its digits: 10^19725 + 1 holds 65,527 bits, 10^19729 + 1 65,540 (the bound: 65,536). A weight
  -- past a double is refused by the Criteria Set's own check; the bound refuses it first.
  let cases : List (String × Bool) := [
    ("a U_C of 10^19725 + 1 answered",
      answered (Bounded.yardstickKey noUnits (boundTms "1") "uc" "R1" (boundRecords 1) []
        [("R1", [("U_C", tenPowOne 19725)])])),
    ("a U_C of 10^19729 + 1 refused",
      tooLarge (Bounded.yardstickKey noUnits (boundTms "1") "uc" "R1" (boundRecords 1) []
        [("R1", [("U_C", tenPowOne 19729)])])),
    ("a weight of 10^19729 refused by the bound before the Criteria Set's checks",
      tooLarge (Bounded.yardstickKey noUnits (boundTms (tenPow 19729)) "ws" "R1"
        (boundRecords 1) [] [])),
    ("a product w * U_C crossing the bound refused",
      tooLarge (Bounded.yardstickKey noUnits (boundTms "1e300") "uc" "R1" (boundRecords 1) []
        [("R1", [("U_C", tenPowOne 19700)])])),
    ("the corpus's own weights and U_C answered", answered
      (Bounded.yardstickKey noUnits (boundTms "5e-1") "uc" "R1" (boundRecords 3) []
        [("R1", [("U_C", "25e-1")])]))]
  for (what, ok) in cases do
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL yardstick_bound: {what}"
      fail := fail + 1
  return (pass, fail)

/-- The bound's runner: the corpus through the checked functions, then the hand cases. -/
def runBound : IO (Nat × Nat) := do
  let (p1, f1) ← runBoundedCorpus
  let (p2, f2) ← runBoundCases
  return (p1 + p2, f1 + f2)

end Tests.Yardstick
