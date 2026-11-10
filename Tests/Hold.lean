import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of v1's `vectors/hold_corpus.json` (140 cases) against `Principia.Hold`.

A case is `{"id", "fn", "input", "note", "expect"}`. Its input is read into
`Principia.Zone.Value` as v1's JSON reader gives it (`Tests.Zone.toValue`); its `expect` is
v1's `canon` text of the result. A refusal is compared by its reason, the text between
`[REFUSED,` and the final `]`. An answer is read from that text into the function's typed
result, and the typed values are compared. v1's text writes a string unquoted, so a word
holding a comma or a bracket, or an empty word, could be read two ways: a case whose
answer holds one fails rather than passes. The HOLD preimage, one string, is compared as
the text between `[OK,` and the final `]`.

A HOLD and a RELEASE end with their digests, SHA-256 (`Principia.Sha256`; decision D2,
option 1), compared with v1's as every other field is; a RELEASE compares its HOLD's digest
with the digest of the HOLD's fields as v1 did. An owed case would be listed with its reason
in `vectors/hold_corpus.owed.json` (the list must be exactly the owed cases); none is.
-/

namespace Tests.Hold

open Lean
open Principia
open Principia.Hold
open Principia.Zone (Value Owed codePoint)

/-! ## v1's text of a result -/

/-- v1's `canon` text read as a tree: a list in brackets, items between commas. -/
inductive Canon where
  | atom (s : String)
  | list (xs : List Canon)
  deriving Repr, Inhabited

mutual
/-- One item and the text after it. -/
partial def readCanon : List Char → Option (Canon × List Char)
  | '[' :: ']' :: rest => some (.list [], rest)
  | '[' :: rest => readItems rest []
  | cs =>
    let (a, rest) := cs.span fun c => c != ',' && c != '[' && c != ']'
    some (.atom (String.ofList a), rest)
/-- A list's items, up to its closing bracket. -/
partial def readItems (cs : List Char) (acc : List Canon) : Option (Canon × List Char) := do
  let (x, rest) ← readCanon cs
  match rest with
  | ',' :: more => readItems more (acc ++ [x])
  | ']' :: more => some (.list (acc ++ [x]), more)
  | _ => none
end

/-- The text between a prefix and the final `]`. -/
def between (pre e : String) : Option String :=
  if e.startsWith pre && e.endsWith "]" then
    some (String.ofList ((e.toList.drop pre.length).dropLast))
  else none

/-- v1's expectation: a refusal's reason, or the items of an answer. -/
def expectation (e : String) : Option (Except String (List Canon)) :=
  match between "[REFUSED," e with
  | some r => some (.error r)
  | none =>
    match readCanon e.toList with
    | some (.list (.atom "OK" :: items), []) => some (.ok items)
    | _ => none

def atom? : Canon → Option String
  | .atom s => some s
  | _ => none

def atoms? : Canon → Option (List String)
  | .list xs => xs.mapM atom?
  | _ => none

def pairs? : Canon → Option (List (String × String))
  | .list xs => xs.mapM fun
    | .list [.atom a, .atom b] => some (a, b)
    | _ => none
  | _ => none

def nat? (c : Canon) : Option Nat := (atom? c).bind String.toNat?

def int? (c : Canon) : Option Int := (atom? c).bind String.toInt?

/-! ## Answers read from the text -/

def scopeOf : List Canon → Option Scope
  | [held, kind, block, passes] => do
    return { held := ← atoms? held, anchorKind := ← (atom? kind).bind AnchorKind.ofText?,
             anchorBlock := ← atom? block, passes := ← nat? passes }
  | _ => none

def closureOf : List Canon → Option Closure
  | [held, seeds] => do return { held := ← pairs? held, seeds := ← atoms? seeds }
  | _ => none

def allocationOf : List Canon → Option Allocation
  | [.atom id, .list [.atom p, lo, hi, nx]] => do
    return { id, rangePrefix := p, low := ← int? lo, high := ← int? hi, next := ← int? nx }
  | _ => none

/-- v1's `["OK", [hold_id, "HOLD", ...]]`: the record is the answer's one item. -/
def holdRecordOf : List Canon → Option HoldRecord
  | [.list [hid, tag, canary, account, snapshot, failing, kind, anchor, lookback, blocks, seeds,
     held, biblio, digest]] => do
    guard (atom? tag == some "HOLD")
    let cause : Cause :=
      { canaryId := ← atom? canary, account := ← atom? account, snapshot := ← atom? snapshot,
        failingBlock := ← atom? failing, anchorKind := ← (atom? kind).bind AnchorKind.ofText?,
        anchorBlock := ← atom? anchor, lookbackPasses := ← nat? lookback,
        heldBlocks := ← atoms? blocks }
    return { holdId := ← atom? hid, digest := ← atom? digest,
             parts := { cause, seeds := ← atoms? seeds, held := ← pairs? held,
                        biblio := ← pairs? biblio } }
  | _ => none

/-- v1's `["OK", [release_id, "RELEASE", ...]]`: the record is the answer's one item. -/
def releaseRecordOf : List Canon → Option ReleaseRecord
  | [.list [rid, tag, hid, hd, kind, repro, account, snapshot, restored, still, biblio,
     digest]] => do
    guard (atom? tag == some "RELEASE")
    return { releaseId := ← atom? rid, holdId := ← atom? hid, holdDigest := ← atom? hd,
             kind := ← (atom? kind).bind ReproductionKind.ofText?,
             reproductionId := ← atom? repro, account := ← atom? account,
             snapshot := ← atom? snapshot, restored := ← pairs? restored,
             stillHeld := ← atoms? still, biblio := ← pairs? biblio, digest := ← atom? digest }
  | _ => none

/-! ## The words of an answer, which v1's text must carry one to one -/

def plain (w : String) : Bool :=
  !w.isEmpty && !w.any fun c => c == ',' || c == '[' || c == ']'

def pairWords (ps : List (String × String)) : List String := ps.flatMap fun (a, b) => [a, b]

def scopeWords (s : Scope) : List String := s.anchorBlock :: s.held

def closureWords (c : Closure) : List String := pairWords c.held ++ c.seeds

def allocationWords (a : Allocation) : List String := [a.id, a.rangePrefix]

def holdWords (r : HoldRecord) : List String :=
  let c := r.parts.cause
  [r.holdId, c.canaryId, c.account, c.snapshot, c.failingBlock, c.anchorBlock] ++
    c.heldBlocks ++ r.parts.seeds ++ pairWords r.parts.held ++ pairWords r.parts.biblio

def releaseWords (r : ReleaseRecord) : List String :=
  [r.releaseId, r.holdId, r.holdDigest, r.reproductionId, r.account, r.snapshot] ++
    pairWords r.restored ++ r.stillHeld ++ pairWords r.biblio

/-! ## Judging a case -/

/-- A case's result. -/
inductive Judged where
  | pass
  | fail (why : String)
  | owed (reason : String)

/-- Whether a result agrees with v1's: `none` when it does, else what was got. -/
def agrees {α : Type} [DecidableEq α] [Repr α] (words : α → List String)
    (read : List Canon → Option α) (want : Except String (List Canon)) :
    Outcome α → Option String
  | .refused r => match want with
    | .error w => if r == w then none else some s!"refused {repr r}"
    | .ok _ => some s!"refused {repr r}"
  | .ok a => match want with
    | .error _ => some s!"answered {repr a}"
    | .ok items => match read items with
      | none => some s!"answered {repr a}; the expectation does not read as this answer"
      | some b =>
        if !(words a).all plain then some s!"answered {repr a}, ambiguous in v1's text"
        else if a == b then none else some s!"answered {repr a}"

/-- A fully checked case. -/
def judge {α : Type} [DecidableEq α] [Repr α] (words : α → List String)
    (read : List Canon → Option α) (want : Except String (List Canon)) (got : Outcome α) :
    Judged :=
  match agrees words read want got with
  | none => .pass
  | some why => .fail why

def arg (input : Json) (k : String) : IO Value := do
  match input.getObjVal? k with
  | .ok j => return Tests.Zone.toValue j
  | .error e => throw (IO.userError s!"{e} in {input.compress}")

/-- Run one case; `e` is v1's text, `want` what it reads as. -/
def runCase (fn : String) (input : Json) (e : String) (want : Except String (List Canon)) :
    IO Judged := do
  let a := arg input
  match fn with
  | "hold_scope" =>
    return judge scopeWords scopeOf want (holdScope (← a "history") (← a "lookback_passes"))
  | "held_closure" =>
    return judge closureWords closureOf want (heldClosure (← a "records") (← a "seeds"))
  | "tpx_allocate" =>
    return judge allocationWords allocationOf want (custosAllocate (← a "range"))
  | "hold_preimage" =>
    let got := holdPreimage (← a "cause") (← a "seeds") (← a "held") (← a "biblio")
    -- the preimage is one string: the text between "[OK," and the final "]"
    match got, want with
    | .ok p, .ok _ => return if between "[OK," e == some p then .pass else .fail s!"answered {repr p}"
    | _, _ => return judge (fun _ => []) (fun _ => none) want got
  | "hold_record" =>
    return judge holdWords holdRecordOf want
      (holdRecord (← a "hold_id") (← a "cause") (← a "seeds") (← a "held") (← a "biblio"))
  | "release_record" =>
    return judge releaseWords releaseRecordOf want
      (releaseRecord (← a "release_id") (← a "hold") (← a "reproduction") (← a "records")
        (← a "tier"))
  | other => throw (IO.userError s!"unknown function {other}")

/-- Run the corpus: passes and failures; owed cases are counted, printed, and checked
against the owed list. -/
def runHold : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/hold_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/hold_corpus.owed.json"))
  let owedList ← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)
  let listed ← owedList.toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "id")),
          (← IO.ofExcept (o.getObjValAs? String "reason")))
  let mut pass := 0
  let mut fail := 0
  let mut owed : List (String × String × String) := []
  for c in cases do
    let id ← IO.ofExcept (c.getObjValAs? String "id")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let e ← IO.ofExcept (c.getObjValAs? String "expect")
    let some want := expectation e
      | throw (IO.userError s!"hold {id}: expectation does not read: {e}")
    match ← runCase fn (← IO.ofExcept (c.getObjVal? "input")) e want with
    | .pass => pass := pass + 1
    | .fail why =>
      IO.eprintln s!"FAIL hold {id}:\n  expected {e}\n  {why}"
      fail := fail + 1
    | .owed reason => owed := owed ++ [(id, fn, reason)]
  -- The owed cases are exactly the listed ones, each for its listed reason.
  for (id, _, why) in owed do
    unless listed.contains (id, why) do
      IO.eprintln s!"FAIL hold {id}: owed ({why}) but not listed so in vectors/hold_corpus.owed.json"
      fail := fail + 1
  for (id, why) in listed do
    unless owed.any (fun (i, _, w) => i == id && w == why) do
      IO.eprintln s!"FAIL hold {id}: listed as owed ({why}) but not owed for that reason"
      fail := fail + 1
  let per (f : String) := (owed.filter (·.2.1 == f)).length
  IO.println s!"hold: {owed.length} owed (hold_record {per "hold_record"}, release_record {per "release_record"}); every HOLD and RELEASE digest SHA-256, compared with v1's"
  return (pass, fail)

end Tests.Hold
