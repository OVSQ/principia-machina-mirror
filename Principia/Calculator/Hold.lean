import Principia.Calculator.Interface
import Principia.Calculator.Record
import Principia.Hold

/-!
# Family `hold`: hold scope, the HOLD and the RELEASE

Version 1's `tpc_hold` 0.3.0 on the command line (`Principia.Hold`), its arguments named as
version 1's corpus (the hold's corpus) names them, the allocation spelled
`allocate_identifiers` (version 1's `tpx_allocate`). Each answers version 1's list as
canonical JSON: `["OK", ...]`, or `["REFUSED", reason]` at exit code 0, the reason escaped
as version 1 escaped it.

* `hold_scope {"history", "lookback_passes"}`: `["OK", held blocks, anchor kind, anchor
  block, passes]`.
* `held_closure {"records", "seeds"}`: `["OK", [[id, status]], seeds]`.
* `allocate_identifiers {"range"}`: `["OK", id, [prefix, low, high, next]]`.
* `hold_preimage {"cause", "seeds", "held", "biblio"}`: `["OK", preimage]`.
* `hold_record {"hold_id", "cause", "seeds", "held", "biblio"}`: `["OK", [hold_id, "HOLD",
  canary, account, snapshot, failing block, anchor kind, anchor block, lookback passes,
  held blocks, seeds, [[id, status]], [[bib_id, check]], digest]]`.
* `release_record {"release_id", "hold", "reproduction", "records", "tier"}`: `["OK",
  [release_id, "RELEASE", hold_id, hold digest, kind, reproduction id, account, snapshot,
  [[id, status]], still held, [[bib_id, check]], digest]]`.

A HOLD's and a RELEASE's digests are SHA-256 over their field lists. An argument version 1's
function reads must be present; each is read as version 1 read it (a number written with a
fraction or an exponent is a float).

Bounds: at most `maxEntries` entries in any list or object (so at most 4,000 blocks of a
history), at most `maxRecords` records of a register (`records`), strings of at most
`maxText` code points and `maxTextTotal` in all, members' names included. The closure walks
the citations to a fixed point, its work growing with about the cube of a chain's length: a
chain of 1,000 records took 2.3 s, one of 2,000 took 17 s.
-/

namespace Principia.Calculator.Hold

open Principia.Canonical
open Principia.Hold

/-! ## The family's bounds -/

/-- The most entries a list or an object of a request holds, at any depth: the probe's
historical view's 4,000. -/
def maxEntries : Nat := 4000

/-- The most records a register (`records`) holds: the closure's fixed point walks every
record's citations in every round. -/
def maxRecords : Nat := 1000

/-- The most code points a string of a request holds, a member's name included. -/
def maxText : Nat := 16384

/-- The most code points the strings of a request hold in all. -/
def maxTextTotal : Nat := 262144

/-- A request within the bounds. -/
def within (v : Value) : Except Refusal Unit := do
  let s := Record.valueSize v
  if maxEntries < s.entries then
    badArgument s!"a list or an object of the request holds more than {maxEntries} entries (the Calculator's bound)"
  if maxText < s.longest then
    badArgument s!"a string of the request holds more than {maxText} code points (the Calculator's bound)"
  if maxTextTotal < s.text then
    badArgument s!"the strings of the request hold more than {maxTextTotal} code points in all (the Calculator's bound)"
  match v with
  | .obj ms =>
    match ms.lookup "records" with
    | some (.arr rs) => atMost "records" maxRecords rs
    | _ => pure ()
  | _ => pure ()

/-- A request's value as version 1 received it. -/
partial def zoneValue : Value → Zone.Value
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .num _ => .real
  | .str s => .str s
  | .arr xs => .arr (xs.map zoneValue)
  | .obj ms => .obj (ms.map fun (k, v) => (k, zoneValue v))

/-- The request within the bounds, holding exactly `names`, each read as version 1 read it. -/
def read (names : List String) (v : Value) : Except Refusal (String → Zone.Value) := do
  within v
  let ms ← membersOf names v
  for n in names do
    let _ ← needed ms n
  pure fun k => ((ms.lookup k).map zoneValue).getD .null

/-! ## The answers -/

def strs (xs : List String) : Value := .arr (xs.map .str)

def pairs (xs : List (String × String)) : Value := .arr (xs.map fun (a, b) => strs [a, b])

/-- Version 1's answer: `["OK", items...]` or `["REFUSED", reason]`. -/
def answer {α : Type} (f : α → List Value) : Outcome α → Value
  | .ok a => .arr (.str "OK" :: f a)
  | .refused r => .arr [.str "REFUSED", .str r]

def scopeItems (s : Scope) : List Value :=
  [strs s.held, .str s.anchorKind.text, .str s.anchorBlock, .int s.passes]

def closureItems (c : Closure) : List Value := [pairs c.held, strs c.seeds]

def allocationItems (a : Allocation) : List Value :=
  [.str a.id, .arr [.str a.rangePrefix, .int a.low, .int a.high, .int a.next]]

def holdItems (r : HoldRecord) : List Value :=
  let c := r.parts.cause
  [.arr [.str r.holdId, .str "HOLD", .str c.canaryId, .str c.account, .str c.snapshot,
    .str c.failingBlock, .str c.anchorKind.text, .str c.anchorBlock, .int c.lookbackPasses,
    strs c.heldBlocks, strs r.parts.seeds, pairs r.parts.held, pairs r.parts.biblio,
    .str r.digest]]

def releaseItems (r : ReleaseRecord) : List Value :=
  [.arr [.str r.releaseId, .str "RELEASE", .str r.holdId, .str r.holdDigest, .str r.kind.text,
    .str r.reproductionId, .str r.account, .str r.snapshot, pairs r.restored, strs r.stillHeld,
    pairs r.biblio, .str r.digest]]

/-- The family's functions. -/
def calls : Family := [
  ("allocate_identifiers", fun v => do
    let a ← read ["range"] v
    pure (answer allocationItems (custosAllocate (a "range")))),
  ("held_closure", fun v => do
    let a ← read ["records", "seeds"] v
    pure (answer closureItems (heldClosure (a "records") (a "seeds")))),
  ("hold_preimage", fun v => do
    let a ← read ["cause", "seeds", "held", "biblio"] v
    pure (answer (fun p => [.str p]) (holdPreimage (a "cause") (a "seeds") (a "held") (a "biblio")))),
  ("hold_record", fun v => do
    let a ← read ["hold_id", "cause", "seeds", "held", "biblio"] v
    pure (answer holdItems
      (holdRecord (a "hold_id") (a "cause") (a "seeds") (a "held") (a "biblio")))),
  ("hold_scope", fun v => do
    let a ← read ["history", "lookback_passes"] v
    pure (answer scopeItems (holdScope (a "history") (a "lookback_passes")))),
  ("release_record", fun v => do
    let a ← read ["release_id", "hold", "reproduction", "records", "tier"] v
    pure (answer releaseItems (releaseRecord (a "release_id") (a "hold") (a "reproduction")
      (a "records") (a "tier")))),
]

end Principia.Calculator.Hold
