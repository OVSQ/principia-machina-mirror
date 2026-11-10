import Principia.Digest
import Principia.Zone.Fields

/-!
# Hold scope: the hold after a failed canary, and its release

v1's `tpc_hold` 0.3.0 (TPS 3.3.11 to 3.3.15): the
pure functions Custos calls after an account fails a canary.

* `holdScope`: the blocks held, from the anchor to the failing block (v1 `hold_scope`).
* `heldClosure`: the records held in one register, and its seeds (v1 `held_closure`).
* `custosAllocate`: one identifier from the register's range reserved for the records
  Custos writes (v1 `tpx_allocate`). It draws the range's next number, given as input,
  and returns the range advanced: no randomness.
* `holdPreimage` and `holdRecord`: the HOLD record and the bytes its digest covers
  (v1 `hold_preimage`, `hold_record`).
* `releaseRecord`: the RELEASE record, once an independent reproduction matches
  (v1 `release_record`).

Each reads its arguments as parsed JSON (`Principia.Zone.Value`) and never fails on
malformed input: a fault is a refusal with its reason, escaped as a zone's problem is
(v1 `_show`, by Unicode 15.1.0's general category; `Principia.Zone.Text`).

**Digests.** A HOLD or a RELEASE record ends with a digest over its field list:
SHA-256 over the field list's netstring, in lowercase hexadecimal (`Principia.Digest.digestFields`,
`Principia.Sha256`). `holdFields` and `releaseFields` are the field
lists, `holdPreimage` the HOLD's preimage, and a RELEASE refuses a HOLD whose digest is not
the digest of its fields.

Not here, as in v1: writing HELD into the records, the review list of older work from
the same snapshot, the audit block, and the check at release that another HOLD in force
lists a record (Custos's).
-/

namespace Principia.Hold

open Principia.Zone
open Principia.Digest

/-! ## Results and reading -/

/-- A hold function's result: its answer, or a refusal with its reason (escaped). -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | refused (reason : String)
  deriving Repr, DecidableEq

/-- A check's outcome: its answer, or its refusal with the reason escaped (v1 `_refuse`). -/
def finish {α : Type} (r : Except String α) : Outcome α :=
  match r with
  | .ok a => .ok a
  | .error m => .refused (escape m)

/-- The value, or the refusal `m`. -/
def need {α : Type} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, m => .error m

/-- v1 `_is_text` for a string: not empty, and no disallowed code point. -/
def textOk (s : String) : Bool := !s.isEmpty && (firstBad s).isNone

/-- v1 `_is_text`: a field holding a text. -/
def text? : Option Value → Option String
  | some (.str s) => if textOk s then some s else none
  | _ => none

/-- v1 `_text_list`: a list of texts. -/
def textList? : Value → Option (List String)
  | .arr xs => xs.mapM fun
    | .str s => if textOk s then some s else none
    | _ => none
  | _ => none

/-- An integer (v1 `_is_int`: a boolean is none). -/
def int? : Option Value → Option Int
  | some (.int n) => some n
  | _ => none

/-- A pair of texts, `[a, b]`. -/
def pair? : Value → Option (String × String)
  | .arr [.str a, .str b] => if textOk a && textOk b then some (a, b) else none
  | _ => none

/-- No string repeats (v1 `_unique`). -/
def distinct (l : List String) : Bool := l.eraseDups.length == l.length

/-- Code point order, which is UTF-8 byte order (v1's collation of identifiers). -/
def sortStrings (l : List String) : List String := l.mergeSort fun a b => decide (a ≤ b)

/-- Pairs in the code point order of their first item. -/
def sortPairs (l : List (String × String)) : List (String × String) :=
  l.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- A list of pairs as digest fields, each pair's two items in turn. -/
def pairFields (ps : List (String × String)) : List Field :=
  ps.flatMap fun (a, b) => [.text a, .text b]

/-! ## The scope (v1 `hold_scope`) -/

/-- A block's canary outcome. -/
inductive Canary where
  | pass
  | fail
  deriving DecidableEq, Repr

/-- Where the scope begins. -/
inductive AnchorKind where
  /-- The block of the account's `lookback`-th most recent passed canary. -/
  | pass
  /-- The admission block, the account having fewer passes. -/
  | admission
  deriving DecidableEq, Repr

/-- The wire word. -/
def AnchorKind.text : AnchorKind → String
  | .pass => "PASS"
  | .admission => "ADMISSION"

/-- An anchor kind's wire word read back. -/
def AnchorKind.ofText? : String → Option AnchorKind
  | "PASS" => some .pass
  | "ADMISSION" => some .admission
  | _ => none

/-- The held block set. -/
structure Scope where
  /-- The held blocks in order, from the anchor block to the failing block. -/
  held : List String
  anchorKind : AnchorKind
  anchorBlock : String
  /-- The passed canaries counted back from the failing block. -/
  passes : Nat
  deriving DecidableEq, Repr

/-- A block's `canary` field: absent or null, PASS or FAIL; anything else is none. -/
def canary? : Option Value → Option (Option Canary)
  | none | some .null => some none
  | some (.str "PASS") => some (some .pass)
  | some (.str "FAIL") => some (some .fail)
  | _ => none

/-- The history's blocks, each its id and canary; `acc` holds those read, last first. -/
def readBlocks : List Value → List (String × Option Canary) →
    Except String (List (String × Option Canary))
  | [], acc => .ok acc.reverse
  | v :: vs, acc => do
    let .obj b := v | throw "history: block is not an object"
    let bid ← need (text? (get? b "block_id")) "history: block_id is not a name"
    if acc.any (·.1 == bid) then throw ("history: duplicate block " ++ bid)
    let c ← need (canary? (get? b "canary"))
      ("history: block " ++ bid ++ ": canary is not null, PASS or FAIL")
    readBlocks vs ((bid, c) :: acc)

/-- Back from the block before the failing one to the admission block: the passes
counted, and, when the `lookback`-th pass is found, how many blocks of the window lie
before it. A failed canary met first is refused: an earlier failure is its own hold. -/
def walk (lookback : Nat) : List (String × Option Canary) → Nat →
    Except String (Nat × Option Nat)
  | [], passes => .ok (passes, none)
  | (bid, c) :: rest, passes =>
    match c with
    | some .fail => .error ("history: block " ++ bid ++
        " failed a canary inside the scope; an earlier failure is its own hold")
    | some .pass =>
      if passes + 1 == lookback then .ok (passes + 1, some rest.length)
      else walk lookback rest (passes + 1)
    | none => walk lookback rest passes

/-- v1 `hold_scope`, before escaping: the account's ordered blocks under the certificate
in force, the last the failing block; the scope reaches back to the block of the
`lookback`-th most recent passed canary, inclusive, or with fewer passes to the admission
block. Blocks before the admission block belong to a lapsed certificate. -/
def holdScopeCheck (history lookback : Value) : Except String Scope := do
  let lb ← match lookback with
    | .int n =>
      if 1 ≤ n then pure n.toNat else throw "LOOKBACK PASSES is not an integer of at least 1"
    | _ => throw "LOOKBACK PASSES is not an integer of at least 1"
  let .obj h := history | throw "history is not an object"
  let _ ← need (text? (get? h "account")) "history: account is not a name"
  let adm ← need (text? (get? h "admission_block")) "history: admission_block is not a name"
  let bs ← match get? h "blocks" with
    | some (.arr (b :: bs)) => pure (b :: bs)
    | _ => throw "history: blocks is not a non-empty list"
  let blocks ← readBlocks bs []
  let ids := blocks.map (·.1)
  unless ids.contains adm do throw ("history: admission block " ++ adm ++ " is not in blocks")
  unless blocks.getLast?.map (·.2) == some (some .fail) do
    throw "history: the last block is not the failing block"
  let ai := ids.idxOf adm
  let window := ((blocks.take (blocks.length - 1)).drop ai).reverse
  let (passes, anchor) ← walk lb window 0
  let (kind, start) := match anchor with
    | some before => (AnchorKind.pass, ai + before)
    | none => (AnchorKind.admission, ai)
  return { held := ids.drop start, anchorKind := kind,
           anchorBlock := (ids.drop start).headD "", passes }

/-- v1 `hold_scope`. -/
def holdScope (history lookback : Value) : Outcome Scope :=
  finish (holdScopeCheck history lookback)

/-! ## The held records (v1 `held_closure`) -/

/-- What hold reads of a register record. -/
structure RecordFacts where
  id : String
  blockId : String
  author : String
  kind : String
  status : String
  cites : List String
  assumptions : List String
  /-- Who supplied a CORROBORATION that Custos wrote. -/
  suppliedBy : Option String
  /-- The Holder that vetted the RETURN carrying the record. -/
  vettedBy : Option String
  /-- The Holder's block; the record's own when absent. -/
  vettedIn : Option String
  deriving Repr

/-- One record; `ids` are those already read. -/
def readRecord (ids : List String) (v : Value) : Except String RecordFacts := do
  let .obj r := v | throw "records: entry is not an object"
  let rid ← need (text? (get? r "id")) "records: id is not a name"
  if ids.contains rid then throw ("records: duplicate id " ++ rid)
  let txt (f : String) : Except String String :=
    need (text? (get? r f)) ("records: " ++ rid ++ ": " ++ f ++ " is not a name")
  let lst (f : String) : Except String (List String) :=
    match get? r f with
    | none => pure []
    | some v => need (textList? v) ("records: " ++ rid ++ ": " ++ f ++ " is not a list of names")
  let opt (f : String) : Except String (Option String) :=
    match get? r f with
    | none => pure none
    | some v => some <$> need (text? (some v)) ("records: " ++ rid ++ ": " ++ f ++ " is not a name")
  let blockId ← txt "block_id"
  let author ← txt "author"
  let kind ← txt "kind"
  let status ← txt "status"
  let cites ← lst "cites"
  let assumptions ← lst "assumptions"
  let suppliedBy ← opt "supplied_by"
  let vettedBy ← opt "vetted_by"
  let vettedIn ← opt "vetted_in"
  return { id := rid, blockId, author, kind, status, cites, assumptions, suppliedBy,
           vettedBy, vettedIn }

/-- v1 `_read_records`: a list of records with distinct ids. -/
def readRecords (v : Value) : Except String (List RecordFacts) := do
  let .arr xs := v | throw "records is not a list"
  xs.foldlM (fun acc x => do return acc ++ [← readRecord (acc.map (·.id)) x]) []

/-- The seeds (v1 `_seed_ids`): every record the account authored in a held block; every
CORROBORATION it supplied in a held block; every record carried by a RETURN it vetted as
Holder in a held block. In code point order of id. -/
def seedIds (recs : List RecordFacts) (account : String) (blocks : List String) :
    List String :=
  sortStrings ((recs.filter fun r =>
    (r.author == account && blocks.contains r.blockId) ||
    (r.kind == "CORROBORATION" && r.suppliedBy.getD r.author == account &&
      blocks.contains r.blockId) ||
    (r.vettedBy == some account && blocks.contains (r.vettedIn.getD r.blockId))).map (·.id))

/-- The record cites or assumes one of `held`. -/
def reaches (held : List String) (r : RecordFacts) : Bool :=
  (r.cites ++ r.assumptions).any held.contains

/-- One round of propagation: `held`, then every record not yet held that cites or
assumes a held one. -/
def spread (recs : List RecordFacts) (held : List String) : List String :=
  held ++ (recs.filter fun r => !held.contains r.id && reaches held r).map (·.id)

/-- `spread`, `n` rounds. -/
def spreadTimes (recs : List RecordFacts) : Nat → List String → List String
  | 0, held => held
  | n + 1, held => spreadTimes recs n (spread recs held)

/-- The seeds and every record whose citations or ASSUMPTIONS reach one, transitively
(v1 `_propagate`; a cycle does not loop): one round per record reaches the fixed point
(`closure_fixed`). -/
def closure (recs : List RecordFacts) (seeds : List String) : List String :=
  spreadTimes recs recs.length seeds

/-- v1 `held_closure`'s answer. -/
structure Closure where
  /-- The held records, each with the status it had, in code point order of id. -/
  held : List (String × String)
  seeds : List String
  deriving DecidableEq, Repr

/-- v1 `held_closure`, before escaping: the HELD set of one register, from the failed
account and the held blocks. -/
def heldClosureCheck (records seeds : Value) : Except String Closure := do
  let recs ← readRecords records
  let .obj s := seeds | throw "seeds is not an object"
  let account ← need (text? (get? s "account")) "seeds: account is not a name"
  let blocks ← need ((get? s "blocks").bind textList?) "seeds: blocks is not a list of names"
  let sids := seedIds recs account blocks
  let held := closure recs sids
  return { held := sortPairs (recs.filterMap fun r =>
             if held.contains r.id then some (r.id, r.status) else none),
           seeds := sids }

/-- v1 `held_closure`. -/
def heldClosure (records seeds : Value) : Outcome Closure :=
  finish (heldClosureCheck records seeds)

/-! ## Custos's reserved range (v1 `tpx_allocate`) -/

/-- One identifier from the range, and the range after it (TPS 5.7.5's leased range, held
by Custos itself, so a write needs no mutex). -/
structure Allocation where
  /-- `<prefix>-<n>`. -/
  id : String
  rangePrefix : String
  low : Int
  high : Int
  /-- The range's next number after this one. -/
  next : Int
  deriving DecidableEq, Repr

/-- v1 `tpx_allocate`, before escaping. -/
def custosAllocateCheck (range : Value) : Except String Allocation := do
  let .obj r := range | throw "range is not an object"
  let pre ← match get? r "prefix" with
    | some (.str p) => if isIdent p then pure p else throw "range: prefix is not an identifier"
    | _ => throw "range: prefix is not an identifier"
  let bounds := "range: low and high are not integers with 1 <= low <= high"
  let (low, high) ← match int? (get? r "low"), int? (get? r "high") with
    | some lo, some hi => if 1 ≤ lo ∧ lo ≤ hi then pure (lo, hi) else throw bounds
    | _, _ => throw bounds
  let n ← match int? (get? r "next") with
    | some n => if low ≤ n then pure n else throw "range: next is not an integer at or above low"
    | none => throw "range: next is not an integer at or above low"
  if high < n then
    throw ("range: the reserved range " ++ pre ++ " " ++ toString low ++ "-" ++ toString high ++
      " is exhausted")
  return { id := pre ++ "-" ++ toString n, rangePrefix := pre, low, high, next := n + 1 }

/-- v1 `tpx_allocate`. -/
def custosAllocate (range : Value) : Outcome Allocation :=
  finish (custosAllocateCheck range)

/-! ## The HOLD record (v1 `hold_preimage`, `hold_record`) -/

/-- Why the hold was opened, and its scope. -/
structure Cause where
  canaryId : String
  account : String
  snapshot : String
  failingBlock : String
  anchorKind : AnchorKind
  anchorBlock : String
  lookbackPasses : Nat
  /-- The scope's blocks in order: the anchor block first, the failing block last. -/
  heldBlocks : List String
  deriving DecidableEq, Repr

/-- v1 `_read_cause`. -/
def readCause (v : Value) : Except String Cause := do
  let .obj c := v | throw "cause is not an object"
  let txt (f : String) : Except String String :=
    need (text? (get? c f)) ("cause: " ++ f ++ " is not a name")
  let canaryId ← txt "canary_id"
  let account ← txt "account"
  let snapshot ← txt "snapshot"
  let failingBlock ← txt "failing_block"
  let kindText ← txt "anchor_kind"
  let anchorBlock ← txt "anchor_block"
  let anchorKind ← need (AnchorKind.ofText? kindText)
    "cause: anchor_kind is not PASS or ADMISSION"
  let lookbackMsg := "cause: lookback_passes is not an integer of at least 1"
  let lookbackPasses ← match int? (get? c "lookback_passes") with
    | some n => if 1 ≤ n then pure n.toNat else throw lookbackMsg
    | none => throw lookbackMsg
  let blocksMsg := "cause: held_blocks is not a non-empty list of distinct names"
  let heldBlocks ← match (get? c "held_blocks").bind textList? with
    | some l => if !l.isEmpty && distinct l then pure l else throw blocksMsg
    | none => throw blocksMsg
  if heldBlocks.getLast? != some failingBlock then
    throw "cause: failing_block is not the last held block"
  if heldBlocks.head? != some anchorBlock then
    throw "cause: anchor_block is not the first held block"
  return { canaryId, account, snapshot, failingBlock, anchorKind, anchorBlock, lookbackPasses,
           heldBlocks }

/-- v1 `_read_pairs`: the held records, each `[id, prior_status]`, ids distinct, sorted. -/
def readHeld (v : Value) : Except String (List (String × String)) := do
  let .arr xs := v | throw "held is not a list"
  let out ← xs.foldlM (fun acc p => do
    let (a, b) ← need (pair? p) "held: entry is not [id, prior_status]"
    if acc.any (·.1 == a) then throw ("held: duplicate id " ++ a)
    return acc ++ [(a, b)]) []
  return sortPairs out

/-- v1 `_read_biblio`: the bibliography list, each `[bib_id, check]`, none
CONFIRMED, ids distinct, sorted. -/
def readBiblio (v : Value) : Except String (List (String × String)) := do
  let .arr xs := v | throw "biblio is not a list"
  let out ← xs.foldlM (fun acc p => do
    let (a, b) ← need (pair? p) "biblio: entry is not [bib_id, check]"
    if b == "CONFIRMED" then
      throw ("biblio: entry " ++ a ++ " is CONFIRMED; the list holds what is not")
    if acc.any (·.1 == a) then throw ("biblio: duplicate entry " ++ a)
    return acc ++ [(a, b)]) []
  return sortPairs out

/-- A HOLD's parts, read and sorted. -/
structure HoldParts where
  cause : Cause
  /-- The seeds, in code point order. -/
  seeds : List String
  /-- The held records with their prior status, in code point order of id. -/
  held : List (String × String)
  biblio : List (String × String)
  deriving DecidableEq, Repr

/-- v1 `_hold_parts`: every seed is a held record. -/
def holdParts (cause seeds held biblio : Value) : Except String HoldParts := do
  let c ← readCause cause
  let s ← match textList? seeds with
    | some l => if distinct l then pure l else throw "seeds is not a list of distinct names"
    | none => throw "seeds is not a list of distinct names"
  let pairs ← readHeld held
  for x in s do
    unless pairs.any (·.1 == x) do throw ("seed " ++ x ++ " is not in the held list")
  let b ← readBiblio biblio
  return { cause := c, seeds := sortStrings s, held := pairs, biblio := b }

/-- The HOLD digest's field list (TPS 3.3.11, form 2): tagged, the form, the cause, then
each list counted. It leaves out the HOLD's own id, its address. -/
def holdFields (p : HoldParts) : List Field :=
  let c := p.cause
  [.text "TPC-HOLD", .text "2", .text c.canaryId, .text c.account, .text c.snapshot,
   .text c.failingBlock, .text c.anchorKind.text, .text c.anchorBlock,
   .int c.lookbackPasses, .int c.heldBlocks.length] ++ c.heldBlocks.map .text ++
  [.int p.seeds.length] ++ p.seeds.map .text ++
  [.int p.held.length] ++ pairFields p.held ++
  [.int p.biblio.length] ++ pairFields p.biblio

/-- v1 `hold_preimage`: the bytes the HOLD digest covers. -/
def holdPreimage (cause seeds held biblio : Value) : Outcome String :=
  finish ((fun p => preimageFields (holdFields p)) <$> holdParts cause seeds held biblio)

/-- The HOLD record: its id, its parts, and its digest. -/
structure HoldRecord where
  holdId : String
  parts : HoldParts
  digest : String
  deriving DecidableEq, Repr

/-- v1 `hold_record`, before escaping. A HOLD with nothing to hold is refused, never
written empty. -/
def holdRecordCheck (holdId cause seeds held biblio : Value) : Except String HoldRecord := do
  let hid ← need (text? (some holdId)) "hold_id is not a name"
  let p ← holdParts cause seeds held biblio
  if p.held.isEmpty then throw "nothing to hold: the held list is empty"
  return { holdId := hid, parts := p, digest := digestFields (holdFields p) }

/-- v1 `hold_record`. -/
def holdRecord (holdId cause seeds held biblio : Value) : Outcome HoldRecord :=
  finish (holdRecordCheck holdId cause seeds held biblio)

/-! ## The RELEASE record (v1 `release_record`) -/

/-- What matched the held work. -/
inductive ReproductionKind where
  | reproduction
  /-- A community-ledger MATCH (handoff 5.3, 13.3), released through the trust-tier gate. -/
  | ledgerMatch
  deriving DecidableEq, Repr

/-- The wire word. -/
def ReproductionKind.text : ReproductionKind → String
  | .reproduction => "REPRODUCTION"
  | .ledgerMatch => "LEDGER_MATCH"

/-- A reproduction kind's wire word read back. -/
def ReproductionKind.ofText? : String → Option ReproductionKind
  | "REPRODUCTION" => some .reproduction
  | "LEDGER_MATCH" => some .ledgerMatch
  | _ => none

/-- The reproducer's standing as Custos reads it from the score (PD-D-5). -/
structure Tier where
  inTier : Bool
  overrideInForce : Bool
  independentMatches : Nat
  deriving DecidableEq, Repr

/-- The largest count a score holds (v1 `COUNT_MAX`). -/
def countMax : Int := 1000000000

/-- v1 `_tier_problem`: unknown fields (least first), missing fields in order, then each
field's type. -/
def readTier (v : Value) : Except String Tier := do
  let .obj t := v | throw "tier is not an object"
  let fields := ["in_tier", "override_in_force", "independent_matches"]
  match sortStrings ((t.map (·.1)).filter (!fields.contains ·)) with
  | k :: _ => throw ("tier: unknown field " ++ k)
  | [] => pure ()
  for f in fields do
    unless has t f do throw ("tier: missing field " ++ f)
  let flag (f : String) : Except String Bool :=
    match get? t f with
    | some (.bool b) => pure b
    | _ => throw ("tier: " ++ f ++ " is not a boolean")
  let inTier ← flag "in_tier"
  let overrideInForce ← flag "override_in_force"
  let countMsg := "tier: independent_matches is not a count"
  let n ← match get? t "independent_matches" with
    | some (.int n) => if 0 ≤ n ∧ n ≤ countMax then pure n.toNat else throw countMsg
    | _ => throw countMsg
  return { inTier, overrideInForce, independentMatches := n }

/-- The RELEASE record. -/
structure ReleaseRecord where
  releaseId : String
  holdId : String
  holdDigest : String
  kind : ReproductionKind
  reproductionId : String
  /-- The reproducer's account and snapshot. -/
  account : String
  snapshot : String
  /-- The released records, each with the status restored to it, in code point order. -/
  restored : List (String × String)
  /-- The held records a remaining seed still reaches, in code point order. -/
  stillHeld : List String
  /-- The HOLD's bibliography list, unchanged. -/
  biblio : List (String × String)
  digest : String
  deriving DecidableEq, Repr

/-- The RELEASE digest's field list (TPS 3.3.12): tagged, the form, then each list
counted. It leaves out the RELEASE's own id and its digest. -/
def releaseFields (r : ReleaseRecord) : List Field :=
  [.text "TPC-RELEASE", .text "2", .text r.holdId, .text r.holdDigest, .text r.kind.text,
   .text r.reproductionId, .text r.account, .text r.snapshot, .int r.restored.length] ++
  pairFields r.restored ++ [.int r.stillHeld.length] ++ r.stillHeld.map .text ++
  [.int r.biblio.length] ++ pairFields r.biblio

/-- A RELEASE with its digest set: SHA-256 of its fields. -/
def ReleaseRecord.sealed (r : ReleaseRecord) : ReleaseRecord :=
  { r with digest := digestFields (releaseFields r) }

/-- What a RELEASE reads of its HOLD before the HOLD's digest is checked. -/
structure HoldRead where
  releaseId : String
  holdId : String
  parts : HoldParts
  /-- The digest the HOLD carries, as given. -/
  digest : Value

/-- The HOLD record's fields as an object. -/
def holdFieldNames : List String :=
  ["hold_id", "canary_id", "account", "snapshot", "failing_block", "anchor_kind",
   "anchor_block", "lookback_passes", "held_blocks", "seeds", "held", "biblio", "digest"]

/-- v1 `release_record`'s reading of the HOLD, which needs no digest. -/
def readHold (releaseId hold : Value) : Except String HoldRead := do
  let rid ← need (text? (some releaseId)) "release_id is not a name"
  let .obj h := hold | throw "hold is not an object"
  for f in holdFieldNames do
    unless has h f do throw ("hold: missing field " ++ f)
  let hid ← need (text? (get? h "hold_id")) "hold: hold_id is not a name"
  let field (f : String) : Value := (get? h f).getD .null
  let p ← match holdParts hold (field "seeds") (field "held") (field "biblio") with
    | .ok p => pure p
    | .error m => throw ("hold: " ++ m)
  if p.held.isEmpty then throw "hold: the held list is empty"
  return { releaseId := rid, holdId := hid, parts := p, digest := field "digest" }

/-- The HOLD's digest, when it is the digest of the HOLD's fields. -/
def holdDigest? (h : HoldRead) : Option String :=
  match h.digest with
  | .str d => if d == digestFields (holdFields h.parts) then some d else none
  | _ => none

/-- v1 `release_record` after the HOLD's digest has matched (`holdDigest` is it): the
reproduction is independent (another account, not SAME-MODEL, from a REPRODUCTION block),
a ledger MATCH passes the trust-tier gate, the matched seeds leave the seed set, and every
held record no longer reached is released with its prior status. -/
def releaseAfter (h : HoldRead) (holdDigest : String) (reproduction records tier : Value) :
    Except String ReleaseRecord := do
  let .obj r := reproduction | throw "reproduction is not an object"
  let kindMsg := "reproduction: kind is not REPRODUCTION or LEDGER_MATCH"
  let kind ← match get? r "kind" with
    | some (.str k) => need (ReproductionKind.ofText? k) kindMsg
    | _ => throw kindMsg
  let rid ← need (text? (get? r "id")) "reproduction: id is not a name"
  let .obj ind := (get? r "independence").getD .null
    | throw "reproduction: independence is not an object"
  let indText (f : String) : Except String String :=
    need (text? (get? ind f)) ("reproduction: independence " ++ f ++ " is not a name")
  let account ← indText "account"
  let snapshot ← indText "snapshot"
  let origin ← indText "origin"
  let sameModel ← match get? ind "same_model" with
    | none => pure false
    | some (.bool b) => pure b
    | some _ => throw "reproduction: independence same_model is not a boolean"
  let matchedMsg := "reproduction: matched is not a list of distinct names"
  let matched ← match (get? r "matched").bind textList? with
    | some l => if distinct l then pure l else throw matchedMsg
    | none => throw matchedMsg
  let gate ← match kind with
    | .reproduction => match tier with
      | .null => pure none
      | _ => throw "tier is given for a REPRODUCTION"
    | .ledgerMatch => some <$> readTier tier
  let c := h.parts.cause
  if account == c.account then throw "reproduction by the held account is not independent"
  if sameModel || snapshot == c.snapshot then throw "reproduction is SAME-MODEL"
  if origin != "REPRODUCTION BLOCK" then throw "reproduction origin is not REPRODUCTION BLOCK"
  if let some t := gate then
    unless t.inTier do throw "trust-tier gate: NOT IN TIER"
    if t.overrideInForce && t.independentMatches < 2 then throw "trust-tier gate: OVERRIDE MARK"
  let heldIds := h.parts.held.map (·.1)
  for m in matched do
    unless heldIds.contains m do throw ("matched record " ++ m ++ " is not in the hold")
  let recs ← readRecords records
  for x in heldIds do
    unless recs.any (·.id == x) do throw ("held record " ++ x ++ " is not in records")
  let reached := closure recs (h.parts.seeds.filter (!matched.contains ·))
  let still := heldIds.filter reached.contains
  if still.length == heldIds.length then throw "no held record is released by this reproduction"
  let rec0 : ReleaseRecord :=
    { releaseId := h.releaseId, holdId := h.holdId, holdDigest, kind, reproductionId := rid,
      account, snapshot, restored := h.parts.held.filter (!still.contains ·.1),
      stillHeld := still, biblio := h.parts.biblio, digest := "" }
  return rec0.sealed

/-- v1 `release_record`, before escaping. -/
def releaseRecordCheck (releaseId hold reproduction records tier : Value) :
    Except String ReleaseRecord := do
  let h ← readHold releaseId hold
  let some d := holdDigest? h | throw "hold: digest does not match its fields"
  releaseAfter h d reproduction records tier

/-- v1 `release_record`. -/
def releaseRecord (releaseId hold reproduction records tier : Value) : Outcome ReleaseRecord :=
  finish (releaseRecordCheck releaseId hold reproduction records tier)

/-! ## What the kernel checks about the digests -/

/-- A HOLD the Calculator writes ends with SHA-256 of its fields' netstring. -/
theorem holdRecord_digest {i c s h b : Value} {r : HoldRecord}
    (hr : holdRecord i c s h b = .ok r) : r.digest = digestFields (holdFields r.parts) := by
  unfold holdRecord finish at hr
  split at hr
  · rename_i r' hc
    cases hr
    unfold holdRecordCheck at hc
    simp only [bind, Except.bind, pure, Except.pure] at hc
    repeat' split at hc
    all_goals first
      | (cases hc; rfl)
      | simp_all
  · cases hr

/-- The HOLD's digest matches only when it is SHA-256 of the HOLD's fields. -/
theorem holdDigest?_some {h : HoldRead} {d : String} (hd : holdDigest? h = some d) :
    h.digest = .str d ∧ d = digestFields (holdFields h.parts) := by
  unfold holdDigest? at hd
  split at hd
  · rename_i d' he
    split at hd
    · rename_i heq
      cases hd
      exact ⟨he, beq_iff_eq.mp heq⟩
    · cases hd
  · cases hd

/-- A RELEASE is written only for a HOLD whose digest is SHA-256 of its fields. -/
theorem releaseRecord_holdDigest {i h p rs t : Value} {r : ReleaseRecord}
    (hr : releaseRecord i h p rs t = .ok r) :
    ∃ hd d, readHold i h = .ok hd ∧ hd.digest = .str d ∧
      d = digestFields (holdFields hd.parts) ∧ releaseAfter hd d p rs t = .ok r := by
  unfold releaseRecord finish at hr
  split at hr
  · rename_i r' hc
    cases hr
    unfold releaseRecordCheck at hc
    cases hh : readHold i h with
    | error m => simp [hh, bind, Except.bind] at hc
    | ok hd =>
      simp only [hh, bind, Except.bind] at hc
      cases hdg : holdDigest? hd with
      | none => simp [hdg] at hc
      | some d =>
        simp only [hdg] at hc
        obtain ⟨h1, h2⟩ := holdDigest?_some hdg
        exact ⟨hd, d, rfl, h1, h2, hc⟩
  · cases hr

/-- A RELEASE sealed: its digest SHA-256 of its fields, which leave the digest out. -/
theorem ReleaseRecord.sealed_digest (r : ReleaseRecord) :
    r.sealed.digest = digestFields (releaseFields r.sealed) := rfl

/-! ## What the kernel checks about the closure

`heldClosure` and `releaseRecord` hold the records `closure` gives. It is a closure: it
holds its seeds, a record citing or assuming a held record is held, and closing again
changes nothing. The round count is enough because each round that changes the held set
holds one more record (`spread_eq_or_lt`). -/

theorem spreadTimes_contains (recs : List RecordFacts) :
    ∀ (n : Nat) (held : List String) (x : String), x ∈ held → x ∈ spreadTimes recs n held
  | 0, _, _, h => h
  | n + 1, held, x, h => by
    simp only [spreadTimes]
    exact spreadTimes_contains recs n _ x (by simp [spread, h])

theorem spreadTimes_fixed (recs : List RecordFacts) (held : List String)
    (h : spread recs held = held) : ∀ n, spreadTimes recs n held = held
  | 0 => rfl
  | n + 1 => by simp only [spreadTimes, h]; exact spreadTimes_fixed recs held h n

/-- The records not yet held. -/
def outside (recs : List RecordFacts) (held : List String) : Nat :=
  (recs.filter fun r => !held.contains r.id).length

theorem length_filter_mono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | y :: ys, h => by
    have ih := length_filter_mono p q ys (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hy := h y List.mem_cons_self
    cases hp : p y <;> cases hq : q y <;> simp_all <;> omega

theorem length_filter_lt {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      ∀ x ∈ l, q x = true → p x = false → (l.filter p).length < (l.filter q).length
  | [], _, x, hx, _, _ => by simp at hx
  | y :: ys, h, x, hx, hq, hp => by
    have hmono := length_filter_mono p q ys (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hy := h y List.mem_cons_self
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hp, hq]; omega
    · have ih := length_filter_lt p q ys (fun z hz => h z (List.mem_cons_of_mem _ hz)) x hx' hq hp
      cases hpy : p y <;> cases hqy : q y <;> simp_all <;> omega

/-- A round of propagation changes nothing, or holds one more record. -/
theorem spread_eq_or_lt (recs : List RecordFacts) (held : List String) :
    spread recs held = held ∨ outside recs (spread recs held) < outside recs held := by
  by_cases hnew : (recs.filter fun r => !held.contains r.id && reaches held r) = []
  · left
    simp only [spread, hnew, List.map_nil, List.append_nil]
  · right
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hnew
    rw [List.mem_filter] at hr
    obtain ⟨hrm, hrp⟩ := hr
    unfold outside
    apply length_filter_lt (fun r' => !(spread recs held).contains r'.id)
      (fun r' => !held.contains r'.id) recs _ r hrm
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrp
      show (!held.contains r.id) = true
      rw [hrp.1]
      rfl
    · simp only [spread, List.contains_append, Bool.not_or, Bool.not_eq_false',
        Bool.and_eq_false_imp, Bool.not_eq_true']
      intro _
      rw [List.contains_iff_mem]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hrm, hrp⟩)
    · intro x _ hx
      simp only [spread, List.contains_append, Bool.not_or, Bool.and_eq_true] at hx
      exact hx.1

/-- With every record held, a round changes nothing. -/
theorem spread_fixed_of_outside_zero (recs : List RecordFacts) (held : List String)
    (h : outside recs held = 0) : spread recs held = held := by
  have hout : (recs.filter fun r => !held.contains r.id) = [] := List.eq_nil_of_length_eq_zero h
  have hnew : (recs.filter fun r => !held.contains r.id && reaches held r) = [] := by
    rw [List.filter_eq_nil_iff] at hout ⊢
    intro r hr hp
    simp only [Bool.and_eq_true] at hp
    exact hout r hr hp.1
  simp only [spread, hnew, List.map_nil, List.append_nil]

theorem spreadTimes_spread_fixed (recs : List RecordFacts) :
    ∀ (n : Nat) (held : List String), outside recs held ≤ n →
      spread recs (spreadTimes recs n held) = spreadTimes recs n held
  | 0, held, h => spread_fixed_of_outside_zero recs held (by omega)
  | n + 1, held, h => by
    simp only [spreadTimes]
    rcases spread_eq_or_lt recs held with hfix | hlt
    · rw [hfix, spreadTimes_fixed recs held hfix n]
      exact hfix
    · exact spreadTimes_spread_fixed recs n _ (by omega)

/-- The closure is a fixed point of propagation: one round per record is enough. -/
theorem closure_fixed (recs : List RecordFacts) (seeds : List String) :
    spread recs (closure recs seeds) = closure recs seeds :=
  spreadTimes_spread_fixed recs recs.length seeds (List.length_filter_le _ _)

/-- The closure holds its seeds. -/
theorem closure_contains_seeds (recs : List RecordFacts) (seeds : List String) :
    ∀ x ∈ seeds, x ∈ closure recs seeds :=
  fun x hx => spreadTimes_contains recs recs.length seeds x hx

/-- The closure is closed: a record citing or assuming a held record is held. -/
theorem closure_closed (recs : List RecordFacts) (seeds : List String) :
    ∀ r ∈ recs, reaches (closure recs seeds) r = true → r.id ∈ closure recs seeds := by
  intro r hr hreach
  have h := closure_fixed recs seeds
  unfold spread at h
  have hnil := List.append_right_eq_self.mp h
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hnil
  have := hnil r hr
  simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at this
  rw [← List.contains_iff_mem]
  cases hc : (closure recs seeds).contains r.id
  · exact absurd hreach (by simp [this hc])
  · rfl

/-- The closure is idempotent: closing a closed set changes nothing. -/
theorem closure_idem (recs : List RecordFacts) (seeds : List String) :
    closure recs (closure recs seeds) = closure recs seeds :=
  spreadTimes_fixed recs _ (closure_fixed recs seeds) recs.length

end Principia.Hold
