import Principia.Calculator.Interface
import Principia.Calculator.Record
import Principia.Biblio
import Principia.Biblio.Recheck

/-!
# Family `biblio`: the bibliography's checks

Version 1's `tpc_biblio` `run_case` functions on the command line (`Principia.Biblio`), one each
under version 1's name, their arguments named as version 1 named them. The answer is the
structure of version 1's return value, written as canonical JSON:

* `doi {"text"}`: `{"doi", "kind", "id"}`, `kind` `DOI` or `ARXIV`.
* `shape {"text"}`, `withdrawn {"comment"}`: `true` or `false`.
* `arxiv {"text"}`: `{"id", "version", "key", "scheme"}`, `scheme` `NEW` or `OLD`.
* `isbn {"text"}`: `{"isbn13", "given"}`, `given` `"10"` or `"13"`.
* `issn`, `pmid`, `pmcid {"text"}`; `key {"text", "kind"}`; `url {"declaration",
  "identifier"}`; `preimage {"bib_id", "proposed_by", "landed_by", "landed", "supersedes",
  "identifiers", "item"}`: a text.
* `dupe {"identifiers"}`: `{"kind", "key"}`.
* `check {"entry", "existing", "caps"}`: `{"status": "OK", "identifiers": {kind: value},
  "dupe": {"kind", "key"}}`, the identifiers those the entry gives.
* `canon` (the arguments of `preimage`): `{"text", "digest"}`.
* `compare {"entry", "records", "date"}`: `{"check", "results": [[kind, identifier, result,
  fields]], "notices": [{"type", "identifier", "date", "source"}], "check_line",
  "notices_line"}`, the last two the CHECK and NOTICES lines version 1 rendered for `date`
  (`notices_line` empty when there is no notice); an identifier or a date version 1 wrote as
  None is `null`.
* `view {"records", "entries", "findings"}`: `{"records": [[record, [[bib_id, reason]]]],
  "for_hdecl": [bib_id]}`.
* `holdlist {"entries", "account", "blocks", "checks"}`: `[[bib_id, check]]`.
* `recheck_urls {"entries", "declarations", "date", "lookups_today", "recheck"?, "batch"?,
  "cap"?}`: a recheck run's first-round lookups (TPS 5.21.14, 5.21.18, 5.21.19,
  `Principia.Biblio.Recheck`). `entries` lists `{"bib_id", "identifiers": {kind: text},
  "check_line"?: text or null}`, the CHECK LINE as written; `declarations` the REGISTRY
  DECLARATIONS in the form `url` reads; `date` the run's UTC date `YYYY-MM-DD`;
  `lookups_today` the fleet's lookups of the day so far; `recheck` (days), `batch` and `cap`
  BIBLIO RECHECK, BIBLIO RECHECK BATCH and BIBLIO LOOKUP CAP, their declared values when
  absent. Each identifier of kind DOI, ARXIV, PMID or PMCID goes to its first round, the
  first declaration of kind DOI-RA, ARXIV, PMID or PMCID, in that order of kinds; an entry
  with none of them is never due. The answer is `{"lookups": [{"bib_id", "kind",
  "identifier", "registry", "url"}], "failed": [{"bib_id", "kind", "identifier"}], "taken":
  [bib_id], "due": n, "backlog": n}`: `failed` the identifiers whose URL `url` refuses (LOOKUP
  FAILED, counted against the batch, not fetched), `backlog` the due entries not taken. Its
  refusal words: `entries`, `check_line` (not a CHECK LINE, or dated after `date`),
  `declarations` (one not an object of a declared kind, or whose template `url` refuses when
  used), `date`, `lookups_today`, `recheck`, `batch`, `cap`.

Version 1's `ValueError` is refused `BAD_ARGUMENT`, its message the detail; every answer is
computed, so none is refused as owed. Each argument is read as version 1 read it (a number
written with a fraction or an exponent is a float), and every argument version 1's
`run_case` reads must be present.

Bounds: at most `maxEntries` entries in any list or object (so in `existing` and `records`),
`maxIdentifiers` in `identifiers`, strings of at most `maxText` code points each and
`maxTextTotal` in all, members' names included.
-/

namespace Principia.Calculator.Biblio

open Principia.Canonical
open Principia.Biblio

/-! ## The family's bounds -/

/-- The most entries a list or an object of a request holds, at any depth. -/
def maxEntries : Nat := 1024

/-- The most members `identifiers` holds. -/
def maxIdentifiers : Nat := 64

/-- The most code points a string of a request holds, a member's name included. -/
def maxText : Nat := 16384

/-- The most code points the strings of a request hold in all: each text is read in NFC
and NFD, whose cost grows with its length. -/
def maxTextTotal : Nat := 131072

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
    match ms.lookup "identifiers" with
    | some (.obj xs) => atMost "identifiers" maxIdentifiers xs
    | some (.arr xs) => atMost "identifiers" maxIdentifiers xs
    | _ => pure ()
  | _ => pure ()

/-! ## Reading a request -/

/-- A request's value as version 1 received it: a number written with a fraction or an
exponent as Python's `float`. -/
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

/-- A text, or `null` for version 1's None. -/
def orNull : Option String → Value
  | some s => .str s
  | none => .null

/-- A list of texts. -/
def strs (xs : List String) : Value := .arr (xs.map .str)

/-- An answer, or version 1's `ValueError` refused `BAD_ARGUMENT` with its message. -/
def answer {α : Type} (f : α → Value) : Check α → Except Refusal Value
  | .ok a => .ok (f a)
  | .error (.refused m) => badArgument m

def doiValue (d : DoiNorm) : Value :=
  .obj [("doi", .str d.doi), ("kind", .str (match d.kind with
    | .doi => "DOI"
    | .arxiv => "ARXIV")), ("id", .str d.id)]

def arxivValue (a : ArxivId) : Value :=
  .obj [("id", .str a.id), ("version", .int a.version), ("key", .str a.key),
    ("scheme", .str (match a.scheme with
      | .new => "NEW"
      | .old => "OLD"))]

def isbnValue (i : Isbn) : Value :=
  .obj [("isbn13", .str i.isbn13), ("given", .str (if i.givenTen then "10" else "13"))]

def dupeValue (d : Dupe) : Value := .obj [("kind", .str d.kind), ("key", .str d.key)]

/-- The identifiers an entry gives, in version 1's order of kinds. -/
def identifiersValue (ids : Identifiers) : Value :=
  .obj (identKinds.filterMap fun k => (ids.get k).map fun v => (k, .str v))

def checkValue (r : CheckResult) : Value :=
  .obj [("status", .str "OK"), ("identifiers", identifiersValue r.identifiers),
    ("dupe", dupeValue r.dupe)]

def canonValue (c : CanonEntry) : Value := .obj [("text", .str c.text), ("digest", .str c.digest)]

def noticeValue (n : Notice) : Value :=
  .obj [("type", .str n.type), ("identifier", orNull n.identifier), ("date", orNull n.date),
    ("source", .str n.source)]

def compareValue (x : Comparison × String × String) : Value :=
  let (c, cl, nl) := x
  .obj [("check", .str c.check),
    ("results", .arr (c.results.map fun r =>
      .arr [.str r.kind, .str r.identifier, .str r.result, strs r.fields])),
    ("notices", .arr (c.notices.map noticeValue)),
    ("check_line", .str cl), ("notices_line", .str nl)]

def viewValue (v : LiteratureView) : Value :=
  .obj [("records", .arr (v.records.map fun (rid, flagged) =>
      .arr [.str rid, .arr (flagged.map fun (b, reason) => .arr [.str b, .str reason])])),
    ("for_hdecl", strs v.forHdecl)]

def pairsValue (xs : List (String × String)) : Value :=
  .arr (xs.map fun (a, b) => .arr [.str a, .str b])

/-- The arguments of `canon` and `preimage`. -/
def entryArgs : List String :=
  ["bib_id", "proposed_by", "landed_by", "landed", "supersedes", "identifiers", "item"]

/-- A one-text function. -/
def textCall {α : Type} (name : String) (f : Zone.Value → Check α) (g : α → Value) : Call :=
  fun v => do
    let a ← read [name] v
    answer g (f (a name))

/-! ## The recheck's first call -/

section RecheckUrls

open Principia.Biblio.Recheck (Planned Entry)

/-- An identifier kind's first-round registry kind (5.21.14), in 5.21.19's order of the
PRIMARY kinds; ISBN and ISSN have none. -/
def firstRound : List (String × String) :=
  [("DOI", "DOI-RA"), ("ARXIV", "ARXIV"), ("PMID", "PMID"), ("PMCID", "PMCID")]

/-- A count member: absent or `null`, its declared value; else a count, or its word. -/
def countOr (ms : List (String × Value)) (name : String) (dflt : Nat) : Except Refusal Nat :=
  match optional ms name with
  | none => .ok dflt
  | some (.int n) => if 0 ≤ n then .ok n.toNat else badArgument name
  | some _ => badArgument name

/-- The declarations: objects, each of a declared kind, kept with their kinds. -/
def readDeclarations (v : Value) : Except Refusal (List (String × Value)) := do
  let xs ← match v with
    | .arr xs => pure xs
    | _ => badArgument "declarations"
  xs.mapM fun
    | .obj ms => match ms.lookup "kind" with
      | some (.str k) => if declKinds.contains k then pure (k, Value.obj ms) else badArgument "declarations"
      | _ => badArgument "declarations"
    | _ => badArgument "declarations"

/-- One identifier's first round: the first declaration of its registry kind, and the URL `url`
builds, or `none` when `url` refuses the identifier. -/
def plan (decls : List (String × Value)) (kind ident : String) : Except Refusal (Option Planned) := do
  let some rk := firstRound.lookup kind | pure none
  let some (_, d) := decls.find? (·.1 == rk) | pure none
  match registryUrl (zoneValue d) (.str ident) with
  | .ok url => pure (some ⟨kind, ident, some (rk, url)⟩)
  | .error (.refused "identifier") => pure (some ⟨kind, ident, none⟩)
  | .error _ => badArgument "declarations"

/-- An entry read on day `today`: its `bib_id`, its CHECK LINE's date, its identifiers'
first rounds. -/
def readEntry (decls : List (String × Value)) (today : Nat) : Value → Except Refusal Entry
  | .obj ms => do
    unless ms.all (fun m => ["bib_id", "identifiers", "check_line"].contains m.1) do badArgument "entries"
    let bib ← match ms.lookup "bib_id" with
      | some (.str b) => if b.isEmpty then badArgument "entries" else pure b
      | _ => badArgument "entries"
    let ids ← match ms.lookup "identifiers" with
      | some (.obj xs) => pure xs
      | _ => badArgument "entries"
    unless ids.all (fun x => identKinds.contains x.1) && (ids.map (·.1)).eraseDups.length == ids.length do
      badArgument "entries"
    let ids ← ids.mapM fun
      | (k, .str t) => pure (k, t)
      | _ => badArgument "entries"
    let day ← match ms.lookup "check_line" with
      | none | some .null => pure none
      | some (.str line) => match Principia.Biblio.Recheck.checkDate line with
        | some d => if today < d then badArgument "check_line" else pure (some d)
        | none => badArgument "check_line"
      | some _ => badArgument "check_line"
    let planned ← firstRound.filterMapM fun (k, _) =>
      match ids.lookup k with
      | some t => plan decls k t
      | none => pure none
    pure ⟨bib, day, planned⟩
  | _ => badArgument "entries"

/-- `recheck_urls`. -/
def recheckUrls (v : Value) : Except Refusal Value := do
  within v
  let ms ← membersOf ["entries", "declarations", "date", "lookups_today", "recheck", "batch", "cap"] v
  let es ← match ← needed ms "entries" with
    | .arr xs => pure xs
    | _ => badArgument "entries"
  let decls ← readDeclarations (← needed ms "declarations")
  let today ← match ← needed ms "date" with
    | .str d => match Principia.Biblio.Recheck.parseDate d with
      | some n => pure n
      | none => badArgument "date"
    | _ => badArgument "date"
  let done ← match ← needed ms "lookups_today" with
    | .int n => if 0 ≤ n then pure n.toNat else badArgument "lookups_today"
    | _ => badArgument "lookups_today"
  let tuning : Principia.Parameters.BibliographyTuning := {}
  let period ← countOr ms "recheck" (tuning.recheck.count / 86400)
  let batch ← countOr ms "batch" tuning.recheckBatch
  let cap ← countOr ms "cap" tuning.lookupCap
  let entries ← es.mapM (readEntry decls today)
  if (entries.map (·.bibId)).eraseDups.length != entries.length then badArgument "entries"
  let c := Principia.Biblio.Recheck.choose today period batch cap done entries
  let due := (Principia.Biblio.Recheck.order today period entries).length
  let lookups := c.taken.flatMap fun e => e.planned.filterMap fun p => p.target.map fun (r, u) =>
    Value.obj [("bib_id", .str e.bibId), ("kind", .str p.kind), ("identifier", .str p.identifier),
      ("registry", .str r), ("url", .str u)]
  let failed := c.taken.flatMap fun e => e.planned.filterMap fun p => if p.target.isSome then none else
    some (Value.obj [("bib_id", .str e.bibId), ("kind", .str p.kind), ("identifier", .str p.identifier)])
  pure (.obj [("lookups", .arr lookups), ("failed", .arr failed),
    ("taken", .arr (c.taken.map fun e => .str e.bibId)), ("due", .int due), ("backlog", .int c.backlog)])

end RecheckUrls

/-- The family's functions. -/
def calls : Family := [
  ("arxiv", textCall "text" arxivParse arxivValue),
  ("canon", fun v => do
    let a ← read entryArgs v
    answer canonValue (biblioCanon (a "bib_id") (a "proposed_by") (a "landed_by") (a "landed")
      (a "supersedes") (a "identifiers") (a "item"))),
  ("check", fun v => do
    let a ← read ["entry", "existing", "caps"] v
    answer checkValue (biblioCheck (a "entry") (a "existing") (a "caps"))),
  ("compare", fun v => do
    let a ← read ["entry", "records", "date"] v
    answer compareValue (do
      let c ← biblioCompare (a "entry") (a "records")
      return (c, ← checkLine c (a "date"), ← noticesLine c (a "date")))),
  ("doi", textCall "text" doiNorm doiValue),
  ("dupe", textCall "identifiers" dupeKey dupeValue),
  ("holdlist", fun v => do
    let a ← read ["entries", "account", "blocks", "checks"] v
    answer pairsValue (biblioHoldList (a "entries") (a "account") (a "blocks") (a "checks"))),
  ("isbn", textCall "text" isbnCheck isbnValue),
  ("issn", textCall "text" issnCheck Value.str),
  ("key", fun v => do
    let a ← read ["text", "kind"] v
    answer Value.str (keyForm (a "text") (a "kind"))),
  ("pmcid", textCall "text" pmcidCheck Value.str),
  ("pmid", textCall "text" pmidCheck Value.str),
  ("preimage", fun v => do
    let a ← read entryArgs v
    answer Value.str (biblioPreimage (a "bib_id") (a "proposed_by") (a "landed_by") (a "landed")
      (a "supersedes") (a "identifiers") (a "item"))),
  ("recheck_urls", recheckUrls),
  ("shape", textCall "text" doiShape Value.bool),
  ("url", fun v => do
    let a ← read ["declaration", "identifier"] v
    answer Value.str (registryUrl (a "declaration") (a "identifier"))),
  ("view", fun v => do
    let a ← read ["records", "entries", "findings"] v
    answer viewValue (literatureView (a "records") (a "entries") (a "findings"))),
  ("withdrawn", textCall "comment" arxivWithdrawn Value.bool),
]

end Principia.Calculator.Biblio
