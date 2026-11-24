import Principia.Biblio
import Principia.CanonicalReader

/-!
# The bibliography recheck's second call: the payloads read, each entry's next state

A recheck run (TPS 5.21.18) makes two starts of the Calculator: `recheck_urls`
(`Principia.Biblio.Recheck`) names the first-round lookups, Custos fetches them, and
`recheck_batch` reads every payload fetched, routes each identifier as TPS 5.21.14 routes it,
compares each entry with its records (`biblioCompare`, 5.21.15) and answers the entry's next
state with the lines to write (5.21.19). This module is that reading and that routing.

**The six payload forms** (the RESPONSE SCHEMAS of the starting six, as the declarations'
record states them, its section 5.8):

* `DOI-RA` (DOI-RA-JSON-1): a JSON array of exactly one object whose `DOI` equals the query
  after A-Z folding; its `RA` names the agency (Crossref goes on to `DOI-CROSSREF`, DataCite to
  `DOI-DATACITE`, any other agency is FOUND UNCOMPARED); a `status` of `DOI does not exist` is
  NOT FOUND; any other answer is LOOKUP FAILED (`agency`).
* `DOI-CROSSREF` (CROSSREF-WORK-JSON-1): `status` `ok`, `message-type` `work`; from `message`
  the year of `issued`'s first date part, `title[0]`, `subtitle[0]`, the first author's
  `family` (else `name`, an organisation), `DOI`, `ISSN`, `ISBN`, and each `updated-by` entry as
  a notice (its `type`, `DOI`, `updated` date and `source`, else `crossref`).
* `DOI-DATACITE` (DATACITE-DOI-JSONAPI-1): from `data.attributes` the `publicationYear`,
  `titles[0].title`, the first creator's `familyName` (an `Organizational` creator, or one
  without it, by `name`), `doi`, and the `identifiers` entry of type `arXiv`.
* `ARXIV` (ARXIV-ATOM-1): an Atom feed; no entry is NOT FOUND; an entry whose `id` is the API's
  error address is NOT FOUND for `incorrect_id_format`, else LOOKUP FAILED (`agency`); otherwise
  exactly one entry, of the arXiv id asked for, giving the year of `updated` (a versioned
  identifier) or `published` (an unversioned one), `title`, the first author's `name` (GIVEN
  FAMILY), `arxiv:doi` bare or as a `doi.org` URL, the retrieved id, and a withdrawal notice
  when `arxiv:comment` holds the token `withdrawn` (`arxivWithdrawn`).
* `PMID` (EUTILS-ESUMMARY-PUBMED-JSON-1): `result.uids` exactly the PMID asked for (none, or a
  summary carrying `error`, is NOT FOUND; a top-level `error` is LOOKUP FAILED), and from
  `result[uid]` the `title`, the first four digits of `pubdate`, `authors[0].name` (FAMILY
  INITIALS), the `articleids` of idtype `doi`, `issn` and `essn`, the publication type
  `Retracted Publication` and the `references` of type `Retraction in` and `Expression of
  concern in` as notices.
* `PMCID` (PMC-IDCONV-JSON-1): exactly one of `records` whose `requested-id` is the PMCID asked
  for, A-Z folded; one reporting an error (`errmsg`, or `status` `error`) is NOT FOUND; its
  `pmid` goes on to `PMID`, whose summary is the PMCID's record.

**Failure.** A lookup with no answer (`answer`), a status outside 200 to 299 (`status`, so a
404 after the agency named the registry is LOOKUP FAILED, RD-6), a payload that does not read
under its form (`payload`), a registry's own failure (`agency`) or a lookup not supplied
(`lookup`) fails its identifier, and an entry with a failed identifier keeps its prior lines:
it is answered FAILED with the first such kind and word, writes nothing, and stays due for the
next run (the note on Custos's jobs, "Failure"). A payload never fails the batch.

**The second round.** Two routes need a second fetch: a DOI whose agency is Crossref or
DataCite, and a PMCID, whose PMID is then summarised. An entry whose second lookup is not yet
supplied is answered PENDING, and the lookup it needs is listed with its URL; Custos fetches
it and calls again with every lookup of the run. No route asks for a third fetch.
-/

namespace Principia.Biblio.Batch

open Principia.Biblio

/-- A value of a payload, read by the Calculator's reader. -/
abbrev J := Principia.Canonical.Value

/-- A value in the form `biblioCompare` reads. -/
abbrev Z := Principia.Zone.Value

/-- The most code points a payload's text holds; a longer one does not read (`payload`). -/
def maxPayload : Nat := 262144

/-! ## Reading a payload -/

/-- A reading that either holds or fails the payload's form. -/
abbrev P := Except Unit

def bad {α : Type} : P α := .error ()

def lift {α : Type} : Option α → P α
  | some a => pure a
  | none => bad

/-- A member of an object; absent or `null` is `none`. -/
def mem (v : J) (k : String) : Option J :=
  match v with
  | .obj ms => match ms.lookup k with
    | some .null => none
    | x => x
  | _ => none

def str? : J → Option String
  | .str s => some s
  | _ => none

def arr? : J → Option (List J)
  | .arr xs => some xs
  | _ => none

def isObj : J → Bool
  | .obj _ => true
  | _ => false

/-- A text, the empty text as none. -/
def nz (s : String) : Option String := if s.isEmpty then none else some s

/-- A member that, when present, is a text. -/
def optText (v : J) (k : String) : P (Option String) :=
  match mem v k with
  | none => pure none
  | some x => (nz ·) <$> lift (str? x)

/-- A member that, when present, is a list of texts. -/
def textList (v : J) (k : String) : P (List String) :=
  match mem v k with
  | none => pure []
  | some x => do
    let xs ← lift (arr? x)
    xs.mapM fun y => lift (str? y)

/-- A member that, when present, is a list of objects. -/
def objList (v : J) (k : String) : P (List J) :=
  match mem v k with
  | none => pure []
  | some x => do
    let xs ← lift (arr? x)
    unless xs.all isObj do bad
    pure xs

/-- A list's first text, when the member is a list of texts. -/
def firstText (v : J) (k : String) : P (Option String) := do
  pure (((← textList v k).head?).bind nz)

/-- Two decimal digits. -/
def pad2 (n : Int) : String := if n < 10 then "0" ++ toString n else toString n

/-- Four decimal digits. -/
def pad4 (n : Int) : String :=
  let s := toString n
  String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- A Crossref date's parts `[[y, m, d]]`: the year, and the calendar date when all three are
given and real. -/
def dateParts (v : J) (k : String) : P (Option Int × Option String) :=
  match mem v k with
  | none => pure (none, none)
  | some d => do
    let some ps := mem d "date-parts" | pure (none, none)
    let outer ← lift (arr? ps)
    let some first := outer.head? | pure (none, none)
    let parts ← lift (arr? first)
    let ints := parts.filterMap fun
      | .int n => some n
      | _ => none
    match ints with
    | [y, m, dd] =>
      let s := pad4 y ++ "-" ++ pad2 m ++ "-" ++ pad2 dd
      pure (some y, if 0 ≤ y && y ≤ 9999 && 0 ≤ m && 0 ≤ dd then calendar? (.str s) else none)
    | y :: _ => pure (some y, none)
    | [] => pure (none, none)

/-- The year a text's first four characters write, when they are four digits. -/
def yearOf (s : String) : Option Int :=
  let cs := s.toList.take 4
  if cs.length == 4 && allDigits cs then some (digitsValue cs) else none

/-- A notice's identifier: a text with no white space, else none (`readNotice`'s rule). -/
def noticeId (s : Option String) : Option String :=
  s.bind fun t => if t == "-" || t.toList.any isSpace then none else nz t

def zopt : Option String → Z
  | some s => .str s
  | none => .null

/-- A FOUND record's fields, in `readFields`'s form. -/
structure Fields where
  year : Option Int := none
  title : Option String := none
  subtitle : Option String := none
  family : Option String := none
  nameForm : String := "FAMILY"
  doi : Option String := none
  issn : List String := []
  isbn : List String := []
  arxivDoi : Option String := none
  arxivId : Option String := none

def Fields.z (f : Fields) : Z :=
  .obj [("year", (f.year.map Principia.Zone.Value.int).getD .null), ("title", zopt f.title),
    ("subtitle", zopt f.subtitle), ("family", zopt f.family),
    ("name_form", if f.family.isSome then .str f.nameForm else .null), ("doi", zopt f.doi),
    ("issn", .arr (f.issn.map .str)), ("isbn", .arr (f.isbn.map .str)),
    ("arxiv_doi", zopt f.arxivDoi), ("arxiv_id", zopt f.arxivId)]

/-- A notice in `readNotice`'s form; its type is put under the key form by the comparison. -/
def noticeZ (type : String) (identifier date : Option String) (source : String) : Z :=
  .obj [("type", .str type), ("identifier", zopt (noticeId identifier)), ("date", zopt date),
    ("source", .str source)]

/-- A registry's found record: its fields and its notices. -/
abbrev Found := Fields × List Z

/-! ### The six forms -/

/-- DOI-RA-JSON-1: `some (some agency)` FOUND, `some none` NOT FOUND, `none` the agency's
own failure. -/
def agency (v : J) (doi : String) : P (Option (Option String)) := do
  let xs ← lift (arr? v)
  let [o] := xs | bad
  unless isObj o do bad
  let some d ← optText o "DOI" | bad
  unless fold d == fold doi do bad
  match ← optText o "RA" with
  | some ra => pure (some (some ra))
  | none =>
    if (← optText o "status") == some "DOI does not exist" then pure (some none) else pure none

/-- CROSSREF-WORK-JSON-1. -/
def crossref (v : J) : P Found := do
  unless (mem v "status").bind str? == some "ok" && (mem v "message-type").bind str? == some "work" do bad
  let m ← lift (mem v "message")
  unless isObj m do bad
  let (year, _) ← dateParts m "issued"
  let family ← match (← objList m "author").head? with
    | some a => do
      match ← optText a "family" with
      | some f => pure (some f)
      | none => optText a "name"
    | none => pure none
  let notices ← (← objList m "updated-by").mapM fun u => do
    let some type ← optText u "type" | bad
    let (_, date) ← dateParts u "updated"
    pure (noticeZ type (← optText u "DOI") date ((← optText u "source").getD "crossref"))
  let title ← firstText m "title"
  let subtitle ← firstText m "subtitle"
  let doi ← optText m "DOI"
  let issn ← textList m "ISSN"
  let isbn ← textList m "ISBN"
  pure ({ year, title, subtitle, family, doi, issn, isbn }, notices)

/-- DATACITE-DOI-JSONAPI-1. -/
def datacite (v : J) : P Found := do
  let d ← lift (mem v "data")
  let a ← lift (mem d "attributes")
  unless isObj a do bad
  let year ← match mem a "publicationYear" with
    | none => pure none
    | some (.int n) => pure (some n)
    | some (.str s) => if s.length == 4 then pure (yearOf s) else bad
    | some _ => bad
  let title ← match (← objList a "titles").head? with
    | some t => optText t "title"
    | none => pure none
  let family ← match (← objList a "creators").head? with
    | some c =>
      if (← optText c "nameType") == some "Organizational" then optText c "name"
      else do
        match ← optText c "familyName" with
        | some f => pure (some f)
        | none => optText c "name"
    | none => pure none
  let arxivId ← (← objList a "identifiers").findSomeM? fun i => do
    if (← optText i "identifierType") == some "arXiv" then optText i "identifier" else pure none
  let doi ← optText a "doi"
  pure ({ year, title, family, doi, arxivId }, [])

/-! ### The Atom feed -/

/-- The contents of every element `tag` of a text, in order (an empty element for `<tag/>`).
The Atom feed's elements nest no element of their own name. -/
def elems (s tag : String) : List String :=
  ((s.splitOn ("<" ++ tag)).drop 1).filterMap fun p =>
    if p.startsWith ">" || p.startsWith " " || p.startsWith "\n" || p.startsWith "/" then
      let pieces := p.splitOn ">"
      if (pieces.headD "").endsWith "/" then some ""
      else some (((String.intercalate ">" (pieces.drop 1)).splitOn ("</" ++ tag ++ ">")).headD "")
    else none

/-- An element's text: the XML entities decoded, white space collapsed, empty as none. -/
def elemText (s tag : String) : Option String :=
  (elems s tag).head?.bind fun t =>
    let d := (String.ofList (decodeEntities t.toList)).map fun c => if isSpace c then ' ' else c
    nz (" ".intercalate ((d.splitOn " ").filter (!·.isEmpty)))

/-- `arxiv:doi`, bare or as a `doi.org` URL. -/
def bareDoi (s : String) : String :=
  match ["https://doi.org/", "http://doi.org/", "https://dx.doi.org/", "http://dx.doi.org/"].find? (fun p => s.startsWith p) with
  | some p => String.ofList (s.toList.drop p.length)
  | none => s

/-- The API's error address. -/
def errorAddress : String := "http://arxiv.org/api/errors"

/-- ARXIV-ATOM-1 for the arXiv id `asked`: `some found`, `none` NOT FOUND; an error entry
other than an incorrect format fails as the agency's (`.ok (.error ())` is not used: the
outer `Except String` carries the word). -/
def arxiv (s : String) (asked : ArxivId) : Except String (Option Found) := do
  unless (elems s "feed").length == 1 do throw "payload"
  match elems s "entry" with
  | [] => pure none
  | [e] =>
    let some id := elemText e "id" | throw "payload"
    if id.startsWith errorAddress then
      if (id.splitOn "incorrect_id_format").length > 1 then pure none else throw "agency"
    else
      let some got := ["http://arxiv.org/abs/", "https://arxiv.org/abs/"].find? (fun p => id.startsWith p)
        | throw "payload"
      let rid := String.ofList (id.toList.drop got.length)
      match arxivParse (.str rid) with
      | .ok a => unless a.key == asked.key do throw "payload"
      | .error _ => throw "payload"
      let updated := elemText e "updated"
      let dated := if asked.version != 0 then updated else elemText e "published"
      let family := (elems e "author").head?.bind (elemText · "name")
      let comment := elemText e "arxiv:comment"
      let withdrawn := match arxivWithdrawn (.str (comment.getD "")) with
        | .ok b => b
        | .error _ => false
      let notices := if withdrawn then
        [noticeZ "withdrawn" (some rid) (updated.bind fun u => calendar? (.str (String.ofList (u.toList.take 10)))) "arxiv"]
        else []
      let f : Fields := { year := dated.bind yearOf, title := elemText e "title", family := family }
      pure (some ({ f with nameForm := "GIVEN FAMILY", arxivDoi := (elemText e "arxiv:doi").map bareDoi, arxivId := some rid }, notices))
  | _ => throw "payload"

/-- EUTILS-ESUMMARY-PUBMED-JSON-1 for the PMID `pmid`: `some found`, `none` NOT FOUND. -/
def esummary (v : J) (pmid : String) : Except String (Option Found) := do
  unless isObj v do throw "payload"
  if (mem v "error").isSome then throw "agency"
  let read {α : Type} (x : P α) : Except String α := match x with
    | .ok a => pure a
    | .error _ => throw "payload"
  let some r := mem v "result" | throw "payload"
  let uids ← read (textList r "uids")
  if uids.isEmpty then return none
  unless uids == [pmid] do throw "payload"
  let some doc := mem r pmid | throw "payload"
  unless isObj doc do throw "payload"
  if (mem doc "error").isSome then return none
  read (do
    let family ← match (← objList doc "authors").head? with
      | some a => optText a "name"
      | none => pure none
    let doi ← (← objList doc "articleids").findSomeM? fun i => do
      if (← optText i "idtype") == some "doi" then optText i "value" else pure none
    let issn := (← [optText doc "issn", optText doc "essn"].mapM id).filterMap id
    let retracted := if (← textList doc "pubtype").contains "Retracted Publication" then
      [noticeZ "Retracted Publication" none none "pubmed"] else []
    let refs ← (← objList doc "references").filterMapM fun x => do
      let some t ← optText x "reftype" | pure none
      if t == "Retraction in" || t == "Expression of concern in" then
        let id ← match mem x "pmid" with
          | some (.str s) => pure (some s)
          | some (.int n) => pure (some (toString n))
          | _ => pure none
        pure (some (noticeZ t id none "pubmed"))
      else pure none
    let year := (← optText doc "pubdate").bind yearOf
    let title ← optText doc "title"
    pure (some ({ year := year, title := title, family := family, nameForm := "FAMILY INITIALS", doi := doi, issn := issn }, retracted ++ refs)))

/-- PMC-IDCONV-JSON-1 for the PMCID `pmcid`: `some pmid` converted, `none` NOT FOUND. -/
def idconv (v : J) (pmcid : String) : Except String (Option String) := do
  let read {α : Type} (x : P α) : Except String α := match x with
    | .ok a => pure a
    | .error _ => throw "payload"
  let recs ← read (objList v "records")
  if (mem v "records").isNone then throw "payload"
  let mine ← recs.filterM fun r => do
    pure ((← read (optText r "requested-id")).map fold == some (fold pmcid))
  let [r] := mine | throw "payload"
  if (mem r "errmsg").isSome || (mem r "status").bind str? == some "error" then return none
  match mem r "pmid" with
  | some (.str s) => pure (some s)
  | some (.int n) => pure (some (toString n))
  | none => throw "agency"
  | some _ => throw "payload"

/-! ## Routing one identifier -/

/-- One lookup Custos made: its HTTP status (`none`: no answer) and the payload's text. -/
structure Lookup where
  status : Option Nat
  text : Option String

/-- A lookup's text, when it answered with a 2xx status and a text within the bound. -/
def body (l : Lookup) : Except String String :=
  match l.status with
  | none => throw "answer"
  | some s =>
    if s < 200 || 300 ≤ s then throw "status"
    else match l.text with
      | some t => if maxPayload < t.length then throw "payload" else pure t
      | none => throw "payload"

/-- A lookup's JSON payload. -/
def json (l : Lookup) : Except String J := do
  match Principia.Canonical.readString (← body l) with
  | .ok v => pure v
  | .error _ => throw "payload"

/-- A form's reading, its failure the word `payload`. -/
def form {α : Type} (x : P α) : Except String α :=
  match x with
  | .ok a => pure a
  | .error _ => throw "payload"

/-- What one identifier comes to: its REGISTRY RECORD, a second lookup owed (the registry kind
and the identifier its URL is built from), or a failure's word. -/
inductive Outcome where
  | record (r : Z)
  | owed (registry identifier : String)
  | failed (word : String)

/-- A REGISTRY RECORD in `readRecord`'s form. -/
def recordZ (kind identifier : String) (registry status : Option String) (found : Option Found)
    (ra : Option Z) : Z :=
  .obj ([("kind", .str kind), ("identifier", .str identifier), ("registry", zopt registry),
    ("status", zopt status), ("fields", (found.map (·.1.z)).getD .null),
    ("notices", .arr ((found.map (·.2)).getD []))] ++
    (match ra with
     | some r => [("ra", r)]
     | none => []))

/-- The record of a found or not-found answer at a registry. -/
def foundOrNot (kind identifier registry : String) (f : Option Found) (ra : Option Z) : Z :=
  recordZ kind identifier (some registry) (some (if f.isSome then "FOUND" else "NOT FOUND")) f ra

/-- The outcome of a computation whose failure is a word. -/
def settle (x : Except String Outcome) : Outcome :=
  match x with
  | .ok o => o
  | .error w => .failed w

/-- One identifier of kind `kind` (normalized `ident`), its lookups found by registry kind. -/
def route (kind ident : String) (find : String → Option Lookup) : Outcome := settle do
  let need (registry : String) : Except String Lookup := match find registry with
    | some l => pure l
    | none => throw "lookup"
  if kind == "DOI" then
    match ← form (agency (← json (← need "DOI-RA")) ident) with
    | none => throw "agency"
    | some none =>
      pure (.record (recordZ "DOI" ident none none none
        (some (.obj [("status", .str "NOT FOUND"), ("ra", .null)]))))
    | some (some ra) =>
      let raZ : Z := .obj [("status", .str "FOUND"), ("ra", .str ra)]
      let second := if ra == "Crossref" then some ("DOI-CROSSREF", "crossref")
        else if ra == "DataCite" then some ("DOI-DATACITE", "datacite") else none
      match second with
      | none => pure (.record (recordZ "DOI" ident none none none (some raZ)))
      | some (rk, name) =>
        match find rk with
        | none => pure (.owed rk ident)
        | some l =>
          let v ← json l
          let f ← form (if rk == "DOI-CROSSREF" then crossref v else datacite v)
          pure (.record (foundOrNot "DOI" ident name (some f) (some raZ)))
  else if kind == "ARXIV" then
    let asked ← match arxivParse (.str ident) with
      | .ok a => pure a
      | .error _ => throw "lookup"
    let f ← arxiv (← body (← need "ARXIV")) asked
    pure (.record (foundOrNot "ARXIV" ident "arxiv" f none))
  else if kind == "PMID" then
    let f ← esummary (← json (← need "PMID")) ident
    pure (.record (foundOrNot "PMID" ident "pubmed" f none))
  else
    match ← idconv (← json (← need "PMCID")) ident with
    | none => pure (.record (foundOrNot "PMCID" ident "pubmed" none none))
    | some pmid =>
      match find "PMID" with
      | none => pure (.owed "PMID" pmid)
      | some l =>
        let f ← esummary (← json l) pmid
        pure (.record (foundOrNot "PMCID" ident "pubmed" f none))

/-! ## An entry's next state -/

/-- An entry's next state. -/
inductive Next where
  /-- The lines to write: the CHECK LINE and the NOTICES LINE (`none`: no notice). -/
  | changed (checkLine : String) (noticesLine : Option String)
  /-- The lines as written: nothing to write. -/
  | unchanged
  /-- A second lookup is owed: each is the identifier kind, the registry kind and the
  identifier its URL is built from. -/
  | pending (owed : List (String × String × String))
  /-- A lookup failed: the prior lines are kept; the kind and the word. -/
  | failed (kind word : String)
  /-- The entry itself does not read: the comparison's word. -/
  | refused (word : String)

/-- The state of one entry (`item`, `ids` as the comparison reads them) on `date`, its lines
as written, its lookups found by identifier kind and registry kind. -/
def next (item identifiers : Z) (written : Option String × Option String) (date : String)
    (find : String → String → Option Lookup) : Next :=
  let entry : Z := .obj [("item", item), ("identifiers", identifiers)]
  match biblioCompare entry (.arr []), readIdentifiers identifiers with
  | .error (.refused w), _ => .refused w
  | _, .error (.refused w) => .refused w
  | .ok _, .ok ids =>
    let outs := primaryOrder.filterMap fun k => (ids.get k).map fun i => (k, route k i (find k))
    match outs.findSome? fun (k, o) => match o with
      | .failed w => some (k, w)
      | _ => none with
    | some (k, w) => .failed k w
    | none =>
      let owed := outs.filterMap fun (k, o) => match o with
        | .owed r i => some (k, r, i)
        | _ => none
      if !owed.isEmpty then .pending owed
      else
        let recs := outs.filterMap fun (_, o) => match o with
          | .record r => some r
          | _ => none
        match biblioCompare entry (.arr recs) with
        | .error _ => .failed "" "payload"
        | .ok c =>
          match checkLine c (.str date), noticesLine c (.str date) with
          | .ok cl, .ok nl =>
            let nl := nz nl
            if written.1 == some cl && written.2 == nl then .unchanged else .changed cl nl
          | _, _ => .refused "date"

end Principia.Biblio.Batch
