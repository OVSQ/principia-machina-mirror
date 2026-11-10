import Principia.Digest
import Principia.Zone.Fields
import Principia.Biblio.Table

/-!
# Bibliography: identifiers, the key form, the write check, the canonical entry, the
# registry URL and comparison, the literature view and the hold list

v1's `tpc_biblio` 0.2.0 (the zone bibliography), the UWC bibliography's pure
functions, each reading its arguments as parsed JSON (`Principia.Zone.Value`):

* the identifier checks `doiNorm`, `doiShape`, `arxivParse`, `isbnCheck`, `issnCheck`,
  `pmidCheck`, `pmcidCheck` (RD-5);
* the key form `keyForm` (RD-9), and the duplicate key `dupeKey` (RD-20);
* the write check `biblioCheck` (checks BC1 to BC9);
* the canonical entry `biblioCanon` and its preimage `biblioPreimage`;
* `registryUrl`, `biblioCompare` with the CHECK and NOTICES lines
  `arxivWithdrawn`;
* `literatureView` and `biblioHoldList`.

A refused argument is v1's `ValueError`, its short fixed message as written. Text is read as
v1 read it, at Unicode 15.1.0 (the Declarer's choice of Unicode version): the zones'
text rule (`_first_bad`, `_text`: line endings as LF, then NFC; `Principia.Zone.Text`) and
the key form's NFD and NFC (`Principia.Unicode`). The canonical entry's digest is SHA-256
over its field list's netstring (`Principia.Digest.digestFields`, `Principia.Sha256`; the Declarer's
choice of SHA-256).
-/

namespace Principia.Biblio

open Principia.Zone
open Principia.Digest

/-! ## Results -/

/-- Why a check stops: v1's refusal. -/
inductive Fault where
  | refused (message : String)
  deriving DecidableEq, Repr

/-- A check: its answer, or the fault that stops it. -/
abbrev Check (α : Type) := Except Fault α

/-- v1's `raise ValueError(message)`. -/
def refuse {α : Type} (message : String) : Check α := throw (.refused message)

/-- v1's `try: ... except ValueError: raise ValueError(message)`: a refusal takes the new
message. -/
def relabel {α : Type} (message : String) : Check α → Check α
  | .error (.refused _) => .error (.refused message)
  | r => r

/-- v1's `try: ... except ValueError: ...`: a refusal is `none`. -/
def attempt {α : Type} : Check α → Check (Option α)
  | .ok a => .ok (some a)
  | .error (.refused _) => .ok none

/-! ## Text: the zones' rules, ASCII, the table's classes

v1's `_first_bad` and `_text` are the zones' (`Principia.Zone.firstBad`,
`Principia.Zone.text`). -/

/-- v1 `_is_text`: a non-empty string with no disallowed code point. -/
def isText (v : Value) : Check Bool :=
  match v with
  | .str s => if s.isEmpty then pure false else pure (firstBad s).isNone
  | _ => pure false

/-- The string of a value v1 has checked with `_is_text`. -/
def text? (v : Value) : Check (Option String) := do
  match v with
  | .str s => if ← isText v then return some s else return none
  | _ => return none

/-- v1 `_fold`: A-Z to a-z, every other code point as it is. -/
def fold (s : String) : String :=
  s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def isHexDigit (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- A non-empty run of ASCII digits. -/
def allDigits (s : List Char) : Bool := !s.isEmpty && s.all isDigit

/-- The value of ASCII digits. -/
def digitsValue (s : List Char) : Nat := s.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- v1 `_is_space`: TAB, LF, CR, or a code point of the table's class Z. -/
def isSpace (c : Char) : Bool := c == '\t' || c == '\n' || c == '\r' || ucls c == some 'Z'

/-- The text after an ASCII-case-insensitive prefix (`[hH][tT]...`), whose own characters
are ASCII lower-case letters and punctuation. -/
def dropFolded? (s : String) (pre : String) : Option String :=
  if fold (String.ofList (s.toList.take pre.length)) == pre then
    some (String.ofList (s.toList.drop pre.length))
  else none

/-! ## Identifiers (RD-5) -/

/-- What a DOI stands for. -/
inductive DoiKind where
  | doi
  /-- An arXiv DOI (prefix 10.48550, DataCite's, BR F19). -/
  | arxiv
  deriving DecidableEq, Repr

def DoiKind.text : DoiKind → String
  | .doi => "DOI"
  | .arxiv => "ARXIV"

/-- v1 `doi_norm`'s answer. -/
structure DoiNorm where
  /-- The DOI as given after its wrapper, NFC. -/
  doi : String
  kind : DoiKind
  /-- The folded DOI, the duplicate key; for an arXiv DOI, the arXiv id. -/
  id : String
  deriving DecidableEq, Repr

/-- The arXiv numbering scheme. -/
inductive Scheme where
  | new
  | old
  deriving DecidableEq, Repr

def Scheme.text : Scheme → String
  | .new => "NEW"
  | .old => "OLD"

/-- v1 `arxiv_parse`'s answer. -/
structure ArxivId where
  /-- The id with its version, as given. -/
  id : String
  /-- The version; 0 when none is given. -/
  version : Nat
  /-- The id without its version. -/
  key : String
  scheme : Scheme
  deriving DecidableEq, Repr

/-- v1 `_pct_decode_once`: one percent-decoding; `none` when a `%` is not followed by two
hexadecimal digits or the bytes are not UTF-8. -/
def pctDecodeOnce (s : String) : Option String :=
  let rec go : List UInt8 → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | b :: rest, acc =>
      if b == 0x25 then
        match rest with
        | h1 :: h2 :: more =>
          let c1 := Char.ofNat h1.toNat
          let c2 := Char.ofNat h2.toNat
          if isHexDigit c1 && isHexDigit c2 then
            match hexValue? (String.ofList [c1, c2]).toUpper with
            | some v => go more (v.toUInt8 :: acc)
            | none => none
          else none
        | _ => none
      else go rest (b :: acc)
  (go s.toUTF8.toList []).bind fun bytes => String.fromUTF8? (ByteArray.mk bytes.toArray)

/-- v1 `_graphic`: no disallowed code point (the zones' text safety), and no TAB, LF, CR or
code point of the table's classes Z, C or F. -/
def graphic (s : String) : Check Bool := do
  if (firstBad s).isSome then return false
  return s.toList.all fun c =>
    !(c == '\t' || c == '\n' || c == '\r' ||
      match ucls c with
      | some k => k == 'Z' || k == 'C' || k == 'F'
      | none => false)

/-- The registrant code `[0-9]+(\.[0-9]+)*`. -/
def registrantOk (reg : List Char) : Bool :=
  (String.ofList reg).splitOn "." |>.all fun g => allDigits g.toList

/-- v1 `_doi_split`: a DOI's prefix and suffix, `10.` + registrant + `/` + a non-empty
suffix of graphic code points. -/
def doiSplit (s : String) : Check (Option (String × String)) := do
  if s.isEmpty then return none
  unless ← graphic s do return none
  match s.toList with
  | '1' :: '0' :: '.' :: rest =>
    let reg := rest.takeWhile (· != '/')
    let suffix := rest.drop (reg.length + 1)
    if reg.length == rest.length || !registrantOk reg || suffix.isEmpty then return none
    return some ("10." ++ String.ofList reg, String.ofList suffix)
  | _ => return none

/-- v1 `doi_shape`: the shape alone, no wrapper; a value that is not a string is false. -/
def doiShape (v : Value) : Check Bool :=
  match v with
  | .str s => return (← doiSplit s).isSome
  | _ => pure false

/-- `v[1-9][0-9]*` at the end of an id, or nothing: the version, 0 for none. -/
def version? : List Char → Option Nat
  | [] => some 0
  | 'v' :: d :: ds => if d != '0' && allDigits (d :: ds) then some (digitsValue (d :: ds)) else none
  | _ => none

/-- The NEW scheme, `YYMM.NNNN` (YYMM 0704 to 1412) or `YYMM.NNNNN` (YYMM 1501 on), with an
optional version. -/
def arxivNew? (s : String) : Option (Check ArxivId) :=
  match s.toList with
  | y1 :: y2 :: m1 :: m2 :: '.' :: rest =>
    if !allDigits [y1, y2, m1, m2] then none
    else
      let nn := rest.takeWhile isDigit
      if nn.length != 4 && nn.length != 5 then none
      else match version? (rest.drop nn.length) with
        | none => none
        | some v =>
          let yymm := digitsValue [y1, y2, m1, m2]
          let mm := digitsValue [m1, m2]
          some (do
            if mm < 1 || mm > 12 then refuse "arxiv"
            if nn.length == 4 && (yymm < 704 || yymm > 1412) then refuse "arxiv"
            if nn.length == 5 && yymm < 1501 then refuse "arxiv"
            return { id := s, version := v, key := String.ofList ([y1, y2, m1, m2, '.'] ++ nn),
                     scheme := .new })
  | _ => none

/-- The OLD scheme's archive, `[a-z][a-z-]{1,15}`. -/
def archiveOk : List Char → Bool
  | c :: cs =>
    isLower c && 1 ≤ cs.length && cs.length ≤ 15 && cs.all fun d => isLower d || d == '-'
  | [] => false

/-- v1's two-digit years of the OLD scheme. -/
def oldYears : List String :=
  ["91", "92", "93", "94", "95", "96", "97", "98", "99", "00", "01", "02", "03", "04", "05",
   "06", "07"]

/-- The OLD scheme, `archive[.SC]/YYMMNNN`, with an optional version. -/
def arxivOld? (s : String) : Option (Check ArxivId) :=
  let cs := s.toList
  let before := cs.takeWhile (· != '/')
  if before.length == cs.length then none
  else
    let after := cs.drop (before.length + 1)
    let (arch, sc) := match (String.ofList before).splitOn "." with
      | [a] => (a.toList, some [])
      | [a, c] => if c.length == 2 && c.toList.all isUpper then (a.toList, some ('.' :: c.toList))
                  else ([], none)
      | _ => ([], none)
    match sc with
    | none => none
    | some sc =>
      if !archiveOk arch || after.length < 7 || !allDigits (after.take 7) then none
      else match version? (after.drop 7) with
        | none => none
        | some v =>
          let yy := String.ofList (after.take 2)
          let mm := String.ofList ((after.drop 2).take 2)
          some (do
            if !oldYears.contains yy || mm < "01" || mm > "12" then refuse "arxiv"
            if yy == "07" && mm > "03" then refuse "arxiv"
            return { id := s, version := v,
                     key := String.ofList (arch ++ sc ++ ['/'] ++ after.take 7),
                     scheme := .old })

/-- v1 `arxiv_parse`. -/
def arxivParse (v : Value) : Check ArxivId := do
  let .str text := v | refuse "arxiv"
  let s := match dropFolded? text "arxiv:" with
    | some rest => rest
    | none =>
      match (dropFolded? text "https://arxiv.org/" <|> dropFolded? text "http://arxiv.org/") with
      | some rest => if rest.startsWith "abs/" then String.ofList (rest.toList.drop 4) else text
      | none => text
  match arxivNew? s with
  | some r => r
  | none => match arxivOld? s with
    | some r => r
    | none => refuse "arxiv"

/-- The arXiv DOI's prefix. -/
def arxivDoiPrefix : String := "10.48550"

/-- v1 `doi_norm`: strip one wrapper (`doi:`, or a doi.org or dx.doi.org URL, decoded once),
apply the zones' text rule, then the shape; an arXiv DOI's suffix must be `arXiv.` and an
id `arxiv_parse` accepts. -/
def doiNorm (v : Value) : Check DoiNorm := do
  let .str text := v | refuse "doi"
  let s ← match dropFolded? text "doi:" with
    | some rest => pure rest
    | none =>
      let url :=
        ["https://dx.doi.org/", "http://dx.doi.org/", "https://doi.org/", "http://doi.org/"]
      match url.findSome? (dropFolded? text) with
      | some rest => match pctDecodeOnce rest with
        | some d => pure d
        | none => refuse "doi"
      | none => pure text
  let s := Zone.text s
  let some (pre, suffix) ← doiSplit s | refuse "doi"
  if pre == arxivDoiPrefix then
    let some rest := dropFolded? suffix "arxiv." | refuse "doi"
    let a ← relabel "doi" (arxivParse (.str rest))
    return { doi := s, kind := .arxiv, id := a.id }
  return { doi := s, kind := .doi, id := fold s }

/-- v1 `isbn_check`'s answer. -/
structure Isbn where
  isbn13 : String
  /-- Given as an ISBN-10 (`true`) or an ISBN-13. -/
  givenTen : Bool
  deriving DecidableEq, Repr

/-- The ISBN-13 check digit of twelve digits. -/
def isbn13Check (twelve : List Char) : Char :=
  let total := (twelve.zipIdx).foldl (fun t (c, i) =>
    t + (if i % 2 == 0 then 1 else 3) * (c.toNat - '0'.toNat)) 0
  Char.ofNat ('0'.toNat + (10 - total % 10) % 10)

/-- v1 `isbn_check`: ASCII hyphens and spaces removed; an ISBN-10 (weights 10 to 1, the sum
a multiple of 11) is converted to 13, an ISBN-13 (978 or 979) checked. -/
def isbnCheck (v : Value) : Check Isbn := do
  let .str text := v | refuse "isbn"
  let s := text.toList.filter fun c => c != '-' && c != ' '
  if s.length == 10 && allDigits (s.take 9) && (isDigit s[9]! || s[9]! == 'X' || s[9]! == 'x') then
    let nine := s.take 9
    let total := (nine.zipIdx).foldl (fun t (c, i) => t + (10 - i) * (c.toNat - '0'.toNat)) 0
      + (if s[9]! == 'X' || s[9]! == 'x' then 10 else s[9]!.toNat - '0'.toNat)
    if total % 11 != 0 then refuse "isbn"
    let twelve := ['9', '7', '8'] ++ nine
    return { isbn13 := String.ofList (twelve ++ [isbn13Check twelve]), givenTen := true }
  if s.length == 13 && allDigits s &&
      (s.take 3 == ['9', '7', '8'] || s.take 3 == ['9', '7', '9']) then
    if isbn13Check (s.take 12) != s[12]! then refuse "isbn"
    return { isbn13 := String.ofList s, givenTen := false }
  refuse "isbn"

/-- v1 `issn_check`: `NNNN-NNNC`, weights 8 to 2, X for 10; returned with X upper. -/
def issnCheck (v : Value) : Check String := do
  let .str text := v | refuse "issn"
  let s := text.toList
  if !(s.length == 9 && allDigits (s.take 4) && s[4]! == '-' && allDigits ((s.drop 5).take 3) &&
      (isDigit s[8]! || s[8]! == 'X' || s[8]! == 'x')) then refuse "issn"
  let seven := s.take 4 ++ (s.drop 5).take 3
  let total := (seven.zipIdx).foldl (fun t (c, i) => t + (8 - i) * (c.toNat - '0'.toNat)) 0
  let r := total % 11
  let c := if r == 0 then 0 else 11 - r
  let want := if c == 10 then 'X' else Char.ofNat ('0'.toNat + c)
  let given := if s[8]! == 'x' then 'X' else s[8]!
  if given != want then refuse "issn"
  return String.ofList (s.take 8 ++ [want])

/-- v1 `pmid_check`: decimal digits, no leading zero. -/
def pmidCheck (v : Value) : Check String := do
  let .str text := v | refuse "pmid"
  match text.toList with
  | d :: ds => if d != '0' && allDigits (d :: ds) then return text else refuse "pmid"
  | [] => refuse "pmid"

/-- v1 `pmcid_check`: `PMC` in any ASCII case and decimal digits; returned with `PMC` upper. -/
def pmcidCheck (v : Value) : Check String := do
  let .str text := v | refuse "pmcid"
  match dropFolded? text "pmc" with
  | some ds => if allDigits ds.toList then return "PMC" ++ ds else refuse "pmcid"
  | none => refuse "pmcid"

/-! ## The key form (RD-9) -/

/-- KF0's closed set of title markers, longest first where one extends another. -/
def markers : List String := ["RETRACTED ARTICLE", "RETRACTED", "WITHDRAWN ARTICLE", "WITHDRAWN"]

/-- KF0 (a title only): after leading white space, one marker followed by `:` is removed
once (v1 `_strip_marker`). -/
def stripMarker (s : String) : String :=
  let rest := s.toList.dropWhile isSpace
  let up := fold (String.ofList rest)
  match markers.find? (fun mk => up.startsWith (fold mk ++ ":")) with
  | some mk => String.ofList (rest.drop (mk.length + 1))
  | none => s

/-- The text after the first `>`. -/
def afterClose : List Char → List Char
  | [] => []
  | '>' :: rest => rest
  | _ :: rest => afterClose rest

theorem afterClose_le : ∀ l : List Char, (afterClose l).length ≤ l.length
  | [] => by simp [afterClose]
  | c :: rest => by
    by_cases h : c = '>'
    · subst h; simp [afterClose]
    · have := afterClose_le rest
      simp only [afterClose]; simp; omega

/-- KF1: every markup run `<` + an ASCII letter or `/` ... up to the next `>` removed
(v1's `<[A-Za-z/][^>]*>`, left to right). -/
def stripMarkup (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '<' :: c :: rest =>
    if (isLower c || isUpper c || c == '/') && rest.contains '>' then
      have := afterClose_le rest
      stripMarkup (afterClose rest)
    else '<' :: stripMarkup (c :: rest)
  | c :: rest => c :: stripMarkup rest
termination_by cs.length
decreasing_by all_goals simp_wf <;> omega

/-- KF2's named entities. -/
def namedEntity? : String → Option Char
  | "amp" => some '&'
  | "lt" => some '<'
  | "gt" => some '>'
  | "quot" => some '"'
  | "apos" => some '\''
  | _ => none

/-- An entity's closing `;`: the body, and what follows the `;`. -/
def entityEnd (body : List Char) : List Char → Option (List Char × List Char)
  | ';' :: after => some (body, after)
  | _ => none

theorem entityEnd_shorter {body more b a : List Char} (h : entityEnd body more = some (b, a)) :
    a.length < more.length := by
  unfold entityEnd at h
  split at h <;> simp_all

/-- ASCII letters. -/
def isLetter (c : Char) : Bool := isLower c || isUpper c

/-- An entity body after `&`, up to its `;`: `#` digits, `#x` hexadecimal digits, or ASCII
letters (v1's `&(#[0-9]+|#[xX][0-9A-Fa-f]+|[A-Za-z]+);`); the body and what follows `;`. -/
def entityAt? (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | '#' :: x :: hs =>
    if !((x :: hs).takeWhile isDigit).isEmpty then
      entityEnd ('#' :: (x :: hs).takeWhile isDigit)
        ((x :: hs).drop ((x :: hs).takeWhile isDigit).length)
    else if (x == 'x' || x == 'X') && !(hs.takeWhile isHexDigit).isEmpty then
      entityEnd ('#' :: x :: hs.takeWhile isHexDigit) (hs.drop (hs.takeWhile isHexDigit).length)
    else none
  | _ =>
    if (cs.takeWhile isLetter).isEmpty then none
    else entityEnd (cs.takeWhile isLetter) (cs.drop (cs.takeWhile isLetter).length)

/-- What follows an entity is shorter than the text it was read from. -/
theorem entityAt?_shorter (cs body after : List Char) (h : entityAt? cs = some (body, after)) :
    after.length < cs.length := by
  unfold entityAt? at h
  split at h
  · split at h
    · have := entityEnd_shorter h
      simp only [List.length_drop, List.length_cons] at this ⊢
      omega
    · split at h
      · have := entityEnd_shorter h
        simp only [List.length_drop, List.length_cons] at this ⊢
        omega
      · simp at h
  · split at h
    · simp at h
    · have := entityEnd_shorter h
      simp only [List.length_drop] at this
      omega

/-- v1 `_entity`: a named entity of the five, or a numeric one naming a scalar value at most
10FFFF (no more than 7 decimal or 6 hexadecimal digits); any other stays as written. -/
def entityText (body : List Char) : List Char :=
  let kept := '&' :: body ++ [';']
  match body with
  | '#' :: x :: hs =>
    let value :=
      if x == 'x' || x == 'X' then
        (if hs.length > 6 then none else hexValue? (String.ofList hs).toUpper)
      else (if hs.length + 1 > 7 then none else some (digitsValue (x :: hs)))
    match value with
    | some cp => if cp > 0x10FFFF || (0xD800 ≤ cp && cp ≤ 0xDFFF) then kept else [Char.ofNat cp]
    | none => kept
  | _ => match namedEntity? (String.ofList body) with
    | some c => [c]
    | none => kept

/-- KF2: entities decoded left to right; a decoded text is not read again. -/
def decodeEntities (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '&' :: rest =>
    match h : entityAt? rest with
    | some (body, after) =>
      have := entityAt?_shorter rest body after h
      entityText body ++ decodeEntities after
    | none => '&' :: decodeEntities rest
  | c :: rest => c :: decodeEntities rest
termination_by cs.length
decreasing_by all_goals simp_wf <;> omega

/-- KF0 to KF2 of a text, the markup and the entities, before its NFD. -/
def keyFormBase (text : String) (title : Bool) : List Char :=
  let s := if title then stripMarker text else text
  decodeEntities (stripMarkup s.toList)

/-- KF3 to KF5 over the NFD of a text: the table's classes M, P, S, F and C removed, TAB,
LF, CR and class Z read as a space; A-Z folded; NFC; spaces collapsed and trimmed. -/
def keyFormOfNfd (cs : List Char) : String :=
  let kept := cs.filterMap fun c =>
    if isSpace c then some ' '
    else match ucls c with
      | some k => if "MPSFC".toList.contains k then none else some c
      | none => some c
  let folded := Unicode.nfc (fold (String.ofList kept))
  " ".intercalate ((folded.splitOn " ").filter (· != ""))

/-- v1 `biblio_key_form` over a text: KF0 for a title, KF1, KF2, then KF3 to KF5 (NFD; the
table's classes M, P, S, F and C removed, TAB, LF, CR and class Z read as a space; A-Z
folded; NFC; spaces collapsed and trimmed), at Unicode 15.1.0. -/
def keyFormText (text : String) (title : Bool) : String :=
  keyFormOfNfd (Unicode.nfdList (keyFormBase text title))

/-- v1 `biblio_key_form`: `kind` is `title` or `name`. -/
def keyForm (text kind : Value) : Check String := do
  let title ← match kind with
    | .str "title" => pure true
    | .str "name" => pure false
    | _ => refuse "key"
  let .str t := text | refuse "key"
  pure (keyFormText t title)

/-! ## The CSL item (BC1 to BC5) -/

/-- RD-3: the CSL data schema 1.0 subset, in serialization order (40 keys). -/
def cslKeys : List String :=
  ["type", "id", "title", "title-short", "author", "editor", "translator", "container-author",
   "collection-editor", "issued", "accessed", "original-date", "container-title",
   "container-title-short", "collection-title", "collection-number", "publisher",
   "publisher-place", "volume", "issue", "page", "number", "number-of-pages", "edition",
   "genre", "medium", "event-title", "event-place", "chapter-number", "version", "language",
   "DOI", "ISBN", "ISSN", "PMID", "PMCID", "URL", "original-title", "archive",
   "archive_location"]

def nameRoles : List String :=
  ["author", "editor", "translator", "container-author", "collection-editor"]

def dateFields : List String := ["issued", "accessed", "original-date"]

def nameKeys : List String :=
  ["family", "given", "dropping-particle", "non-dropping-particle", "suffix", "literal"]

def dateKeys : List String := ["date-parts", "circa"]

/-- The 45 CSL types. -/
def cslTypes : List String :=
  ["article", "article-journal", "article-magazine", "article-newspaper", "bill", "book",
   "broadcast", "chapter", "classic", "collection", "dataset", "document", "entry",
   "entry-dictionary", "entry-encyclopedia", "event", "figure", "graphic", "hearing",
   "interview", "legal_case", "legislation", "manuscript", "map", "motion_picture",
   "musical_score", "pamphlet", "paper-conference", "patent", "performance", "periodical",
   "personal_communication", "post", "post-weblog", "regulation", "report", "review",
   "review-book", "software", "song", "speech", "standard", "thesis", "treaty", "webpage"]

/-- A field of a read item. -/
inductive ItemValue where
  | text (s : String)
  /-- A role's names, each its parts in `nameKeys` order. -/
  | names (ns : List (List (String × String)))
  | date (parts : List (List Int)) (circa : Option Bool)
  deriving DecidableEq, Repr

/-- A read item: its fields in `cslKeys` order. -/
abbrev Item := List (String × ItemValue)

/-- v1 `_keys_within` for an object: every key is allowed. -/
def keysWithin (e : Entry) (allowed : List String) : Bool := e.all fun (k, _) => allowed.contains k

/-- An integer in a closed range (v1 `_is_int`: a boolean is none). -/
def intIn (v : Value) (lo hi : Int) : Bool :=
  match v with
  | .int n => lo ≤ n && n ≤ hi
  | _ => false

/-- A string field: not empty, no disallowed code point, the text rule applied. -/
def readText (field : String) (v : Value) : Check String := do
  let .str s := v | refuse ("type:" ++ field)
  if s.isEmpty then refuse ("type:" ++ field)
  if (firstBad s).isSome then refuse ("text:" ++ field)
  pure (Zone.text s)

/-- v1 `_read_names`: a list of objects, each with non-empty string parts and a family or a
literal. -/
def readNames (role : String) (v : Value) : Check (List (List (String × String))) := do
  let .arr xs := v | refuse ("type:" ++ role)
  xs.mapM fun nm => do
    let .obj e := nm | refuse ("type:" ++ role)
    unless keysWithin e nameKeys do refuse ("subset:" ++ role)
    let parts ← nameKeys.filterMapM fun k => do
      match get? e k with
      | none => pure none
      | some x => return some (k, ← readText role x)
    unless parts.any (fun p => p.1 == "family" || p.1 == "literal") do refuse ("type:" ++ role)
    return parts

/-- A date part's bounds by position: year, month, day. -/
def datePartOk (x : Value) (i : Nat) : Bool :=
  if i == 0 then intIn x (-9999) 9999 else if i == 1 then intIn x 1 12 else intIn x 1 31

/-- v1 `_read_date`: `date-parts`, one or two lists of one to three integers (year -9999 to
9999, month 1 to 12, day 1 to 31), and an optional boolean `circa`. -/
def readDate (field : String) (v : Value) : Check ItemValue := do
  let .obj e := v | refuse ("type:" ++ field)
  unless keysWithin e dateKeys do refuse ("subset:" ++ field)
  let some (.arr dp) := get? e "date-parts" | refuse ("type:" ++ field)
  if dp.length < 1 || dp.length > 2 then refuse ("type:" ++ field)
  let parts ← dp.mapM fun p => do
    let .arr q := p | refuse ("type:" ++ field)
    unless 1 ≤ q.length && q.length ≤ 3 && q.zipIdx.all (fun (x, i) => datePartOk x i) do
      refuse ("type:" ++ field)
    return q.filterMap fun
      | .int n => some n
      | _ => none
  let circa ← match get? e "circa" with
    | none => pure none
    | some (.bool b) => pure (some b)
    | some _ => refuse ("type:" ++ field)
  return .date parts circa

/-- v1 `_read_item` (BC1 to BC3): the item's fields in `cslKeys` order, strings under the
text rule. -/
def readItem (v : Value) : Check Item := do
  let .obj e := v | refuse "type:item"
  for (k, _) in e do
    unless cslKeys.contains k do refuse ("subset:" ++ k)
  cslKeys.filterMapM fun k => do
    match get? e k with
    | none => pure none
    | some x =>
      if nameRoles.contains k then return some (k, .names (← readNames k x))
      else if dateFields.contains k then return some (k, ← readDate k x)
      else
        let t ← readText k x
        if k == "type" && !cslTypes.contains t then refuse "type:type"
        return some (k, .text t)

/-- A read item's string field. -/
def textOf (o : Item) (k : String) : Option String :=
  match o.lookup k with
  | some (.text s) => some s
  | _ => none

/-- A read item's names of a role, empty when absent. -/
def namesOf (o : Item) (k : String) : List (List (String × String)) :=
  match o.lookup k with
  | some (.names ns) => ns
  | _ => []

/-- v1 `_require` (BC4): type, title, issued, and an author or editor. -/
def require (o : Item) : Check Unit := do
  for k in ["type", "title", "issued"] do
    unless (o.lookup k).isSome do refuse ("required:" ++ k)
  if (namesOf o "author").isEmpty && (namesOf o "editor").isEmpty then refuse "required:author"

/-- RD-4's caps, supplied by Custos (the tuning option BIBLIO ENTRY MAX and the field caps). -/
structure Caps where
  entryMax : Nat
  title : Nat
  text : Nat
  name : Nat
  url : Nat
  names : Nat
  deriving DecidableEq, Repr

/-- v1 `_read_caps`: exactly the six caps, each an integer 1 to 10^9. -/
def readCaps (v : Value) : Check Caps := do
  let .obj e := v | refuse "caps"
  unless keysWithin e ["entry_max", "title", "text", "name", "url", "names"] && e.length == 6 do
    refuse "caps"
  for (_, x) in e do
    unless intIn x 1 1000000000 do refuse "caps"
  let n (k : String) : Nat := match get? e k with
    | some (.int i) => i.toNat
    | _ => 0
  return { entryMax := n "entry_max", title := n "title", text := n "text", name := n "name",
           url := n "url", names := n "names" }

/-- v1 `_caps_ok` (BC5): lengths in code points after the text rule. -/
def capsOk (o : Item) (caps : Caps) : Check Unit := do
  for (k, v) in o do
    match v with
    | .names ns =>
      if ns.length > caps.names then refuse ("cap:" ++ k)
      for nm in ns do
        for (_, p) in nm do
          if p.length > caps.name then refuse ("cap:" ++ k)
    | .date _ _ => pure ()
    | .text s =>
      let lim := if k == "title" then caps.title else if k == "URL" then caps.url else caps.text
      if s.length > lim then refuse ("cap:" ++ k)

/-! ## The canonical JSON of an item (RD-11) -/

/-- Four lower-case hexadecimal digits. -/
def hex4Lower (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

/-- v1 `_json_str`: `"` and `\` escaped, a control character as `\u00xx`. -/
def jsonStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 then "\\u" ++ hex4Lower c.toNat
    else c.toString) ++ "\""

/-- One field's canonical JSON. -/
def ItemValue.json : ItemValue → String
  | .text s => jsonStr s
  | .names ns => "[" ++ ",".intercalate (ns.map fun nm =>
      "{" ++ ",".intercalate (nm.map fun (k, v) => jsonStr k ++ ":" ++ jsonStr v) ++ "}") ++ "]"
  | .date parts circa =>
    "{\"date-parts\":[" ++ ",".intercalate (parts.map fun p =>
      "[" ++ ",".intercalate (p.map toString) ++ "]") ++ "]" ++
    (match circa with
     | some b => ",\"circa\":" ++ (if b then "true" else "false")
     | none => "") ++ "}"

/-- v1 `_canon_json`: the item as canonical JSON, no white space outside strings. -/
def canonJson (o : Item) : String :=
  "{" ++ ",".intercalate (o.map fun (k, v) => jsonStr k ++ ":" ++ v.json) ++ "}"

/-! ## Identifiers of an entry, the duplicate key (RD-5, RD-20) -/

/-- RD-5's kinds in the digest's and the render's fixed order. -/
def identKinds : List String := ["DOI", "ARXIV", "ISBN", "ISSN", "PMID", "PMCID"]

/-- An entry's identifiers in their stored forms: the DOI as given (NFC), the arXiv id with
its version, the ISBN-13, the ISSN with X upper, the PMID, the PMCID upper. -/
structure Identifiers where
  doi : Option String := none
  arxiv : Option String := none
  isbn : Option String := none
  issn : Option String := none
  pmid : Option String := none
  pmcid : Option String := none
  deriving DecidableEq, Repr

/-- The identifier of a kind. -/
def Identifiers.get (ids : Identifiers) : String → Option String
  | "DOI" => ids.doi
  | "ARXIV" => ids.arxiv
  | "ISBN" => ids.isbn
  | "ISSN" => ids.issn
  | "PMID" => ids.pmid
  | "PMCID" => ids.pmcid
  | _ => none

/-- v1 `_read_identifiers` (BC6). -/
def readIdentifiers (v : Value) : Check Identifiers := do
  let .obj e := v | refuse "identifiers"
  unless keysWithin e identKinds do refuse "identifiers"
  let one (k : String) (f : Value → Check String) : Check (Option String) :=
    match get? e k with
    | none => pure none
    | some x => some <$> relabel ("identifier:" ++ k) (f x)
  let doi ← one "DOI" fun x => do
    let d ← doiNorm x
    if d.kind != .doi then refuse "doi"
    return d.doi
  let arxiv ← one "ARXIV" fun x => (·.id) <$> arxivParse x
  let isbn ← one "ISBN" fun x => (·.isbn13) <$> isbnCheck x
  let issn ← one "ISSN" issnCheck
  let pmid ← one "PMID" pmidCheck
  let pmcid ← one "PMCID" pmcidCheck
  return { doi, arxiv, isbn, issn, pmid, pmcid }

/-- v1 `biblio_dupe_key`'s answer: the kind is DOI, ARXIV, ISBN or NONE. -/
structure Dupe where
  kind : String
  key : String
  deriving DecidableEq, Repr

/-- v1 `_dupe_of`: the folded DOI, else the arXiv key, else the ISBN-13, else NONE. -/
def dupeOf (ids : Identifiers) : Check Dupe := do
  match ids.doi, ids.arxiv, ids.isbn with
  | some d, _, _ => return { kind := "DOI", key := fold d }
  | none, some a, _ => return { kind := "ARXIV", key := (← arxivParse (.str a)).key }
  | none, none, some i => return { kind := "ISBN", key := i }
  | none, none, none => return { kind := "NONE", key := "" }

/-- v1 `biblio_dupe_key`. -/
def dupeKey (v : Value) : Check Dupe := do dupeOf (← readIdentifiers v)

/-- v1 `_mismatch` (BC7): the item's own identifiers agree with IDENTIFIERS. -/
def mismatch (o : Item) (ids : Identifiers) : Check Unit := do
  if let some x := textOf o "DOI" then
    let d ← relabel "mismatch:DOI" (doiNorm (.str x))
    if d.kind == .arxiv then
      let bad ← match ids.doi, ids.arxiv with
        | none, some a => do
          let k1 := (← arxivParse (.str a)).key
          let k2 := (← arxivParse (.str d.id)).key
          pure (k1 != k2)
        | _, _ => pure true
      if bad then refuse "mismatch:DOI"
    else if ids.doi.map fold != some d.id then refuse "mismatch:DOI"
  if let some x := textOf o "ISBN" then
    let v ← relabel "mismatch:ISBN" ((·.isbn13) <$> isbnCheck (.str x))
    if ids.isbn != some v then refuse "mismatch:ISBN"
  for (k, f) in [("ISSN", issnCheck), ("PMID", pmidCheck), ("PMCID", pmcidCheck)] do
    if let some x := textOf o k then
      let v ← relabel ("mismatch:" ++ k) (f (.str x))
      if ids.get k != some v then refuse ("mismatch:" ++ k)

/-! ## The write check -/

/-- v1 `biblio_check`'s answer. -/
structure CheckResult where
  identifiers : Identifiers
  dupe : Dupe
  deriving DecidableEq, Repr

/-- v1 `biblio_check`: BC1 to BC9 in order, the first failure refused. `existing` lists the
UWC's landed entries as `[kind, key, bib_id]`. -/
def biblioCheck (entry existing caps : Value) : Check CheckResult := do
  let .obj e := entry | refuse "entry"
  unless keysWithin e ["item", "identifiers", "supersedes"] && e.length == 3 do refuse "entry"
  let sup ← match get? e "supersedes" with
    | some .null => pure none
    | some x => do
      match ← text? x with
      | some s => pure (some s)
      | none => refuse "entry"
    | none => refuse "entry"
  let .arr ex := existing | refuse "existing"
  let landed ← ex.mapM fun x => do
    match x with
    | .arr [.str k, .str key, b] =>
      if !["DOI", "ARXIV", "ISBN"].contains k || key.isEmpty then refuse "existing"
      match ← text? b with
      | some bid => pure (k, key, bid)
      | none => refuse "existing"
    | _ => refuse "existing"
  let caps ← readCaps caps
  let o ← readItem ((get? e "item").getD .null)
  require o
  capsOk o caps
  let ids ← readIdentifiers ((get? e "identifiers").getD .null)
  mismatch o ids
  let dupe ← dupeOf ids
  if dupe.kind != "NONE" then
    for (k, key, bid) in landed do
      if k == dupe.kind && key == dupe.key && sup != some bid then refuse ("duplicate:" ++ bid)
  if (canonJson o).utf8ByteSize > caps.entryMax then refuse "size"
  return { identifiers := ids, dupe }

/-! ## The canonical entry and its digest -/

/-- The canonical entry: its text, and its digest. -/
structure CanonEntry where
  text : String
  digest : String
  deriving DecidableEq, Repr

/-- v1 `_canon_parts`: the item's canonical text (its `id` the BIB ID), and the digest's
field list: `TPC-BIB`, the form, the entry's addresses and dates, each identifier kind with
its stored form or "", then the text. -/
def canonParts (bibId proposedBy landedBy landed supersedes identifiers item : Value) :
    Check (String × List Field) := do
  let mut addr : List String := []
  for (nm, v) in [("bib_id", bibId), ("proposed_by", proposedBy), ("landed_by", landedBy),
                  ("landed", landed)] do
    match ← text? v with
    | some s => addr := addr ++ [s]
    | none => refuse nm
  let sup ← match supersedes with
    | .null => pure ""
    | x => do
      match ← text? x with
      | some s => pure s
      | none => refuse "supersedes"
  let ids ← readIdentifiers identifiers
  let o ← readItem item
  let bid := addr.headD ""
  if let some i := textOf o "id" then
    if i != bid then refuse "id"
  let o2 := cslKeys.filterMap fun k =>
    if k == "id" then some ("id", ItemValue.text bid) else (o.lookup k).map ((k, ·))
  let text := canonJson o2
  let fields := ["TPC-BIB", "1"] ++ addr ++ [sup] ++
    identKinds.flatMap (fun k => [k, (ids.get k).getD ""]) ++ [text]
  return (text, fields.map Field.text)

/-- v1 `biblio_preimage`: the bytes the entry's digest covers. -/
def biblioPreimage (bibId proposedBy landedBy landed supersedes identifiers item : Value) :
    Check String := do
  let (_, fields) ← canonParts bibId proposedBy landedBy landed supersedes identifiers item
  return preimageFields fields

/-- v1 `biblio_canon`: the canonical text, and SHA-256 over the digest's field list. -/
def biblioCanon (bibId proposedBy landedBy landed supersedes identifiers item : Value) :
    Check CanonEntry := do
  let (text, fields) ← canonParts bibId proposedBy landedBy landed supersedes identifiers item
  return { text, digest := digestFields fields }

/-- The canonical entry's digest is SHA-256 of the preimage `biblioPreimage` gives. -/
theorem biblioCanon_digest {b p l d s i t : Value} {c : CanonEntry}
    (h : biblioCanon b p l d s i t = .ok c) :
    ∃ pre, biblioPreimage b p l d s i t = .ok pre ∧ c.digest = Digest.ofPreimage pre := by
  unfold biblioCanon at h
  unfold biblioPreimage
  cases hc : canonParts b p l d s i t with
  | error f => simp [hc, bind, Except.bind] at h
  | ok tf =>
    obtain ⟨text, fields⟩ := tf
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    exact ⟨_, rfl, by rw [← h]; rfl⟩

/-! ## The registry URL -/

def declKinds : List String :=
  ["DOI-RA", "DOI-CROSSREF", "DOI-DATACITE", "ARXIV", "PMID", "PMCID"]

def asciiAlnum (c : Char) : Bool := isDigit c || isLower c || isUpper c

/-- RFC 3986's unreserved characters and `/ : ( )`, which the slot keeps raw. -/
def urlSafe (c : Char) : Bool := asciiAlnum c || "-._~/:()".toList.contains c

/-- A template's characters after its authority. -/
def templateChar (c : Char) : Bool :=
  asciiAlnum c || "-._~:/?#[]@!$&'()*+,;=%".toList.contains c

/-- Two upper-case hexadecimal digits. -/
def hex2Upper (n : Nat) : String :=
  let ds := (Nat.toDigits 16 n).map Char.toUpper
  String.ofList (List.replicate (2 - ds.length) '0' ++ ds)

/-- v1 `_pct_encode`: every UTF-8 byte as `%XX` except the safe ASCII characters. -/
def pctEncode (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b < 0x80 && urlSafe c then c.toString else "%" ++ hex2Upper b.toNat)

/-- v1's `https://host[:port]/` at the start of a text: the index after its `/`. -/
def authorityEnd? (s : String) : Option Nat := do
  let rest ← if s.startsWith "https://" then some (s.toList.drop 8) else none
  let host := rest.takeWhile fun c => asciiAlnum c || c == '.' || c == '-'
  let first ← host.head?
  let last ← host.getLast?
  if !(asciiAlnum first && asciiAlnum last) then none
  let after := rest.drop host.length
  let portLen ← match after with
    | ':' :: more =>
      let ds := more.takeWhile isDigit
      if ds.isEmpty then none else some (1 + ds.length)
    | _ => some 0
  match after.drop portLen with
  | '/' :: _ => some (8 + host.length + portLen + 1)
  | _ => none

/-- The index of a pattern's first occurrence, or the text's length. -/
def findIndex (s pat : String) : Nat := ((s.splitOn pat).headD "").length

/-- The identifier a declaration's kind takes: a DOI of kind DOI, an arXiv id with its
version, a PMID or a PMCID. -/
def declaredIdentifier (kind : String) (identifier : Value) : Check String := do
  if kind.startsWith "DOI-" then
    let n ← doiNorm identifier
    if n.kind != .doi then refuse "identifier"
    return n.doi
  else if kind == "ARXIV" then return (← arxivParse identifier).id
  else if kind == "PMID" then pmidCheck identifier
  else pmcidCheck identifier

/-- v1 `registry_url`: an https template with exactly one `{ID}` in its path or query, the
identifier checked by the declaration's kind and percent-encoded into the slot; a `.` or `..`
path segment is refused. -/
def registryUrl (declaration identifier : Value) : Check String := do
  let .obj d := declaration | refuse "declaration"
  unless keysWithin d ["kind", "template", "name"] && has d "kind" && has d "template" do
    refuse "declaration"
  let kind ← match get? d "kind" with
    | some (.str k) => if declKinds.contains k then pure k else refuse "declaration"
    | _ => refuse "declaration"
  if let some n := get? d "name" then
    unless ← isText n do refuse "declaration"
  let tmpl ← match get? d "template" with
    | some (.str t) => pure t
    | _ => refuse "template"
  if (tmpl.splitOn "{ID}").length != 2 then refuse "template"
  let plain := tmpl.replace "{ID}" "x"
  let fullOk := match authorityEnd? plain with
    | some n => (plain.toList.drop n).all templateChar
    | none => false
  if plain.toList.contains '{' || plain.toList.contains '}' || !fullOk ||
      plain.toList.contains '#' then
    refuse "template"
  match authorityEnd? tmpl with
  | none => refuse "template"
  | some n => if findIndex tmpl "{ID}" < n then refuse "template"
  let v ← relabel "identifier" (declaredIdentifier kind identifier)
  let url := tmpl.replace "{ID}" (pctEncode v)
  let path := ((String.ofList (url.toList.drop 8)).splitOn "?").headD ""
  if (path.splitOn "/").any (fun seg => seg == "." || seg == "..") then refuse "identifier"
  return url

/-! ## Comparison with the registries -/

/-- No string repeats. -/
def distinct (l : List String) : Bool := l.eraseDups.length == l.length

/-- Code point order, which is UTF-8 byte order (v1's `sorted`). -/
def sortStrings (l : List String) : List String := l.mergeSort fun a b => decide (a ≤ b)

/-- The comparison's results, in the CHECK value's order. -/
def results : List String :=
  ["NOT FOUND", "FIELDS DIFFER", "LOOKUP FAILED", "FOUND UNCOMPARED", "NO LOOKUP", "CONFIRMED"]

def primaryOrder : List String := ["DOI", "ARXIV", "PMID", "PMCID"]

def resultOrder : List String := ["DOI", "ARXIV", "PMID", "PMCID", "ISBN", "ISSN"]

def lookupStatus : List String := ["FOUND", "NOT FOUND", "FAILED"]

def nameForms : List String := ["FAMILY", "GIVEN FAMILY", "FAMILY INITIALS"]

def fieldKeys : List String :=
  ["year", "title", "subtitle", "family", "name_form", "doi", "issn", "isbn", "arxiv_doi",
   "arxiv_id"]

/-- v1 `_calendar`: `YYYY-MM-DD`, a date of the Gregorian calendar. -/
def calendar? (v : Value) : Option String :=
  match v with
  | .str s =>
    let cs := s.toList
    if !(cs.length == 10 && allDigits (cs.take 4) && cs[4]! == '-' &&
        allDigits ((cs.drop 5).take 2) &&
        cs[7]! == '-' && allDigits (cs.drop 8)) then none
    else
      let y := digitsValue (cs.take 4)
      let mo := digitsValue ((cs.drop 5).take 2)
      let d := digitsValue (cs.drop 8)
      let leap := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
      let last := match mo with
        | 2 => if leap then 29 else 28
        | 4 | 6 | 9 | 11 => 30
        | _ => 31
      if mo < 1 || mo > 12 || d < 1 || d > last then none else some s
  | _ => none

/-- A registry notice, its type under the key form (kind name). -/
structure Notice where
  type : String
  identifier : Option String
  date : Option String
  source : String
  deriving DecidableEq, Repr

/-- A FOUND record's fields. -/
structure RegistryFields where
  year : Option Int
  title : Option String
  subtitle : Option String
  family : Option String
  nameForm : Option String
  doi : Option String
  issn : List String
  isbn : List String
  arxivDoi : Option String
  arxivId : Option String
  deriving DecidableEq, Repr

/-- One REGISTRY RECORD, read. -/
structure RegistryRecord where
  kind : String
  /-- For a DOI: the registration agency lookup's status, and the agency when FOUND. -/
  raStatus : Option String
  registry : Option String
  status : Option String
  fields : Option RegistryFields
  notices : List Notice
  deriving DecidableEq, Repr

/-- A text, or null. -/
def optText (v : Value) : Check (Option (Option String)) := do
  match v with
  | .null => return some none
  | x => match ← text? x with
    | some s => return some (some s)
    | none => return none

/-- v1 `_read_notice`. -/
def readNotice (v : Value) : Check Notice := do
  let .obj n := v | refuse "records"
  unless keysWithin n ["type", "identifier", "date", "source"] && n.length == 4 do refuse "records"
  let field (k : String) : Value := (get? n k).getD .null
  let some type ← text? (field "type") | refuse "records"
  let some source ← text? (field "source") | refuse "records"
  let identifier ← match field "identifier" with
    | .null => pure none
    | x => do
      let some s ← text? x | refuse "records"
      if s == "-" || s.toList.any isSpace then refuse "records"
      pure (some s)
  let date ← match field "date" with
    | .null => pure none
    | x => match calendar? x with
      | some d => pure (some d)
      | none => refuse "records"
  return { type := keyFormText type false, identifier, date, source }

/-- v1 `_read_fields`. -/
def readFields (v : Value) : Check RegistryFields := do
  let .obj f := v | refuse "records"
  unless keysWithin f fieldKeys && f.length == 10 do refuse "records"
  let field (k : String) : Value := (get? f k).getD .null
  let year ← match field "year" with
    | .null => pure none
    | .int n => if -9999 ≤ n && n ≤ 9999 then pure (some n) else refuse "records"
    | _ => refuse "records"
  let mut texts : List (Option String) := []
  for k in ["title", "subtitle", "family", "doi", "arxiv_doi", "arxiv_id"] do
    let some t ← optText (field k) | refuse "records"
    texts := texts ++ [t]
  let family := texts[2]!
  let nameForm ← match field "name_form" with
    | .null => pure none
    | .str s => pure (some s)
    | _ => refuse "records"
  if nameForm.isNone != family.isNone || (match nameForm with
      | some s => !nameForms.contains s
      | none => false) then refuse "records"
  let list (k : String) : Check (List String) := do
    let .arr xs := field k | refuse "records"
    xs.mapM fun x => do
      let some s ← text? x | refuse "records"
      pure s
  let issn ← list "issn"
  let isbn ← list "isbn"
  return { year, title := texts[0]!, subtitle := texts[1]!, family, nameForm, doi := texts[3]!,
           issn, isbn, arxivDoi := texts[4]!, arxivId := texts[5]! }

/-- Whether a record's identifier is the entry's of that kind, after normalization. -/
def sameIdentifier (kind : String) (ident : Value) (ids : Identifiers) : Check Bool := do
  let r ← attempt (do
    if kind == "DOI" then
      let d ← doiNorm ident
      return d.kind == .doi && some d.id == ids.doi.map fold
    else if kind == "ARXIV" then return some (← arxivParse ident).id == ids.arxiv
    else if kind == "PMID" then return some (← pmidCheck ident) == ids.pmid
    else return some (← pmcidCheck ident) == ids.pmcid)
  return r.getD false

/-- v1 `_read_record`: one REGISTRY RECORD, validated against the entry's identifiers. -/
def readRecord (v : Value) (ids : Identifiers) : Check RegistryRecord := do
  let .obj r := v | refuse "records"
  let kind ← match get? r "kind" with
    | some (.str k) => if primaryOrder.contains k then pure k else refuse "records"
    | _ => refuse "records"
  let keys := ["kind", "identifier", "registry", "status", "fields", "notices"] ++
    (if kind == "DOI" then ["ra"] else [])
  unless keysWithin r keys && r.length == keys.length do refuse "records"
  if (ids.get kind).isNone then refuse "records"
  let field (k : String) : Value := (get? r k).getD .null
  unless ← sameIdentifier kind (field "identifier") ids do refuse "records"
  let reg := field "registry"
  let mut raStatus : Option String := none
  if kind == "DOI" then
    let .obj ra := field "ra" | refuse "records"
    unless keysWithin ra ["status", "ra"] && ra.length == 2 do refuse "records"
    let st ← match get? ra "status" with
      | some (.str s) => if lookupStatus.contains s then pure s else refuse "records"
      | _ => refuse "records"
    raStatus := some st
    let agency := (get? ra "ra").getD .null
    if st == "FOUND" then
      let some name ← text? agency | refuse "records"
      let want := if name == "Crossref" then some "crossref"
        else if name == "DataCite" then some "datacite" else none
      match want, reg with
      | some w, .str g => if g != w then refuse "records"
      | some _, _ => refuse "records"
      | none, _ => match reg with
        | .null => pure ()
        | .str "generic" => pure ()
        | _ => refuse "records"
    else
      match agency, reg with
      | .null, .null => pure ()
      | _, _ => refuse "records"
  else
    match reg with
    | .str g => if g != (if kind == "ARXIV" then "arxiv" else "pubmed") then refuse "records"
    | _ => refuse "records"
  let registry : Option String := match reg with
    | .str s => some s
    | _ => none
  let status ← match reg, field "status" with
    | .null, .null => pure none
    | .null, _ => refuse "records"
    | _, .str s => if lookupStatus.contains s then pure (some s) else refuse "records"
    | _, _ => refuse "records"
  let .arr ns := field "notices" | refuse "records"
  if status == some "FOUND" then
    let fields ← readFields (field "fields")
    let notices ← ns.mapM readNotice
    return { kind, raStatus, registry, status, fields := some fields, notices }
  else
    unless (field "fields" matches .null) do refuse "records"
    unless ns.isEmpty do refuse "records"
    return { kind, raStatus, registry, status, fields := none, notices := [] }

/-- The entry's first author's family (a literal serving), or the first editor's when there
is no author, under the key form (v1 `_entry_family`). -/
def entryFamily (o : Item) : Check String := do
  let names := if (namesOf o "author").isEmpty then namesOf o "editor" else namesOf o "author"
  let nm := names.headD []
  pure (keyFormText ((nm.lookup "family").getD ((nm.lookup "literal").getD "")) false)

/-- v1 `_family_equal`: the record's family under its name form against the entry's key. -/
def familyEqual (entryKey recFamily form : String) : Check Bool := do
  let rk := keyFormText recFamily false
  if entryKey == "" || rk == "" then return entryKey == rk
  if form == "FAMILY" then return rk == entryKey
  if form == "GIVEN FAMILY" then return rk == entryKey || rk.endsWith (" " ++ entryKey)
  return rk == entryKey || rk.startsWith (entryKey ++ " ")

/-- Whether a DOI the record carries is the entry's (folded); a DOI that does not check is not. -/
def doiAgrees (ids : Identifiers) (x : String) : Check Bool := do
  let r ← attempt (doiNorm (.str x))
  return match r with
    | some d => d.kind == .doi && some d.id == ids.doi.map fold
    | none => false

/-- v1 `_compare_fields` (RD-8): the differing fields of a FOUND record; `none` for FOUND
UNCOMPARED. The entry's title and family are put under the key form when compared. -/
def compareFields (o : Item) (ids : Identifiers) (rec : RegistryRecord) (f : RegistryFields)
    (primary : Option String) : Check (Option (List String)) := do
  let cmpTitle : Check Bool := do
    match f.title with
    | none => return false
    | some t =>
      let full := match f.subtitle with
        | some s => t ++ " " ++ s
        | none => t
      return keyFormText full true == keyFormText ((textOf o "title").getD "") true
  let cmpFamily : Check Bool := do
    match f.family with
    | none => return false
    | some fam => familyEqual (← entryFamily o) fam (f.nameForm.getD "")
  if rec.kind == "ARXIV" && primary == some "DOI" then
    match f.arxivDoi with
    | none =>
      let both ← if ← cmpTitle then cmpFamily else pure false
      return if both then some [] else none
    | some ad =>
      let mut diff : List String := []
      unless ← doiAgrees ids ad do diff := diff ++ ["arxiv_doi"]
      unless ← cmpFamily do diff := diff ++ ["family"]
      return some diff
  let year := match o.lookup "issued" with
    | some (.date parts _) => (parts.headD []).head?
    | _ => none
  let mut diff : List String := []
  if f.year != year then diff := diff ++ ["year"]
  unless ← cmpTitle do diff := diff ++ ["title"]
  unless ← cmpFamily do diff := diff ++ ["family"]
  if let (some _, some x) := (ids.doi, f.doi) then
    unless ← doiAgrees ids x do diff := diff ++ ["doi"]
  if let (some "datacite", some a, some x) := (rec.registry, ids.arxiv, f.arxivId) then
    let r ← attempt (do return (← arxivParse (.str x)).key == (← arxivParse (.str a)).key)
    unless r.getD false do diff := diff ++ ["arxiv"]
  return some diff

/-- v1 `_in_list`: an ISSN or ISBN against the primary record's list. -/
def inList (kind value : String) (lst : List String) : Check String := do
  if lst.isEmpty then return "NO LOOKUP"
  for x in lst do
    let v ← attempt (if kind == "ISSN" then issnCheck (.str x)
      else (·.isbn13) <$> isbnCheck (.str x))
    if v == some value then return "CONFIRMED"
  return "FIELDS DIFFER"

/-- One identifier's result: its kind, the identifier, the result and the differing fields. -/
structure IdentResult where
  kind : String
  identifier : String
  result : String
  fields : List String
  deriving DecidableEq, Repr

/-- v1 `biblio_compare`'s answer. -/
structure Comparison where
  check : String
  results : List IdentResult
  notices : List Notice
  deriving DecidableEq, Repr

/-- CP4: the first of `results` present among the results; NO LOOKUP when there is none. -/
def checkValue (out : List IdentResult) : String :=
  (results.find? fun v => out.any (·.result == v)).getD "NO LOOKUP"

/-- One identifier's lookup result before the comparison (CP2). -/
def lookupResult (k : String) (r : RegistryRecord) : Option String :=
  if k == "DOI" then
    if r.raStatus == some "NOT FOUND" then some "NOT FOUND"
    else if r.raStatus == some "FAILED" then some "LOOKUP FAILED"
    else if r.registry.isNone then some "FOUND UNCOMPARED"
    else if r.status != some "FOUND" then some "LOOKUP FAILED"
    else none
  else if r.status == some "NOT FOUND" then some "NOT FOUND"
  else if r.status == some "FAILED" then some "LOOKUP FAILED"
  else none

/-- v1 `biblio_compare` (CP1 to CP5): each identifier's result against the registry records
Custos looked up, the CHECK value, and the FOUND records' notices. -/
def biblioCompare (entry records : Value) : Check Comparison := do
  let .obj e := entry | refuse "entry"
  unless keysWithin e ["item", "identifiers"] && e.length == 2 do refuse "entry"
  let o ← readItem ((get? e "item").getD .null)
  require o
  let ids ← readIdentifiers ((get? e "identifiers").getD .null)
  let .arr rs := records | refuse "records"
  let mut recs : List RegistryRecord := []
  for r in rs do
    let rr ← readRecord r ids
    if recs.any (·.kind == rr.kind) then refuse "records"
    recs := recs ++ [rr]
  let recOf (k : String) := recs.find? (·.kind == k)
  let primary := primaryOrder.find? fun k => (ids.get k).isSome
  let mut res : List (String × String × List String) := []
  for k in primaryOrder do
    if (ids.get k).isNone then continue
    match recOf k with
    | none => res := res ++ [(k, "LOOKUP FAILED", [])]
    | some r =>
      match lookupResult k r, r.fields with
      | some v, _ => res := res ++ [(k, v, [])]
      | none, none => refuse "records"  -- not reached: `readRecord` gives a FOUND record its fields
      | none, some f =>
        match ← compareFields o ids r f primary with
        | none => res := res ++ [(k, "FOUND UNCOMPARED", [])]
        | some [] => res := res ++ [(k, "CONFIRMED", [])]
        | some diff => res := res ++ [(k, "FIELDS DIFFER", diff)]
  let pf := match primary.bind recOf with
    | some p => if p.status == some "FOUND" then p.fields else none
    | none => none
  for k in ["ISBN", "ISSN"] do
    if let some v := ids.get k then
      match primary, pf with
      | some _, some f =>
        res := res ++ [(k, ← inList k v (if k == "ISSN" then f.issn else f.isbn), [])]
      | _, _ => res := res ++ [(k, "NO LOOKUP", [])]
  let out := resultOrder.filterMap fun k =>
    (res.find? (·.1 == k)).map fun (_, v, fs) =>
      { kind := k, identifier := (ids.get k).getD "", result := v, fields := fs }
  let check := checkValue out
  let notices := resultOrder.flatMap fun k => match recOf k with
    | some r => if r.status == some "FOUND" then r.notices else []
    | none => []
  return { check, results := out, notices }

/-- v1 `render_check_line`: the CHECK line Custos writes into the entry. -/
def checkLine (c : Comparison) (date : Value) : Check String := do
  let some d := calendar? date | refuse "date"
  return "CHECK " ++ d ++ " " ++ c.check ++
    String.join (c.results.map fun r => " ; " ++ r.kind ++ " " ++ r.identifier ++ " " ++ r.result)

/-- v1 `render_notices_line`: the NOTICES line, empty when there is no notice. -/
def noticesLine (c : Comparison) (date : Value) : Check String := do
  let some d := calendar? date | refuse "date"
  if c.notices.isEmpty then return ""
  return "NOTICES " ++ d ++ String.join (c.notices.map fun n =>
    " ; " ++ n.source ++ " " ++ n.identifier.getD "-" ++ " " ++ n.date.getD "-" ++ " " ++ n.type)

/-- v1 `arxiv_withdrawn` (RD-10): the whole token `withdrawn` in any ASCII case, not adjoined
by an ASCII letter or digit; null is false. -/
def arxivWithdrawn (comment : Value) : Check Bool :=
  match comment with
  | .null => pure false
  | .str s =>
    let low := (fold s).toList
    let token := "withdrawn".toList
    let alnum (c : Option Char) : Bool := match c with
      | some c => isLower c || isDigit c
      | none => false
    pure ((List.range low.length).any fun i =>
      (low.drop i).take token.length == token &&
        !alnum (if i == 0 then none else low[i - 1]?) && !alnum low[i + token.length]?)
  | _ => refuse "comment"

/-! ## The literature view and the hold list -/

def statusWords : List String :=
  ["PROVISIONAL", "ESTABLISHED", "REFUTED", "WITHDRAWN", "HELD", "NOT GRADED"]

def notStanding : List String := ["REFUTED", "WITHDRAWN", "HELD", "NOT GRADED"]

def fk20Results : List String := ["SOURCE AGREES", "SOURCE DIFFERS", "NOT FOUND"]

/-- v1 `_text_list`: a list of texts. -/
def textList? (v : Value) : Check (Option (List String)) := do
  let .arr xs := v | return none
  let mut out : List String := []
  for x in xs do
    match ← text? x with
    | some s => out := out ++ [s]
    | none => return none
  return some out

/-- An entry as the literature view reads it. -/
structure ViewEntry where
  bibId : String
  check : String
  notices : Int
  primary : Bool

/-- v1 `literature_view`'s answer: each standing record with its flagged entries and reasons,
and the entries for the Declarer. -/
structure LiteratureView where
  records : List (String × List (String × String))
  forHdecl : List String
  deriving DecidableEq, Repr

/-- v1 `literature_view`. -/
def literatureView (records entries findings : Value) : Check LiteratureView := do
  let .arr es := entries | refuse "entries"
  let mut ent : List ViewEntry := []
  for x in es do
    let .obj e := x | refuse "entries"
    unless keysWithin e ["bib_id", "check", "notices", "primary"] && e.length == 4 do
      refuse "entries"
    let field (k : String) : Value := (get? e k).getD .null
    let some bid ← text? (field "bib_id") | refuse "entries"
    let check ← match field "check" with
      | .str c => if results.contains c then pure c else refuse "entries"
      | _ => refuse "entries"
    let notices ← match field "notices" with
      | .int n => if 0 ≤ n && n ≤ 1000000000 then pure n else refuse "entries"
      | _ => refuse "entries"
    let .bool primary := field "primary" | refuse "entries"
    if ent.any (·.bibId == bid) then refuse "entries"
    ent := ent ++ [{ bibId := bid, check, notices, primary }]
  let .arr fs := findings | refuse "findings"
  let mut fk : List String := []
  for x in fs do
    let .obj f := x | refuse "findings"
    unless keysWithin f ["bib_id", "result", "agreed"] && f.length == 3 do refuse "findings"
    let field (k : String) : Value := (get? f k).getD .null
    let some bid ← text? (field "bib_id") | refuse "findings"
    let result ← match field "result" with
      | .str r => if fk20Results.contains r then pure r else refuse "findings"
      | _ => refuse "findings"
    let .bool agreed := field "agreed" | refuse "findings"
    unless ent.any (·.bibId == bid) do refuse "literature"
    if result == "NOT FOUND" && agreed then fk := fk ++ [bid]
  let .arr rs := records | refuse "records"
  let mut seen : List String := []
  let mut rows : List (String × List (String × String)) := []
  for x in rs do
    let .obj r := x | refuse "records"
    unless keysWithin r ["id", "status", "literature"] && r.length == 3 do refuse "records"
    let field (k : String) : Value := (get? r k).getD .null
    let some rid ← text? (field "id") | refuse "records"
    let status ← match field "status" with
      | .str s => if statusWords.contains s then pure s else refuse "records"
      | _ => refuse "records"
    if seen.contains rid then refuse "records"
    let some lit ← textList? (field "literature") | refuse "records"
    if !distinct lit then refuse "records"
    seen := seen ++ [rid]
    for b in lit do
      unless ent.any (·.bibId == b) do refuse "literature"
    if notStanding.contains status then continue
    let flagged := (sortStrings lit).flatMap fun b =>
      match ent.find? (·.bibId == b) with
      | some e =>
        (if e.notices > 0 then [(b, "NOTICES")] else []) ++
        (if e.check == "NOT FOUND" then [(b, "NOT FOUND")] else []) ++
        (if fk.contains b then [(b, "FK-20 NOT FOUND")] else [])
      | none => []
    if !flagged.isEmpty then rows := rows ++ [(rid, flagged)]
  let hd := sortStrings ((ent.filter fun e => e.primary && e.check == "NOT FOUND" &&
    fk.contains e.bibId).map (·.bibId))
  return { records := rows.mergeSort (fun a b => decide (a.1 ≤ b.1)), forHdecl := hd }

/-- v1 `biblio_hold_list`: the entries the account proposed or landed in a held block whose
re-run CHECK is not CONFIRMED, as `[bib_id, check]` sorted by bib_id. -/
def biblioHoldList (entries account blocks checks : Value) : Check (List (String × String)) := do
  let some acct ← text? account | refuse "account"
  let some bl ← textList? blocks | refuse "blocks"
  let .arr es := entries | refuse "entries"
  let .obj cs := checks | refuse "checks"
  for (k, v) in cs do
    let ok ← isText (.str k)
    let known := match v with
      | .str c => results.contains c
      | _ => false
    unless ok && known do refuse "checks"
  let mut seen : List String := []
  let mut out : List (String × String) := []
  for x in es do
    let .obj e := x | refuse "entries"
    unless keysWithin e ["bib_id", "proposed_by", "landed_by", "block_id"] && e.length == 4 do
      refuse "entries"
    let mut vals : List String := []
    for k in ["bib_id", "proposed_by", "landed_by", "block_id"] do
      let some s ← text? ((get? e k).getD .null) | refuse "entries"
      vals := vals ++ [s]
    let (bid, prop, land, blk) := (vals[0]!, vals[1]!, vals[2]!, vals[3]!)
    if seen.contains bid then refuse "entries"
    seen := seen ++ [bid]
    if (prop == acct || land == acct) && bl.contains blk then
      match getStr? cs bid with
      | none => refuse "checks"
      | some c => if c != "CONFIRMED" then out := out ++ [(bid, c)]
  return out.mergeSort (fun a b => decide (a.1 ≤ b.1))

/-! ## What the kernel checks

The text a field keeps is its text rule's, NFC with line endings as LF, and the key form
reads its text only through its NFD, so canonically equivalent spellings key alike. A
relabelled refusal stays a refusal, and a refusal treated as `none` is never an answer. The
CHECK value is one of the six results. -/

/-- A relabelled refusal is a refusal, with the new message. -/
theorem relabel_refused {α : Type} (m r : String) :
    relabel m (.error (.refused r) : Check α) = .error (.refused m) := rfl

/-- A refusal attempted is `none`; an answer is kept. -/
theorem attempt_refused {α : Type} (r : String) :
    attempt (.error (.refused r) : Check α) = .ok none := rfl

/-- A string field read is v1's `_text` of the string: line endings as LF, then NFC. -/
theorem readText_text {field : String} {v : Value} {t : String} (h : readText field v = .ok t) :
    ∃ s, v = .str s ∧ t = Zone.text s := by
  unfold readText at h
  split at h
  · rename_i s
    refine ⟨s, rfl, ?_⟩
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp [refuse, throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [refuse, throw, throwThe, MonadExceptOf.throw] at h
      · exact (Except.ok.inj h).symm
  · simp [refuse, throw, throwThe, MonadExceptOf.throw] at h

/-- The key form reads a text only through the NFD of its markup-free, entity-decoded text:
two texts whose NFDs agree there, a composed and a decomposed spelling among them, have one
key form. -/
theorem keyFormText_of_nfd {a b : String} {title : Bool}
    (h : Unicode.nfdList (keyFormBase a title) = Unicode.nfdList (keyFormBase b title)) :
    keyFormText a title = keyFormText b title := by
  simp only [keyFormText, h]

/-- The fold keeps every code point's place. -/
theorem fold_length (s : String) : (fold s).length = s.length := by
  simp [fold]

/-- CP4's CHECK value is one of the six results. -/
theorem checkValue_mem (out : List IdentResult) : checkValue out ∈ results := by
  unfold checkValue
  cases h : results.find? (fun v => out.any (·.result == v)) with
  | none => simp [results]
  | some v => exact List.mem_of_find?_eq_some h

end Principia.Biblio
