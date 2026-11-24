import Principia.Canonical
import Principia.Digest.Injective

/-!
# The specification's digest D(PFS) and the instruction set's digest D(IS)

v1's `tpc_digest` 0.3.0 (TPS 0.1.5 and 1.1): the digest of the published
specification, over the text of the preformatted blocks of its pages, and the digest of the
instruction set, over the specification's version, its digest and the other members of the
index's instruction-artifact class. v1 called the specification TPS; PMA calls it the
Principia Framework Specification, its digest D(PFS).

* `preTexts` (v1 `pre_texts`): the blocks of one page, in order. A block opens at the exact
  text `<pre>` and a line feed and ends at the next exact `</pre>`; the block is the text
  between, as it stands. A pre tag is `<pre` or `</pre`, its letters in any case, followed by
  `>`, `/`, ASCII white space or the end of the text (so `<prefix>` is text); a pre tag of any
  other form, an opening without its line feed, an opening inside a block, a closing outside
  one and an unclosed block are refused. Comments and nowiki are not read: a pre tag inside
  either is read as a tag (v1's named limit).
* `specificationPages` (v1 `tps_pages`): the ordered list of `(title, h)` of the kept pages:
  the root and the section pages with at least one block, the contents page never; the root
  first, then the sections by number, compared as integers part by part; `h` the SHA-256 of
  the page's blocks joined by one line feed, nothing normalized.
* `digestSpecification` (v1 `d_tps`): `digestFields ["TPC-TPS", "1", version, n, title_1,
  h_1, ..., title_n, h_n]` over that list.
* `digestInstructionSet` (v1 `d_is`): `digestFields ["TPC-DIS", "1", version, D(PFS), m,
  title_1, h_1, ...]`, the members in the caller's order.

Each refuses with v1's reason (`Reason`), the first that applies whatever the order of the
pages: `version`, `pages`, `title`, `root`, `pre`; `digest`, `members`. The `…Of` functions
take v1's arguments as JSON values (`Principia.Canonical.Value`), as the Calculator reads them,
and refuse what v1 refused for its type (a version that is not a string, pages that are not a
list of pairs of strings). v1 also refused a text with no UTF-8 form; a Lean string always has
one, and the Calculator's reader refuses a lone surrogate before any function sees it.

The titles and the tags are v1's: the root `The Principia Machina/TPS`, its contents
page, and the tags `TPC-TPS` and `TPC-DIS`, so that every digest of v1's corpus is reproduced.
-/

namespace Principia.Digest.Specification

open Principia.Canonical (Value)

/-! ## v1's constants -/

/-- The specification tree's root title (v1 `TPS_ROOT`). -/
def rootTitle : String := "The Principia Machina/TPS"

/-- The contents page, left out by its title (v1 `TPS_CONTENTS`). -/
def contentsTitle : String := rootTitle ++ "/Contents"

/-- The first field of D(PFS)'s field list (v1 `TPS_TAG`). -/
def specificationTag : String := "TPC-TPS"

/-- The first field of D(IS)'s field list (v1 `DIS_TAG`). -/
def instructionSetTag : String := "TPC-DIS"

/-- The second field of both field lists, the form (v1 `TPS_FORM`, `DIS_FORM`). -/
def form : String := "1"

/-- Why a function refuses: v1's reasons. -/
inductive Reason where
  | version
  | pages
  | title
  | root
  | pre
  | digest
  | members
  deriving DecidableEq, Repr

/-- v1's word for a reason. -/
def Reason.word : Reason → String
  | .version => "version"
  | .pages => "pages"
  | .title => "title"
  | .root => "root"
  | .pre => "pre"
  | .digest => "digest"
  | .members => "members"

/-! ## The blocks of a page (v1 `pre_texts`) -/

/-- ASCII white space as v1 counts it: space, tab, LF, VT, FF, CR. -/
def isAsciiWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0b' || c == '\x0c' || c == '\r'

/-- `word` (lower-case ASCII) begins `cs`, each letter in either case (v1 `_ascii_ieq`). -/
def startsCaseless : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | w :: ws, c :: cs => (c == w || c == w.toUpper) && startsCaseless ws cs

/-- A pre tag: an opening or a closing. -/
inductive Tag where
  | opening
  | closing
  deriving DecidableEq, Repr

/-- `name` begins `cs` in any case and is followed by `>`, `/`, ASCII white space or the end
of the text. -/
def namesTag (name cs : List Char) : Bool :=
  startsCaseless name cs &&
    match cs.drop name.length with
    | [] => true
    | c :: _ => c == '>' || c == '/' || isAsciiWhite c

/-- The pre tag a `<` opens, given the characters after it (v1 `_pre_tag`). -/
def tagAfter (cs : List Char) : Option Tag :=
  if namesTag ['p', 'r', 'e'] cs then some .opening
  else if namesTag ['/', 'p', 'r', 'e'] cs then some .closing
  else none

/-- The scan of a page's text: the characters left, the open block's characters so far
(reversed), and the blocks closed (reversed). An exact opening outside a block opens one, an
exact closing inside a block closes it, any other pre tag is refused, and every other `<` is
text. -/
def scan : List Char → Option (List Char) → List String → Except Reason (List String)
  | [], none, blocks => .ok blocks.reverse
  | [], some _, _ => .error .pre
  | '<' :: 'p' :: 'r' :: 'e' :: '>' :: '\n' :: rest, none, blocks => scan rest (some []) blocks
  | '<' :: '/' :: 'p' :: 'r' :: 'e' :: '>' :: rest, some b, blocks =>
    scan rest none (String.ofList b.reverse :: blocks)
  | '<' :: cs, block, blocks =>
    if (tagAfter cs).isSome then .error .pre else scan cs (block.map ('<' :: ·)) blocks
  | c :: cs, block, blocks => scan cs (block.map (c :: ·)) blocks

/-- v1's `pre_texts`: a page's blocks in order, or the refusal `pre`. -/
def preTexts (wikitext : String) : Except Reason (List String) :=
  scan wikitext.toList none []

/-- v1's `pre_texts` of a JSON value: a text's blocks; anything else refused `pre`. -/
def preTextsOf : Value → Except Reason (List String)
  | .str s => preTexts s
  | _ => .error .pre

/-! ## Versions and titles -/

/-- An ASCII decimal digit (v1's `[0-9]`). -/
def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `0`, or a digit 1 to 9 then ASCII digits (v1's `0|[1-9][0-9]*`). -/
def numeral : List Char → Bool
  | ['0'] => true
  | c :: cs => '1' ≤ c && c ≤ '9' && cs.all isAsciiDigit
  | [] => false

/-- A version: MAJOR.MINOR.PATCH, ASCII digits, no leading zero (v1 `_VERSION`). -/
def versionOk (v : String) : Bool :=
  match v.toList.splitOn '.' with
  | [a, b, c] => numeral a && numeral b && numeral c
  | _ => false

/-- A numeral's value. -/
def numeralValue (cs : List Char) : Nat :=
  cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A section number: two or more parts joined by `.`, each `0` or 1 to 4 digits without a
leading zero; its key, the parts as integers. -/
def sectionKey? (number : List Char) : Option (List Nat) :=
  let parts := number.splitOn '.'
  if 2 ≤ parts.length && parts.all (fun p => p.length ≤ 4 && numeral p) then
    some (parts.map numeralValue)
  else none

/-- Two spaces in a row. -/
def hasDoubleSpace : List Char → Bool
  | ' ' :: ' ' :: _ => true
  | _ :: cs => hasDoubleSpace cs
  | [] => false

/-- A section's name: not empty, without `/`, without a leading, trailing or doubled space. -/
def nameOk (name : List Char) : Bool :=
  match name with
  | [] => false
  | c :: _ => c != ' ' && name.getLast? != some ' ' && !name.contains '/' && !hasDoubleSpace name

/-- A section page's key, given its title after the root and `/`: number, one space, name. -/
def sectionOf (rest : List Char) : Option (List Nat) :=
  match rest.span (· != ' ') with
  | (number, ' ' :: name) => if nameOk name then sectionKey? number else none
  | _ => none

/-- What a title names in the tree. -/
inductive TitleClass where
  | root
  | contents
  | sectionPage (key : List Nat)
  deriving DecidableEq, Repr

/-- A section's key. -/
def TitleClass.key? : TitleClass → Option (List Nat)
  | .sectionPage k => some k
  | _ => none

/-- v1's `_title_class`: the root, the contents page, a section page with its key, or `none`
for a title outside these forms or holding `_` or a control character (U+0000 to U+001F,
U+007F). -/
def titleClass (title : String) : Option TitleClass :=
  if title.any (fun c => c == '_' || c.toNat < 0x20 || c.toNat == 0x7F) then none
  else if title == rootTitle then some .root
  else if title == contentsTitle then some .contents
  else match (rootTitle ++ "/").toList.isPrefixOf? title.toList with
    | some rest => (sectionOf rest).map .sectionPage
    | none => none

/-- A section page's key, from its title. -/
def sectionKeyOf (title : String) : Option (List Nat) :=
  (titleClass title).bind TitleClass.key?

/-- The titles pass v1's title check: every title in one of the forms, no title twice and no
section number twice. -/
def titlesOk (titles : List String) : Bool :=
  titles.all (fun t => (titleClass t).isSome) && decide titles.Nodup &&
    decide (titles.filterMap sectionKeyOf).Nodup

/-! ## The kept pages (v1 `tps_pages`) -/

/-- A page's `h`: SHA-256 of its blocks joined by one line feed, in lowercase hexadecimal. -/
def pageDigest (blocks : List String) : String :=
  Sha256.digestText ("\n".intercalate blocks)

/-- The order of the kept pages: the root (`none`) first, then the sections by number,
compared as integers part by part, a number before its extensions. -/
def keyLe : Option (List Nat) → Option (List Nat) → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => lexLe a b
where
  lexLe : List Nat → List Nat → Bool
    | [], _ => true
    | _ :: _, [] => false
    | x :: xs, y :: ys => x < y || (x == y && lexLe xs ys)

/-- A kept page's row: its order key, its title and its `h`; the contents page and a page
without a block are not kept. -/
def row (title : String) (c : TitleClass) (blocks : List String) :
    Option (Option (List Nat) × String × String) :=
  if c == .contents || blocks.isEmpty then none else some (c.key?, title, pageDigest blocks)

/-- A page's row, from its title and its blocks. -/
def rowOf (page : String × Except Reason (List String)) :
    Option (Option (List Nat) × String × String) :=
  match titleClass page.1, page.2 with
  | some c, .ok blocks => row page.1 c blocks
  | _, _ => none

/-- A page whose blocks are refused. -/
def blocksRefused : Except Reason (List String) → Bool
  | .error _ => true
  | .ok _ => false

/-- The kept pages' list from each page's title and its blocks as `preTexts` read them:
`title` (v1's check of every title), then `root`, then `pre` (a page's blocks refused, the
contents page's included), then the kept pages' rows sorted by their keys. -/
def pagesOfBlocks (pages : List (String × Except Reason (List String))) :
    Except Reason (List (String × String)) :=
  let titles := pages.map Prod.fst
  if !titlesOk titles then .error .title
  else if !titles.contains rootTitle then .error .root
  else if pages.any (fun p => blocksRefused p.2) then .error .pre
  else .ok (((pages.filterMap rowOf).mergeSort fun a b => keyLe a.1 b.1).map Prod.snd)

/-- v1's `tps_pages` over pages already read as `(title, wikitext)` pairs. -/
def specificationPages (pages : List (String × String)) : Except Reason (List (String × String)) :=
  pagesOfBlocks (pages.map fun p => (p.1, preTexts p.2))

/-- Pages as v1 takes them: a list of `[title, wikitext]` pairs of strings. -/
def readPages : Value → Option (List (String × String))
  | .arr ps => ps.mapM fun
    | .arr [.str t, .str w] => some (t, w)
    | _ => none
  | _ => none

/-- v1's `tps_pages(pages)`: `pages` when they are not a list of pairs of strings. -/
def specificationPagesOf (pages : Value) : Except Reason (List (String × String)) :=
  match readPages pages with
  | some ps => specificationPages ps
  | none => .error .pages

/-! ## D(PFS) (v1 `d_tps`) -/

/-- D(PFS)'s field list over the kept pages' list. -/
def specificationFields (version : String) (rows : List (String × String)) : List Field :=
  [.text specificationTag, .text form, .text version, .int rows.length] ++
    rows.flatMap fun r => [.text r.1, .text r.2]

/-- D(PFS)'s preimage over pages read as `(title, wikitext)` pairs: `version` first. -/
def preimageSpecification (version : String) (pages : List (String × String)) :
    Except Reason String :=
  if versionOk version then
    (specificationPages pages).map fun rows => preimageFields (specificationFields version rows)
  else .error .version

/-- D(PFS) over pages read as `(title, wikitext)` pairs. -/
def digestSpecification (version : String) (pages : List (String × String)) :
    Except Reason String :=
  (preimageSpecification version pages).map ofPreimage

/-- A version as v1 takes it: a string of the form; anything else refused `version`. -/
def versionOf : Value → Except Reason String
  | .str v => if versionOk v then .ok v else .error .version
  | _ => .error .version

/-- D(PFS)'s preimage over v1's arguments as JSON values. -/
def preimageSpecificationOf (version pages : Value) : Except Reason String := do
  let v ← versionOf version
  let rows ← specificationPagesOf pages
  pure (preimageFields (specificationFields v rows))

/-- v1's `d_tps(version, pages)`. -/
def digestSpecificationOf (version pages : Value) : Except Reason String :=
  (preimageSpecificationOf version pages).map ofPreimage

/-! ## D(IS) (v1 `d_is`) -/

/-- D(IS)'s field list. -/
def instructionSetFields (version specification : String) (members : List (String × String)) :
    List Field :=
  [.text instructionSetTag, .text form, .text version, .text specification,
    .int members.length] ++ members.flatMap fun m => [.text m.1, .text m.2]

/-- The members as v1 takes them: each a title that is not empty and a digest, no title
twice. -/
def membersOk (members : List (String × String)) : Bool :=
  members.all (fun m => !m.1.isEmpty && isHex64 m.2) && decide (members.map Prod.fst).Nodup

/-- D(IS)'s preimage: `version`, then `digest` (D(PFS) not 64 lowercase hexadecimal
characters), then `members`. -/
def preimageInstructionSet (version specification : String) (members : List (String × String)) :
    Except Reason String :=
  if !versionOk version then .error .version
  else if !isHex64 specification then .error .digest
  else if !membersOk members then .error .members
  else .ok (preimageFields (instructionSetFields version specification members))

/-- D(IS). -/
def digestInstructionSet (version specification : String) (members : List (String × String)) :
    Except Reason String :=
  (preimageInstructionSet version specification members).map ofPreimage

/-- Members as v1 takes them: a list of `[title, digest]` pairs of strings. -/
def readMembers : Value → Option (List (String × String))
  | .arr ms => ms.mapM fun
    | .arr [.str t, .str h] => some (t, h)
    | _ => none
  | _ => none

/-- D(IS)'s preimage over v1's arguments as JSON values. -/
def preimageInstructionSetOf (version specification members : Value) : Except Reason String := do
  let v ← versionOf version
  let d ← match specification with
    | .str d => if isHex64 d then pure d else throw .digest
    | _ => throw .digest
  let ms ← match readMembers members with
    | some ms => pure ms
    | none => throw .members
  preimageInstructionSet v d ms

/-- v1's `d_is(version, d_tps, members)`. -/
def digestInstructionSetOf (version specification members : Value) : Except Reason String :=
  (preimageInstructionSetOf version specification members).map ofPreimage

/-! ## D(IS)'s members

D(IS)'s members are the Agent Contract's pages outside the specification tree, the stated list
of titles. Each member's `h` is formed as a kept page's is (`pageDigest` of its blocks), and
the members are ordered by title, Lean's `String` order, code point by code point. The stated
list of titles is an argument here. -/

/-- The members' order: Lean's `String` order, code point by code point. -/
def titleLe (a b : String) : Bool := decide (a ≤ b)

/-- A character the wiki reads as a space in a title: the space, `_`, and the other spaces
MediaWiki's title codec folds into one (U+00A0, U+1680, U+180E, U+2000 to U+200A, U+2028,
U+2029, U+202F, U+205F, U+3000). -/
def wikiSpace (c : Char) : Bool :=
  c == ' ' || c == '_' || c.toNat == 0xA0 || c.toNat == 0x1680 || c.toNat == 0x180E ||
    (0x2000 ≤ c.toNat && c.toNat ≤ 0x200A) || c.toNat == 0x2028 || c.toNat == 0x2029 ||
    c.toNat == 0x202F || c.toNat == 0x205F || c.toNat == 0x3000

/-- A direction mark the wiki drops from a title: U+200E, U+200F, U+202A to U+202E. -/
def wikiMark (c : Char) : Bool :=
  c.toNat == 0x200E || c.toNat == 0x200F || (0x202A ≤ c.toNat && c.toNat ≤ 0x202E)

/-- A run of spaces made one. -/
def collapseSpaces (cs : List Char) : List Char :=
  (cs.foldl (fun acc c => match c, acc with
    | ' ', ' ' :: _ => acc
    | _, _ => c :: acc) []).reverse

/-- Spaces at either end dropped. -/
def trimSpaces (cs : List Char) : List Char :=
  ((cs.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-- A title as the wiki names its page: direction marks dropped, every space of `wikiSpace` a
space, runs of spaces one, spaces at either end dropped, one leading colon dropped with the
spaces after it, the first character in upper case (`Char.toUpper`, which changes only `a` to
`z`; the tree's titles begin with `T`, and no other character's upper case is `T`). Two titles
the wiki names one page by fold to one title here in these respects; the tree's titles are
their own fold. -/
def wikiTitle (title : String) : String :=
  let cs := trimSpaces (collapseSpaces
    ((title.toList.filter (fun c => !wikiMark c)).map (fun c => if wikiSpace c then ' ' else c)))
  let cs := match cs with
    | ':' :: rest => trimSpaces rest
    | _ => cs
  match cs with
  | c :: rest => String.ofList (c.toUpper :: rest)
  | [] => ""

/-- A title names a page of the specification tree, as written or as the wiki names its
page. -/
def treeTitle (t : String) : Bool := (titleClass t).isSome || (titleClass (wikiTitle t)).isSome

/-- A member's page has at least one block and its blocks are not refused. -/
def memberBlocksOk (wikitext : String) : Bool :=
  match preTexts wikitext with
  | .ok (_ :: _) => true
  | _ => false

/-- A member's row: its title and the `h` of its page's blocks; `members` when the title has
no page, `pre` when the page's blocks are refused or there is none. -/
def memberRow (pages : List (String × String)) (title : String) :
    Except Reason (String × String) :=
  match pages.lookup title with
  | none => .error .members
  | some w =>
    match preTexts w with
    | .ok (b :: bs) => .ok (title, pageDigest (b :: bs))
    | _ => .error .pre

/-- D(IS)'s members, `(title, h)` for each stated title, from the pages as `(title, wikitext)`
pairs, ordered by title. It refuses, the first that applies whatever the order of either list:
`title` (a title of either list is a title of the specification tree, as written or as the wiki
names its page, `treeTitle`); then `members` (an empty
title, a title twice in either list, a page whose title is not stated, a stated title with no
page); then `pre` (a page's blocks refused, or a page with no block). -/
def memberPages (stated : List String) (pages : List (String × String)) :
    Except Reason (List (String × String)) :=
  let titles := pages.map Prod.fst
  if (stated ++ titles).any treeTitle then .error .title
  else if stated.any String.isEmpty || !decide stated.Nodup || !decide titles.Nodup ||
      !stated.all (titles.contains ·) || !titles.all (stated.contains ·) then .error .members
  else if pages.any (fun p => !memberBlocksOk p.2) then .error .pre
  else (stated.mergeSort titleLe).mapM (memberRow pages)

/-- Titles as given: a list of strings. -/
def readTitles : Value → Option (List String)
  | .arr ts => ts.mapM fun
    | .str t => some t
    | _ => none
  | _ => none

/-- D(IS)'s members over JSON values: `members` when the titles are not a list of strings,
`pages` when the pages are not a list of pairs of strings. -/
def memberPagesOf (titles pages : Value) : Except Reason (List (String × String)) :=
  match readTitles titles, readPages pages with
  | none, _ => .error .members
  | some _, none => .error .pages
  | some ts, some ps => memberPages ts ps

/-! ## Answers as v1 writes them -/

/-- v1's answer: `["OK", value]` or `["REFUSED", reason]`. -/
def answer {α : Type} (f : α → Value) : Except Reason α → Value
  | .ok a => .arr [.str "OK", f a]
  | .error r => .arr [.str "REFUSED", .str r.word]

/-- A list of `(title, h)` pairs as v1 writes it: `[[title, h], ...]`. -/
def pairsValue (rows : List (String × String)) : Value :=
  .arr (rows.map fun r => .arr [.str r.1, .str r.2])

/-! ## What Lean proves -/

/-- D(PFS) is the digest of the kept pages' list (v1 0.3.0: `d_tps` is built on `tps_pages`):
whenever the version is of the form, the specification's digest is `digestFields` over the
field list of exactly the list `specificationPages` answers, and it refuses exactly when that
list is refused, with the same reason. -/
theorem digestSpecification_pages {version : String} (hv : versionOk version = true)
    (pages : List (String × String)) :
    digestSpecification version pages =
      (specificationPages pages).map fun rows =>
        digestFields (specificationFields version rows) := by
  unfold digestSpecification preimageSpecification
  simp only [hv, ↓reduceIte]
  cases specificationPages pages <;> rfl

/-- A version not of the form is refused first, whatever the pages. -/
theorem digestSpecification_version {version : String} (hv : versionOk version = false)
    (pages : List (String × String)) :
    digestSpecification version pages = .error .version := by
  simp [digestSpecification, preimageSpecification, hv, Except.map]

/-- A banner, a link or any other text outside the blocks moves nothing (TPS 1.1, D(TPS)):
two page lists with the same titles in the same order whose pages read as the same blocks (or
are refused alike) have the same list, and so the same D(PFS). -/
theorem specificationPages_blocks {p q : List (String × String)}
    (h : p.map (fun x => (x.1, preTexts x.2)) = q.map (fun x => (x.1, preTexts x.2))) :
    specificationPages p = specificationPages q := by
  unfold specificationPages
  rw [h]

/-- The same, for D(PFS). -/
theorem digestSpecification_blocks (version : String) {p q : List (String × String)}
    (h : p.map (fun x => (x.1, preTexts x.2)) = q.map (fun x => (x.1, preTexts x.2))) :
    digestSpecification version p = digestSpecification version q := by
  unfold digestSpecification preimageSpecification
  rw [specificationPages_blocks h]

/-- Every D(PFS) is 64 characters. -/
theorem digestSpecification_length {version : String} {pages : List (String × String)}
    {d : String} (h : digestSpecification version pages = .ok d) : d.length = 64 := by
  unfold digestSpecification at h
  cases hp : preimageSpecification version pages with
  | error e => simp [hp, Except.map] at h
  | ok p =>
    simp only [hp, Except.map, Except.ok.injEq] at h
    rw [← h]
    exact ofPreimage_length p

/-- Every D(IS) is 64 characters. -/
theorem digestInstructionSet_length {version specification : String}
    {members : List (String × String)} {d : String}
    (h : digestInstructionSet version specification members = .ok d) : d.length = 64 := by
  unfold digestInstructionSet at h
  cases hp : preimageInstructionSet version specification members with
  | error e => simp [hp, Except.map] at h
  | ok p =>
    simp only [hp, Except.map, Except.ok.injEq] at h
    rw [← h]
    exact ofPreimage_length p

/-- A list of pairs from its flattened list. -/
theorem flatPairs_inj : ∀ {a b : List (String × String)},
    (a.flatMap fun r => [r.1, r.2]) = (b.flatMap fun r => [r.1, r.2]) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (x, y) :: a, (x', y') :: b, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    rw [h.1, h.2.1, flatPairs_inj h.2.2]

theorem fieldsBytes_pairs (rows : List (String × String)) :
    (rows.flatMap fun r => [Field.text r.1, Field.text r.2]).map Field.bytes =
      rows.flatMap fun r => [r.1, r.2] := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp [List.flatMap_cons, ih, Field.bytes]

/-- **SC5.** D(PFS)'s preimage stands for one version and one list of kept pages. -/
theorem specificationFields_injective {v v' : String} {rows rows' : List (String × String)}
    (h : preimageFields (specificationFields v rows) =
      preimageFields (specificationFields v' rows')) :
    v = v' ∧ rows = rows' := by
  have hb := preimageFields_bytes h
  simp only [specificationFields, List.map_cons, fieldsBytes_pairs,
    Field.bytes, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hb
  exact ⟨hb.1, flatPairs_inj hb.2.2⟩

/-- **SC5.** D(IS)'s preimage stands for one version, one D(PFS) and one list of members. -/
theorem instructionSetFields_injective {v v' d d' : String} {ms ms' : List (String × String)}
    (h : preimageFields (instructionSetFields v d ms) =
      preimageFields (instructionSetFields v' d' ms')) :
    v = v' ∧ d = d' ∧ ms = ms' := by
  have hb := preimageFields_bytes h
  simp only [instructionSetFields, List.map_cons, fieldsBytes_pairs,
    Field.bytes, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hb
  exact ⟨hb.1, hb.2.1, flatPairs_inj hb.2.2.2⟩

/-! ### The order of the pages

The kept pages' list is sorted by key; two orders of the same pages give two lists, each a
permutation of the other and each sorted, and their rows have distinct keys (the root is one
title, a section's number is never twice), so the two are one list. -/

/-- Two lists, each a permutation of the other, each ordered by `r`, are equal when `r` is
antisymmetric on their elements. -/
theorem eq_of_perm_of_pairwise {α : Type} {r : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise r → l₂.Pairwise r →
      (∀ a ∈ l₁, ∀ b ∈ l₁, r a b → r b a → a = b) → l₁ = l₂
  | [], l₂, hp, _, _, _ => (List.nil_perm.mp hp).symm
  | a :: t₁, [], hp, _, _, _ => absurd (List.perm_nil.mp hp) (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂, hanti => by
    have hab : a = b := by
      by_cases h : a = b
      · exact h
      · have hb : b ∈ t₁ := by
          have : b ∈ a :: t₁ := hp.mem_iff.mpr List.mem_cons_self
          rcases List.mem_cons.mp this with h' | h'
          · exact absurd h'.symm h
          · exact h'
        have ha : a ∈ t₂ := by
          have : a ∈ b :: t₂ := hp.mem_iff.mp List.mem_cons_self
          rcases List.mem_cons.mp this with h' | h'
          · exact absurd h' h
          · exact h'
        have rab : r a b := (List.pairwise_cons.mp h₁).1 b hb
        have rba : r b a := (List.pairwise_cons.mp h₂).1 a ha
        exact hanti a List.mem_cons_self b (List.mem_cons_of_mem a hb) rab rba
    subst hab
    have ht := eq_of_perm_of_pairwise (hp.cons_inv) (List.pairwise_cons.mp h₁).2
      (List.pairwise_cons.mp h₂).2
      (fun x hx y hy => hanti x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
    rw [ht]

theorem lexLe_total : ∀ (a b : List Nat), keyLe.lexLe a b = true ∨ keyLe.lexLe b a = true
  | [], _ => by simp [keyLe.lexLe]
  | _ :: _, [] => by simp [keyLe.lexLe]
  | x :: xs, y :: ys => by
    simp only [keyLe.lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    rcases Nat.lt_trichotomy x y with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases lexLe_total xs ys with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inr (Or.inl h)

theorem lexLe_trans : ∀ (a b c : List Nat), keyLe.lexLe a b = true → keyLe.lexLe b c = true →
    keyLe.lexLe a c = true
  | [], _, _, _, _ => by simp [keyLe.lexLe]
  | _ :: _, [], _, h, _ => by simp [keyLe.lexLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [keyLe.lexLe] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [keyLe.lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact Or.inl (Nat.lt_trans h₁ h₂)
    · exact Or.inl h₁
    · exact Or.inl h₂
    · exact Or.inr ⟨rfl, lexLe_trans xs ys zs h₁ h₂⟩

theorem lexLe_antisymm : ∀ (a b : List Nat), keyLe.lexLe a b = true → keyLe.lexLe b a = true →
    a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [keyLe.lexLe] at h
  | _ :: _, [], h, _ => by simp [keyLe.lexLe] at h
  | x :: xs, y :: ys, h₁, h₂ => by
    simp only [keyLe.lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨h₂', h₂⟩
    · omega
    · omega
    · omega
    · rw [lexLe_antisymm xs ys h₁ h₂]

theorem keyLe_total (a b : Option (List Nat)) : keyLe a b = true ∨ keyLe b a = true := by
  cases a <;> cases b <;> simp [keyLe, lexLe_total]

theorem keyLe_trans (a b c : Option (List Nat)) : keyLe a b = true → keyLe b c = true →
    keyLe a c = true := by
  cases a <;> cases b <;> cases c <;> simp [keyLe] <;> exact lexLe_trans _ _ _

theorem keyLe_antisymm (a b : Option (List Nat)) : keyLe a b = true → keyLe b a = true →
    a = b := by
  cases a <;> cases b <;> simp [keyLe]
  exact lexLe_antisymm _ _

/-- In a list whose images are distinct, two elements of one image are one element. -/
theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α} {a b : α}, (l.map f).Nodup → a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, a, b, hn, ha, hb, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd hf.symm (hn.1 b hb')
    · exact absurd hf (hn.1 a ha')
    · exact eq_of_map_nodup hn.2 ha' hb' hf

/-- In a list whose present images are distinct, two elements of one present image are one
element. -/
theorem eq_of_filterMap_nodup {α β : Type} {f : α → Option β} {k : β} :
    ∀ {l : List α} {a b : α}, (l.filterMap f).Nodup → a ∈ l → b ∈ l → f a = some k →
      f b = some k → a = b
  | [], _, _, _, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, a, b, hn, ha, hb, hfa, hfb => by
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · simp only [List.filterMap_cons, hfa, List.nodup_cons, List.mem_filterMap] at hn
      exact absurd ⟨b, hb', hfb⟩ hn.1
    · simp only [List.filterMap_cons, hfb, List.nodup_cons, List.mem_filterMap] at hn
      exact absurd ⟨a, ha', hfa⟩ hn.1
    · have hn' : (l.filterMap f).Nodup := by
        simp only [List.filterMap_cons] at hn
        split at hn
        · exact hn
        · exact (List.nodup_cons.mp hn).2
      exact eq_of_filterMap_nodup hn' ha' hb' hfa hfb

theorem titleClass_root {t : String} (h : titleClass t = some .root) : t = rootTitle := by
  unfold titleClass at h
  split at h
  · simp at h
  · split at h
    · rename_i h'; simpa using h'
    · split at h
      · simp at h
      · split at h
        · simp [Option.map] at h
          split at h <;> simp at h
        · simp at h

theorem titlesOk_perm {p q : List String} (h : p.Perm q) : titlesOk p = titlesOk q := by
  unfold titlesOk
  have h1 : p.all (fun t => (titleClass t).isSome) = q.all (fun t => (titleClass t).isSome) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun hp x hx => hp x (h.mem_iff.mpr hx), fun hq x hx => hq x (h.mem_iff.mp hx)⟩
  have h2 : decide p.Nodup = decide q.Nodup := decide_eq_decide.mpr h.nodup_iff
  have h3 : decide (p.filterMap sectionKeyOf).Nodup = decide (q.filterMap sectionKeyOf).Nodup :=
    decide_eq_decide.mpr (h.filterMap _).nodup_iff
  rw [h1, h2, h3]

theorem rowOf_eq_some {p : String × Except Reason (List String)}
    {r : Option (List Nat) × String × String} (h : rowOf p = some r) :
    ∃ c, titleClass p.1 = some c ∧ c ≠ .contents ∧ r.1 = c.key? := by
  unfold rowOf at h
  split at h
  · rename_i c bs hc _
    unfold row at h
    split at h
    · simp at h
    · rename_i hn
      refine ⟨c, hc, ?_, ?_⟩
      · intro hc'; subst hc'; simp at hn
      · simp only [Option.some.injEq] at h; rw [← h]
  · simp at h

theorem rows_unique {pages : List (String × Except Reason (List String))}
    (hok : titlesOk (pages.map Prod.fst) = true) {r r' : Option (List Nat) × String × String}
    (hr : r ∈ pages.filterMap rowOf) (hr' : r' ∈ pages.filterMap rowOf) (hk : r.1 = r'.1) :
    r = r' := by
  simp only [titlesOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hnd⟩, hkeys⟩ := hok
  obtain ⟨p, hp, hpr⟩ := List.mem_filterMap.mp hr
  obtain ⟨p', hp', hpr'⟩ := List.mem_filterMap.mp hr'
  obtain ⟨c, hc, hcn, hrc⟩ := rowOf_eq_some hpr
  obtain ⟨c', hc', hcn', hrc'⟩ := rowOf_eq_some hpr'
  have htitle : p.1 = p'.1 := by
    cases c with
    | contents => exact absurd rfl hcn
    | root =>
      cases c' with
      | contents => exact absurd rfl hcn'
      | root => rw [titleClass_root hc, titleClass_root hc']
      | sectionPage k' => simp [hrc, hrc', TitleClass.key?] at hk
    | sectionPage k =>
      cases c' with
      | contents => exact absurd rfl hcn'
      | root => simp [hrc, hrc', TitleClass.key?] at hk
      | sectionPage k' =>
        simp only [hrc, hrc', TitleClass.key?, Option.some.injEq] at hk
        subst hk
        exact eq_of_filterMap_nodup (k := k) hkeys (List.mem_map_of_mem hp)
          (List.mem_map_of_mem hp') (by simp [sectionKeyOf, hc, TitleClass.key?])
          (by simp [sectionKeyOf, hc', TitleClass.key?])
  have hpp : p = p' := eq_of_map_nodup hnd hp hp' htitle
  subst hpp
  rw [hpr] at hpr'
  exact Option.some.inj hpr'

theorem pagesOfBlocks_perm {p q : List (String × Except Reason (List String))} (h : p.Perm q) :
    pagesOfBlocks p = pagesOfBlocks q := by
  have ht : titlesOk (p.map Prod.fst) = titlesOk (q.map Prod.fst) := titlesOk_perm (h.map _)
  have hr : (p.map Prod.fst).contains rootTitle = (q.map Prod.fst).contains rootTitle :=
    (h.map _).contains_eq
  have hb : p.any (fun x => blocksRefused x.2) = q.any (fun x => blocksRefused x.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    exact ⟨fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.mp hx, h'⟩,
      fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.mpr hx, h'⟩⟩
  unfold pagesOfBlocks
  simp only [ht, hr, hb]
  split
  · rfl
  · rename_i hok
    split
    · rfl
    · split
      · rfl
      · congr 2
        have hok' : titlesOk (p.map Prod.fst) = true := by rw [ht]; simpa using hok
        apply eq_of_perm_of_pairwise (r := fun a b => keyLe a.1 b.1 = true)
        · exact (List.mergeSort_perm _ _).trans
            ((h.filterMap _).trans (List.mergeSort_perm _ _).symm)
        · exact List.pairwise_mergeSort (fun a b c => keyLe_trans a.1 b.1 c.1)
            (fun a b => by simpa using keyLe_total a.1 b.1) _
        · exact List.pairwise_mergeSort (fun a b c => keyLe_trans a.1 b.1 c.1)
            (fun a b => by simpa using keyLe_total a.1 b.1) _
        · intro a ha b hb hab hba
          exact rows_unique hok' (List.mem_mergeSort.mp ha) (List.mem_mergeSort.mp hb)
            (keyLe_antisymm _ _ hab hba)

/-- **The order of the pages.** v1 takes the pages "in any order", and its reasons are "the
first that applies whatever the order of the pages": the kept pages' list, or the refusal, is
the same for every order the same pages are given in. -/
theorem specificationPages_perm {p q : List (String × String)} (h : p.Perm q) :
    specificationPages p = specificationPages q :=
  pagesOfBlocks_perm (h.map _)

/-- The same, for D(PFS). -/
theorem digestSpecification_perm (version : String) {p q : List (String × String)}
    (h : p.Perm q) : digestSpecification version p = digestSpecification version q := by
  unfold digestSpecification preimageSpecification
  rw [specificationPages_perm h]


/-- `<pre>` and a line feed, a block, `</pre>`: one block, as it stands. -/
theorem preTexts_example :
    preTexts "''banner''\n\n<pre>\nA\nB\n</pre>\n\n[[Category:X]]\n" = .ok ["A\nB\n"] := by
  rfl

/-- A pre tag in another case is refused. -/
theorem preTexts_upper : preTexts "<PRE>\nA\n</PRE>" = .error .pre := by rfl

/-! ### D(IS)'s members -/

/-- A lowercase hexadecimal digit, as `isHex64` reads one. -/
def lowHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

theorem hexDigit_low16 : ∀ k : Fin 16, lowHexDigit (Sha256.hexDigit (UInt8.ofNat k.val)) = true := by
  decide

theorem hexDigit_low {n : UInt8} (h : n.toNat < 16) : lowHexDigit (Sha256.hexDigit n) = true := by
  simpa using hexDigit_low16 ⟨n.toNat, h⟩

theorem shiftRight4_lt (b : UInt8) : (b >>> 4).toNat < 16 := by
  simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := b.toNat_lt
  omega

theorem and15_lt (b : UInt8) : (b &&& 15).toNat < 16 := by
  simp [UInt8.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

/-- Every `h` is a digest as D(IS) takes one: 64 lowercase hexadecimal characters. -/
theorem isHex64_pageDigest (blocks : List String) : isHex64 (pageDigest blocks) = true := by
  have hlen := Sha256.digestText_length ("\n".intercalate blocks)
  simp only [isHex64, pageDigest, hlen, beq_self_eq_true, Bool.true_and]
  simp only [Sha256.digestText, Sha256.hex, String.all_bool_eq, String.toList_ofList,
    List.all_eq_true, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  rintro c ⟨b, _, rfl | rfl⟩
  · exact hexDigit_low (shiftRight4_lt b)
  · exact hexDigit_low (and15_lt b)

theorem lookup_mem {t : String} {w : String} :
    ∀ {pages : List (String × String)}, pages.lookup t = some w → (t, w) ∈ pages
  | [], h => by simp at h
  | (k, v) :: ps, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      have : t = k := by simpa using hk
      subst this; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem memberRow_ok {pages : List (String × String)} {t : String} {m : String × String}
    (h : memberRow pages t = .ok m) :
    m.1 = t ∧ ∃ w bs, (t, w) ∈ pages ∧ preTexts w = .ok bs ∧ m.2 = pageDigest bs := by
  unfold memberRow at h
  split at h
  · simp at h
  · rename_i w hw
    split at h
    · rename_i b bs hb
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, w, b :: bs, lookup_mem hw, hb, rfl⟩
    · simp at h

/-- What `mapM` of `memberRow` answers: one row per title, in order, each from its title. -/
theorem mapM_memberRow {pages : List (String × String)} :
    ∀ {l : List String} {ms : List (String × String)}, l.mapM (memberRow pages) = .ok ms →
      ms.map Prod.fst = l ∧ ∀ m ∈ ms, ∃ t ∈ l, memberRow pages t = .ok m
  | [], ms, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | a :: l, ms, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hfa : memberRow pages a with
    | error e => simp [hfa] at h
    | ok b =>
      cases hl : l.mapM (memberRow pages) with
      | error e => simp [hfa, hl] at h
      | ok bs =>
        simp only [hfa, hl, Except.ok.injEq] at h
        subst h
        have ih := mapM_memberRow hl
        refine ⟨?_, ?_⟩
        · rw [List.map_cons, ih.1, (memberRow_ok hfa).1]
        · intro m hm
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact ⟨a, List.mem_cons_self, hfa⟩
          · obtain ⟨t, ht, h'⟩ := ih.2 m hm'
            exact ⟨t, List.mem_cons_of_mem _ ht, h'⟩

/-- What `memberPages` answers on `.ok`: the stated titles sorted, each row from its title;
the stated titles have no repeat and no empty title. -/
theorem memberPages_rows {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms) :
    (stated.mergeSort titleLe).mapM (memberRow pages) = .ok ms ∧
      stated.Nodup ∧ stated.all (fun t => !t.isEmpty) = true := by
  unfold memberPages at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hm2
      split at h
      · simp at h
      · simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or,
          Bool.not_eq_false] at hm2
        refine ⟨h, Decidable.of_not_not hm2.1.1.1.2, ?_⟩
        simp only [List.all_eq_true, Bool.not_eq_true']
        intro t ht
        have := List.any_eq_false.mp (Bool.eq_false_iff.mpr hm2.1.1.1.1) t ht
        simpa using this

/-- **The members' titles.** On `.ok ms`, the members' titles are exactly the stated titles
sorted by `titleLe`. -/
theorem memberPages_titles {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms) :
    ms.map Prod.fst = stated.mergeSort titleLe :=
  (mapM_memberRow (memberPages_rows h).1).1

/-- The members' titles are a permutation of the stated titles and ordered by title. -/
theorem memberPages_sorted {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms) :
    (ms.map Prod.fst).Perm stated ∧ (ms.map Prod.fst).Pairwise (fun a b => a ≤ b) := by
  rw [memberPages_titles h]
  refine ⟨List.mergeSort_perm _ _, ?_⟩
  have hp := List.pairwise_mergeSort (le := titleLe)
    (fun a b c hab hbc => by
      simp only [titleLe, decide_eq_true_eq] at *
      exact String.le_trans hab hbc)
    (fun a b => by
      simp only [titleLe, Bool.or_eq_true, decide_eq_true_eq]
      exact String.le_total a b) stated
  exact hp.imp fun hab => by simpa [titleLe] using hab

/-- **The members' digests.** On `.ok ms`, each member's `h` is `pageDigest` of the blocks of
its own page, that page given under the member's title. -/
theorem memberPages_digest {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms) :
    ∀ m ∈ ms, ∃ w bs, (m.1, w) ∈ pages ∧ preTexts w = .ok bs ∧ m.2 = pageDigest bs := by
  intro m hm
  obtain ⟨t, _, ht⟩ := (mapM_memberRow (memberPages_rows h).1).2 m hm
  have hr := memberRow_ok ht
  rw [hr.1]
  exact hr.2

/-- **The members pass D(IS)'s check.** On `.ok ms`, `membersOk ms` holds: each title is not
empty, each `h` is 64 lowercase hexadecimal characters, no title is twice. -/
theorem memberPages_membersOk {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms) :
    membersOk ms = true := by
  obtain ⟨_, hnd, hne⟩ := memberPages_rows h
  have ht := memberPages_titles h
  unfold membersOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨fun m hm => ⟨?_, ?_⟩, ?_⟩
  · have hmem : m.1 ∈ stated := by
      have : m.1 ∈ ms.map Prod.fst := List.mem_map_of_mem hm
      rw [ht] at this
      exact (List.mergeSort_perm _ _).mem_iff.mp this
    have := List.all_eq_true.mp hne m.1 hmem
    simpa using this
  · obtain ⟨_, bs, _, _, hd⟩ := memberPages_digest h m hm
    rw [hd]
    exact isHex64_pageDigest bs
  · rw [ht]
    exact (List.mergeSort_perm _ _).nodup_iff.mpr hnd

/-- So D(IS) never refuses `members` on what `memberPages` answers. -/
theorem digestInstructionSet_memberPages {stated : List String} {pages : List (String × String)}
    {ms : List (String × String)} (h : memberPages stated pages = .ok ms)
    (version specification : String) :
    digestInstructionSet version specification ms ≠ .error .members := by
  have hok := memberPages_membersOk h
  unfold digestInstructionSet preimageInstructionSet
  cases versionOk version <;> cases isHex64 specification <;>
    simp [hok, Except.map]

/-- **A title of the specification tree is refused.** A title of either list that names the
root, the contents page or a section page is refused `title`. -/
theorem memberPages_treeTitle {stated : List String} {pages : List (String × String)}
    {t : String} (ht : t ∈ stated ∨ t ∈ pages.map Prod.fst) (hc : (titleClass t).isSome = true) :
    memberPages stated pages = .error .title := by
  have hany : (stated ++ pages.map Prod.fst).any treeTitle = true :=
    List.any_eq_true.mpr ⟨t, List.mem_append.mpr ht, by simp [treeTitle, hc]⟩
  unfold memberPages
  simp only [hany, ↓reduceIte]

/-- **A tree title as the wiki spells it is refused.** A title of either list whose page, as
the wiki names it, is the root, the contents page or a section page is refused `title`. -/
theorem memberPages_wikiTreeTitle {stated : List String} {pages : List (String × String)}
    {t : String} (ht : t ∈ stated ∨ t ∈ pages.map Prod.fst)
    (hc : (titleClass (wikiTitle t)).isSome = true) :
    memberPages stated pages = .error .title := by
  have hany : (stated ++ pages.map Prod.fst).any treeTitle = true :=
    List.any_eq_true.mpr ⟨t, List.mem_append.mpr ht, by simp [treeTitle, hc]⟩
  unfold memberPages
  simp only [hany, ↓reduceIte]

/-- The root, spelled with underscores, a lower-case first letter, spaces around and doubled,
or a leading colon, folds to the root. -/
theorem wikiTitle_root_variants :
    wikiTitle "The_Principia_Machina/TPS" = rootTitle ∧
      wikiTitle "the Principia Machina/TPS" = rootTitle ∧
      wikiTitle "  The Principia  Machina/TPS " = rootTitle ∧
      wikiTitle ": The\u00A0Principia_Machina/TPS\u200E" = rootTitle := by
  decide

/-- The tree's own titles are their own fold. -/
theorem wikiTitle_tree : wikiTitle rootTitle = rootTitle ∧ wikiTitle contentsTitle = contentsTitle ∧
    wikiTitle "The Principia Machina/TPS/1.2 Rules" = "The Principia Machina/TPS/1.2 Rules" := by
  decide

end Principia.Digest.Specification
