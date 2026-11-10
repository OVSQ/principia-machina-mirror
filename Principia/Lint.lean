import Principia.Zone.Fields
import Principia.Identity
import Principia.Lint.Tables

/-!
# The prompt lint: coded findings on a sponsor zone and a tool list

v1's `tpc_lint` 0.1.0 (feature F5, "prompt lint as TPC functions PRB runs
locally"): pure functions over the SPONSOR ZONE and the JSON
text of the tool list a model is offered, returning coded findings. The lint is advisory:
it reads no meaning and decides nothing, and no finding refuses, holds or scores anything.

* `lint`: the findings (v1's `lint`), each a code, an item and a locator, never an
  excerpt of the input: the item is a table entry's id, `U+XXXX` for a hidden character,
  `-` for the cap, or an input fault; the locator is `Z:<line>:<column>` in the zone,
  `T:<tool>:<path>` in the tools (member names only from `KNOWN_KEYS`, any other member by
  its rank `@<r>`, list indices, `:key` for a member's key), or `-`.
* `counts` and `countsOf`: the findings counted per code (v1's `lint_counts`), the only
  lint output PRB may place in CAPABILITY.
* `lintNorm` and `nameTokens`: the matching normalization of a text and PL7's tokens of a
  tool name, which v1's corpus tests on their own.

The codes: PL0 the input cannot be linted (exactly one finding, in v1's order of checks);
PL1 hidden characters (the zones' text rule); PL2 credential shapes; PL3 a source of
authorization other than the human; PL4 relaxation or probe-spotting; PL5 a second TPS or
GTP text; PL6 tool text addressed to the model; PL7 open-ended tools; PL8 the zone over
the SPONSOR ZONE CAP; PL9 instructions to persist or to write memory or instruction files.
PL3, PL4 and PL9 carry the negation guard. The tables are v1's text (`Principia.Lint.Tables`).

Matching is v1's: line endings to LF, NFC, A-Z folded to a-z, every run of White_Space one
space; a phrase or a credential shape may not start or end inside a run of `a-z0-9`; a
shape's class runs are possessive. Findings are unique and in v1's order (`Finding.key`).

**Text.** v1 puts the zone and every tool string in NFC, after its line endings, and reads
PL1 from the general category; so does the port, at Unicode 15.1.0, v1's version
(`Principia.Zone.textChars`, `Principia.Zone.disallowed`). Nothing is owed: the lint always answers (`lint_ok`).

A text that is a Lean `String` holds no surrogate, so v1's fault for a `str` holding one
cannot arise; bytes that are not UTF-8 are the `bytes` input's fault, as in v1.
-/

namespace Principia.Lint

open Principia.Zone (Value whiteSpace)

/-! ## Constants -/

/-- v1's `VERSION`. -/
def version : String := "0.1.0"

/-- `LINT_MAX_BYTES`: the largest zone or tool text, in bytes of UTF-8. -/
def maxBytes : Nat := 1048576

/-- `LINT_CAP_MAX`: the largest SPONSOR ZONE CAP, in code points. -/
def capMax : Nat := 1048576

/-! ## Findings -/

/-- A finding's code. -/
inductive Code where
  | pl0 | pl1 | pl2 | pl3 | pl4 | pl5 | pl6 | pl7 | pl8 | pl9
  deriving DecidableEq, Repr

/-- The codes in v1's order (`CODES`). -/
def Code.all : List Code := [.pl0, .pl1, .pl2, .pl3, .pl4, .pl5, .pl6, .pl7, .pl8, .pl9]

/-- A code's rank in `CODES`. -/
def Code.index : Code → Nat
  | .pl0 => 0 | .pl1 => 1 | .pl2 => 2 | .pl3 => 3 | .pl4 => 4
  | .pl5 => 5 | .pl6 => 6 | .pl7 => 7 | .pl8 => 8 | .pl9 => 9

/-- `PL0` ... `PL9`. -/
def Code.text (c : Code) : String := "PL" ++ toString c.index

/-- A code that a scan finds: every code but PL0. -/
inductive Detector where
  | pl1 | pl2 | pl3 | pl4 | pl5 | pl6 | pl7 | pl8 | pl9
  deriving DecidableEq, Repr

/-- A detector's code. -/
def Detector.code : Detector → Code
  | .pl1 => .pl1 | .pl2 => .pl2 | .pl3 => .pl3 | .pl4 => .pl4 | .pl5 => .pl5
  | .pl6 => .pl6 | .pl7 => .pl7 | .pl8 => .pl8 | .pl9 => .pl9

/-- No scan finds PL0. -/
theorem Detector.code_ne_pl0 (d : Detector) : d.code ≠ .pl0 := by cases d <;> decide

/-- PL0's items: why the input cannot be linted. -/
inductive Fault where
  /-- `ZONE-TYPE`: the zone is not text. -/
  | zoneType
  /-- `ZONE-UTF8`: the zone's bytes are not UTF-8. -/
  | zoneUtf8
  /-- `ZONE-SIZE`: over `maxBytes` of UTF-8. -/
  | zoneSize
  /-- `TOOLS-TYPE` -/
  | toolsType
  /-- `TOOLS-UTF8` -/
  | toolsUtf8
  /-- `TOOLS-SIZE` -/
  | toolsSize
  /-- `TOOLS-JSON`: identity's canonical tools refuse the text (D(PROMPT)'s own refusal). -/
  | toolsJson
  /-- `TOOLS-SHAPE`: not a JSON list of objects. -/
  | toolsShape
  /-- `CAP`: not an integer from 1 to `capMax`. -/
  | cap
  deriving DecidableEq, Repr

/-- v1's word for a fault. -/
def Fault.text : Fault → String
  | .zoneType => "ZONE-TYPE" | .zoneUtf8 => "ZONE-UTF8" | .zoneSize => "ZONE-SIZE"
  | .toolsType => "TOOLS-TYPE" | .toolsUtf8 => "TOOLS-UTF8" | .toolsSize => "TOOLS-SIZE"
  | .toolsJson => "TOOLS-JSON" | .toolsShape => "TOOLS-SHAPE" | .cap => "CAP"

/-- Every fault, for reading v1's word back. -/
def Fault.all : List Fault :=
  [.zoneType, .zoneUtf8, .zoneSize, .toolsType, .toolsUtf8, .toolsSize, .toolsJson,
    .toolsShape, .cap]

/-- A finding's item. -/
inductive Item where
  /-- A table entry's id (`PL2-01` ...). -/
  | entry (id : String)
  /-- PL1: the hidden code point, shown `U+XXXX`. -/
  | codePoint (c : Char)
  /-- PL8: `-`. -/
  | dash
  /-- PL0: the fault. -/
  | fault (f : Fault)
  deriving DecidableEq, Repr

/-- An item's text. -/
def Item.text : Item → String
  | .entry id => id
  | .codePoint c => Principia.Zone.codePoint c
  | .dash => "-"
  | .fault f => f.text

/-- One step of a tool locator's path. -/
inductive Seg where
  /-- A member named in `KNOWN_KEYS`, shown by its name. -/
  | name (k : String)
  /-- Any other member, shown `@<rank>`: its rank in canonical key order. -/
  | rank (r : Nat)
  /-- A list index. -/
  | index (r : Nat)
  deriving DecidableEq, Repr

/-- A step's text. -/
def Seg.text : Seg → String
  | .name k => k
  | .rank r => "@" ++ toString r
  | .index r => toString r

/-- Where a finding is. -/
inductive Locator where
  /-- `-`: the input as a whole (PL0). -/
  | none
  /-- `Z:<line>:<column>`, both from 1, in code points after LF and NFC. -/
  | zone (line col : Nat)
  /-- `T:<tool>:<path>`, the tool's index from 0; `key` when the finding is in a key. -/
  | tool (index : Nat) (path : List Seg) (key : Bool)
  deriving DecidableEq, Repr

/-- A tool locator's text after `T:<tool>:`: the path, and `:key` for a key. -/
def pathText (path : List Seg) (key : Bool) : String :=
  "/".intercalate (path.map Seg.text) ++ (if key then ":key" else "")

/-- A locator's text. -/
def Locator.text : Locator → String
  | .none => "-"
  | .zone l c => "Z:" ++ toString l ++ ":" ++ toString c
  | .tool i path key => "T:" ++ toString i ++ ":" ++ pathText path key

/-- A finding. -/
structure Finding where
  /-- Its code. -/
  code : Code
  /-- Its item. -/
  item : Item
  /-- Its locator. -/
  locator : Locator
  deriving DecidableEq, Repr

/-- A text's place in code point order, as a list of numbers: each code point plus one,
then 0, so that a text before another in code point order (a prefix first) comes first,
and a list of such texts compares as the texts one after the other. -/
def textKey (s : String) : List Nat := s.toList.map (·.toNat + 1) ++ [0]

/-- v1's sort key, `(code, zone before tools, line and column or tool and path, item)`,
as one list of numbers compared lexicographically. Two findings with one key are one
finding (`(code, item, locator)` in v1). -/
def Finding.key (f : Finding) : List Nat :=
  match f.locator with
  | .zone l c => [f.code.index, 0, l, c] ++ textKey "" ++ textKey f.item.text
  | .tool i path key => [f.code.index, 1, i, 0] ++ textKey (pathText path key) ++ textKey f.item.text
  | .none => [f.code.index, 2, 0, 0] ++ textKey "" ++ textKey f.item.text

/-- v1's canonical text of a finding (`lint_json`'s item; every field is ASCII). -/
def Finding.json (f : Finding) : String :=
  "{\"code\":\"" ++ f.code.text ++ "\",\"item\":\"" ++ f.item.text ++ "\",\"locator\":\"" ++
    f.locator.text ++ "\"}"

/-- `lint_json`: the canonical text of a finding list. -/
def findingsJson (fs : List Finding) : String := "[" ++ ",".intercalate (fs.map Finding.json) ++ "]"

/-- A finding a scan makes: its detector, never PL0. -/
structure Found where
  /-- What found it. -/
  detector : Detector
  /-- Its item. -/
  item : Item
  /-- Its locator. -/
  locator : Locator

/-- The finding. -/
def Found.finding (f : Found) : Finding := ⟨f.detector.code, f.item, f.locator⟩

/-- The PL0 finding of a fault. -/
def pl0 (f : Fault) : Finding := ⟨.pl0, .fault f, .none⟩

/-! ## Outcomes -/

/-- v1's `ValueError` words, of the functions other than `lint`. -/
inductive Refusal where
  /-- `findings`: `lint_counts` of a list that is not findings. -/
  | findings
  /-- `text`: `lint_norm` of what is not a text, or of a text over `maxBytes`. -/
  | text
  /-- `name`: `name_tokens` of what is not a text, or of a text over `maxBytes`. -/
  | name
  deriving DecidableEq, Repr

/-- v1's word. -/
def Refusal.message : Refusal → String
  | .findings => "findings"
  | .text => "text"
  | .name => "name"

/-- Why a function stops without a value. -/
inductive Stop where
  /-- v1 refuses with this word. -/
  | refused (r : Refusal)
  deriving DecidableEq, Repr

/-- A function's outcome: its value, or why it stops. -/
abbrev Outcome := Except Stop

/-! ## Inputs -/

/-- An input of `lint`, as v1 takes it: a text, bytes read as UTF-8, or anything else. -/
inductive Input where
  /-- A text (v1's `str`). -/
  | text (s : String)
  /-- Bytes (v1's `bytes`), read as UTF-8. -/
  | bytes (b : ByteArray)
  /-- Anything else. -/
  | other

/-- v1's `_text_of`: the input as a text, or its fault (type, UTF-8, size, in v1's order). -/
def textOf (x : Input) (type utf8 size : Fault) : Except Fault String :=
  match x with
  | .other => .error type
  | .bytes b =>
    match String.fromUTF8? b with
    | none => .error utf8
    | some s => if b.size > maxBytes then .error size else .ok s
  | .text s => if s.utf8ByteSize > maxBytes then .error size else .ok s

/-- The cap: an integer from 1 to `capMax` (a boolean, a fraction or a text is not one). -/
def capOf : Value → Option Nat
  | .int n => if 1 ≤ n ∧ n ≤ capMax then some n.toNat else none
  | _ => none

/-! ## The text every locator counts in -/

/-- v1's `_lint_text`: line endings as LF (the zones' `_eol`), then NFC; the text every
locator counts in. -/
def lintText (s : String) : Array Char := (Principia.Zone.textChars s).toArray

/-- The code points of a text v1's text rule refuses, with their indices. -/
def hidden (t : Array Char) : List (Nat × Char) := Id.run do
  let mut out : List (Nat × Char) := []
  for i in [0:t.size] do
    let c := t[i]!
    if Principia.Zone.disallowed c then out := (i, c) :: out
  return out.reverse

/-- Each index's line and column, both from 1. -/
def positions (t : Array Char) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := Array.mkEmpty t.size
  let mut line := 1
  let mut start := 0
  for i in [0:t.size] do
    out := out.push (line, i + 1 - start)
    if t[i]! == '\n' then
      line := line + 1
      start := i + 1
  return out

/-! ## Matching -/

/-- `_W`: `a-z0-9`, the characters a phrase may not start or end inside a run of. -/
def isWord (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- A-Z folded to a-z, ASCII only. -/
def fold (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- v1's `_normalize`: the matching text (A-Z folded, every run of White_Space one space)
and, for each of its code points, its index in the text. -/
def normalize (t : Array Char) : Array Char × Array Nat := Id.run do
  let mut out : Array Char := Array.mkEmpty t.size
  let mut map : Array Nat := Array.mkEmpty t.size
  let mut inSpace := false
  for i in [0:t.size] do
    let c := t[i]!
    if whiteSpace c then
      unless inSpace do
        out := out.push ' '
        map := map.push i
      inSpace := true
    else
      out := out.push (fold c)
      map := map.push i
      inSpace := false
  return (out, map)

/-- The code point at `i` is in `a-z0-9`. -/
def wordAt (m : Array Char) (i : Nat) : Bool := (m[i]?.map isWord).getD false

/-- The text has `a` at `pos`. -/
def startsAt (m : Array Char) (pos : Nat) : List Char → Bool
  | [] => true
  | c :: cs => m[pos]? == some c && startsAt m (pos + 1) cs

/-- v1's start boundary: a match may not start inside a run of `a-z0-9`. -/
def startInside (m : Array Char) (j : Nat) : Bool := wordAt m j && j > 0 && wordAt m (j - 1)

/-- v1's end boundary of a phrase ending before `pos`. -/
def endOk (m : Array Char) (pos : Nat) : Bool :=
  !wordAt m (pos - 1) || pos ≥ m.size || !wordAt m pos

/-- v1's `_tmatch`: some phrase of the template's parts, from `k` on, matches at `pos` and
ends at a boundary. -/
def tmatch (m : Array Char) (pos : Nat) : Template → Bool
  | [] => endOk m pos
  | alts :: rest => alts.any fun a => startsAt m pos a && tmatch m (pos + a.length) rest

/-- A possessive run: how many of the class's characters follow `pos`, at most `hi`. -/
def runLength (m : Array Char) (chars : List Char) (pos hi : Nat) : Nat :=
  go 0 hi
where
  /-- `k` taken, `fuel` more allowed. -/
  go (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 =>
      match m[pos + k]? with
      | some c => if chars.contains c then go (k + 1) fuel else k
      | none => k

/-- A shape's elements from `pos`: where they end, or `none`. -/
def matchElements (m : Array Char) (pos : Nat) : List Element → Option Nat
  | [] => some pos
  | .lit s :: rest => if startsAt m pos s then matchElements m (pos + s.length) rest else none
  | .cls chars lo hi :: rest =>
    let n := runLength m chars pos hi
    if n < lo then none else matchElements m (pos + n) rest

/-- v1's `_pattern_at`: the shape matches at `j`, a closing literal ending at a boundary and
a closing class run at a character outside its class. -/
def patternAt (m : Array Char) (j : Nat) (els : List Element) : Bool :=
  !startInside m j &&
    match matchElements m j els with
    | none => false
    | some pos =>
      match els.getLast? with
      | some (.lit s) => !((s.getLast?.map isWord).getD false && wordAt m pos)
      | some (.cls chars _ _) => !((m[pos]?.map chars.contains).getD false)
      | none => true

/-- A rule of the tables. -/
inductive Rule where
  /-- A credential shape (PL2). -/
  | shape (els : List Element)
  /-- A phrase template. -/
  | phrase (parts : Template)

/-- The rule matches at `j` (v1's `_pattern_at`, or the start boundary and `_tmatch`). -/
def Rule.matchesAt (m : Array Char) (j : Nat) : Rule → Bool
  | .shape els => patternAt m j els
  | .phrase parts => !startInside m j && tmatch m j parts

/-- The characters a match of the rule can start with; `none` when it could start with any. -/
def Rule.firstChars : Rule → Option (List Char)
  | .shape (.lit (c :: _) :: _) => some [c]
  | .shape _ => none
  | .phrase (alts :: _) => alts.mapM List.head?
  | .phrase [] => none

/-- A rule and what it finds. -/
structure Probe where
  /-- Its code. -/
  detector : Detector
  /-- The entry's id. -/
  id : String
  /-- The rule. -/
  rule : Rule
  /-- Under the negation guard (PL3, PL4, PL9). -/
  guarded : Bool

/-- Probes by the character a match starts with: an ASCII character's bucket, the probes
that can start with another character, and those that can start with any. -/
structure Dispatch where
  /-- By ASCII character. -/
  ascii : Array (List Probe)
  /-- Starting with a character beyond ASCII. -/
  wide : List Probe
  /-- Starting with any character. -/
  anywhere : List Probe

/-- Sort the probes into their buckets. -/
def Dispatch.ofProbes (ps : List Probe) : Dispatch :=
  ps.foldl (init := ⟨Array.replicate 128 [], [], []⟩) fun d p =>
    match p.rule.firstChars with
    | none => { d with anywhere := d.anywhere ++ [p] }
    | some cs =>
      let cs := cs.eraseDups
      let d := if cs.any (·.toNat ≥ 128) then { d with wide := d.wide ++ [p] } else d
      cs.foldl (init := d) fun d c =>
        if c.toNat < 128 then { d with ascii := d.ascii.modify c.toNat (· ++ [p]) } else d

/-- The probes to try where the text has `c`: every probe whose match could start there. -/
def Dispatch.at (d : Dispatch) (c : Char) : List Probe :=
  (if c.toNat < 128 then d.ascii.getD c.toNat [] else d.wide) ++ d.anywhere

/-- Every match of the probes, with the index it starts at. Trying only the probes a
match could start with at each index finds what trying every probe at every index finds
(v1's `_cands` and `_template_hits`), in another order; findings are sorted after. -/
def scan (d : Dispatch) (m : Array Char) : List (Probe × Nat) := Id.run do
  let mut out : List (Probe × Nat) := []
  for j in [0:m.size] do
    for p in d.at m[j]! do
      if p.rule.matchesAt m j then out := (p, j) :: out
  return out

/-- A phrase table's probes. -/
def phraseProbes (d : Detector) (guarded : Bool) (es : List (Entry Template)) : List Probe :=
  es.flatMap fun e => e.rules.map fun parts => ⟨d, e.id, .phrase parts, guarded⟩

/-- PL2's probes. -/
def shapeProbes : List Probe :=
  tables.pl2.flatMap fun e => e.rules.map fun els => ⟨.pl2, e.id, .shape els, false⟩

/-- The zone's probes: PL2, then PL3, PL4, PL5, PL9 (PL3, PL4 and PL9 guarded). -/
def zoneDispatch : Dispatch :=
  .ofProbes (shapeProbes ++ phraseProbes .pl3 true tables.pl3 ++ phraseProbes .pl4 true tables.pl4 ++
    phraseProbes .pl5 false tables.pl5 ++ phraseProbes .pl9 true tables.pl9)

/-- A tool string's probes outside `description` and `title`, and a key's: PL2. -/
def shapeDispatch : Dispatch := .ofProbes shapeProbes

/-- A `description` or `title` string's probes: PL2 and PL6. -/
def toolTextDispatch : Dispatch := .ofProbes (shapeProbes ++ phraseProbes .pl6 false tables.pl6)

/-- PL7's description probes. -/
def pl7Dispatch : Dispatch :=
  .ofProbes (tables.pl7.flatMap fun e => e.templates.map fun parts => ⟨.pl7, e.id, .phrase parts, false⟩)

/-! ## The negation guard (PL3, PL4, PL9) -/

/-- `a-z`, `0-9`, the apostrophe and U+2019: the characters of a token. -/
def isToken (c : Char) : Bool := isWord c || c == '\'' || c == '’'

/-- v1's `_negated`'s scan, backwards from index `p - 1`: the tokens found so far (nearest
first), at most `NEG_WINDOW`, stopping at a sentence stop. `cur` is the token being read. -/
def negTokens (m : Array Char) : Nat → List Char → List String → List String
  | 0, cur, toks =>
    if !cur.isEmpty && toks.length < tables.negWindow then toks ++ [String.ofList cur] else toks
  | p + 1, cur, toks =>
    let c := m[p]!
    if isToken c then negTokens m p (c :: cur) toks
    else
      let toks' := if cur.isEmpty then toks else toks ++ [String.ofList cur]
      if !cur.isEmpty && toks'.length == tables.negWindow then toks'
      else if tables.negStop.contains c then toks'
      else negTokens m p [] toks'

/-- The negation guard: one of the last `NEG_WINDOW` tokens before `j`, within its
sentence, is a negation. -/
def negated (m : Array Char) (j : Nat) : Bool := (negTokens m j [] []).any tables.neg.contains

/-! ## The zone -/

/-- The zone's findings: PL1 per occurrence, PL8, then the zone's tables. -/
def zoneFound (t : Array Char) (cap : Nat) : List Found :=
  let pos := positions t
  let loc (i : Nat) : Locator := let (l, c) := pos.getD i (0, 0); .zone l c
  let pl1 := (hidden t).map fun (i, c) => (⟨.pl1, .codePoint c, loc i⟩ : Found)
  let pl8 : List Found := if t.size > cap then [⟨.pl8, .dash, loc cap⟩] else []
  let (m, map) := normalize t
  let phrases := (scan zoneDispatch m).filterMap fun (p, j) =>
    if p.guarded && negated m j then none
    else some (⟨p.detector, .entry p.id, loc (map.getD j 0)⟩ : Found)
  pl1 ++ pl8 ++ phrases

/-! ## The tools -/

/-- v1's `_read_canon`'s tree of a canonical JSON text. -/
inductive Node where
  /-- An object, its members in canonical key order. -/
  | obj (members : List (String × Node))
  /-- A list. -/
  | arr (items : List Node)
  /-- A text. -/
  | str (s : String)
  /-- A number, `true`, `false` or `null`, as written. -/
  | lit (text : String)
  deriving Inhabited

/-- A canonical string's body after its opening quote: the decoded code points, in
reverse, and the text after the closing quote. -/
def readCanonString : List Char → List Char → Option (List Char × List Char)
  | acc, '"' :: rest => some (acc, rest)
  | acc, '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    match Principia.Identity.hex4 a b c d with
    | some cp => readCanonString (Char.ofNat cp :: acc) rest
    | none => none
  | acc, '\\' :: e :: rest =>
    match e with
    | '"' => readCanonString ('"' :: acc) rest
    | '\\' => readCanonString ('\\' :: acc) rest
    | 'b' => readCanonString ('\x08' :: acc) rest
    | 'f' => readCanonString ('\x0c' :: acc) rest
    | 'n' => readCanonString ('\n' :: acc) rest
    | 'r' => readCanonString ('\r' :: acc) rest
    | 't' => readCanonString ('\t' :: acc) rest
    | _ => none
  | acc, c :: rest => readCanonString (c :: acc) rest
  | _, [] => none

/-- A literal's characters: up to `,`, `]`, `}` or the end. -/
def takeLiteral : List Char → List Char × List Char
  | c :: cs => if c == ',' || c == ']' || c == '}' then ([], c :: cs)
    else let (l, r) := takeLiteral cs; (c :: l, r)
  | [] => ([], [])

mutual
/-- v1's `_read_canon`'s `value()`, on a canonical text (no white space); `fuel` bounds
the recursion. -/
def readCanonValue : Nat → List Char → Option (Node × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match cs with
    | '{' :: '}' :: rest => some (.obj [], rest)
    | '{' :: rest => readCanonMembers fuel rest []
    | '[' :: ']' :: rest => some (.arr [], rest)
    | '[' :: rest => readCanonItems fuel rest []
    | '"' :: rest => (readCanonString [] rest).map fun (s, r) => (.str (String.ofList s.reverse), r)
    | cs => let (l, r) := takeLiteral cs; some (.lit (String.ofList l), r)

/-- An object's members, in reverse so far, and the text after `}`. -/
def readCanonMembers : Nat → List Char → List (String × Node) → Option (Node × List Char)
  | 0, _, _ => none
  | fuel + 1, '"' :: cs, acc => do
    let (k, r) ← readCanonString [] cs
    match r with
    | ':' :: r => do
      let (v, r) ← readCanonValue fuel r
      let acc := (String.ofList k.reverse, v) :: acc
      match r with
      | ',' :: r => readCanonMembers fuel r acc
      | '}' :: r => some (.obj acc.reverse, r)
      | _ => none
    | _ => none
  | _, _, _ => none

/-- A list's items, in reverse so far, and the text after `]`. -/
def readCanonItems : Nat → List Char → List Node → Option (Node × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc => do
    let (v, r) ← readCanonValue fuel cs
    match r with
    | ',' :: r => readCanonItems fuel r (v :: acc)
    | ']' :: r => some (.arr (v :: acc).reverse, r)
    | _ => none
end

/-- The tree of a canonical text, which is read whole. -/
def readCanon (canon : String) : Option Node :=
  let cs := canon.toList
  match readCanonValue (2 * cs.length + 2) cs with
  | some (v, []) => some v
  | _ => none

/-- The tools as a list of objects, each its members; `none` for another shape
(`TOOLS-SHAPE`). -/
def toolList (canon : String) : Option (List (List (String × Node))) :=
  match readCanon canon with
  | some (.arr items) => items.mapM fun | .obj ms => some ms | _ => none
  | _ => none

/-- A member's step: its name when `KNOWN_KEYS` holds it, else its rank. -/
def segOf (k : String) (r : Nat) : Seg := if tables.knownKeys.contains k then .name k else .rank r

/-- A member's step shows its name only when `KNOWN_KEYS` holds it: no other key is ever
shown. -/
theorem segOf_name {k n : String} {r : Nat} (h : segOf k r = .name n) :
    n ∈ tables.knownKeys := by
  unfold segOf at h
  split at h
  · rename_i hk
    cases h
    exact List.contains_iff_mem.mp hk
  · cases h

/-- v1's `_tool_string`: PL1 (each distinct code point once, after the order's
uniqueness), PL2, and PL6 in a `description` or `title` value, on the string's
`_lint_text`. -/
def toolString (s : String) (i : Nat) (path : List Seg) (key pl6 : Bool) : List Found :=
  let loc := Locator.tool i path key
  let t := lintText s
  let pl1 := (hidden t).map fun (_, c) => (⟨.pl1, .codePoint c, loc⟩ : Found)
  let m := (normalize t).1
  let hits := scan (if pl6 then toolTextDispatch else shapeDispatch) m
  pl1 ++ hits.map fun (p, _) => (⟨p.detector, .entry p.id, loc⟩ : Found)

mutual
/-- v1's `_walk` of a value, `keyName` the member it is the value of. -/
def walkNode (i : Nat) (path : List Seg) (keyName : Option String) : Node → List Found
  | .obj ms => walkMembers i path 0 ms
  | .arr xs => walkItems i path 0 xs
  | .str s => toolString s i path false (keyName == some "description" || keyName == some "title")
  | .lit _ => []

/-- The members of an object from rank `r`: each key, then its value. -/
def walkMembers (i : Nat) (path : List Seg) (r : Nat) : List (String × Node) → List Found
  | [] => []
  | (k, v) :: rest =>
    let p := path ++ [segOf k r]
    toolString k i p true false ++ walkNode i p (some k) v ++ walkMembers i path (r + 1) rest

/-- The items of a list from index `r`. -/
def walkItems (i : Nat) (path : List Seg) (r : Nat) : List Node → List Found
  | [] => []
  | v :: rest => walkNode i (path ++ [.index r]) none v ++ walkItems i path (r + 1) rest
end

/-! ## PL7: open-ended tools -/

/-- `_ALNUM`'s capitals. -/
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- `_LOWDIG` -/
def isLowerOrDigit (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- v1's tokenizer: `cur` the token being read (reversed), `toks` those read (reversed). A
token is a maximal run of ASCII letters and digits, split where a lower-case letter or a
digit is followed by a capital. -/
def tokensGo : List Char → List Char → List String → List String
  | [], cur, toks => (if cur.isEmpty then toks else String.ofList cur.reverse :: toks).reverse
  | c :: cs, cur, toks =>
    if isUpper c || isLowerOrDigit c then
      match cur with
      | p :: _ =>
        if isUpper c && isLowerOrDigit p then tokensGo cs [c] (String.ofList cur.reverse :: toks)
        else tokensGo cs (c :: cur) toks
      | [] => tokensGo cs [c] toks
    else if cur.isEmpty then tokensGo cs [] toks
    else tokensGo cs [] (String.ofList cur.reverse :: toks)

/-- PL7's tokens of a known text, folded. -/
def tokensOf (t : Array Char) : List String :=
  (tokensGo t.toList [] []).map fun tok => String.ofList (tok.toList.map fold)

/-- The token sequence occurs in the tokens, in order and together. -/
def hasSeq (toks seq : List String) : Bool :=
  match toks with
  | [] => seq.isEmpty
  | _ :: rest => seq.isPrefixOf toks || hasSeq rest seq

/-- An object's member. -/
def memberOf (ms : List (String × Node)) (k : String) : Option Node := ms.lookup k

/-- v1's `_pl7`: the tool's `name` and `description`, and those of its `function` object. -/
def pl7Found (i : Nat) (tool : List (String × Node)) : List Found :=
  let places : List (List (String × Node) × List Seg) :=
    (tool, []) :: (match memberOf tool "function" with
      | some (.obj fm) => [(fm, [Seg.name "function"])]
      | _ => [])
  places.flatMap fun (obj, pre) =>
    let byDescription : List String :=
      match memberOf obj "description" with
      | some (.str s) => ((scan pl7Dispatch (normalize (lintText s)).1).map (·.1.id)).eraseDups
      | _ => []
    let toks : Option (List String) :=
      match memberOf obj "name" with
      | some (.str s) => some (tokensOf (lintText s))
      | _ => none
    tables.pl7.flatMap fun e =>
      (if byDescription.contains e.id then
        [(⟨.pl7, .entry e.id, .tool i (pre ++ [.name "description"]) false⟩ : Found)] else []) ++
      (match toks with
       | some ts =>
         if e.seqs.any (hasSeq ts) then [(⟨.pl7, .entry e.id, .tool i (pre ++ [.name "name"]) false⟩ : Found)]
         else []
       | none => [])

/-- Every tool's findings: its strings and keys, then PL7. -/
def toolsFound : Nat → List (List (String × Node)) → List Found
  | _, [] => []
  | i, tool :: rest => walkMembers i [] 0 tool ++ pl7Found i tool ++ toolsFound (i + 1) rest

/-! ## Order and uniqueness -/

/-- The findings after the first, keeping each whose key is past the last kept. -/
def keepAfter (last : List Nat) : List (List Nat × Finding) → List Finding
  | [] => []
  | (k, f) :: rest => if last < k then f :: keepAfter k rest else keepAfter last rest

/-- The first finding, then those past it. -/
def keepIncreasing : List (List Nat × Finding) → List Finding
  | [] => []
  | (k, f) :: rest => f :: keepAfter k rest

/-- v1's ORDER: the findings sorted by their key, each key once. -/
def ordered (fs : List Finding) : List Finding :=
  keepIncreasing ((fs.map fun f => (f.key, f)).mergeSort fun a b => decide (a.1 ≤ b.1))

/-! ## The lint -/

/-- `lint(zone, tools, cap)`: the findings, in v1's order. -/
def lint (zone tools : Input) (cap : Value) : Outcome (List Finding) :=
  match textOf zone .zoneType .zoneUtf8 .zoneSize with
  | .error f => .ok [pl0 f]
  | .ok z =>
  match textOf tools .toolsType .toolsUtf8 .toolsSize with
  | .error f => .ok [pl0 f]
  | .ok t =>
  -- v1's `canonical_tools`: every string of the tools in NFC.
  match Principia.Identity.canonicalJson t with
  | none => .ok [pl0 .toolsJson]
  | some canon =>
  match toolList canon with
  | none => .ok [pl0 .toolsShape]
  | some tl =>
  match capOf cap with
  | none => .ok [pl0 .cap]
  | some n => .ok (ordered ((zoneFound (lintText z) n ++ toolsFound 0 tl).map Found.finding))

/-! ## Counts, the normalization and the tokens -/

/-- `lint_counts` of findings: the number of each code, in `CODES` order. -/
def counts (fs : List Finding) : List Nat := Code.all.map fun c => (fs.filter (·.code == c)).length

/-- `counts_json`: `{"PL0":n,...,"PL9":n}`. -/
def countsJson (ns : List Nat) : String :=
  "{" ++ ",".intercalate ((Code.all.zip ns).map fun (c, n) => "\"" ++ c.text ++ "\":" ++ toString n) ++ "}"

/-- A finding as `lint_counts` checks it: an object of exactly `code`, `item` and
`locator`, every value a text, the code one of `CODES`. -/
def findingCode : Value → Option Code
  | .obj kvs =>
    if kvs.length == 3 && ["code", "item", "locator"].all (fun k => kvs.any (·.1 == k)) &&
        kvs.all (fun kv => match kv.2 with | .str _ => true | _ => false) then
      match kvs.lookup "code" with
      | some (.str s) => Code.all.find? (·.text == s)
      | _ => none
    else none
  | _ => none

/-- `lint_counts(findings)` of a value: the counts, or refused `findings`. -/
def countsOf : Value → Outcome (List Nat)
  | .arr xs =>
    match xs.mapM findingCode with
    | some cs => .ok (Code.all.map fun c => (cs.filter (· == c)).length)
    | none => .error (.refused .findings)
  | _ => .error (.refused .findings)

/-- A text argument: a text of at most `maxBytes`, else refused with the word. -/
def textArg (v : Value) (r : Refusal) : Outcome String :=
  match v with
  | .str s => if s.utf8ByteSize > maxBytes then .error (.refused r) else .ok s
  | _ => .error (.refused r)

/-- `lint_norm(text)`: the matching normalization of a text. -/
def lintNorm (v : Value) : Outcome String := do
  let t := lintText (← textArg v .text)
  pure (String.ofList (normalize t).1.toList)

/-- `name_tokens(name)`: PL7's tokens of a tool name. -/
def nameTokens (v : Value) : Outcome (List String) := do
  let t := lintText (← textArg v .name)
  pure (tokensOf t)

/-- The tables' version and recorded SHA-256 (the corpus's `tables`). -/
def tablesAnswer : String := "tables " ++ tablesVersion ++ " " ++ tablesSha256

/-! ## Theorems -/

/-- `_lint_text` is NFC of the text with its line endings as LF. -/
theorem lintText_nfc (s : String) :
    (lintText s).toList = Unicode.nfcList (Principia.Zone.eolChars s.toList) := by
  simp [lintText, Principia.Zone.textChars_eq]

/-- The lint never stops: it always answers with findings, PL0's among them. -/
theorem lint_ok (z t : Input) (cap : Value) : ∃ fs, lint z t cap = .ok fs := by
  unfold lint
  repeat' split
  all_goals exact ⟨_, rfl⟩

/-- `keepAfter` keeps only findings of the list. -/
theorem mem_keepAfter {f : Finding} {last : List Nat} {l : List (List Nat × Finding)}
    (h : f ∈ keepAfter last l) : ∃ k, (k, f) ∈ l := by
  induction l generalizing last with
  | nil => simp [keepAfter] at h
  | cons x rest ih =>
    obtain ⟨k, g⟩ := x
    unfold keepAfter at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact ⟨k, h ▸ List.mem_cons_self⟩
      · obtain ⟨k', hk'⟩ := ih h
        exact ⟨k', List.mem_cons_of_mem _ hk'⟩
    · obtain ⟨k', hk'⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hk'⟩

/-- `ordered` keeps only findings it was given. -/
theorem mem_ordered {f : Finding} {fs : List Finding} (h : f ∈ ordered fs) : f ∈ fs := by
  unfold ordered at h
  generalize hl : (fs.map fun f => (f.key, f)).mergeSort (fun a b => decide (a.1 ≤ b.1)) = l at h
  have key_mem : ∀ k g, (k, g) ∈ l → g ∈ fs := by
    intro k g hm
    rw [← hl, List.mem_mergeSort, List.mem_map] at hm
    obtain ⟨g', hg', he⟩ := hm
    cases he
    exact hg'
  cases l with
  | nil => simp [keepIncreasing] at h
  | cons x rest =>
    obtain ⟨k, g⟩ := x
    simp only [keepIncreasing] at h
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ key_mem k g List.mem_cons_self
    · obtain ⟨k', hk'⟩ := mem_keepAfter h
      exact key_mem k' f (List.mem_cons_of_mem _ hk')

/-- Every key `keepAfter` keeps is past `last`, and each is past the ones before it. -/
theorem keepAfter_increasing (last : List Nat) (l : List (List Nat × Finding))
    (hk : ∀ p ∈ l, p.1 = p.2.key) :
    (∀ f ∈ keepAfter last l, last < f.key) ∧ (keepAfter last l).Pairwise (fun a b => a.key < b.key) := by
  induction l generalizing last with
  | nil => simp [keepAfter]
  | cons x rest ih =>
    obtain ⟨k, g⟩ := x
    have hrest : ∀ p ∈ rest, p.1 = p.2.key := fun p hp => hk p (List.mem_cons_of_mem _ hp)
    have hkg : k = g.key := hk (k, g) List.mem_cons_self
    unfold keepAfter
    split
    · rename_i hlt
      obtain ⟨h1, h2⟩ := ih k hrest
      refine ⟨?_, ?_⟩
      · intro f hf
        rcases List.mem_cons.mp hf with hf | hf
        · subst hf; rw [← hkg]; exact hlt
        · exact List.lt_trans hlt (h1 f hf)
      · refine List.Pairwise.cons (fun f hf => ?_) h2
        rw [← hkg]; exact h1 f hf
    · exact ih last hrest

/-- v1's ORDER holds: each finding's key is before the next one's, so the findings are
sorted and unique. -/
theorem ordered_increasing (fs : List Finding) :
    (ordered fs).Pairwise (fun a b => a.key < b.key) := by
  unfold ordered
  generalize hl : (fs.map fun f => (f.key, f)).mergeSort (fun a b => decide (a.1 ≤ b.1)) = l
  have hk : ∀ p ∈ l, p.1 = p.2.key := by
    intro p hp
    rw [← hl, List.mem_mergeSort, List.mem_map] at hp
    obtain ⟨g, _, he⟩ := hp
    subst he
    rfl
  cases l with
  | nil => simp [keepIncreasing]
  | cons x rest =>
    obtain ⟨k, g⟩ := x
    have hkg : k = g.key := hk (k, g) List.mem_cons_self
    obtain ⟨h1, h2⟩ := keepAfter_increasing k rest (fun p hp => hk p (List.mem_cons_of_mem _ hp))
    simp only [keepIncreasing]
    refine List.Pairwise.cons (fun f hf => ?_) h2
    rw [← hkg]; exact h1 f hf

/-- The lint's findings are in v1's order and unique. -/
theorem lint_increasing {z t : Input} {cap : Value} {fs : List Finding}
    (h : lint z t cap = .ok fs) : fs.Pairwise (fun a b => a.key < b.key) := by
  unfold lint at h
  repeat' split at h
  all_goals first
    | (cases h; exact List.pairwise_singleton _ _)
    | (cases h; exact ordered_increasing _)
    | cases h

/-- PL0: when the input cannot be linted, its finding is the only one. -/
theorem lint_pl0_alone {z t : Input} {cap : Value} {fs : List Finding} {f : Finding}
    (h : lint z t cap = .ok fs) (hf : f ∈ fs) (h0 : f.code = .pl0) : fs = [f] := by
  unfold lint at h
  repeat' split at h
  all_goals first
    | (cases h; simp at hf; subst hf; rfl)
    | (cases h
       have := mem_ordered hf
       obtain ⟨g, _, rfl⟩ := List.mem_map.mp this
       exact absurd h0 (Detector.code_ne_pl0 g.detector))
    | cases h

/-- Every finding is counted once, under its code. -/
theorem counts_sum (fs : List Finding) : (counts fs).sum = fs.length := by
  induction fs with
  | nil => simp [counts, Code.all]
  | cons f fs ih =>
    unfold counts at ih ⊢
    cases hc : f.code <;> simp_all [Code.all, List.filter_cons] <;> omega

end Principia.Lint
