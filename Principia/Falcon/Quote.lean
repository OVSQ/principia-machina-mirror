import Principia.Falcon.Canon

/-!
# The QUOTE CHECK: the TOKEN RULE

v1's `tpc_falcon` 0.2.0: `falcon_quote_match(value, quote_text, affix, scale,
accounting)`, PASS when the value occurs in the quote text as a whole token under the
TOKEN RULE (TK0 to TK10 in v1's text), else FAIL; and `quote_check(page_text, quote,
value, ...)`, TK11: UNKNOWN without page text, PASS when the quote is a whole token of
the page text and the value a whole token of the quote, else FAIL.

Every step is v1's, in v1's order, over v1's character classes (`ucls`, the table of
`Principia.Falcon.Classes`):

* TK0 (`prep`): every character of class F is removed, then the text is put in
  `canon_text`'s form (NFC at Unicode 15.1.0, whitespace collapsed).
* TK10's accounting reading (`accounting`): `(` number `)` becomes `-` number.
* TK1 to TK8 (`joins`): for each gap between two characters, whether they lie in one
  word or number token; v1's `_joins`, loop for loop.
* The declared forms (`formEnd`, `suffixOk`, `prefixOk`) and the match (`quoteMatch`).

Indices are v1's: positions in the text's code points, a gap `g` lying between
characters `g - 1` and `g`. A refusal (`text`, `affix`, `scale`, `accounting`) is found
before any NFC is needed, so a refused case is never owed.
-/

namespace Principia.Falcon.Quote

open Principia.Canonical (Value)
open Principia.Falcon

/-! ## The catalogues -/

/-- TK3's separators (v1's `_SEP`): `.`, `,`, `'`, RIGHT SINGLE QUOTATION MARK, `_`. -/
def sepChars : List Char := ['.', ',', '\'', Char.ofNat 0x2019, '_']

/-- TK4's joining characters beside the dashes (v1's `_JOIN3X`): MINUS SIGN, `/`, `:`,
`~`, FULLWIDTH TILDE, FRACTION SLASH, DIVISION SLASH, RATIO, DIVISION SIGN, BIG SOLIDUS,
SWUNG DASH. -/
def join3Chars : List Char :=
  [Char.ofNat 0x2212, '/', ':', '~', Char.ofNat 0xFF5E, Char.ofNat 0x2044, Char.ofNat 0x2215,
    Char.ofNat 0x2236, Char.ofNat 0xF7, Char.ofNat 0x29F8, Char.ofNat 0x2053]

/-- TK4's vulgar fractions (v1's `_VULGAR`): U+00BC to U+00BE, U+2150 to U+215F, U+2189. -/
def vulgar (c : Char) : Bool :=
  let n := c.toNat
  (0xBC ≤ n && n ≤ 0xBE) || (0x2150 ≤ n && n ≤ 0x215F) || n == 0x2189

/-- TK4's fraction slashes (v1's `_FRAC_SL`): `/`, FRACTION SLASH, DIVISION SLASH. -/
def fracSlashes : List Char := ['/', Char.ofNat 0x2044, Char.ofNat 0x2215]

/-- TK5's multiplication signs (v1's `_MULT`): `*`, MULTIPLICATION SIGN, MIDDLE DOT. -/
def multChars : List Char := ['*', Char.ofNat 0xD7, Char.ofNat 0xB7]

/-- TK5's superscript signs (v1's `_SUPSIGN`): SUPERSCRIPT PLUS SIGN, SUPERSCRIPT MINUS. -/
def supSigns : List Char := [Char.ofNat 0x207A, Char.ofNat 0x207B]

/-- TK6's affix words that stand before or after a number (v1's `_AFFIX_WORDS`). -/
def affixWords : List String := ["percent", "pct"]

/-- The declared affixes that may stand before a number (v1's `_AFFIX_BOTH`). -/
def affixBoth : List String := ["percent", "pct", "per cent"]

/-- TK6's affix words after a number only (v1's `_AFFIX_AFTER`). -/
def affixAfter : List String := ["permille", "bp", "bps", "pp", "ppm", "ppb", "ppt", "ppq"]

/-- TK6's two-word affixes (v1's `_TWO_WORDS`). -/
def twoWords : List (String × String) :=
  [("per", "cent"), ("per", "mille"), ("basis", "point"), ("basis", "points"),
    ("percentage", "point"), ("percentage", "points")]

/-- TK7's scale words (v1's `_SCALE_WORDS`). -/
def scaleWords : List String :=
  ["hundred", "thousand", "million", "billion", "trillion", "quadrillion", "lakh", "crore",
    "dozen", "tenth", "hundredth", "thousandth", "millionth", "billionth", "trillionth"]

/-- TK7's case-free abbreviations (v1's `_SCALE_CI`). -/
def scaleCi : List String := ["mn", "bn", "mln", "bln", "tn", "trn", "mio", "mrd"]

/-- TK7's exact-case abbreviations (v1's `_SCALE_ABBR`). -/
def scaleAbbr : List String := ["k", "K", "M", "m", "B", "MM"]

/-- TK10's accounting characters (v1's `_ACC_CH`). -/
def accChars : List Char := "0123456789.,'_".toList ++ [Char.ofNat 0x2019]

/-- An ASCII decimal digit. -/
def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- v1's `_alow`: ASCII lower case, or `none` for a word that is not ASCII. -/
def alow (w : List Char) : Option String :=
  if w.all (fun c => c.toNat ≤ 127) then some (String.ofList (w.map Char.toLower)) else none

/-! ## TK0: the text's form -/

/-- v1's `_prep` on a string: the class-F characters removed, then `canon_text`. -/
def prepString (s : String) : Result String :=
  canonText (String.ofList (s.toList.filter fun c => ucls c != some .format))

/-- v1's `_prep`: a text that is not a string is refused (`text`). -/
def prep : Value → Result String
  | .str s => prepString s
  | _ => refuse "text"

/-- The refusal `_prep` raises, found without NFC: only a text that is not a string. -/
def textOk : Value → Bool
  | .str _ => true
  | _ => false

/-- TK10's accounting reading of one `(`: the characters after it that are accounting
characters or spaces, and what follows them. -/
def accRun : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if accChars.contains c || ucls c == some .space then
      let (b, r) := accRun cs
      (c :: b, r)
    else ([], c :: cs)

theorem accRun_length (cs : List Char) :
    (accRun cs).1.length + (accRun cs).2.length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold accRun
    split
    · simp only [List.length_cons]; omega
    · simp

/-- A number as TK10 reads it between brackets: it ends in an ASCII digit and starts with
one, or with `.` or `,` and then one. -/
def accNumber (b : List Char) : Bool :=
  match b.getLast?, b with
  | some l, f :: rest =>
    asciiDigit l &&
      (asciiDigit f || ((f == '.' || f == ',') && (rest.head?.map asciiDigit).getD false))
  | _, _ => false

/-- v1's `_acc` (TK10): each `(` number `)` becomes `-` number. -/
def accounting : List Char → List Char
  | [] => []
  | '(' :: cs =>
    match _h : (accRun cs).2 with
    | ')' :: r' =>
      if accNumber (accRun cs).1 then '-' :: (accRun cs).1 ++ accounting r'
      else '(' :: accounting cs
    | _ => '(' :: accounting cs
  | c :: cs => c :: accounting cs
termination_by cs => cs.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals
    first
      | omega
      | (have h1 := accRun_length cs
         rw [_h] at h1
         simp only [List.length_cons] at h1
         omega)

/-! ## TK1 to TK8: the joins -/

/-- v1's `_classes`: per character, the class tests the joins read. -/
structure Classes where
  /-- L, M, D or N. -/
  alnum : Array Bool
  /-- D or N. -/
  num : Array Bool
  /-- D. -/
  nd : Array Bool
  /-- P or S. -/
  sign : Array Bool
  /-- P, or one of `join3Chars`. -/
  j3 : Array Bool
  /-- Z. -/
  zs : Array Bool
  /-- L or M (v1's `let`). -/
  letter : Array Bool
  /-- An affix sign or C (v1's `sym`). -/
  sym : Array Bool

/-- v1's `_classes(h)`. -/
def classes (h : Array Char) : Classes :=
  let cl := h.map ucls
  let isIn (ks : List CharClass) := cl.map fun k => match k with
    | some k => ks.contains k
    | none => false
  { alnum := isIn [.letter, .mark, .digit, .number]
    num := isIn [.digit, .number]
    nd := isIn [.digit]
    sign := isIn [.dash, .math]
    j3 := (h.zip cl).map fun (c, k) => k == some .dash || join3Chars.contains c
    zs := isIn [.space]
    letter := isIn [.letter, .mark]
    sym := (h.zip cl).map fun (c, k) => affixSigns.contains c || k == some .currency }

/-- An array's entry at an index, false outside it (every read v1 guards). -/
def at? (a : Array Bool) (k : Int) : Bool :=
  if 0 ≤ k then a.getD k.toNat false else false

/-- v1's `fz(k)`: the first index at or after `k` that is not a space. -/
def fz (zs : Array Bool) (k : Nat) : Nat :=
  if k < zs.size ∧ zs.getD k false = true then fz zs (k + 1) else k
termination_by zs.size - k

/-- v1's `bz(k)`: the last index at or before `k` that is not a space, or `-1`. -/
def bz (zs : Array Bool) (k : Int) : Int :=
  if h : 0 ≤ k ∧ at? zs k = true then bz zs (k - 1) else k
termination_by (k + 1).toNat
decreasing_by have := h.1; omega

/-- v1's `run(k)`: the first index at or after `k` that is not L or M. -/
def run (letter : Array Bool) (k : Nat) : Nat :=
  if k < letter.size ∧ letter.getD k false = true then run letter (k + 1) else k
termination_by letter.size - k

/-- The first index at or before `k` whose predecessor is not L or M (v1's
`while bs > 0 and let[bs - 1]: bs -= 1`). -/
def backRun (letter : Array Bool) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => if letter.getD k false then backRun letter k else k + 1

/-- The first index at or before `k` whose predecessor is not a space (v1's
`while t > 0 and zs[t - 1]: t -= 1`). -/
def backSpace (zs : Array Bool) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => if zs.getD k false then backSpace zs k else k + 1

/-- The first index at or after `k` that is not D or N (v1's `while D(e): e += 1`). -/
def digitRun (num : Array Bool) (k : Nat) : Nat :=
  if k < num.size ∧ num.getD k false = true then digitRun num (k + 1) else k
termination_by num.size - k

/-- `h[a:b]`, as v1 slices. -/
def slice (h : Array Char) (a b : Nat) : List Char := (h.extract a b).toList

/-- `h[a:a+len(s)] == s`. -/
def standsAt (h : Array Char) (a : Nat) (s : String) : Bool :=
  slice h a (a + s.length) == s.toList

/-- v1's `link(a, b)`: every gap from `a` to `b` joined. -/
def link (J : Array Bool) (a b : Int) : Array Bool :=
  (List.range (b + 1 - a).toNat).foldl (fun J (i : Nat) => J.setIfInBounds (a + i).toNat true) J

/-- v1's `_joins(h, K)`: `J[g]` for each gap `g` from 0 to `n`, true where the
characters on both sides lie in one word or number token (TK0 to TK8). -/
def joins (h : Array Char) (K : Classes) : Array Bool := Id.run do
  let n := h.size
  let ni : Int := n
  let D (k : Int) : Bool := decide (0 ≤ k) && decide (k < ni) && at? K.num k
  let lead (k : Int) : Bool :=
    D k || (decide (0 ≤ k) && decide (k < ni) && ".,".toList.contains (h.getD k.toNat ' ') &&
      D (k + 1))
  let ch (k : Int) : Char := if 0 ≤ k then h.getD k.toNat ' ' else ' '
  let fz' (k : Int) : Int := fz K.zs k.toNat
  let mut J : Array Bool := Array.replicate (n + 1) false
  -- the first pass, character by character
  for kn in [0:n] do
    let k : Int := kn
    let c := ch k
    if 1 ≤ k && at? K.alnum (k - 1) && at? K.alnum k then
      J := J.setIfInBounds kn true
    if sepChars.contains c && D (k - 1) && D (k + 1) then
      J := link J k (k + 1)
    if ".,".toList.contains c && D (k + 1) then
      J := J.setIfInBounds (kn + 1) true
    if at? K.zs k && D (k - 1) then
      let t := fz' k
      if D t && D (t + 1) && D (t + 2) && !D (t + 3) then
        J := link J k t
    if at? K.j3 k then
      let a := bz K.zs (k - 1)
      let b := fz' (k + 1)
      if D a && D b then
        J := link J (a + 1) b
    if "eE".toList.contains c && D (k - 1) && decide (k + 1 < ni) && at? K.sign (k + 1) &&
        D (k + 2) then
      J := J.setIfInBounds (kn + 1) true
    if c == '^' && D (k - 1) then
      J := J.setIfInBounds kn true
      if D (k + 1) || (decide (k + 1 < ni) && at? K.sign (k + 1) && D (k + 2)) then
        J := J.setIfInBounds (kn + 1) true
    if supSigns.contains c && D (k - 1) then
      J := J.setIfInBounds kn true
  -- after the last digit of a number: fractions, exponents, affixes, scales
  for dn in [0:n] do
    let d : Int := dn
    if !D d || D (d + 1) then continue
    let k := fz' (d + 1)
    if d + 1 < k && k < ni then
      if vulgar (ch k) then
        J := link J (d + 1) k
      else if D k then
        let e : Int := digitRun K.num k.toNat
        if e < ni && fracSlashes.contains (ch e) && D (e + 1) then
          J := link J (d + 1) k
    if k < ni then
      let k2 : Int :=
        if multChars.contains (ch k) then k + 1
        else if "xX".toList.contains (ch k) && d + 1 < k && k + 1 < ni && at? K.zs (k + 1) then
          k + 1
        else -1
      if 0 ≤ k2 then
        let k3 := fz' k2
        if standsAt h k3.toNat "10" && !(k3 + 2 < ni && at? K.nd (k3 + 2)) then
          J := link J (d + 1) (k3 + 1)
    let t := k
    if ni ≤ t then continue
    if at? K.sym t then
      J := link J (d + 1) t
    if standsAt h t.toNat "**" then
      let q0 := fz' (t + 2)
      let q := if q0 < ni && at? K.sign q0 then q0 + 1 else q0
      if D q then
        J := link J (d + 1) q
    if !at? K.letter t then continue
    let e : Int := run K.letter t.toNat
    let w := slice h t.toNat e.toNat
    let lw := alow w
    let whole := e == ni || !at? K.alnum e
    if w == ['e'] || w == ['E'] then
      let q0 := fz' e
      let q := if q0 < ni && at? K.sign q0 then q0 + 1 else q0
      if D q then
        J := link J (d + 1) q
    match lw with
    | none => continue
    | some lw =>
      if !whole then continue
      let ws := String.ofList w
      if affixWords.contains lw || affixAfter.contains lw || scaleWords.contains lw ||
          scaleCi.contains lw || scaleAbbr.contains ws ||
          (lw.toList.getLast? == some 's' &&
            scaleWords.contains (String.ofList lw.toList.dropLast)) then
        J := link J (d + 1) (e - 1)
      else if ["per", "basis", "percentage"].contains lw then
        let t2 := fz' e
        if e < t2 && t2 < ni && at? K.letter t2 then
          let e2 : Int := run K.letter t2.toNat
          if (match alow (slice h t2.toNat e2.toNat) with
              | some lw2 => twoWords.contains (lw, lw2)
              | none => false) && (e2 == ni || !at? K.alnum e2) then
            J := link J (d + 1) (e2 - 1)
      else if lw == "times" then
        let t2 := fz' e
        if e < t2 && standsAt h t2.toNat "10^" then
          J := link J (d + 1) (t2 + 2)
  -- an affix word before a number: percent, pct, per cent
  for sn in [0:n] do
    let s : Int := sn
    if !at? K.letter s || (0 < s && at? K.alnum (s - 1)) then continue
    let e : Int := run K.letter sn
    let lw := alow (slice h sn e.toNat)
    let mut ok := match lw with
      | some w => affixWords.contains w
      | none => false
    if lw == some "cent" then
      let b := bz K.zs (s - 1)
      if b < s - 1 && 0 ≤ b && at? K.letter b then
        let bs := backRun K.letter b.toNat
        ok := alow (slice h bs (b.toNat + 1)) == some "per"
    if ok then
      let t := fz' e
      if lead t then
        J := link J e t
  -- signs and prefix symbols, from the right
  for i in [0:n] do
    let k : Int := n - 1 - i
    if at? K.sign k then
      if lead (k + 1) || (k + 1 < ni && (at? K.sign (k + 1) || at? K.sym (k + 1)) &&
          at? J (k + 2)) then
        J := J.setIfInBounds (k + 1).toNat true
      else
        let t := fz' (k + 1)
        if k + 1 < t && (lead t || (t < ni && (at? K.sign t || at? K.sym t) && at? J (t + 1))) then
          if !D (bz K.zs (k - 1)) then
            J := link J (k + 1) t
    else if at? K.sym k then
      let t := fz' (k + 1)
      if lead t || (t < ni && at? K.sign t && at? J (t + 1)) then
        J := link J (k + 1) t
  return J

/-! ## TK8: the declared forms -/

/-- v1's `_check_affix`: none, or a string `affixOk` accepts. -/
def checkAffix : Value → Bool
  | .null => true
  | .str a => affixOk a
  | _ => false

/-- v1's `_check_scale`: none, or a declared scale. -/
def checkScale : Value → Bool
  | .null => true
  | .str s => scaleOk s
  | _ => false

/-- v1's `_check_flags`: the refusal, if any, in v1's order. -/
def checkFlags (affix scale accounting : Value) : Option String :=
  if !checkAffix affix then some "affix"
  else if !checkScale scale then some "scale"
  else match accounting with
    | .bool _ => none
    | _ => some "accounting"

/-- v1's `_form_end(h, t, form, K)`: the end of the declared affix or scale standing at
`t`, or `none`. -/
def formEnd (h : Array Char) (K : Classes) (t : Nat) (form : String) : Option Nat :=
  let n := h.size
  if affixNames.contains form || scaleNames.contains form then
    if n ≤ t || !K.letter.getD t false then none
    else
      let e := run K.letter t
      let w := slice h t e
      if scaleAbbr.contains form then (if w == form.toList then some e else none)
      else
        let lw := alow w
        match form.splitOn " " with
        | [first, second] =>
          let t2 := fz K.zs e
          if lw != some first || t2 == e || n ≤ t2 || !K.letter.getD t2 false then none
          else
            let e2 := run K.letter t2
            let lw2 := alow (slice h t2 e2)
            if lw2 == some second ||
                (["point", "points"].contains second &&
                  (lw2 == some "point" || lw2 == some "points")) then some e2
            else none
        | _ =>
          if scaleWords.contains form then
            (if lw == some form || lw == some (form ++ "s") then some e else none)
          else if lw == some form then some e else none
  else if standsAt h t form then some (t + form.length) else none

/-- One step of v1's `_suffix_ok`: the first remaining form that stands after the
spaces at `pos`, its end and the forms left. -/
def takeForm (h : Array Char) (K : Classes) (pos : Nat) :
    List String → Option (Nat × List String)
  | [] => none
  | f :: fs =>
    match formEnd h K (fz K.zs pos) f with
    | some e => some (e, fs)
    | none => (takeForm h K pos fs).map fun (e, rest) => (e, f :: rest)

/-- v1's `_suffix_ok(h, j, affix, scale, J, K)`: the declared scale and affix, each at
most once and in either order, end the token after `j`. -/
def suffixOk (h : Array Char) (K : Classes) (J : Array Bool) (j : Nat)
    (affix scale : Option String) : Bool :=
  let forms := [scale, affix].filterMap id
  let ends (pos : Nat) : Bool :=
    pos == h.size || (!K.alnum.getD pos false && !J.getD pos false)
  match takeForm h K j forms with
  | none => false
  | some (p1, rest) =>
    match takeForm h K p1 rest with
    | none => ends p1
    | some (p2, _) => ends p2

/-- v1's `_prefix_ok(h, i, affix, J, K)`: the declared affix stands before the token at
`i`. -/
def prefixOk (h : Array Char) (K : Classes) (J : Array Bool) (i : Nat) (affix : String) :
    Bool :=
  let t := backSpace K.zs i
  let start : Option Nat :=
    if affixNames.contains affix then
      if !affixBoth.contains affix then none
      else
        let s := backRun K.letter t
        if s == t then none
        else
          let lw := alow (slice h s t)
          if affix == "per cent" then
            let b := backSpace K.zs s
            let s2 := backRun K.letter b
            if lw != some "cent" || b == s || s2 == b || alow (slice h s2 b) != some "per" then
              none
            else some s2
          else if lw != some affix then none
          else some s
    else
      if t < affix.length then none
      else
        let s := t - affix.length
        if slice h s t != affix.toList then none else some s
  match start with
  | none => false
  | some s => s == 0 || (!K.alnum.getD (s - 1) false && !J.getD s false)

/-- TK0 always answers: the class-F characters removed, then NFC and the collapse. -/
theorem prepString_nfc (s : String) :
    prepString s = .ok (String.ofList (collapse
      (Unicode.nfc (String.ofList (s.toList.filter fun c => ucls c != some .format))).toList)) :=
  canonText_nfc _

/-! ## The match -/

/-- The result of a quote match or check. -/
inductive Verdict where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

/-- v1's word for a verdict. -/
def Verdict.word : Verdict → String
  | .pass => "PASS"
  | .fail => "FAIL"
  | .unknown => "UNKNOWN"

/-- v1's `render_quote`. -/
def renderQuote (v : Verdict) : String := "quote|" ++ v.word

/-- The TOKEN RULE's match over prepared texts (v1's `falcon_quote_match` after its
checks): whether `v` occurs in `h` as a whole token, under the declared affix and scale. -/
def matchPrepared (v h : List Char) (affix scale : Option String) : Verdict :=
  if v.isEmpty then .fail
  else
    let ha := h.toArray
    let n := ha.size
    let K := classes ha
    let J := joins ha K
    let vf := (v.head?.map ucls).getD none
    let vl := (v.getLast?.map ucls).getD none
    let preOk := [some CharClass.digit, some .number, some .dash, some .math].contains vf ||
      (match v.head? with
        | some c => ".,".toList.contains c
        | none => false)
    let postOk := [some CharClass.digit, some .number].contains vl
    let found := (List.range n).any fun i =>
      if slice ha i (i + v.length) != v then false
      else
        let j := i + v.length
        let left0 := i == 0 || (!K.alnum.getD (i - 1) false && !J.getD i false)
        let right0 := j == n || (!K.alnum.getD j false && !J.getD j false)
        let right := if !right0 && postOk && (affix.isSome || scale.isSome) then
            suffixOk ha K J j affix scale
          else right0
        let left := if !left0 && preOk then
            match affix with
            | some a => prefixOk ha K J i a
            | none => left0
          else left0
        left && right
    if found then .pass else .fail

/-- TK1: an empty value never passes. -/
theorem matchPrepared_nil (h : List Char) (affix scale : Option String) :
    matchPrepared [] h affix scale = .fail := rfl

/-- A declared form as a string, when one is declared. -/
def formOf : Value → Option String
  | .str s => some s
  | _ => none

/-- v1's `falcon_quote_match(value, quote_text, affix, scale, accounting)`. -/
def quoteMatch (value quoteText affix scale accountingFlag : Value) : Result Verdict :=
  if !textOk value || !textOk quoteText then refuse "text"
  else
    match checkFlags affix scale accountingFlag with
    | some w => refuse w
    | none => do
      let v ← prep value
      let h ← prep quoteText
      let acc := match accountingFlag with
        | .bool b => b
        | _ => false
      let (v, h) := if acc then (accounting v.toList, accounting h.toList)
        else (v.toList, h.toList)
      return matchPrepared v h (formOf affix) (formOf scale)

/-- v1's `quote_check(page_text, quote, value, affix, scale, accounting)` (TK11). -/
def quoteCheck (pageText quoteText value affix scale accountingFlag : Value) :
    Result Verdict :=
  if !textOk quoteText || !textOk value then refuse "text"
  else
    match checkFlags affix scale accountingFlag with
    | some w => refuse w
    | none =>
      match pageText with
      | .null => .ok .unknown
      | .str _ => do
        let q ← quoteMatch quoteText pageText affix scale accountingFlag
        if q != .pass then return .fail
        let v ← quoteMatch value quoteText affix scale accountingFlag
        return (if v == .pass then .pass else .fail)
      | _ => refuse "text"

end Principia.Falcon.Quote
