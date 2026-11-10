import Principia.Canonical
import Principia.Decimal
import Principia.Units
import Principia.Zone.Text
import Principia.Falcon.Classes

/-!
# The falcons' canonical forms

v1's `tpc_falcon` 0.2.0: `falcon_canon(value, spec)`, the canonical form of a
falcon's field value under its field spec, which the reconciliation compares; and
`render_canon`, its text. A false DIFFER costs a rung; a false AGREED is the soundness
defect, so each form makes equal only what v1's makes equal.

| spec type | canonical form | here |
|---|---|---|
| `text` | NFC, then XML Schema's whiteSpace collapse | `canonText` |
| `decimal` | the zone serialization's DECIMAL (zone schemas 5.6) | `Principia.Decimal.canon` |
| `unitvalue` | `<decimal> <UNIT>`, split at the first space | `canonUnitValue` |
| `date` | an ISO 8601 calendar date, YYYY-MM-DD | `canonDate` |
| `url` | the syntax-based steps of RFC 3986 6.2.2 | `canonUrl` |
| `enum` | one of the spec's values, as it is | `falconCanon` |
| `boolean` | `true` or `false` | `falconCanon` |

**One function each, shared where v1's is the same.** v1's falcon `canon_decimal` is the
zones' `canon_decimal` letter for letter (the same grammar, `-?[0-9]+(\.[0-9]+)?([eE][-+]?
[0-9]{1,4})?`, and the same string arithmetic), so it is `Principia.Decimal.canon`. v1's
falcon `canon_unit` reads a UNIT by tpm_units 0.2.0's closed catalogue, its 24 prefixes,
one reading per token, the merge and the two ranges, and spells it in catalogue order then
prefix power: the units' `Principia.Units.tokens` and `spelling` do exactly that, so they
are called. (The two differ only in the order of their refusal checks, a refused symbol
before a reading; the catalogue holds no refused symbol and no symbol that ends in one,
so every UNIT is refused by both or by neither.)

**Text and NFC.** v1 normalized text to NFC with Python's `unicodedata` at Unicode 15.1.0;
so does the Calculator, with Unicode 15.1.0's tables (`Principia.Unicode.nfc`). v1 refused a lone surrogate; a Lean string cannot
hold one, and the Calculator's JSON reader refuses it before any function runs.

**Refusals.** v1 raised `ValueError` with a short word (`text`, `decimal`, `unitvalue`,
`date`, `url`, `enum`, `boolean`, `schema`), and its corpus writes `ERROR:<word>`. Here a
refusal is `Fault.refused word`.
-/

namespace Principia.Falcon

open Principia.Canonical (Value)

/-! ## Faults -/

/-- A falcon function's fault: v1's refusal, by its word. Nothing is owed: with SHA-256
and Unicode's tables every falcon function answers. -/
inductive Fault where
  | refused (word : String)
  deriving DecidableEq, Repr

/-- A falcon function's result. -/
abbrev Result (α : Type) := Except Fault α

/-- v1's `raise ValueError(word)`. -/
def refuse {α : Type} (word : String) : Result α := .error (.refused word)

/-! ## JSON objects as v1 reads them -/

/-- An object's members. -/
abbrev Members := List (String × Value)

/-- v1's `o.get(k)`: the member named `k`; Python keeps the last of repeated keys. -/
def field? (ms : Members) (k : String) : Option Value := List.lookup k ms.reverse

/-- v1's `k in o`. -/
def hasField (ms : Members) (k : String) : Bool := (field? ms k).isSome

/-- The string a member holds, if it holds one. -/
def strField? (ms : Members) (k : String) : Option String :=
  match field? ms k with
  | some (.str s) => some s
  | _ => none

/-- v1's `_keys_are`: every required key present, and no key outside the required and
the optional ones. -/
def keysAre (ms : Members) (required optional : List String) : Bool :=
  required.all (hasField ms) && ms.all fun m => required.contains m.1 || optional.contains m.1

/-- v1's `_is_int(x, lo, hi)`: an integer (never a boolean or a float) from `lo` to `hi`. -/
def isInt (v : Value) (lo hi : Int) : Bool :=
  match v with
  | .int i => lo ≤ i && i ≤ hi
  | _ => false

/-- The integer an `isInt` value holds, as a natural number when it is one. -/
def natOf (v : Value) : Nat :=
  match v with
  | .int i => i.toNat
  | _ => 0

/-- v1's `_is_name(x)`: a string, not empty. -/
def isName (v : Value) : Bool :=
  match v with
  | .str s => s ≠ ""
  | _ => false

/-- The strings of a list of strings, when it is one. -/
def strings? (v : Value) : Option (List String) :=
  match v with
  | .arr vs => vs.mapM fun x => match x with
    | .str s => some s
    | _ => none
  | _ => none

/-- An object's members, when it is one. -/
def members? (v : Value) : Option Members :=
  match v with
  | .obj ms => some ms
  | _ => none

/-- v1's `_keys_are(o, required, optional)` on any value: an object first. -/
def keysAreV (v : Value) (required optional : List String) : Bool :=
  match v with
  | .obj ms => keysAre ms required optional
  | _ => false

/-- Strings each different from every one before it (v1's `x in v[:i]` refused). -/
def distinct : List String → Bool
  | [] => true
  | s :: rest => !rest.contains s && distinct rest

/-! ## The render -/

/-- v1's `_esc` of one character: `|` and `\` backslashed, the C0 controls and DEL as
`\xHH` in lower-case hexadecimal, every other character as it is. -/
def escChar (c : Char) : List Char :=
  if c = '|' then ['\\', '|']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 0x20 ∨ c.toNat = 0x7F then
    ['\\', 'x', Canonical.hexDigit (c.toNat / 16), Canonical.hexDigit (c.toNat % 16)]
  else [c]

/-- v1's `_esc`. -/
def esc (s : String) : String := String.ofList (s.toList.flatMap escChar)

/-- v1's `render_canon`. -/
def renderCanon (c : String) : String := "OK|" ++ esc c

/-! ## text -/

/-- XML Schema's white space: TAB, LF, CR and SPACE (v1's `[\t\n\r ]`). -/
def xmlSpace (c : Char) : Bool := c = '\t' || c = '\n' || c = '\r' || c = ' '

/-- XML Schema's whiteSpace collapse: every run of white space becomes one SPACE, and a
leading or trailing one goes (v1's `_WS.sub(" ", s).strip(" ")`). `started` says a
character has been kept, `pending` that white space followed it. -/
def collapseFrom (started pending : Bool) : List Char → List Char
  | [] => []
  | c :: cs =>
    if xmlSpace c then collapseFrom started true cs
    else if started && pending then ' ' :: c :: collapseFrom true false cs
    else c :: collapseFrom true false cs

/-- The collapse of a whole string. -/
def collapse (cs : List Char) : List Char := collapseFrom false false cs

/-- The characters of v1's `canon_text`: NFC, then the collapse. -/
def canonTextChars (s : String) : List Char := collapse (Unicode.nfcList s.toList)

/-- v1's `canon_text` of a string: NFC, then the collapse. It never refuses a string. -/
def canonText (s : String) : Result String := .ok (String.ofList (canonTextChars s))

/-! ## decimal and unitvalue -/

/-- v1's `canon_decimal`. -/
def canonDecimal (s : String) : Result String :=
  match Decimal.canon s with
  | some d => .ok d
  | none => refuse "decimal"

/-- v1's falcon `canon_unit`: the UNIT's canonical spelling. -/
def canonUnit (u : String) : Result String :=
  match Units.tokens u with
  | .ok items => .ok (Units.spelling items)
  | .error _ => refuse "unit"

/-- v1's `unitvalue`: split at the first SPACE, the decimal then the UNIT; either
refused refuses the value. -/
def canonUnitValue (s : String) : Result String :=
  let (d, rest) := s.toList.span (· ≠ ' ')
  match rest with
  | [] => refuse "unitvalue"
  | _ :: u =>
    match Decimal.canon (String.ofList d), canonUnit (String.ofList u) with
    | some d', .ok u' => .ok (d' ++ " " ++ u')
    | _, _ => refuse "unitvalue"

/-! ## date -/

/-- An ASCII digit's value. -/
def digitValue (c : Char) : Nat := c.toNat - '0'.toNat

/-- The value of ASCII digits, most significant first. -/
def digitsValue (cs : List Char) : Nat := cs.foldl (fun acc c => acc * 10 + digitValue c) 0

/-- A Gregorian leap year. -/
def leapYear (y : Nat) : Bool := y % 4 = 0 && (y % 100 ≠ 0 || y % 400 = 0)

/-- The days of a month, 1 to 12. -/
def monthDays (y m : Nat) : Nat :=
  match m with
  | 2 => if leapYear y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-- The year, month and day digits of `YYYY-MM-DD` or `YYYYMMDD`. -/
def dateDigits : List Char → Option (List Char × List Char × List Char)
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] => some ([y1, y2, y3, y4], [m1, m2], [d1, d2])
  | [y1, y2, y3, y4, m1, m2, d1, d2] => some ([y1, y2, y3, y4], [m1, m2], [d1, d2])
  | _ => none

/-- v1's `canon_date`: a real day of 0000-9999, written `YYYY-MM-DD`. -/
def canonDate (s : String) : Result String :=
  match dateDigits s.toList with
  | some (y, m, d) =>
    if (y ++ m ++ d).all Char.isDigit then
      let yv := digitsValue y
      let mv := digitsValue m
      let dv := digitsValue d
      if 1 ≤ mv && mv ≤ 12 && 1 ≤ dv && dv ≤ monthDays yv mv then
        .ok (String.ofList (y ++ '-' :: m ++ '-' :: d))
      else refuse "date"
    else refuse "date"
  | none => refuse "date"

/-! ## url -/

/-- An ASCII letter or digit. -/
def alnum (c : Char) : Bool := c.isAlphanum

/-- RFC 3986's unreserved characters. -/
def unreserved (c : Char) : Bool := alnum c || c = '-' || c = '.' || c = '_' || c = '~'

/-- RFC 3986's characters (v1's `_URLCH`). -/
def urlChar (c : Char) : Bool := alnum c || "-._~:/?#[]@!$&'()*+,;=%".toList.contains c

/-- A userinfo character, and an IP literal's inner character (v1's `_USERINFO`,
`_IPLIT`). -/
def userinfoChar (c : Char) : Bool := alnum c || "-._~!$&'()*+,;=:%".toList.contains c

/-- A reg-name character (v1's `_REGNAME`). -/
def regNameChar (c : Char) : Bool := alnum c || "-._~!$&'()*+,;=%".toList.contains c

/-- A hexadecimal digit, either case. -/
def hexChar (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- An upper-case hexadecimal digit. -/
def upperHexChar (c : Char) : Bool := c.isDigit || ('A' ≤ c && c ≤ 'F')

/-- A hexadecimal digit's value. -/
def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Every `%` followed by two hexadecimal digits (v1's `_BADPCT` finds none). -/
def percentsWellFormed : List Char → Bool
  | [] => true
  | '%' :: rest =>
    (match rest with
      | a :: b :: _ => hexChar a && hexChar b
      | _ => false) && percentsWellFormed rest
  | _ :: rest => percentsWellFormed rest

/-- v1's `_PCT.sub(_pct, s)`: from left to right, each `%XX` becomes its character when
that is unreserved, else `%` and the digits in upper case. -/
def decodePercents : List Char → List Char
  | [] => []
  | '%' :: rest@(a :: b :: r) =>
    if hexChar a && hexChar b then
      let c := Char.ofNat (hexValue a * 16 + hexValue b)
      if unreserved c then c :: decodePercents r
      else '%' :: a.toUpper :: b.toUpper :: decodePercents r
    else '%' :: decodePercents rest
  | c :: rest => c :: decodePercents rest

/-- v1's `_HOSTCASE.sub(_host_case, host)`: from left to right, an upper-case `%XX`
is kept and every other upper-case letter is lowered. -/
def hostCase : List Char → List Char
  | [] => []
  | '%' :: rest@(a :: b :: r) =>
    if upperHexChar a && upperHexChar b then '%' :: a :: b :: hostCase r
    else '%' :: hostCase rest
  | c :: rest => (if 'A' ≤ c && c ≤ 'Z' then c.toLower else c) :: hostCase rest

/-- RFC 3986 5.2.4's "remove the last segment": the output, held reversed, loses its
characters back to and including its last `/`, or all of them when it has none. -/
def dropLastSegment (outRev : List Char) : List Char :=
  match outRev.dropWhile (· ≠ '/') with
  | [] => []
  | _ :: r => r

/-- RFC 3986 5.2.4, step by step, as v1 wrote it (`remove_dot_segments`); the output is
held reversed. -/
def removeDotsFrom (outRev : List Char) : List Char → List Char
  | [] => outRev.reverse
  | '.' :: '.' :: '/' :: r => removeDotsFrom outRev r
  | '.' :: '/' :: r => removeDotsFrom outRev r
  | '/' :: '.' :: '/' :: r => removeDotsFrom outRev ('/' :: r)
  | ['/', '.'] => removeDotsFrom outRev ['/']
  | '/' :: '.' :: '.' :: '/' :: r => removeDotsFrom (dropLastSegment outRev) ('/' :: r)
  | ['/', '.', '.'] => removeDotsFrom (dropLastSegment outRev) ['/']
  | ['.'] => outRev.reverse
  | ['.', '.'] => outRev.reverse
  | '/' :: r =>
    let seg := r.takeWhile (· ≠ '/')
    removeDotsFrom (seg.reverse ++ '/' :: outRev) (r.dropWhile (· ≠ '/'))
  | c :: r =>
    let seg := r.takeWhile (· ≠ '/')
    removeDotsFrom (seg.reverse ++ c :: outRev) (r.dropWhile (· ≠ '/'))
termination_by cs => cs.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first
    | omega
    | (have := (List.dropWhile_suffix (l := r) (· ≠ '/')).length_le; omega)

/-- v1's `remove_dot_segments`. -/
def removeDotSegments (path : String) : String :=
  String.ofList (removeDotsFrom [] path.toList)

/-- The five parts of a reference by RFC 3986 Appendix B (v1's `_APPB`): scheme,
authority, path, query and fragment. -/
structure UrlParts where
  scheme : Option (List Char)
  authority : Option (List Char)
  path : List Char
  query : Option (List Char)
  fragment : Option (List Char)

/-- RFC 3986 Appendix B's split. Each optional part is taken when it is there, as the
regular expression's greedy groups take it. -/
def splitReference (cs : List Char) : UrlParts :=
  let (s, afterS) := cs.span fun c => !":/?#".toList.contains c
  let (scheme, r1) : Option (List Char) × List Char :=
    match s, afterS with
    | _ :: _, ':' :: r => (some s, r)
    | _, _ => (none, cs)
  let (authority, r2) : Option (List Char) × List Char :=
    match r1 with
    | '/' :: '/' :: r => (some (r.takeWhile fun c => !"/?#".toList.contains c),
        r.dropWhile fun c => !"/?#".toList.contains c)
    | _ => (none, r1)
  let path := r2.takeWhile fun c => c ≠ '?' && c ≠ '#'
  let r3 := r2.dropWhile fun c => c ≠ '?' && c ≠ '#'
  let (query, r4) : Option (List Char) × List Char :=
    match r3 with
    | '?' :: r => (some (r.takeWhile (· ≠ '#')), r.dropWhile (· ≠ '#'))
    | _ => (none, r3)
  let fragment := match r4 with
    | '#' :: r => some r
    | _ => none
  { scheme, authority, path, query, fragment }

/-- A scheme: a letter, then letters, digits, `+`, `.` and `-` (v1's `_SCHEME`). -/
def schemeOk : List Char → Bool
  | c :: cs => c.isAlpha && cs.all fun d => alnum d || d = '+' || d = '.' || d = '-'
  | [] => false

/-- A port: nothing, or `:` and digits (v1's `_PORT`). -/
def portOk : List Char → Bool
  | [] => true
  | ':' :: ds => ds.all Char.isDigit
  | _ => false

/-- An authority in canonical form, `//` included: at most one `@`, the userinfo kept,
the host lowered outside its `%XX`, the port kept; `none` when it is refused. -/
def canonAuthority (auth : List Char) : Option (List Char) := do
  if 1 < auth.count '@' then none
  let (ui, hp) ←
    if auth.contains '@' then
      let u := auth.takeWhile (· ≠ '@')
      if u.all userinfoChar then pure (u ++ ['@'], (auth.dropWhile (· ≠ '@')).drop 1)
      else none
    else pure ([], auth)
  let (host, port) ←
    match hp with
    | '[' :: inner =>
      let lit := inner.takeWhile (· ≠ ']')
      match inner.dropWhile (· ≠ ']') with
      | ']' :: port =>
        if lit.all userinfoChar then pure ('[' :: lit ++ [']'], port) else none
      | _ => none
    | _ =>
      let h := hp.takeWhile (· ≠ ':')
      if h.all regNameChar then pure (h, hp.dropWhile (· ≠ ':')) else none
  if !portOk port then none
  pure ('/' :: '/' :: ui ++ hostCase host ++ port)

/-- v1's `canon_url` on characters, or `none` when it is refused. -/
def canonUrlChars (cs : List Char) : Option (List Char) := do
  if cs.isEmpty || !cs.all urlChar || !percentsWellFormed cs then none
  let p := splitReference (decodePercents cs)
  let scheme ← p.scheme
  if !schemeOk scheme then none
  let auth ← match p.authority with
    | some a => canonAuthority a
    | none => pure []
  let path := if p.authority.isSome || p.path.head? = some '/' then removeDotsFrom [] p.path
    else p.path
  pure (scheme.map Char.toLower ++ ':' :: auth ++ path ++
    (match p.query with | some q => '?' :: q | none => []) ++
    (match p.fragment with | some f => '#' :: f | none => []))

/-- v1's `canon_url`: only the syntax-based steps of RFC 3986 6.2.2. -/
def canonUrl (s : String) : Result String :=
  match canonUrlChars s.toList with
  | some cs => .ok (String.ofList cs)
  | none => refuse "url"

/-! ## Field specs -/

/-- The value types (v1's `TYPES`). -/
def valueTypes : List String := ["text", "decimal", "unitvalue", "date", "url", "enum", "boolean"]

/-- The affixes declared by name (v1's `_AFFIX_DECL`). -/
def affixNames : List String :=
  ["percent", "per cent", "pct", "per mille", "permille", "bp", "bps", "basis point",
    "basis points", "pp", "percentage point", "percentage points", "ppm", "ppb", "ppt", "ppq"]

/-- The affix signs (v1's `_AFFIXES`): PERCENT SIGN, PER MILLE SIGN, PER TEN THOUSAND
SIGN, DEGREE SIGN, PRIME, DOUBLE PRIME, FULLWIDTH PERCENT SIGN, SMALL PERCENT SIGN,
ARABIC PERCENT SIGN, ARABIC-INDIC PER MILLE SIGN, ARABIC-INDIC PER TEN THOUSAND SIGN. -/
def affixSigns : List Char :=
  ['%', '‰', '‱', '°', '′', '″', '％', '﹪', '٪',
    '؉', '؊']

/-- The scales declared (v1's `_SCALE_DECL`: the words, the case-insensitive
abbreviations, the abbreviations). -/
def scaleNames : List String :=
  ["hundred", "thousand", "million", "billion", "trillion", "quadrillion", "lakh", "crore",
    "dozen", "tenth", "hundredth", "thousandth", "millionth", "billionth", "trillionth",
    "mn", "bn", "mln", "bln", "tn", "trn", "mio", "mrd",
    "k", "K", "M", "m", "B", "MM"]

/-- v1's `_check_affix` of a string: a declared name, or one to four characters, the
first an affix sign or a currency symbol and the rest letters. -/
def affixOk (a : String) : Bool :=
  affixNames.contains a ||
    match a.toList with
    | c :: cs => cs.length ≤ 3 && (affixSigns.contains c || ucls c = some .currency) &&
        cs.all fun d => ucls d = some .letter
    | [] => false

/-- v1's `_check_scale` of a string. -/
def scaleOk (s : String) : Bool := scaleNames.contains s

/-- A field name: an ASCII letter, then ASCII letters, digits and `_`; never `IV`. -/
def nameOk : Option Value → Bool
  | some (.str s) =>
    s ≠ "IV" &&
      match s.toList with
      | c :: cs => c.isAlpha && cs.all fun d => d.isAlphanum || d = '_'
      | [] => false
  | _ => false

/-- A field class: MECHANICAL or INSPECTION. -/
def classOk : Option Value → Bool
  | some (.str "MECHANICAL") | some (.str "INSPECTION") => true
  | _ => false

/-- The affix or the scale, when present: only with `quote` true, a string, and one v1
accepts. -/
def quotedStringOk (ms : Members) (k : String) (ok : String → Bool) : Bool :=
  match field? ms k with
  | none => true
  | some (.str s) =>
    (match field? ms "quote" with
      | some (.bool true) => true
      | _ => false) && ok s
  | some _ => false

/-- An enum's values: a non-empty list of distinct strings. -/
def valuesOk : Option Value → Bool
  | some (.arr vs@(_ :: _)) =>
    match vs.mapM fun v => match v with | .str s => some s | _ => none with
    | some ss => distinct ss
    | none => false
  | _ => false

/-- A field spec's own checks, rows aside: its keys for its type, its name, its class,
its `quote`, its affix and scale, an enum's values. `allowRows` admits the type `rows`'s
keys. -/
def fieldChecks (ms : Members) (allowRows : Bool) : Bool :=
  match strField? ms "type" with
  | none => false
  | some t =>
    let base := ["name", "type", "class"]
    let keysOk :=
      if t = "enum" then keysAre ms (base ++ ["values"]) ["quote"]
      else if t = "rows" && allowRows then keysAre ms (base ++ ["key", "columns"]) []
      else if t = "decimal" || t = "unitvalue" then keysAre ms base ["quote", "affix", "scale"]
      else if valueTypes.contains t then keysAre ms base ["quote"]
      else false
    keysOk && nameOk (field? ms "name") && classOk (field? ms "class") &&
      (match field? ms "quote" with
        | none | some (.bool _) => true
        | some _ => false) &&
      quotedStringOk ms "affix" affixOk && quotedStringOk ms "scale" scaleOk &&
      (t ≠ "enum" || valuesOk (field? ms "values"))

/-- A column of a `rows` field: its name and class, when its spec passes. -/
def columnOf : Value → Option (String × String)
  | .obj ms =>
    if fieldChecks ms false then
      match strField? ms "name", strField? ms "class" with
      | some n, some c => some (n, c)
      | _, _ => none
    else none
  | _ => none

/-- A `rows` field's own checks: MECHANICAL; columns, a non-empty list of passing
specs with distinct names; a key, a non-empty list of distinct column names, each a
MECHANICAL column. -/
def rowsOk (ms : Members) : Bool :=
  match strField? ms "class", field? ms "columns", field? ms "key" with
  | some "MECHANICAL", some (.arr cols@(_ :: _)), some (.arr key@(_ :: _)) =>
    match cols.mapM columnOf, key.mapM fun k => match k with | .str s => some s | _ => none with
    | some named, some names =>
      distinct (named.map (·.1)) && distinct names &&
        names.all fun n => List.lookup n named = some "MECHANICAL"
    | _, _ => false
  | _, _, _ => false

/-- v1's `_check_spec(spec, allow_rows)`: true when it raises nothing. -/
def specOk (spec : Value) (allowRows : Bool) : Bool :=
  match spec with
  | .obj ms =>
    fieldChecks ms allowRows && (strField? ms "type" ≠ some "rows" || rowsOk ms)
  | _ => false

/-! ## The canonical form of a field value -/

/-- v1's `falcon_canon(value, spec)`. -/
def falconCanon (value spec : Value) : Result String :=
  if !specOk spec false then refuse "schema"
  else
    match spec with
    | .obj ms =>
      match strField? ms "type", value with
      | some "text", .str s => canonText s
      | some "text", _ => refuse "text"
      | some "decimal", .str s => canonDecimal s
      | some "decimal", _ => refuse "decimal"
      | some "unitvalue", .str s => canonUnitValue s
      | some "unitvalue", _ => refuse "unitvalue"
      | some "date", .str s => canonDate s
      | some "date", _ => refuse "date"
      | some "url", .str s => canonUrl s
      | some "url", _ => refuse "url"
      | some "enum", .str s =>
        match field? ms "values" with
        | some (.arr vs) =>
          if vs.any (fun v => match v with | .str t => t == s | _ => false) then .ok s
          else refuse "enum"
        | _ => refuse "enum"
      | some "enum", _ => refuse "enum"
      | _, .bool b => .ok (if b then "true" else "false")
      | _, _ => refuse "boolean"
    | _ => refuse "schema"

/-- v1's `run_case` for `canon`: the render of the canonical form, or the refusal. -/
def canonCase (value spec : Value) : Result String :=
  (falconCanon value spec).map renderCanon

/-! ## Guarantees

The render is injective: two canonical forms that render alike are equal, so comparing
v1's render text compares the forms themselves (`renderCanon_injective`). `unesc` undoes
`esc` (`unesc_esc`): `|` and `\` are backslashed, and a control character's `\x` and two
hexadecimal digits are read back, never confused with a backslashed character.

A text form is always answered, as NFC then the collapse (`canonText_nfc`); two texts with one
NFC have one form (`canonText_of_nfc`). -/

/-- A lower-case hexadecimal digit's value: the inverse of `Canonical.hexDigit` on 0 to 15. -/
def lowerHexValue (c : Char) : Nat :=
  if c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

theorem lowerHexValue_hexDigit : ∀ k : Fin 16, lowerHexValue (Canonical.hexDigit k) = k := by
  decide

/-- v1's `_esc` undone. -/
def unesc : List Char → List Char
  | '\\' :: 'x' :: a :: b :: rest =>
    Char.ofNat (lowerHexValue a * 16 + lowerHexValue b) :: unesc rest
  | '\\' :: c :: rest => c :: unesc rest
  | c :: rest => c :: unesc rest
  | [] => []

theorem unesc_escChar (c : Char) (s : List Char) : unesc (escChar c ++ s) = c :: unesc s := by
  unfold escChar
  split
  · next h => subst h; simp [unesc]
  · split
    · next h0 h => subst h; simp [unesc]
    · split
      · next h0 h1 h =>
        have h16 : c.toNat / 16 < 16 := by omega
        have hm : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
        simp only [List.cons_append, List.nil_append, unesc]
        have e1 := lowerHexValue_hexDigit ⟨c.toNat / 16, h16⟩
        have e2 := lowerHexValue_hexDigit ⟨c.toNat % 16, hm⟩
        simp only at e1 e2
        rw [e1, e2]
        have : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by
          have := Nat.div_add_mod c.toNat 16; omega
        rw [this, Char.ofNat_toNat]
      · next h0 h1 h2 =>
        simp only [List.cons_append, List.nil_append]
        rw [unesc.eq_def]
        split <;> simp_all

theorem unesc_flatMap (cs : List Char) : unesc (cs.flatMap escChar) = cs := by
  induction cs with
  | nil => simp [unesc]
  | cons c cs ih => rw [List.flatMap_cons, unesc_escChar, ih]

/-- `unesc` undoes `esc`. -/
theorem unesc_esc (s : String) : unesc (esc s).toList = s.toList := by
  simp only [esc, String.toList_ofList, unesc_flatMap]

/-- `esc` is injective. -/
theorem esc_injective {a b : String} (h : esc a = esc b) : a = b := by
  have h' := congrArg (fun s => unesc s.toList) h
  simp only [unesc_esc] at h'
  exact String.ext h'

/-- The render of a canonical form is injective (the corpus compares render texts). -/
theorem renderCanon_injective {a b : String} (h : renderCanon a = renderCanon b) : a = b := by
  unfold renderCanon at h
  have h' := congrArg String.toList h
  simp only [String.toList_append] at h'
  exact esc_injective (String.ext (List.append_cancel_left h'))

/-- A text's canonical form is always answered: the collapse of its NFC. -/
theorem canonText_nfc (s : String) :
    canonText s = .ok (String.ofList (collapse (Unicode.nfc s).toList)) := by
  simp [canonText, canonTextChars, Unicode.nfc]

/-- Two texts with one NFC have one canonical form: a text in NFD and its NFC compare
AGREED, as in v1. -/
theorem canonText_of_nfc {a b : String} (h : Unicode.nfc a = Unicode.nfc b) :
    canonText a = canonText b := by
  rw [canonText_nfc, canonText_nfc, h]

end Principia.Falcon
