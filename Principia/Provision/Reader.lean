import Principia.Digest
import Principia.Zone
import Principia.Strike.Conditions

/-!
# Provisions: answers, the strict reader and the patterns

v1's `tpc_module` 0.1.1 (tpm_module_spec 0.2.0; rulings S48-S54; version 1's
module reader), the functions of TPS 5.22 that PMA calls on a Provision. This file holds what every Provision function shares:
the answer and its owed reasons, v1's strict JSON reader for a Provision's text (2.7), the
patterns of an ID, a VERSION, a slot, a digest, a date and an answer key (2.6), and the
field checks every refusal starts from (2.8, 2.9).

**Answers.** A function's answer is v1's `["OK", ...]`, its `["REFUSED", reason]` (the
reason passed through v1's `_show`), or owed: what the Calculator cannot settle yet, named
and never guessed.
* `Owed.digest`: a digest the `DigestHook` has no value for. A digest is taken through the
  hook; the Calculator's is SHA-256 (`DigestHook.calculator`, `Principia.Sha256`), which has one for every preimage (`DigestHook.calculator_digest`), so no answer of
  the Calculator's is owed for a digest. The runner also answers every case through a second
  hook, v1's own SHA-256 values for the very preimages the Calculator computes
  (the Provisions' digest corpus), which has none for a preimage v1 never digested.
* `Owed.exact`: a number the fundamental tests cannot settle within the Calculator's exact
  bounds (the bound on an exact number's size).

**Text.** As v1, the strict reader puts every string of a Provision's text in NFC as it reads
it, keys included, and refuses a key twice after NFC; `_text` and `_first_bad` are the
zones', and a refusal is shown with its disallowed code points escaped, all at Unicode
15.1.0 (`Principia.Zone.Text`).
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-! ## Answers -/

/-- What the Calculator cannot settle yet, and so does not answer. -/
inductive Owed where
  /-- A digest the hook has no value for: never the Calculator's hook, SHA-256. -/
  | digest
  /-- A number beyond the Calculator's exact bounds: what was met. -/
  | exact (what : String)
  deriving DecidableEq, Repr

/-- An owed reason as the owed list spells it. -/
def Owed.word : Owed → String
  | .digest => "digests"
  | .exact what => "exact: " ++ what

/-- Why a computation stopped: v1's refusal, its reason before `_show`, or owed. -/
inductive Stop where
  | refused (reason : String)
  | owed (why : Owed)
  deriving Repr

/-- A computation that may stop. -/
abbrev Run := Except Stop

/-- v1's `_R`: refuse with a reason. -/
def refuse {α : Type} (msg : String) : Run α := throw (.refused msg)

/-- Stop, owed. -/
def owe {α : Type} (why : Owed) : Run α := throw (.owed why)

/-- A function's answer: v1's `["OK", ...]`, its `["REFUSED", reason]`, or owed. -/
inductive Answer (α : Type) where
  | ok (a : α)
  | refused (reason : String)
  | owed (why : Owed)
  deriving Repr

/-- v1's `_show`. -/
def showReason (msg : String) : String := Strike.showMessage false msg

/-- A computation's answer, its refusal shown as v1's `_refuse` shows it. -/
def finish {α : Type} (r : Run α) : Answer α :=
  match r with
  | .ok a => .ok a
  | .error (.owed w) => .owed w
  | .error (.refused m) => .refused (showReason m)

/-! ## SHA-256, as the functions take it -/

/-- A digest of a preimage (its UTF-8 bytes), as 64 lowercase hexadecimal digits, or `none`
where the hook has no value for it. -/
structure DigestHook where
  sha256 : String → Option String

/-- The Calculator's hook: SHA-256 (`Principia.Digest.ofPreimage`). -/
def DigestHook.calculator : DigestHook := ⟨fun p => some (Digest.ofPreimage p)⟩

/-- A digest through the hook, owed when the hook has none. -/
def DigestHook.digest (D : DigestHook) (preimage : String) : Run String :=
  match D.sha256 preimage with
  | some h => pure h
  | none => owe .digest

/-- Through the Calculator's hook every preimage has its digest, SHA-256: nothing is owed
for one. -/
theorem DigestHook.calculator_digest (preimage : String) :
    DigestHook.calculator.digest preimage = .ok (Digest.ofPreimage preimage) := rfl

/-! ## The strict reader (2.7)

v1 drives `tpc_identity`'s lexer to values: RFC 8259 strict, white space ` \t\n\r` only, a
string's escapes and surrogate pairs checked and its raw control characters refused, an
exponent of at most four digits, depth at most 64, a key twice or a key holding U+0000
refused. A number is an integer when it is written `-?(0|[1-9][0-9]{0,3})`; any other number
is v1's NOT-AN-INTEGER value, which every field refuses (`Value.real`). Each step takes one
unit of fuel and at least every second step consumes a character, so twice the text's
length and four more never run out. -/

/-- JSON white space. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The text after its white space. -/
def skipWs (cs : List Char) : List Char := cs.dropWhile isWs

/-- An ASCII digit. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- A hexadecimal digit's value. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits and the rest. -/
def hex4? : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    pure ((((← hexVal? a) * 16 + (← hexVal? b)) * 16 + (← hexVal? c)) * 16 + (← hexVal? d), rest)
  | _ => none

/-- A string's body after its opening quote: its code points, reversed onto `acc`, and the
text after its closing quote. -/
def readString : Nat → List Char → List Char → Option (List Char × List Char)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | _ + 1, '"' :: rest, acc => some (acc.reverse, rest)
  | f + 1, '\\' :: e :: rest, acc =>
    if e == '"' || e == '\\' || e == '/' then readString f rest (e :: acc)
    else if e == 'b' then readString f rest ('\x08' :: acc)
    else if e == 'f' then readString f rest ('\x0c' :: acc)
    else if e == 'n' then readString f rest ('\n' :: acc)
    else if e == 'r' then readString f rest ('\r' :: acc)
    else if e == 't' then readString f rest ('\t' :: acc)
    else if e == 'u' then
      match hex4? rest with
      | none => none
      | some (cp, r1) =>
        if 0xD800 ≤ cp && cp ≤ 0xDBFF then
          match r1 with
          | '\\' :: 'u' :: r2 =>
            match hex4? r2 with
            | some (lo, r3) =>
              if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
                readString f r3 (Char.ofNat (0x10000 + (cp - 0xD800) * 1024 + (lo - 0xDC00)) :: acc)
              else none
            | none => none
          | _ => none
        else if 0xDC00 ≤ cp && cp ≤ 0xDFFF then none
        else readString f r1 (Char.ofNat cp :: acc)
    else none
  | _ + 1, ['\\'], _ => none
  | f + 1, c :: rest, acc => if c.toNat < 0x20 then none else readString f rest (c :: acc)

/-- An exponent's digits: one to four of them. -/
def expDigits (cs : List Char) : Option (List Char) :=
  let ds := cs.takeWhile isDigit
  if ds.isEmpty || ds.length > 4 then none else some (cs.drop ds.length)

/-- The rest of a number after its integer part: a fraction, then an exponent. -/
def numberTail (cs : List Char) : Option (List Char) := do
  let afterFrac ← match cs with
    | '.' :: r => let ds := r.takeWhile isDigit; if ds.isEmpty then none else some (r.drop ds.length)
    | _ => some cs
  match afterFrac with
  | c :: r =>
    if c == 'e' || c == 'E' then
      match r with
      | s :: r' => if s == '+' || s == '-' then expDigits r' else expDigits r
      | [] => none
    else some afterFrac
  | [] => some afterFrac

/-- A number's characters and the rest (v1's `number`). -/
def readNumberChars (cs : List Char) : Option (List Char) := do
  let r0 := match cs with
    | '-' :: r => r
    | r => r
  match r0 with
  | '0' :: r1 => numberTail r1
  | c :: r1 => if '1' ≤ c && c ≤ '9' then numberTail (r1.dropWhile isDigit) else none
  | [] => none

/-- v1's `_RX_INT`: `-?(0|[1-9][0-9]{0,3})`. -/
def isSmallInt (lit : List Char) : Bool :=
  let ds := match lit with
    | '-' :: r => r
    | r => r
  match ds with
  | ['0'] => true
  | c :: r => '1' ≤ c && c ≤ '9' && r.length ≤ 3 && r.all isDigit
  | [] => false

/-- A small integer's value. -/
def intOf (lit : List Char) : Int :=
  match lit with
  | '-' :: r => -((r.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0 : Nat) : Int)
  | r => ((r.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0 : Nat) : Int)

/-- The most a value may nest (v1's `MAX_DEPTH`). -/
def maxDepth : Nat := 64

/-- A character a number's text may hold. -/
def isNumberChar (c : Char) : Bool :=
  isDigit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

/-- A number's characters, from the text at the number and the text after it: those it
consumed, every one a number's character, counted without measuring the rest of the
text. -/
def numberLiteral (cs rest : List Char) : List Char :=
  let run := cs.takeWhile isNumberChar
  run.take (run.length - (rest.takeWhile isNumberChar).length)

/-- Whether a list of keys holds one twice: adjacent once sorted. -/
def hasRepeat (keys : List String) : Bool :=
  let rec go : List String → Bool
    | a :: b :: r => a == b || go (b :: r)
    | _ => false
  go (keys.mergeSort fun a b => decide (a ≤ b))

-- `sf` is a string's fuel, the whole text's length and one more, which no string read from
-- it uses up; it is measured once, so that a string costs its own length. The items and
-- members are gathered last first and reversed once, and a key twice is found by one sort
-- when the object closes: a text with a key twice is refused either way.
mutual
/-- A value at `depth` and the text after it. -/
def readValue : Nat → Nat → Nat → List Char → Option (Value × List Char)
  | 0, _, _, _ => none
  | f + 1, sf, depth, cs =>
    if depth > maxDepth then none else
    match skipWs cs with
    | '{' :: r => readObject f sf depth r
    | '[' :: r => readArray f sf depth r
    | '"' :: r =>
      (readString sf r []).map fun (s, rest) => (.str (Unicode.nfc (String.ofList s)), rest)
    | c :: r =>
      if c == '-' || isDigit c then
        (readNumberChars (c :: r)).map fun rest =>
          let lit := numberLiteral (c :: r) rest
          (if isSmallInt lit then .int (intOf lit) else .real, rest)
      else if (c :: r).take 4 == "true".toList then some (.bool true, r.drop 3)
      else if (c :: r).take 5 == "false".toList then some (.bool false, r.drop 4)
      else if (c :: r).take 4 == "null".toList then some (.null, r.drop 3)
      else none
    | [] => none

/-- An object after its `{`. -/
def readObject : Nat → Nat → Nat → List Char → Option (Value × List Char)
  | 0, _, _, _ => none
  | f + 1, sf, depth, cs =>
    match skipWs cs with
    | '}' :: r => some (.obj [], r)
    | _ => readMembers f sf depth cs []

/-- An object's members, the ones read so far in `acc`, last first. -/
def readMembers : Nat → Nat → Nat → List Char → List (String × Value) → Option (Value × List Char)
  | 0, _, _, _, _ => none
  | f + 1, sf, depth, cs, acc =>
    match skipWs cs with
    | '"' :: r =>
      match readString sf r [] with
      | none => none
      | some (k, r1) =>
        if k.contains '\x00' then none else
        match skipWs r1 with
        | ':' :: r2 =>
          match readValue f sf (depth + 1) r2 with
          | none => none
          | some (v, r3) =>
            let key := Unicode.nfc (String.ofList k)
            match skipWs r3 with
            | ',' :: r4 => readMembers f sf depth r4 ((key, v) :: acc)
            | '}' :: r4 =>
              let ms := ((key, v) :: acc).reverse
              if hasRepeat (ms.map (·.1)) then none else some (.obj ms, r4)
            | _ => none
        | _ => none
    | _ => none

/-- An array after its `[`. -/
def readArray : Nat → Nat → Nat → List Char → Option (Value × List Char)
  | 0, _, _, _ => none
  | f + 1, sf, depth, cs =>
    match skipWs cs with
    | ']' :: r => some (.arr [], r)
    | _ => readItems f sf depth cs []

/-- An array's items, the ones read so far in `acc`, last first. -/
def readItems : Nat → Nat → Nat → List Char → List Value → Option (Value × List Char)
  | 0, _, _, _, _ => none
  | f + 1, sf, depth, cs, acc =>
    match readValue f sf (depth + 1) cs with
    | none => none
    | some (v, r) =>
      match skipWs r with
      | ',' :: r1 => readItems f sf depth r1 (v :: acc)
      | ']' :: r1 => some (.arr (v :: acc).reverse, r1)
      | _ => none
end

/-- A whole text as one JSON value, or `none` when it is not JSON (RFC 8259, strict). -/
def readJson (text : String) : Option Value :=
  let cs := text.toList
  match readValue (2 * cs.length + 4) (cs.length + 1) 0 cs with
  | some (v, rest) => if (skipWs rest).isEmpty then some v else none
  | none => none

/-- The longest text read, in UTF-8 bytes (RD-MS-16). -/
def maxBytes : Nat := 262144

/-- The refusal of a text that is not JSON. -/
def notJson : String := "MODULE: the text is not JSON (RFC 8259, strict)"

/-- v1's `_read` with the bound before it: the value of a text, every string of it in NFC, or
the refusal. -/
def readText (text : Value) : Run Value := do
  let .str t := text | refuse "MODULE: the text is not a string"
  if t.utf8ByteSize > maxBytes then refuse s!"MODULE: the text is longer than {maxBytes} bytes"
  let some v := readJson t | refuse notJson
  pure v

/-! ## Patterns (2.6) -/

/-- An upper-case ASCII letter. -/
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- A lower-case ASCII letter. -/
def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- The parts of a list between separators. -/
def splitOn (sep : Char) (cs : List Char) : List (List Char) := cs.splitOn sep

/-- v1's `_is_module_id`: at most 32 code points, `[A-Z][A-Z0-9]*(-[A-Z0-9]+)*`. -/
def isProvisionId (s : String) : Bool :=
  let cs := s.toList
  cs.length ≤ 32 &&
  match splitOn '-' cs with
  | (c :: first) :: rest =>
    isUpper c && first.all (fun d => isUpper d || isDigit d) &&
      rest.all fun p => !p.isEmpty && p.all fun d => isUpper d || isDigit d
  | _ => false

/-- `0|[1-9][0-9]{0,3}`. -/
def isVersionPart (p : List Char) : Bool :=
  match p with
  | ['0'] => true
  | c :: r => '1' ≤ c && c ≤ '9' && r.length ≤ 3 && r.all isDigit
  | [] => false

/-- v1's `_is_version`: three integers of at most four digits, without a leading zero. -/
def isVersion (s : String) : Bool :=
  match splitOn '.' s.toList with
  | [a, b, c] => isVersionPart a && isVersionPart b && isVersionPart c
  | _ => false

/-- A digit run's value. -/
def digitsVal (cs : List Char) : Nat := cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- v1's `_vkey`: a VERSION's three integers, compared as such. -/
def versionKey (s : String) : List Nat := (splitOn '.' s.toList).map digitsVal

/-- `a < b` on version keys, lexicographic. -/
def keyLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && keyLt as bs)

/-- v1's `_is_slot`: at most 32 code points, `[A-Z][A-Z0-9_]*`. -/
def isSlot (s : String) : Bool :=
  match s.toList with
  | c :: r => s.length ≤ 32 && isUpper c && r.all fun d => isUpper d || isDigit d || d == '_'
  | [] => false

/-- v1's `_is_digest`: 64 lowercase hexadecimal digits. -/
def isDigest (s : String) : Bool :=
  s.length == 64 && s.all fun c => isDigit c || ('a' ≤ c && c ≤ 'f')

/-- A leap year of the Gregorian calendar. -/
def leap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- v1's `_is_date`: `YYYY-MM-DD`, a day of the Gregorian calendar, year at least 1. -/
def isDate (s : String) : Bool :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] =>
    [y1, y2, y3, y4, m1, m2, d1, d2].all isDigit &&
      let y := digitsVal [y1, y2, y3, y4]
      let mo := digitsVal [m1, m2]
      let d := digitsVal [d1, d2]
      let days := if mo == 2 && leap y then 29
        else [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31].getD (mo - 1) 0
      1 ≤ y && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ days
  | _ => false

/-- v1's `_is_entry_name`: an identifier of at most 64 code points with a lower-case
letter. -/
def isEntryName (s : String) : Bool := Zone.isIdent s && s.length ≤ 64 && s.toList.any isLower

/-- The text after `n` code points. -/
def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- The text without its last `n` code points. -/
def dropLastChars (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

/-- v1's `_is_answer_key`: a slot name, or `FIXED:` and an identifier. -/
def isAnswerKey (k : String) : Bool :=
  isSlot k || (k.startsWith "FIXED:" && Zone.isIdent (dropChars k 6))

/-- v1's `_is_pattern`: an ID, or an ID followed by `-*`. -/
def isPattern (s : String) : Bool :=
  isProvisionId s || (s.endsWith "-*" && isProvisionId (dropLastChars s 2))

/-- v1's `_matches`: a pattern `X-*` matches every ID starting `X-`; an ID matches itself. -/
def idMatches (p id : String) : Bool :=
  if p.endsWith "-*" then id.startsWith (dropLastChars p 1) else id == p

/-! ## Lists of names -/

/-- Strings in code point order (stable). -/
def sortStrs (xs : List String) : List String := xs.mergeSort fun a b => decide (a ≤ b)

/-- Strings in code point order, without repeats (Python's `sorted(set(...))`). -/
def sortedSet (xs : List String) : List String := sortStrs xs.eraseDups

/-- v1's `_least_dup`: the least name that occurs twice or more. -/
def leastDup (xs : List String) : Option String :=
  (sortStrs (xs.filter fun x => xs.count x ≥ 2)).head?

/-- Strictly increasing in code point order: sorted without repeats. -/
def strictlySorted : List String → Bool
  | a :: b :: r => decide (a < b) && strictlySorted (b :: r)
  | _ => true

/-! ## Field checks (2.8, 2.9) -/

/-- An object's keys in code point order. -/
def keysOf (o : Entry) : List String := sortStrs (o.map (·.1))

/-- v1's `_fields`: no unknown field (the least named first), then every required one. -/
def fields (tag : String) (o : Entry) (req : List String) (opt : List String := []) :
    Run Unit := do
  for k in keysOf o do
    unless req.contains k || opt.contains k do refuse (tag ++ ": unknown field " ++ k)
  for f in req do
    unless has o f do refuse (tag ++ ": missing field " ++ f)

/-- v1's `_first_bad`. -/
def firstBad (s : String) : Run (Option String) := pure (Zone.firstBad s)

/-- v1's `_text`: line endings to LF and NFC. -/
def text (s : String) : Run String := pure (Zone.text s)

/-- v1's `_str`: a string, free of disallowed code points, not blank where it must not be. -/
def str (tag f : String) (v : Value) (blankOk : Bool := true) : Run String := do
  let .str s := v | refuse (tag ++ ": field " ++ f ++ " has the wrong type")
  if let some b ← firstBad s then refuse (tag ++ ": field " ++ f ++ " contains disallowed character " ++ b)
  if !blankOk && Zone.blank s then refuse (tag ++ ": field " ++ f ++ " is blank")
  pure s

/-- A list of strings, or `none`. -/
def strList? : Value → Option (List String)
  | .arr xs => xs.mapM fun | .str s => some s | _ => none
  | _ => none

/-- A list of objects, or `none`. -/
def objList? : Value → Option (List Entry)
  | .arr xs => xs.mapM fun | .obj e => some e | _ => none
  | _ => none

/-- v1's `_strs`: a list of strings, at most `cap`, each free of disallowed code points. -/
def strs (tag f : String) (v : Value) (cap : Option Nat := none) : Run (List String) := do
  let some xs := strList? v | refuse (tag ++ ": field " ++ f ++ " has the wrong type")
  if let some c := cap then
    if xs.length > c then refuse (tag ++ ": field " ++ f ++ s!" has more than {c} entries")
  for x in xs do
    if let some b ← firstBad x then refuse (tag ++ ": field " ++ f ++ " contains disallowed character " ++ b)
  pure xs

/-- v1's `_objs`: a list of objects, at most `cap`. -/
def objs (tag f : String) (v : Value) (cap : Nat) : Run (List Entry) := do
  let some xs := objList? v | refuse (tag ++ ": field " ++ f ++ " has the wrong type")
  if xs.length > cap then refuse (tag ++ ": field " ++ f ++ s!" has more than {cap} entries")
  pure xs

/-- v1's `_dimension`: the normalized DIMENSION, or why not. -/
def dimension (tag v : String) : Run String :=
  match Dimension.normalize v with
  | some d => pure d
  | none =>
    if Dimension.outOfRange v then refuse (tag ++ ": DIMENSION " ++ v ++ ": an exponent is out of range")
    else refuse (tag ++ ": DIMENSION " ++ v ++ " is not a dimension")

/-- v1's `_tag`: a prefix and the field's string, or `?`. -/
def tagOf (pre : String) (e : Entry) (f : String) : String := pre ++ (getStr? e f).getD "?"

/-- A field that `fields` has checked is present. -/
def field (e : Entry) (f : String) : Value := (get? e f).getD .null

/-- v1's `unit_parse`: a UNIT's canonical spelling and DIMENSION, or its reason. -/
def unitParse (u : String) : Except String (String × String) :=
  match Units.tokens u with
  | .error r => .error r
  | .ok items => .ok (Units.spelling items, Dimension.canon (Units.dimExps items))

end Principia.Provision
