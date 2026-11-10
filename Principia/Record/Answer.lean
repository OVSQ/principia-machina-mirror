import Principia.Canonical
import Principia.CanonicalReader
import Principia.Digest
import Principia.Zone.Text
import Principia.Record.Table

/-!
# The register functions' answers, and what they share

v1's `tpc_record` 0.1.0 answered every function with a list in TPM's canonical JSON:
`["OK", ...]`, `["REFUSED", problems]` (problems `[code, field, message]`, sorted in code
point order, none twice), and for some functions `["INSPECT", reason]`,
`["CONVENTION", reason]`, `["NOT", reasons]` or `["ELIGIBLE", ...]`. Here an answer is
that list as a `Principia.Canonical.Value`, written by `Value.canonicalJson`, or owed.

**Digests.** A digest is SHA-256 over a field list's netstring, in lowercase hexadecimal
(`Principia.Digest.digestFields`, `Principia.Sha256`): a function that
writes a digest computes it, and a check that compares one computes it and compares.

**Owed.** A function never answers what the Calculator cannot settle yet:
`number`, a value v1 computed in floating point that has no exact form here, or whose exact
form is not the answer v1 gave (the Calculator's numbers are exact).

Also here: v1's helpers that read text: `_show`, `_text`, `_first_bad`, the identifier,
date and version forms, the problem list. Text is read as v1 read it: NFC and the general
category at Unicode 15.1.0 (`Principia.Zone.Text`).
-/

namespace Principia.Record

open Principia.Canonical (Value)
open Principia.Zone (codePoint)

/-! ## Owed -/

/-- What a register function cannot settle yet, or will not form. -/
inductive Owed where
  /-- A number v1 computed in floating point (the Calculator's numbers are exact): what was met. -/
  | number (what : String)
  /-- Not owed but refused: a value the function would form from its arguments that could
  cross the bound on an exact value's size, "exact value too large". -/
  | tooLarge
  deriving DecidableEq, Repr

/-- An owed answer's reason, as the owed list spells it. -/
def Owed.word : Owed → String
  | .number _ => "number"
  | .tooLarge => "too large"

/-- A computation that may be owed. -/
abbrev M := Except Owed

/-- A register function's answer: v1's result list, or owed. -/
inductive Answer where
  | done (result : Value)
  | owed (why : Owed)
  deriving Repr

/-- An answer from a computation that may be owed. -/
def Answer.ofM : M Value → Answer
  | .ok v => .done v
  | .error o => .owed o

/-! ## Values -/

namespace V

/-- v1's `obj.get(k)`: the member's value, when `v` is an object holding `k`. -/
def get? : Value → String → Option Value
  | .obj ms, k => ms.lookup k
  | _, _ => none

/-- v1's `k in obj`. -/
def has (v : Value) (k : String) : Bool := (get? v k).isSome

/-- The object's keys, in order. -/
def keys : Value → List String
  | .obj ms => ms.map Prod.fst
  | _ => []

/-- The string a value holds. -/
def str? : Option Value → Option String
  | some (.str s) => some s
  | _ => none

/-- The string member `k` of `v`. -/
def getStr? (v : Value) (k : String) : Option String := str? (get? v k)

/-- v1's `type(v) is str`. -/
def isStr : Value → Bool
  | .str _ => true
  | _ => false

/-- v1's `type(v) is dict`. -/
def isObj : Value → Bool
  | .obj _ => true
  | _ => false

/-- v1's `type(v) is list`. -/
def isArr : Value → Bool
  | .arr _ => true
  | _ => false

/-- v1's `_members`: the strings of a list, `[]` for anything else. -/
def members : Option Value → List String
  | some (.arr xs) => xs.filterMap (fun | .str s => some s | _ => none)
  | _ => []

/-- The strings of a list, when every item is one. -/
def strList? : Value → Option (List String)
  | .arr xs => xs.mapM (fun | .str s => some s | _ => none)
  | _ => none

/-- The object `v` with member `k` set to `x` (replacing, or appended). -/
def set (v : Value) (k : String) (x : Value) : Value :=
  match v with
  | .obj ms => if ms.any (·.1 == k) then .obj (ms.map fun m => if m.1 == k then (k, x) else m)
    else .obj (ms ++ [(k, x)])
  | _ => v

/-- The object `v` without member `k`. -/
def erase (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => .obj (ms.filter (·.1 != k))
  | _ => v

/-- A list of strings as a value. -/
def strs (xs : List String) : Value := .arr (xs.map .str)

end V

/-- v1's `cj`: TPM's canonical JSON (schema 11.4). An object never holds a key twice here
(the reader refuses one), so the writer always answers. -/
def cj (v : Value) : String := v.canonicalJson.getD ""

/-! ## Text: v1's `_show`, `_text` and `_first_bad` -/

/-- v1's `_shown_char`: general category C, and U+2028 and U+2029; TAB and LF included. -/
def shownChar (c : Char) : M Bool := pure (Zone.disallowed c || c == '\t' || c == '\n')

/-- v1's `_show` (schema 12.1): a slot value in a message, each shown code point written
`<U+XXXX>`. -/
def showSlot (s : String) : M String := do
  let parts ← s.toList.mapM fun c => do
    if ← shownChar c then pure ("<" ++ codePoint c ++ ">") else pure c.toString
  pure (String.join parts)

/-- v1's `_v`: a string shown as given, any other value as its canonical JSON, shown. -/
def showArg : Value → M String
  | .str s => showSlot s
  | v => showSlot (cj v)

/-- v1's `_vj`: the value's canonical JSON, shown. -/
def showJson (v : Value) : M String := showSlot (cj v)

/-- v1's `tpc_zone._text`: line endings as LF, then NFC. -/
def text (s : String) : M String := pure (Zone.text s)

/-- v1's `tpc_zone._first_bad`: the first disallowed code point after line-ending
normalization, as `U+XXXX`. -/
def firstBad (s : String) : M (Option String) := pure (Zone.firstBad s)

/-- v1's text test (`_first_bad(s) is None and not _blank(s)`): a text, not blank. -/
def isText (s : String) : M Bool := do
  return (← firstBad s).isNone && !Zone.blank s

/-! ## Problems -/

/-- A problem: its code, its field and its message. -/
abbrev Problem := String × String × String

/-- Code point order of problems: by code, then field, then message (v1's `sorted` of
triples). -/
def problemLt (a b : Problem) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 &&
    (decide (a.2.1 < b.2.1) || (a.2.1 == b.2.1 && decide (a.2.2 < b.2.2))))

/-- Adjacent repeats dropped. -/
def dedupAdjacent : List Problem → List Problem
  | a :: b :: rest => if a == b then dedupAdjacent (b :: rest) else a :: dedupAdjacent (b :: rest)
  | l => l

/-- v1's `_problems`: sorted in code point order, no triple twice. -/
def sortProblems (ps : List Problem) : List Problem :=
  dedupAdjacent (ps.mergeSort fun a b => !problemLt b a)

/-- A problem as v1's list. -/
def Problem.toValue (p : Problem) : Value := .arr [.str p.1, .str p.2.1, .str p.2.2]

/-- v1's `["REFUSED", problems]`. -/
def refused (ps : List Problem) : Value :=
  .arr [.str "REFUSED", .arr ((sortProblems ps).map Problem.toValue)]

/-- v1's `_one`: a refusal with one problem. -/
def one (code field msg : String) : Value := refused [(code, field, msg)]

/-- v1's `["OK"]`. -/
def okV : Value := .arr [.str "OK"]

/-- v1's `["OK", ...]`. -/
def okWith (vs : List Value) : Value := .arr (.str "OK" :: vs)

/-- v1's `[word, reason]` (`INSPECT`, `CONVENTION`). -/
def worded (w reason : String) : Value := .arr [.str w, .str reason]

/-- v1's `_bad_arg`: REC-50, the argument's canonical JSON shown. -/
def badArg (argument : String) (v : Value) (what : String) : M Value := do
  return one "REC-50" "-" s!"{argument} {← showJson v} is not {what}"

/-- v1's `_or_list`: `a`, `a or b`, `a, b or c`. -/
def orList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | last :: rest => ", ".intercalate rest.reverse ++ " or " ++ last

/-- v1's `_and_list`. -/
def andList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | last :: rest => ", ".intercalate rest.reverse ++ " and " ++ last

/-! ## Forms of text (v1's regular expressions, each over the whole string) -/

/-- `[0-9]`. -/
def digitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `[1-9][0-9]*`. -/
def posDigits : List Char → Bool
  | c :: cs => '1' ≤ c && c ≤ '9' && cs.all digitC
  | [] => false

/-- The text before the first `-`, and after it. -/
def cutDash (cs : List Char) : Option (List Char × List Char) :=
  match cs.idxOf? '-' with
  | some i => some (cs.take i, cs.drop (i + 1))
  | none => none

/-- v1's `_RID`: `[A-Za-z_][A-Za-z0-9_]*-[1-9][0-9]*`. -/
def isRid (s : String) : Bool :=
  match cutDash s.toList with
  | some (p, n) => Zone.isIdent (String.ofList p) && posDigits n
  | none => false

/-- v1's `_BIB`: `[A-Za-z_][A-Za-z0-9_]*-BIB[1-9][0-9]*`. -/
def isBib (s : String) : Bool :=
  match cutDash s.toList with
  | some (p, 'B' :: 'I' :: 'B' :: n) => Zone.isIdent (String.ofList p) && posDigits n
  | _ => false

/-- `[0-9a-f]`. -/
def lowHex (c : Char) : Bool := digitC c || ('a' ≤ c && c ≤ 'f')

/-- v1's `_HEX64`: 64 lowercase hexadecimal characters. -/
def isHex64 (s : String) : Bool := s.length == 64 && s.all lowHex

/-- Runs of lowercase hexadecimal of the given lengths, joined by `-`. -/
def hexRuns (cs : List Char) (lens : List Nat) : Bool :=
  let parts := (cs.splitOn '-')
  parts.length == lens.length && (parts.zip lens).all fun (p, n) => p.length == n && p.all lowHex

/-- v1's `_UUID4`: `[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}`. -/
def isUuid4 (s : String) : Bool :=
  let cs := s.toList
  hexRuns cs [8, 4, 4, 4, 12] && cs[14]? == some '4' &&
    (match cs[19]? with
     | some c => c == '8' || c == '9' || c == 'a' || c == 'b'
     | none => false)

/-- `0|[1-9][0-9]{0,3}`. -/
def versionPart (p : List Char) : Bool := p == ['0'] || (posDigits p && p.length ≤ 4)

/-- v1's `_VERSION`: `n.n.n`, each `0` or one to four digits without a leading zero. -/
def isVersion (s : String) : Bool :=
  match s.toList.splitOn '.' with
  | [a, b, c] => versionPart a && versionPart b && versionPart c
  | _ => false

/-- The value of ASCII digits. -/
def digitsNat (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- v1's `_date_ok`: a calendar date of the proleptic Gregorian calendar. -/
def dateOk (y mo d : Nat) : Bool :=
  let leap := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
  let days := [31, if leap then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
  1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ days.getD (mo - 1) 0

/-- `[0-9]{n}` at the head: the digits and the rest. -/
def takeDigits (n : Nat) (cs : List Char) : Option (List Char × List Char) :=
  if (cs.take n).length == n && (cs.take n).all digitC then some (cs.take n, cs.drop n) else none

/-- v1's `_DATE` read at the head of `cs`: `YYYY-MM-DD`, the rest after it. -/
def readDate (cs : List Char) : Option ((Nat × Nat × Nat) × List Char) := do
  let (y, r) ← takeDigits 4 cs
  let r ← match r with | '-' :: r => some r | _ => none
  let (mo, r) ← takeDigits 2 r
  let r ← match r with | '-' :: r => some r | _ => none
  let (d, r) ← takeDigits 2 r
  pure ((digitsNat y, digitsNat mo, digitsNat d), r)

/-- v1's `_day_ok`: a date `YYYY-MM-DD` of the calendar. -/
def dayOk (s : String) : Bool :=
  match readDate s.toList with
  | some ((y, mo, d), []) => dateOk y mo d
  | _ => false

/-- v1's `_utc_ok`: `YYYY-MM-DDTHH:MM:SSZ`, a date of the calendar and a time of the day. -/
def utcOk (s : String) : Bool :=
  match readDate s.toList with
  | some ((y, mo, d), 'T' :: r) =>
    match takeDigits 2 r with
    | some (h, ':' :: r) =>
      match takeDigits 2 r with
      | some (mi, ':' :: r) =>
        match takeDigits 2 r with
        | some (se, ['Z']) =>
          dateOk y mo d && digitsNat h ≤ 23 && digitsNat mi ≤ 59 && digitsNat se ≤ 59
        | _ => false
      | _ => false
    | _ => false
  | _ => false

/-- `<word> YYYY-MM-DD BY <rest>`: the date's text and the rest (one or more code points). -/
def readStateLine (word : String) (s : String) : Option (String × String) :=
  let cs := s.toList
  let w := (word ++ " ").toList
  if w.isPrefixOf cs then
    let r := cs.drop w.length
    match readDate r with
    | some (_, ' ' :: 'B' :: 'Y' :: ' ' :: rest) =>
      if rest.isEmpty then none else some (String.ofList (r.take 10), String.ofList rest)
    | _ => none
  else none

/-- v1's `_stateline_ok`: `OPEN`, `SETTLED <date> BY <ids>` (each a record identifier,
joined by `, `) or `STANDING <date> BY <text>` (not blank). -/
def statelineOk (s : String) : Bool :=
  if s == "OPEN" then true
  else
    match readStateLine "SETTLED" s with
    | some (d, ids) => dayOk d && (Table.split ids ", ").all isRid
    | none =>
      match readStateLine "STANDING" s with
      | some (d, t) => dayOk d && !Zone.blank t
      | none => false

/-- v1's `_EOM`: `EOM(<identifier>)`, its identifier. -/
def eomName? (s : String) : Option String :=
  let cs := s.toList
  if "EOM(".toList.isPrefixOf cs && cs.getLast? == some ')' then
    let n := String.ofList ((cs.drop 4).dropLast)
    if Zone.isIdent n then some n else none
  else none

end Principia.Record
