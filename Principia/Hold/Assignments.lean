import Principia.CanonicalReader
import Principia.Record.Answer
import Principia.Zone.Text

/-!
# The assignment block's reader

The block `pma-assignments` on a UWC's collaboration page: written by the Holder by its own
edit, read by Custos through this reader before a RETURN. Its text is a
JSON list of rows, one per assigned block, each an object of exactly six members
(the Custos operations note, section 4.4; version 1's ASSIGNMENT row, TPS 5.8.3):

* `block`: the work block's name, in the lock's form (a letter or digit, then at most 63
  letters, digits, `_`, `.`, `:` or `-`);
* `assignee`: the Coworker's account, in the lock's account form (`PageTexts::isAccount`);
* `grant`: the Holder's grant number at assignment, an integer of at least 0;
* `kind`: the block kind (REPRODUCTION, EOM-0 among them), an upper-case word: a capital
  letter or digit, then at most 63 capitals, digits, `_` or `-`;
* `ends`: the end time, in the record's time form `YYYY-MM-DDTHH:MM:SSZ` (`Record.utcOk`);
* `range`: the identifiers leased for the block, `null` for none, else an object of exactly
  `prefix` (an identifier), `low`, `high` and `next` (integers, `0 ≤ low ≤ next ≤ high + 1`).

The reader answers each row's account, block name, kind and end time, marked `LIVE` or
`EXPIRED` against the server time: a row is EXPIRED when the server time passes its end time
(TPS 5.8.5), so a row ending at the server time is live. The reader never guesses: a block it
cannot read is refused whole, with one word and the index (from 0) of the first bad row:

* `MALFORMED`: the text is not one JSON list (index `none`), or a row is not an object of the
  six members in their forms;
* `TIME`: a row's end time is not in the record's time form;
* `HOLDER`: a row assigns a block to the Holder's own account;
* `DUPLICATE`: a row names a block an earlier row names.

A row's faults are judged in that order. `blocks_nodup` proves that an accepted block's names
are pairwise distinct.
-/

namespace Principia.Hold.Assignments

open Principia.Canonical (Value readString)

/-! ## The forms -/

/-- A work block's name, the lock's form: `[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}`. -/
def blockOk (s : String) : Bool :=
  let alnum (c : Char) := c.isAlphanum
  match s.toList with
  | c :: cs => alnum c && cs.length ≤ 63 && cs.all fun d => alnum d || "_.:-".contains d
  | [] => false

/-- A block kind: `[A-Z0-9][A-Z0-9_-]{0,63}`. -/
def kindOk (s : String) : Bool :=
  let word (c : Char) := c.isUpper || c.isDigit
  match s.toList with
  | c :: cs => word c && cs.length ≤ 63 && cs.all fun d => word d || d == '_' || d == '-'
  | [] => false

/-- A code point the lock's account form refuses: a control character, one of
`# < > [ ] | { } / _`, or a space MediaWiki does not take in a user name. -/
def accountBanned (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) || "#<>[]|{}/_".contains c || n == 0xA0 ||
    n == 0x1680 || n == 0x180E || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0x200E || n == 0x200F ||
    (0x202A ≤ n && n ≤ 0x202E) || n == 0xFFFD

/-- Whether a list of code points holds two spaces in a row. -/
def doubleSpace : List Char → Bool
  | ' ' :: ' ' :: _ => true
  | _ :: cs => doubleSpace cs
  | [] => false

/-- An account name in the lock's form (`PageTexts::isAccount`): at least one code point and at
most 255 UTF-8 bytes, no space at either end, no two spaces in a row, no banned code point. -/
def accountOk (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && s.utf8ByteSize ≤ 255 && cs.head? != some ' ' && cs.getLast? != some ' ' &&
    !doubleSpace cs && cs.all fun c => !accountBanned c

/-- A time in the record's form `YYYY-MM-DDTHH:MM:SSZ`, a real date and time of day. -/
def timeOk (s : String) : Bool := Principia.Record.utcOk s

/-- Whether the server time `now` has passed the end time `ends`: both in the record's time
form, whose fixed width makes their order as text their order in time. -/
def passed (now ends : String) : Bool := decide (ends < now)

/-! ## A row -/

/-- The refusal words. -/
inductive Word where
  | malformed
  | time
  | holder
  | duplicate
  deriving DecidableEq, Repr

/-- A word's text. -/
def Word.text : Word → String
  | .malformed => "MALFORMED"
  | .time => "TIME"
  | .holder => "HOLDER"
  | .duplicate => "DUPLICATE"

/-- Why the block is refused: the word and the first bad row's index (`none`: no row is at
fault, the text is not one JSON list). -/
structure Fault where
  word : Word
  index : Option Nat
  deriving DecidableEq, Repr

/-- A row the reader answers. -/
structure Row where
  account : String
  block : String
  kind : String
  ends : String
  expired : Bool
  deriving DecidableEq, Repr

/-- The six members of a row. -/
def members : List String := ["assignee", "block", "ends", "grant", "kind", "range"]

/-- An object of exactly the members `names`. -/
def exactly (names : List String) (ms : List (String × Value)) : Bool :=
  ms.length == names.length && names.all fun n => (ms.lookup n).isSome

/-- A leased range: `null`, or `{"prefix", "low", "high", "next"}` in their forms. -/
def rangeOk : Value → Bool
  | .null => true
  | .obj ms =>
    exactly ["high", "low", "next", "prefix"] ms &&
    match ms.lookup "prefix", ms.lookup "low", ms.lookup "high", ms.lookup "next" with
    | some (.str p), some (.int lo), some (.int hi), some (.int nx) =>
      Principia.Zone.isIdent p && 0 ≤ lo && lo ≤ nx && nx ≤ hi + 1
    | _, _, _, _ => false
  | _ => false

/-- A grant number: an integer of at least 0. -/
def grantOk : Value → Bool
  | .int n => 0 ≤ n
  | _ => false

/-- Row `i` read, against the Holder and the server time. -/
def readRow (holder now : String) (i : Nat) : Value → Except Fault Row
  | .obj ms =>
    if !exactly members ms then .error ⟨.malformed, some i⟩ else
    match ms.lookup "block", ms.lookup "assignee", ms.lookup "kind", ms.lookup "ends" with
    | some (.str b), some (.str a), some (.str k), some e =>
      if !(blockOk b && accountOk a && kindOk k && grantOk ((ms.lookup "grant").getD .null) &&
          rangeOk ((ms.lookup "range").getD (.str ""))) then .error ⟨.malformed, some i⟩
      else match e with
        | .str t =>
          if !timeOk t then .error ⟨.time, some i⟩
          else if a == holder then .error ⟨.holder, some i⟩
          else .ok { account := a, block := b, kind := k, ends := t, expired := passed now t }
        | _ => .error ⟨.time, some i⟩
    | _, _, _, _ => .error ⟨.malformed, some i⟩
  | _ => .error ⟨.malformed, some i⟩

/-! ## The block -/

/-- The rows from index `i` on, `seen` the block names of the rows before. -/
def scan (holder now : String) : Nat → List String → List Value → Except Fault (List Row)
  | _, _, [] => .ok []
  | i, seen, v :: vs =>
    match readRow holder now i v with
    | .error f => .error f
    | .ok r =>
      if seen.contains r.block then .error ⟨.duplicate, some i⟩
      else match scan holder now (i + 1) (r.block :: seen) vs with
        | .error f => .error f
        | .ok rs => .ok (r :: rs)

/-- The assignment block's text read: its rows, or the block refused whole. -/
def assignments (text holder now : String) : Except Fault (List Row) :=
  match readString text with
  | .ok (.arr vs) => scan holder now 0 [] vs
  | _ => .error ⟨.malformed, none⟩

/-! ## What Lean proves -/

/-- The rows `scan` accepts have block names pairwise distinct and none among `seen`. -/
theorem scan_nodup (holder now : String) :
    ∀ (vs : List Value) (i : Nat) (seen : List String) (rows : List Row),
      scan holder now i seen vs = .ok rows →
        (rows.map (·.block)).Nodup ∧ ∀ r ∈ rows, r.block ∉ seen := by
  intro vs
  induction vs with
  | nil =>
    intro i seen rows h
    simp only [scan, Except.ok.injEq] at h
    subst h
    simp
  | cons v vs ih =>
    intro i seen rows h
    simp only [scan] at h
    split at h
    · cases h
    · rename_i r _
      split at h
      · cases h
      · rename_i hnot
        split at h
        · cases h
        · rename_i rs hrs
          simp only [Except.ok.injEq] at h
          subst h
          have ⟨hnd, hout⟩ := ih (i + 1) (r.block :: seen) rs hrs
          have hr : r.block ∉ seen := by simpa using hnot
          refine ⟨?_, ?_⟩
          · simp only [List.map_cons, List.nodup_cons]
            refine ⟨?_, hnd⟩
            intro hm
            obtain ⟨q, hq, hqb⟩ := List.mem_map.mp hm
            exact hout q hq (by simp [hqb])
          · intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hr
            · intro hs
              exact hout q hq (List.mem_cons_of_mem _ hs)

/-- A block the reader accepts has pairwise distinct block names. -/
theorem blocks_nodup {text holder now : String} {rows : List Row}
    (h : assignments text holder now = .ok rows) : (rows.map (·.block)).Nodup := by
  unfold assignments at h
  split at h
  · exact (scan_nodup holder now _ 0 [] rows h).1
  · cases h

/-- No row the reader accepts is assigned to the Holder. -/
theorem readRow_not_holder {holder now : String} {i : Nat} {v : Value} {r : Row}
    (h : readRow holder now i v = .ok r) : r.account ≠ holder := by
  unfold readRow at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i a _ _ _ _ _ _ _
        split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h
              · rename_i hne
                simp only [Except.ok.injEq] at h
                subst h
                simpa using hne
          · cases h
      · cases h
  · cases h

/-- A row ending at the server time is live: it is EXPIRED only once the time passes. -/
theorem passed_self (t : String) : passed t t = false := by
  simp [passed]

end Principia.Hold.Assignments
