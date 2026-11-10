import Principia.Unicode

/-!
# Zone text: the rules every string of a zone meets

v1's `tpc_zone` text safety (tpm_zone_schemas 0.2.0, section 6): a string is
refused if, after line-ending normalization, it holds a code point of Unicode
general category C (control, format, surrogate, private use, unassigned) other
than TAB and LF, or U+2028 or U+2029; a problem message shows each such code point
as `<U+XXXX>`. Also here: v1's `_eol`, `_text`, `_first_bad`, `_show`, `_blank` and
`_is_ident`.

The general category and NFC are Unicode 15.1.0's, the version of v1's `unicodedata`,
read from `Principia.Unicode`:
`disallowed` is v1's `_disallowed` over `Unicode.generalCategory` (`disallowed_iff`), and
`text` is v1's `_text`, line endings as LF and then `Unicode.nfc` (`textChars_eq`).
-/

namespace Principia.Zone

/-- v1's `_disallowed`: general category C except TAB and LF, plus U+2028 and U+2029. -/
def disallowed (c : Char) : Bool :=
  if c == '\t' || c == '\n' then false
  else if c.toNat == 0x2028 || c.toNat == 0x2029 then true
  else (Unicode.generalCategory c).major == 'C'

/-- v1's `_eol`: CRLF and a lone CR become LF, as MediaWiki stores text. -/
def eolChars : List Char → List Char
  | '\r' :: '\n' :: cs => '\n' :: eolChars cs
  | '\r' :: cs => '\n' :: eolChars cs
  | c :: cs => c :: eolChars cs
  | [] => []

/-- v1's `_text` as code points: line endings as LF (`_eol`), then NFC. Text below U+00C0,
ASCII among it, is its own NFC (`Unicode.nfcList_of_lt`) and is returned as it stands;
`textChars_eq` states that the result is NFC's in every case. -/
def textChars (s : String) : List Char :=
  let cs := eolChars s.toList
  if cs.all (·.toNat < 0xC0) then cs else Unicode.nfcList cs

/-- v1's `_text`: the canonical text of a string, line endings as LF, then NFC. -/
def text (s : String) : String := String.ofList (textChars s)

/-- Upper-case hexadecimal, at least four digits (`"%04X"`). -/
def hex4 (n : Nat) : String :=
  let ds := (Nat.toDigits 16 n).map Char.toUpper
  String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

/-- `U+XXXX`. -/
def codePoint (c : Char) : String := "U+" ++ hex4 c.toNat

/-- v1's `_first_bad`: the first disallowed code point after line-ending
normalization, as `U+XXXX`. -/
def firstBad (s : String) : Option String :=
  ((eolChars s.toList).find? disallowed).map codePoint

/-- v1's `_show`: a problem message with every disallowed code point escaped. -/
def escape (msg : String) : String :=
  String.join (msg.toList.map fun c => if disallowed c then "<" ++ codePoint c ++ ">" else c.toString)

/-- Unicode White_Space (the Unicode Character Database's property list), as v1 lists it so both residences agree. -/
def whiteSpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F ||
    n == 0x3000

/-- v1's `_blank`: empty, or every code point White_Space. -/
def blank (s : String) : Bool := s.toList.all whiteSpace

/-- An ASCII letter or `_`. -/
def identStart (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

/-- v1's `_is_ident`: `[A-Za-z_][A-Za-z0-9_]*`, ASCII only. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => identStart c && cs.all fun d => identStart d || ('0' ≤ d && d ≤ '9')
  | [] => false

/-! ## What Lean proves -/

/-- v1's `_disallowed`, stated: a code point is refused exactly when it is neither TAB nor
LF and is U+2028, U+2029 or of a general category C (Cc, Cf, Cs, Co, Cn) at Unicode
15.1.0. -/
theorem disallowed_iff (c : Char) :
    disallowed c = true ↔ c ≠ '\t' ∧ c ≠ '\n' ∧
      (c.toNat = 0x2028 ∨ c.toNat = 0x2029 ∨ (Unicode.generalCategory c).major = 'C') := by
  unfold disallowed
  by_cases ht : c = '\t'
  · simp [ht]
  by_cases hn : c = '\n'
  · simp [hn]
  by_cases hs : c.toNat = 0x2028 ∨ c.toNat = 0x2029
  · rcases hs with hs | hs <;> simp [ht, hn, hs]
  · simp only [not_or] at hs
    simp [ht, hn, hs.1, hs.2]

/-- TAB and LF are never refused, whatever their category (Cc). -/
theorem disallowed_tab_lf : disallowed '\t' = false ∧ disallowed '\n' = false := by
  simp [disallowed]

/-- `_text` is line endings as LF, then NFC, on every string. -/
theorem textChars_eq (s : String) : textChars s = Unicode.nfcList (eolChars s.toList) := by
  simp only [textChars]
  split
  · rename_i h
    exact (Unicode.nfcList_of_lt (by simpa using h)).symm
  · rfl

/-- `_text` is NFC of the text with its line endings as LF. -/
theorem text_eq (s : String) : text s = Unicode.nfc (String.ofList (eolChars s.toList)) := by
  rw [text, textChars_eq, Unicode.nfc, String.toList_ofList]

end Principia.Zone
