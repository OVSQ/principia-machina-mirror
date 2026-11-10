import Principia.Canonical
import Principia.Wire

/-!
# Reading JSON text

The Calculator's reader of a request: one JSON text (RFC 8259) to one `Value`, written
by hand, so that nothing that reaches an output passes through `Lean.Json` (collision
register R5: it sorts object keys and keeps one of two members with one key).

* **Text.** UTF-8, at most `maxTextBytes` bytes; a byte order mark is not white space
  and is refused. White space is space, tab, line feed and carriage return.
* **Numbers.** The RFC's grammar, read as `readNumber?` reads a literal: without a
  fraction or an exponent an integer, otherwise an exact decimal; nothing is rounded.
  At most `maxNumberDigits` digits before the exponent and `maxExponentDigits` in it
  (v1's DECIMAL grammar bound), checked before any digit is converted, so that no
  number costs more to read or to write than its bounded size allows; a non-integer
  that v1 would have read as an infinite double is refused. Integers stay integers at
  any value within the digit bound; a number that would underflow stays exact.
* **Strings.** The eight short escapes and `\uXXXX` (hexadecimal in either case); a
  surrogate pair is joined into one character, and a lone surrogate is refused, as is
  a raw character below U+0020. No normalization (NFC waits on the Declarer's choice of normalization).
* **Arrays and objects.** At most `maxDepth` levels of nesting. Members keep their
  order; an object holding a key twice is refused, keys compared code point by code
  point.

Every refusal is a distinct `ReadError`, with the place it was found, counted in
characters (code points) from the start of the text.
-/

namespace Principia.Canonical

/-! ## Equality of values

Member order counts: two objects with one set of members in two orders are two
values (their canonical JSON is one text). -/

mutual
/-- Structural equality of two values. -/
def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr xs, .arr ys => Value.beqList xs ys
  | .obj ms, .obj ns => Value.beqMembers ms ns
  | _, _ => false

/-- Structural equality of two lists of values. -/
def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.beq x y && Value.beqList xs ys
  | _, _ => false

/-- Structural equality of two lists of members. -/
def Value.beqMembers : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, x) :: ms, (l, y) :: ns => k == l && Value.beq x y && Value.beqMembers ms ns
  | _, _ => false
end

instance : BEq Value := ⟨Value.beq⟩

/-! ## Bounds -/

/-- The largest text read, in bytes: 1 MiB, the size of the document test T2 sent to a
Lean binary on the wiki's host. A text at the bound reads and writes in under half a
second in about 120 MB; the bound is raised by a change of the library when a family needs more. -/
def maxTextBytes : Nat := 1048576

/-- The deepest nesting of arrays and objects read (v1 tpc_identity's bound). -/
def maxDepth : Nat := 64

/-! A number's bounds are `readNumber?`'s, in `Principia.Canonical`: `maxNumberDigits`,
`maxExponentDigits`, and v1's infinite double (`Decimal.overflowsDouble`). -/

/-! ## Refusals -/

/-- Why a text is refused. -/
inductive ReadError where
  /-- The bytes are not UTF-8. -/
  | notUtf8
  /-- The text is longer than `maxTextBytes`. -/
  | tooLarge
  /-- The text holds no value: it is empty or white space. -/
  | noValue
  /-- Something other than white space follows the value. -/
  | trailingText
  /-- The text ends inside a value. -/
  | unexpectedEnd
  /-- A character that cannot stand where it stands. -/
  | unexpectedCharacter
  /-- Arrays and objects nested deeper than `maxDepth`. -/
  | tooDeep
  /-- A number outside the grammar: a leading zero, a point or an exponent without
  digits, a sign alone. -/
  | badNumber
  /-- A number with more than `maxNumberDigits` digits before its exponent. -/
  | numberTooLong
  /-- An exponent with more than `maxExponentDigits` digits. -/
  | exponentTooLong
  /-- A number v1 would have read as an infinite double (`|x| ≥ 2^1024 - 2^970`). -/
  | numberTooLarge
  /-- An escape that is none of the nine. -/
  | badEscape
  /-- A `\u` escape of a surrogate that is not half of a pair. -/
  | loneSurrogate
  /-- A raw character below U+0020 inside a string. -/
  | controlCharacter
  /-- An object holding a key twice. -/
  | duplicateKey
  deriving DecidableEq, Repr, Inhabited

instance : WireWord ReadError where
  members := [.notUtf8, .tooLarge, .noValue, .trailingText, .unexpectedEnd,
    .unexpectedCharacter, .tooDeep, .badNumber, .numberTooLong, .exponentTooLong,
    .numberTooLarge, .badEscape, .loneSurrogate, .controlCharacter, .duplicateKey]
  toWire
    | .notUtf8 => "NOT_UTF8"
    | .tooLarge => "TOO_LARGE"
    | .noValue => "NO_VALUE"
    | .trailingText => "TRAILING_TEXT"
    | .unexpectedEnd => "UNEXPECTED_END"
    | .unexpectedCharacter => "UNEXPECTED_CHARACTER"
    | .tooDeep => "TOO_DEEP"
    | .badNumber => "BAD_NUMBER"
    | .numberTooLong => "NUMBER_TOO_LONG"
    | .exponentTooLong => "EXPONENT_TOO_LONG"
    | .numberTooLarge => "NUMBER_TOO_LARGE"
    | .badEscape => "BAD_ESCAPE"
    | .loneSurrogate => "LONE_SURROGATE"
    | .controlCharacter => "CONTROL_CHARACTER"
    | .duplicateKey => "DUPLICATE_KEY"
  read_toWire a := by cases a <;> decide

/-- A refused text: why, and where, as the number of characters before the place;
`none` for a refusal of the bytes as a whole. -/
structure ReadFailure where
  error : ReadError
  position : Option Nat
  deriving DecidableEq, Repr

/-- Inside the reader a failure carries the number of characters left unread, which
`readString` turns into a position. -/
abbrev Failed := ReadError × Nat

/-- A step of the reader: what it read and the characters after it. -/
abbrev Step (α : Type) := Except Failed (α × List Char)

/-- Refuse at the place where `rest` begins. -/
def failAt {α : Type} (e : ReadError) (rest : List Char) : Except Failed α :=
  .error (e, rest.length)

/-! ## The pieces -/

/-- The text after any white space. -/
def skipSpace : List Char → List Char
  | ' ' :: cs => skipSpace cs
  | '\t' :: cs => skipSpace cs
  | '\n' :: cs => skipSpace cs
  | '\r' :: cs => skipSpace cs
  | cs => cs

/-- `true`, `false` or `null`, its first character already seen. -/
def readLiteral (v : Value) : List Char → List Char → Step Value
  | [], cs => .ok (v, cs)
  | _ :: _, [] => failAt .unexpectedEnd []
  | w :: ws, c :: cs => if c = w then readLiteral v ws cs else failAt .unexpectedCharacter (c :: cs)

/-- A run of digits is wanted at `cs`: refuse it as the text's end or as a bad number. -/
def wantDigit {α : Type} (cs : List Char) : Except Failed α :=
  if cs.isEmpty then failAt .unexpectedEnd cs else failAt .badNumber cs

/-- A number (RFC 8259 section 6), from its first character, `-` or a digit. -/
def readNumberText (cs : List Char) : Step Value :=
  let (neg, afterSign) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let ip := afterSign.takeWhile Char.isDigit
  let afterInt := afterSign.drop ip.length
  if ip.isEmpty then wantDigit afterInt
  else if ip.head? = some '0' ∧ 1 < ip.length then failAt .badNumber (afterSign.drop 1)
  else
    let fracStep : Except Failed (Option (List Char) × List Char) :=
      match afterInt with
      | '.' :: r =>
        let fd := r.takeWhile Char.isDigit
        if fd.isEmpty then wantDigit r else .ok (some fd, r.drop fd.length)
      | r => .ok (none, r)
    match fracStep with
    | .error f => .error f
    | .ok (frac, afterFrac) =>
      let fd := frac.getD []
      let expStep : Except Failed (Option (Bool × List Char) × List Char) :=
        match afterFrac with
        | c :: r =>
          if c = 'e' ∨ c = 'E' then
            let (eneg, r') := match r with
              | '-' :: r'' => (true, r'')
              | '+' :: r'' => (false, r'')
              | r'' => (false, r'')
            let ed := r'.takeWhile Char.isDigit
            if ed.isEmpty then wantDigit r'
            else if maxExponentDigits < ed.length then failAt .exponentTooLong r'
            else .ok (some (eneg, ed), r'.drop ed.length)
          else .ok (none, c :: r)
        | [] => .ok (none, [])
      match expStep with
      | .error f => .error f
      | .ok (expo, rest) =>
        if maxNumberDigits < ip.length + fd.length then failAt .numberTooLong cs
        else
          let mag : Int := digitsValue (ip ++ fd)
          let m := if neg then -mag else mag
          match frac, expo with
          | none, none => .ok (.int m, rest)
          | _, _ =>
            let e : Int := match expo with
              | some (eneg, ed) => if eneg then -(digitsValue ed : Int) else digitsValue ed
              | none => 0
            let x : Decimal := ⟨m, e - fd.length⟩
            if x.overflowsDouble then failAt .numberTooLarge cs else .ok (.num x, rest)

/-- The value of a hexadecimal digit, either case. -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits as a number. -/
def hex4 (a b c d : Char) : Option Nat := do
  let a ← hexValue a
  let b ← hexValue b
  let c ← hexValue c
  let d ← hexValue d
  pure (((a * 16 + b) * 16 + c) * 16 + d)

/-- After `\u` and fewer than four further characters: the end of the text if they
are all hexadecimal, else a bad escape. -/
def shortUnicode {α : Type} (escape rest : List Char) : Except Failed α :=
  if rest.all fun c => (hexValue c).isSome then failAt .unexpectedEnd [] else failAt .badEscape escape

/-- A string's characters after its opening quotation mark, up to and past its closing
one; `acc` holds the characters read so far, last first. -/
def readStringBody : List Char → List Char → Step String
  | [], _ => failAt .unexpectedEnd []
  | c :: rest, acc =>
    if c = '"' then .ok (String.ofList acc.reverse, rest)
    else if c = '\\' then
      match rest with
      | '"' :: r => readStringBody r ('"' :: acc)
      | '\\' :: r => readStringBody r ('\\' :: acc)
      | '/' :: r => readStringBody r ('/' :: acc)
      | 'b' :: r => readStringBody r ('\x08' :: acc)
      | 'f' :: r => readStringBody r ('\x0c' :: acc)
      | 'n' :: r => readStringBody r ('\n' :: acc)
      | 'r' :: r => readStringBody r ('\r' :: acc)
      | 't' :: r => readStringBody r ('\t' :: acc)
      | 'u' :: a :: b :: c' :: d :: r =>
        match hex4 a b c' d with
        | none => failAt .badEscape (c :: rest)
        | some n =>
          if n < 0xD800 ∨ 0xDFFF < n then readStringBody r (Char.ofNat n :: acc)
          else if 0xDBFF < n then failAt .loneSurrogate (c :: rest)
          else
            match r with
            | '\\' :: 'u' :: a' :: b' :: c'' :: d' :: r' =>
              match hex4 a' b' c'' d' with
              | some m =>
                if 0xDC00 ≤ m ∧ m ≤ 0xDFFF then
                  readStringBody r' (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)) :: acc)
                else failAt .loneSurrogate (c :: rest)
              | none => failAt .loneSurrogate (c :: rest)
            | _ => failAt .loneSurrogate (c :: rest)
      | 'u' :: r => shortUnicode (c :: rest) r
      | [] => failAt .unexpectedEnd []
      | _ :: _ => failAt .badEscape (c :: rest)
    else if c.toNat < 0x20 then failAt .controlCharacter (c :: rest)
    else readStringBody rest (c :: acc)

/-- The earlier of two candidate repetitions, by their member index. -/
def earlierRepeat (a : Option ((String × List Char) × Nat)) (b : (String × List Char) × Nat) :
    Option ((String × List Char) × Nat) :=
  match a with
  | some x => if x.2 ≤ b.2 then some x else some b
  | none => some b

/-- Over keys sorted stably, adjacent equal keys: the later of each pair is a repetition;
the one earliest in the text wins. -/
def firstRepeat : List ((String × List Char) × Nat) → Option ((String × List Char) × Nat) →
    Option ((String × List Char) × Nat)
  | a :: b :: rest, best =>
    firstRepeat (b :: rest) (if a.1.1 = b.1.1 then earlierRepeat best b else best)
  | _, best => best

/-- Where a key repeats an earlier one: the text from the earliest repeated key on, or
`none` when the keys are distinct. Keys come in text order, each with the text from
where it begins; sorting them (`O(n log n)`) finds the repetitions. -/
def repeatedKey (keys : List (String × List Char)) : Option (List Char) :=
  let sorted := keys.zipIdx.mergeSort fun a b => decide (a.1.1 ≤ b.1.1)
  (firstRepeat sorted none).map fun x => x.1.2

/-! ## Values

`readValue`, `readElements` and `readMembers` run on fuel, one unit per call, so that
they are structurally recursive and the kernel evaluates them. Every call reads at
least one character before the next three calls, so `4 * (n + 2)` units for a text of
`n` characters are never used up; the refusal on empty fuel cannot occur. -/

mutual
/-- A value, after any white space. `depth` counts the arrays and objects open. -/
def readValue : Nat → Nat → List Char → Step Value
  | 0, _, cs => failAt .unexpectedEnd cs
  | fuel + 1, depth, cs =>
    match skipSpace cs with
    | [] => failAt .unexpectedEnd []
    | c :: rest =>
      if c = '{' then
        if maxDepth ≤ depth then failAt .tooDeep (c :: rest)
        else
          match skipSpace rest with
          | '}' :: r => .ok (.obj [], r)
          | r => readMembers fuel (depth + 1) r []
      else if c = '[' then
        if maxDepth ≤ depth then failAt .tooDeep (c :: rest)
        else
          match skipSpace rest with
          | ']' :: r => .ok (.arr [], r)
          | r => readElements fuel (depth + 1) r []
      else if c = '"' then
        match readStringBody rest [] with
        | .ok (s, r) => .ok (.str s, r)
        | .error f => .error f
      else if c = 't' then readLiteral (.bool true) ['r', 'u', 'e'] rest
      else if c = 'f' then readLiteral (.bool false) ['a', 'l', 's', 'e'] rest
      else if c = 'n' then readLiteral .null ['u', 'l', 'l'] rest
      else if c = '-' ∨ c.isDigit then readNumberText (c :: rest)
      else failAt .unexpectedCharacter (c :: rest)

/-- An array's elements after `[`, the first not yet read; `acc` last first. -/
def readElements : Nat → Nat → List Char → List Value → Step Value
  | 0, _, cs, _ => failAt .unexpectedEnd cs
  | fuel + 1, depth, cs, acc =>
    match readValue fuel depth cs with
    | .error f => .error f
    | .ok (v, rest) =>
      match skipSpace rest with
      | ',' :: r => readElements fuel depth r (v :: acc)
      | ']' :: r => .ok (.arr (v :: acc).reverse, r)
      | [] => failAt .unexpectedEnd []
      | r => failAt .unexpectedCharacter r

/-- An object's members after `{`, the first not yet read; `acc` last first, each
member with the text from where its key begins. -/
def readMembers : Nat → Nat → List Char → List ((String × Value) × List Char) → Step Value
  | 0, _, cs, _ => failAt .unexpectedEnd cs
  | fuel + 1, depth, cs, acc =>
    match skipSpace cs with
    | [] => failAt .unexpectedEnd []
    | '"' :: rest =>
      match readStringBody rest [] with
      | .error f => .error f
      | .ok (k, afterKey) =>
        match skipSpace afterKey with
        | ':' :: r =>
          match readValue fuel depth r with
          | .error f => .error f
          | .ok (v, rest') =>
            let acc := ((k, v), '"' :: rest) :: acc
            match skipSpace rest' with
            | ',' :: r' => readMembers fuel depth r' acc
            | '}' :: r' =>
              let ms := acc.reverse
              match repeatedKey (ms.map fun m => (m.1.1, m.2)) with
              | some keyText => failAt .duplicateKey keyText
              | none => .ok (.obj (ms.map Prod.fst), r')
            | [] => failAt .unexpectedEnd []
            | r' => failAt .unexpectedCharacter r'
        | [] => failAt .unexpectedEnd []
        | r => failAt .unexpectedCharacter r
    | r => failAt .unexpectedCharacter r
end

/-- The one value of a text's characters, white space allowed around it. -/
def readChars (cs : List Char) : Except Failed Value :=
  match skipSpace cs with
  | [] => failAt .noValue []
  | start =>
    match readValue (4 * (cs.length + 2)) 0 start with
    | .error f => .error f
    | .ok (v, rest) =>
      match skipSpace rest with
      | [] => .ok v
      | r => failAt .trailingText r

/-- Read a text already decoded: its one value, or why not and where. -/
def readString (s : String) : Except ReadFailure Value :=
  let cs := s.toList
  match readChars cs with
  | .ok v => .ok v
  | .error (e, left) => .error ⟨e, some (cs.length - left)⟩

/-- Read a request's bytes: UTF-8, at most `maxTextBytes`, one JSON value. -/
def readText (bytes : ByteArray) : Except ReadFailure Value :=
  if maxTextBytes < bytes.size then .error ⟨.tooLarge, none⟩
  else
    match String.fromUTF8? bytes with
    | none => .error ⟨.notUtf8, none⟩
    | some s => readString s

/-! ## What the kernel checks about the reader -/

/-- A text over the bound is refused whole, before it is decoded. -/
theorem readText_tooLarge {bytes : ByteArray} (h : maxTextBytes < bytes.size) :
    readText bytes = .error ⟨.tooLarge, none⟩ := by
  simp [readText, h]

/-- Bytes that are not UTF-8 are refused whole. -/
theorem readText_notUtf8 {bytes : ByteArray} (h : bytes.size ≤ maxTextBytes)
    (hu : String.fromUTF8? bytes = none) : readText bytes = .error ⟨.notUtf8, none⟩ := by
  simp [readText, Nat.not_lt.mpr h, hu]

/-- Each hexadecimal digit canonical JSON writes reads back as its value. -/
theorem hexValue_hexDigit : ∀ k < 16, hexValue (hexDigit k) = some k := by decide

/-- What `escapeChar` writes, followed by more of a string, reads back as the
character. -/
theorem readStringBody_escapeChar (c : Char) (rest acc : List Char) :
    readStringBody (escapeChar c ++ rest) acc = readStringBody rest (c :: acc) := by
  unfold escapeChar
  by_cases hq : c = '"'
  · subst hq; simp [readStringBody]
  by_cases hb : c = '\\'
  · subst hb; simp [readStringBody]
  by_cases hc : c.toNat < 0x20
  · have h1 := hexValue_hexDigit (c.toNat / 16) (by omega)
    have h2 := hexValue_hexDigit (c.toNat % 16) (Nat.mod_lt _ (by decide))
    have h0 : hexValue '0' = some 0 := by decide
    have hn : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by omega
    have hlt : c.toNat < 55296 := by omega
    simp [hq, hb, hc, readStringBody, hex4, h0, h1, h2]
    simp [hn, hlt, Char.ofNat_toNat]
  · simp only [hq, hb, hc, ite_false, List.singleton_append]
    rw [readStringBody.eq_def]
    simp [hq, hb, hc]

/-- An escaped string body, closed by its quotation mark, reads back as its characters. -/
theorem readStringBody_quoted (cs tail acc : List Char) :
    readStringBody (cs.flatMap escapeChar ++ '"' :: tail) acc =
      .ok (String.ofList (acc.reverse ++ cs), tail) := by
  induction cs generalizing acc with
  | nil =>
    rw [List.flatMap_nil, List.nil_append, readStringBody.eq_def]
    simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc, readStringBody_escapeChar, ih]
    simp

theorem skipSpace_quote (cs : List Char) : skipSpace ('"' :: cs) = '"' :: cs := by
  rw [skipSpace.eq_def]
  split <;> simp_all

/-- Reading a string's canonical JSON gives the string back: every string survives the
writer and the reader (a part of SC5's serialization round trip). -/
theorem readString_quote (s : String) : readString (quote s) = .ok (.str s) := by
  have hfuel : ∀ n : Nat, 4 * (n + 2) = (4 * n + 7) + 1 := by intro n; omega
  simp only [readString, readChars, quote, String.toList_ofList, List.cons_append,
    skipSpace_quote, hfuel, readValue]
  simp [readStringBody_quoted, skipSpace]

end Principia.Canonical
