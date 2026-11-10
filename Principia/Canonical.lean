import Principia.Exact

/-!
# Canonical serialization

v1's byte-identity contract (tpc_strike `canon` and `_canon_float`; tpm_record_schema
0.3.1 section 11.4, TPM's canonical JSON, as tpc_record `cj` and tpc_strike `_ccj`
write it), ported by hand: `Lean.Json` reads inputs only and sorts object keys
(collision register R5), so no text here passes through it.

* **The twelve-digit form** of a number (v1 `_canon_float`): C's `printf("%.12g")`,
  one rounding to twelve significant digits, ties to even; fixed notation for decimal
  exponents -4 to 11, otherwise exponent notation with a sign and at least two digits;
  trailing zeros removed; zero, of either sign, written `0`.
* **canon** (v1 `canon`): a result's text. A boolean `true` or `false`, an integer in
  base 10, a number in the twelve-digit form, a string as itself, a list as
  `[e1,e2,...]`; null and objects are refused.
* **Canonical JSON** (11.4): object keys sorted in code point order at every level;
  separators `,` and `:` with no white space; strings quoted with only `"` and `\`
  escaped and U+0000 to U+001F written `\u00XX` (lowercase hexadecimal); `/` and every
  other character, non-ASCII included, written as itself; integers in base 10; a
  number in the twelve-digit form; no final line feed. An object holding a key twice is
  refused: its text would depend on the order of its members.

v1 computed with IEEE doubles: a number was first rounded to the nearest double and
then written. PMA has no floating point (the Lean rules): a number is an exact decimal
or an exact rational, rounded once, to twelve significant digits. Where v1's double and
the exact value round apart, the case is a recorded v2 divergence
(the divergence list of the canonical corpus). v1 also wrote `inf` and `-inf` for an
overflowed double; an exact number never overflows, so PMA has no such text. The
numeric primitives, the exact rounding and the `%g` layout, are the first section
below and nothing else, so a change of the number model stays local to it.
-/

namespace Principia.Canonical

/-! ## The twelve-digit form -/

/-- canon's twelve significant digits (v1's function constant; C `"%.12g"`). -/
def significantDigits : Nat := 12

/-- The decimal digits of `n`, most significant first (`[0]` for zero). -/
def digitsOf (n : Nat) : List Char := Nat.toDigits 10 n

/-- `num / den ≥ 10 ^ e`, decided exactly. -/
def atLeastPow (num den : Nat) (e : Int) : Bool :=
  if 0 ≤ e then decide (den * 10 ^ e.toNat ≤ num) else decide (den ≤ num * 10 ^ (-e).toNat)

/-- `e` when `num / den ≥ 10 ^ e`, else `e - 1`. -/
def exponentBelow (num den : Nat) (e : Int) : Int :=
  if atLeastPow num den e then e else e - 1

/-- `⌊log₁₀ (num / den)⌋` for `num` and `den` positive. With `a` and `b` the digit
counts of `num` and `den`, the quotient lies in `[10^(a-b-1), 10^(a-b+1))`, so one
exact comparison with `10^(a-b)` settles it. -/
def decimalExponent (num den : Nat) : Int :=
  exponentBelow num den (((digitsOf num).length : Int) - (digitsOf den).length)

/-- `num / den` times `10 ^ k`, as a numerator and a denominator. -/
def scaleBy (num den : Nat) (k : Int) : Nat × Nat :=
  if 0 ≤ k then (num * 10 ^ k.toNat, den) else (num, den * 10 ^ (-k).toNat)

/-- The integer nearest `n / d`, ties to even (as C's `printf` rounds the exact value
it is given). -/
def roundHalfEven (n d : Nat) : Nat :=
  if d < 2 * (n % d) || (2 * (n % d) == d && n / d % 2 == 1) then n / d + 1 else n / d

/-- A rounded `p`-digit integer `m` at exponent `e`; a carry to `10 ^ p` moves to the
next exponent. -/
def carryDigits (p m : Nat) (e : Int) : Nat × Int :=
  if m == 10 ^ p then (10 ^ (p - 1), e + 1) else (m, e)

/-- `num / den` rounded to `p` significant digits when its decimal exponent is `e`. -/
def roundAt (p num den : Nat) (e : Int) : Nat × Int :=
  carryDigits p (roundHalfEven (scaleBy num den ((p : Int) - 1 - e)).1
    (scaleBy num den ((p : Int) - 1 - e)).2) e

/-- `num / den`, both positive, rounded to `p` significant digits, ties to even: the
pair `(m, e)` with `10^(p-1) ≤ m < 10^p` and `num / den ≈ m × 10^(e - p + 1)`; `e` is
the decimal exponent after rounding (a carry out of the top digit raises it). -/
def roundSignificant (p num den : Nat) : Nat × Int :=
  roundAt p num den (decimalExponent num den)

/-- A digit list without its trailing zeros. -/
def dropTrailingZeros (l : List Char) : List Char :=
  (l.reverse.dropWhile (· == '0')).reverse

/-- `"." ++ fraction`, or nothing for an empty fraction. -/
def fractionText (fp : List Char) : String :=
  if fp.isEmpty then "" else "." ++ String.ofList fp

/-- C's `%g` layout of the rounded pair `(m, e)` at precision `p` (v1 `_canon_float`
from the digits of `"%.11e"`): fixed notation when `-4 ≤ e < p`, else one digit, the
fraction and `e`, a sign and the exponent in at least two digits. -/
def gLayout (p m : Nat) (e : Int) : String :=
  let digits := digitsOf m
  if -4 ≤ e ∧ e < p then
    if 0 ≤ e then
      String.ofList (digits.take (e.toNat + 1)) ++
        fractionText (dropTrailingZeros (digits.drop (e.toNat + 1)))
    else
      "0" ++ fractionText (dropTrailingZeros (List.replicate ((-e).toNat - 1) '0' ++ digits))
  else
    let ex := toString e.natAbs
    String.ofList (digits.take 1) ++ fractionText (dropTrailingZeros (digits.drop 1)) ++
      "e" ++ (if e < 0 then "-" else "+") ++ (if ex.length < 2 then "0" ++ ex else ex)

/-- The `%g` layout of a rounded pair at twelve digits, with its sign. -/
def signedLayout (negative : Bool) (r : Nat × Int) : String :=
  (if negative then "-" else "") ++ gLayout significantDigits r.1 r.2

/-- The twelve-digit form of the exact rational `num / den`, negated when `negative`;
`0` for zero of either sign. -/
def ratioText (negative : Bool) (num den : Nat) : String :=
  if num = 0 ∨ den = 0 then "0"
  else signedLayout negative (roundSignificant significantDigits num den)

/-- An exact decimal number `mantissa × 10 ^ exponent`, as a JSON number literal
denotes it. Not normalized: `3`, `3.0` and `30e-1` are three spellings of one value,
and every function below reads the value only. -/
structure Decimal where
  /-- The integer the digits spell, with its sign. -/
  mantissa : Int
  /-- The power of ten it is scaled by. -/
  exponent : Int
  deriving Repr, DecidableEq

/-- The numerator and denominator of a decimal's magnitude. -/
def Decimal.magnitude (x : Decimal) : Nat × Nat :=
  if 0 ≤ x.exponent then (x.mantissa.natAbs * 10 ^ x.exponent.toNat, 1)
  else (x.mantissa.natAbs, 10 ^ (-x.exponent).toNat)

/-- The twelve-digit form of a decimal (v1 `_canon_float`, exact). Its cost grows with
the mantissa's digits and the exponent; a decimal read from text is first held to the
bounds below. -/
def Decimal.text (x : Decimal) : String :=
  ratioText (x.mantissa < 0) x.magnitude.1 x.magnitude.2

/-! ## Bounds on a number read from text

A literal enters exactly, as a sign, digits and an exponent, and nothing is computed
from it until the digits and the exponent are within these bounds, so that no literal
costs more to read or to write than its bounded size allows. A literal v1 would have
read as an infinite double (Python's `float` gives `inf` from `|x| ≥ 2^1024 - 2^970`) is
refused; a literal that would underflow to zero is kept exact, its treatment being each
function family's. -/

/-- The most digits a number literal may carry before its exponent. -/
def maxNumberDigits : Nat := 4096

/-- The most digits a literal's exponent may carry (v1's DECIMAL grammar bound). -/
def maxExponentDigits : Nat := 4

/-- The least magnitude an IEEE double rounds to infinity: `2^1024 - 2^970`, halfway
between the largest double and `2^1024` (the tie goes to infinity, the even side). It is
the units family's `Exact.overflowBound`, one constant for the whole Calculator. -/
def doubleOverflow : Nat := Exact.overflowBound

/-- `|x| ≥ 2^1024 - 2^970`: v1 would have read `x` as an infinite double. The decimal
exponent of `x` settles it unless it is 308, the threshold's own; only then are the two
compared exactly, at a cost bounded by the mantissa's digits. -/
def Decimal.overflowsDouble (x : Decimal) : Bool :=
  let m := x.mantissa.natAbs
  if m = 0 then false
  else
    let top : Int := ((digitsOf m).length : Int) - 1 + x.exponent
    if top < 308 then false
    else if 308 < top then true
    else if 0 ≤ x.exponent then decide (doubleOverflow ≤ m * 10 ^ x.exponent.toNat)
    else decide (doubleOverflow * 10 ^ (-x.exponent).toNat ≤ m)

/-! ## Values, canon and canonical JSON -/

/-- A JSON value as the canonical writers take it. `int` is an integer (v1's `int`),
written in base 10 at any size; `num` a number written in the twelve-digit form (v1's
`float`). Object members keep the order they were given in. -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | num (x : Decimal)
  | str (s : String)
  | arr (xs : List Value)
  | obj (members : List (String × Value))
  deriving Repr, Inhabited

/-- Lowercase hexadecimal digit of `n < 16`. -/
def hexDigit (n : Nat) : Char := Nat.digitChar n

/-- One character as canonical JSON writes it inside quotes (11.4). -/
def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 0x20 then ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

/-- A string as canonical JSON writes it: quoted, with only `"`, `\` and U+0000 to
U+001F escaped. -/
def quote (s : String) : String :=
  String.ofList ('"' :: s.toList.flatMap escapeChar ++ ['"'])

mutual
/-- canon (v1 `canon`): a result's text, or `none` for null and for an object, which
v1 refuses. A string is written as itself, unquoted. -/
def Value.canon : Value → Option String
  | .bool b => some (if b then "true" else "false")
  | .int n => some (toString n)
  | .num x => some x.text
  | .str s => some s
  | .arr xs => (Value.canonList xs).map fun parts => "[" ++ ",".intercalate parts ++ "]"
  | .null => none
  | .obj _ => none

/-- canon of each element, or `none` when one is refused. -/
def Value.canonList : List Value → Option (List String)
  | [] => some []
  | x :: xs => do
    let t ← x.canon
    let ts ← Value.canonList xs
    pure (t :: ts)
end

/-- Two members in key order: code point order, as `String`'s `≤` is. -/
def keyLe (a b : String × String) : Bool := decide (a.1 ≤ b.1)

/-- Members sorted by key (a stable merge sort). -/
def sortMembers (members : List (String × String)) : List (String × String) :=
  members.mergeSort keyLe

/-- Adjacent members hold distinct keys: over sorted members, the keys are distinct
(`adjacentKeysDistinct_sortMembers`), found in linear time. -/
def adjacentKeysDistinct : List (String × String) → Bool
  | a :: b :: rest => a.1 != b.1 && adjacentKeysDistinct (b :: rest)
  | _ => true

/-- An object's text from its members, each value already written: the members
sorted by key, `none` when a key occurs twice. Sorting and the check of adjacent keys
take `O(n log n)` comparisons for `n` members. -/
def objectText (members : List (String × String)) : Option String :=
  if adjacentKeysDistinct (sortMembers members) then
    some ("{" ++ ",".intercalate
      ((sortMembers members).map fun m => quote m.1 ++ ":" ++ m.2) ++ "}")
  else none

mutual
/-- TPM's canonical JSON of a value (tpm_record_schema 11.4), or `none` when an
object at any depth holds a key twice. -/
def Value.canonicalJson : Value → Option String
  | .null => some "null"
  | .bool b => some (if b then "true" else "false")
  | .int n => some (toString n)
  | .num x => some x.text
  | .str s => some (quote s)
  | .arr xs => (Value.canonicalJsonList xs).map fun parts => "[" ++ ",".intercalate parts ++ "]"
  | .obj ms => (Value.canonicalJsonMembers ms).bind objectText

/-- The canonical JSON of each element, or `none` when one is refused. -/
def Value.canonicalJsonList : List Value → Option (List String)
  | [] => some []
  | x :: xs => do
    let t ← x.canonicalJson
    let ts ← Value.canonicalJsonList xs
    pure (t :: ts)

/-- Each member's key with its value's canonical JSON, in the order given, or `none`
when a value is refused. -/
def Value.canonicalJsonMembers : List (String × Value) → Option (List (String × String))
  | [] => some []
  | (k, v) :: ms => do
    let t ← v.canonicalJson
    let ts ← Value.canonicalJsonMembers ms
    pure ((k, t) :: ts)
end

/-! ## Reading a number literal -/

/-- The value of a run of ASCII digits. -/
def digitsValue (ds : List Char) : Nat :=
  ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A JSON number literal (RFC 8259: `-? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]?
[0-9]+)?`) read as v1's Python reads it: without a fraction or an exponent it is an
integer (`int`), otherwise a number (`num`), its exact decimal value kept. Anything
else is `none`, Python's `NaN` and `Infinity` included, which are not JSON; so is a
literal past the bounds above (more than `maxNumberDigits` digits before the exponent,
more than `maxExponentDigits` in it), checked before any digit is converted, and a
number v1 would have read as an infinite double. -/
def readNumber? (s : String) : Option Value :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let intPart := cs.takeWhile Char.isDigit
  let cs := cs.drop intPart.length
  let (frac, cs) := match cs with
    | '.' :: rest => (some (rest.takeWhile Char.isDigit), (rest.dropWhile Char.isDigit))
    | _ => (none, cs)
  let (expo, cs) := match cs with
    | c :: rest =>
      if c = 'e' ∨ c = 'E' then
        let (eneg, rest) := match rest with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | _ => (false, rest)
        let ds := rest.takeWhile Char.isDigit
        (some (eneg, ds), rest.drop ds.length)
      else (none, cs)
    | [] => (none, cs)
  let intOk := intPart == ['0'] || (!intPart.isEmpty && intPart.head? != some '0')
  let fracOk := frac.all (!·.isEmpty)
  let expOk := expo.all (!·.2.isEmpty)
  let fd := frac.getD []
  let bounded := intPart.length + fd.length ≤ maxNumberDigits &&
    expo.all (·.2.length ≤ maxExponentDigits)
  if !(cs.isEmpty && intOk && fracOk && expOk && bounded) then none
  else
    let mag : Int := digitsValue (intPart ++ fd)
    let e : Int := match expo with
      | some (eneg, ds) => if eneg then -(digitsValue ds : Int) else digitsValue ds
      | none => 0
    if frac.isNone && expo.isNone then some (.int (if neg then -mag else mag))
    else
      let x : Decimal := ⟨if neg then -mag else mag, e - fd.length⟩
      if x.overflowsDouble then none else some (.num x)

/-! ## Worked examples, checked by the kernel -/

theorem text_two_point_five : (Decimal.mk 25 (-1)).text = "2.5" := by decide
theorem text_three : (Decimal.mk 30 (-1)).text = "3" := by decide
theorem text_tie_to_even : (Decimal.mk 1234567890125 (-1)).text = "123456789012" := by decide
theorem text_exponent : (Decimal.mk 1 12).text = "1e+12" := by decide
theorem text_small : (Decimal.mk 1 (-5)).text = "1e-05" := by decide
theorem text_fixed_small : (Decimal.mk 1 (-4)).text = "0.0001" := by decide
theorem text_negative : (Decimal.mk (-25) (-8)).text = "-2.5e-07" := by decide

/-! ## What the kernel checks about the writers -/

/-- `hexDigit` tells the sixteen digits apart. -/
theorem hexDigit_inj : ∀ i < 16, ∀ j < 16, hexDigit i = hexDigit j → i = j := by decide

/-- Every hexadecimal digit is a printable character. -/
theorem hexDigit_printable : ∀ i < 16, 0x20 ≤ (hexDigit i).toNat := by decide

/-- `escapeChar` writes no control character: U+0000 to U+001F never stand raw. -/
theorem escapeChar_printable (c : Char) : ∀ d ∈ escapeChar c, 0x20 ≤ d.toNat := by
  intro d hd
  unfold escapeChar at hd
  split at hd
  · simp at hd; rcases hd with rfl | rfl <;> decide
  split at hd
  · simp at hd; subst hd; decide
  split at hd
  · rename_i h
    have h1 : c.toNat / 16 < 16 := by omega
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | exact hexDigit_printable _ h1 | exact hexDigit_printable _ h2
  · rename_i h
    simp at hd; subst hd; omega

/-- A quoted string's text holds no control character (11.4). -/
theorem quote_printable (s : String) : ∀ d ∈ (quote s).toList, 0x20 ≤ d.toNat := by
  intro d hd
  simp only [quote, String.toList_ofList, List.cons_append, List.mem_cons, List.mem_append,
    List.mem_flatMap, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | ⟨c, _, hc⟩ | rfl
  · decide
  · exact escapeChar_printable c d hc
  · decide

/-- No character's escape is a prefix of another's: what `escapeChar` writes for one
character, followed by anything, names that character and the rest. -/
theorem escapeChar_prefix {a b : Char} {u v : List Char}
    (h : escapeChar a ++ u = escapeChar b ++ v) : a = b ∧ u = v := by
  unfold escapeChar at h
  split at h <;> split at h <;> (try split at h) <;> (try split at h) <;>
    (try split at h) <;> (try split at h) <;> simp_all
  all_goals first
    | exact absurd h.1.symm ‹¬b = '\\'›
    | (have h1 := hexDigit_inj _ (by omega) _ (by omega) h.1
       have h2 := hexDigit_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h.2.1
       exact Char.toNat_inj.mp (by omega))

/-- An escape is never empty. -/
theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar
  split <;> (try split) <;> (try split) <;> simp

/-- Escaping is injective on character lists. -/
theorem flatMap_escapeChar_inj :
    ∀ {xs ys : List Char}, xs.flatMap escapeChar = ys.flatMap escapeChar → xs = ys
  | [], [], _ => rfl
  | [], y :: _, h => by
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    exact absurd (List.append_eq_nil_iff.mp h.symm).1 (escapeChar_ne_nil y)
  | x :: _, [], h => by
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    exact absurd (List.append_eq_nil_iff.mp h).1 (escapeChar_ne_nil x)
  | _ :: _, _ :: _, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨rfl, h'⟩ := escapeChar_prefix h
    rw [flatMap_escapeChar_inj h']

/-- Canonical JSON tells strings apart: two strings with one quoted text are one
string. -/
theorem quote_injective {s t : String} (h : quote s = quote t) : s = t := by
  simp only [quote, String.ofList_inj, List.cons_append, List.cons.injEq, true_and] at h
  exact String.toList_inj.mp (flatMap_escapeChar_inj (List.append_cancel_right h))

/-! Object members: code point order, whatever order they were given in. -/

theorem keyLe_trans (a b c : String × String) :
    keyLe a b = true → keyLe b c = true → keyLe a c = true := by
  simp only [keyLe, decide_eq_true_eq]
  exact String.le_trans

theorem keyLe_total (a b : String × String) : (keyLe a b || keyLe b a) = true := by
  simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

/-- The members are written in code point order of their keys (11.4). -/
theorem sortMembers_sorted (members : List (String × String)) :
    (sortMembers members).Pairwise fun a b => a.1 ≤ b.1 := by
  have := List.pairwise_mergeSort keyLe_trans keyLe_total members
  simp only [keyLe, decide_eq_true_eq] at this
  exact this

/-- In a list whose keys are distinct, a key names one member. -/
theorem eq_of_key_eq {ms : List (String × String)} (hd : (ms.map Prod.fst).Nodup)
    {a b : String × String} (ha : a ∈ ms) (hb : b ∈ ms) (hk : a.1 = b.1) : a = b := by
  induction ms with
  | nil => simp at ha
  | cons c ms ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hk.symm⟩ hd.1
    · exact absurd ⟨a, ha, hk⟩ hd.1
    · exact ih hd.2 ha hb

/-- With distinct keys, the sorted members do not depend on the order they were given
in. -/
theorem sortMembers_perm {ms ms' : List (String × String)} (hd : (ms.map Prod.fst).Nodup)
    (h : ms.Perm ms') : sortMembers ms = sortMembers ms' := by
  have p : (sortMembers ms).Perm (sortMembers ms') :=
    (List.mergeSort_perm ms keyLe).trans (h.trans (List.mergeSort_perm ms' keyLe).symm)
  apply List.Perm.eq_of_pairwise _ (sortMembers_sorted ms) (sortMembers_sorted ms') p
  intro a b ha hb hab hba
  have ha' : a ∈ ms := (List.mergeSort_perm ms keyLe).subset ha
  have hb' : b ∈ ms := h.symm.subset ((List.mergeSort_perm ms' keyLe).subset hb)
  exact eq_of_key_eq hd ha' hb' (String.le_antisymm hab hba)

/-- Over members sorted by key, the check of adjacent keys is the distinctness of all
keys. -/
theorem adjacentKeysDistinct_iff :
    ∀ {l : List (String × String)}, l.Pairwise (fun a b => a.1 ≤ b.1) →
      (adjacentKeysDistinct l = true ↔ (l.map Prod.fst).Nodup)
  | [], _ => by simp [adjacentKeysDistinct]
  | [_], _ => by simp [adjacentKeysDistinct]
  | a :: b :: rest, h => by
    have hs := h.of_cons
    have ih := adjacentKeysDistinct_iff hs
    simp only [adjacentKeysDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq, ih]
    constructor
    · rintro ⟨hab, hnd⟩
      refine List.nodup_cons.mpr ⟨?_, hnd⟩
      intro hmem
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hmem
      rcases hmem with h1 | ⟨c, hc, h2⟩
      · exact hab h1
      · have hle : a.1 ≤ b.1 := List.rel_of_pairwise_cons h (by simp)
        have hbc : b.1 ≤ c.1 := List.rel_of_pairwise_cons hs hc
        exact hab (String.le_antisymm hle (h2 ▸ hbc))
    · intro hnd
      have hc := List.nodup_cons.mp hnd
      refine ⟨fun heq => hc.1 (by simp [heq]), hc.2⟩

/-- The keys of sorted members are distinct exactly when the members' keys are. -/
theorem adjacentKeysDistinct_sortMembers (ms : List (String × String)) :
    adjacentKeysDistinct (sortMembers ms) = true ↔ (ms.map Prod.fst).Nodup := by
  rw [adjacentKeysDistinct_iff (sortMembers_sorted ms)]
  exact ((List.mergeSort_perm ms keyLe).map Prod.fst).nodup_iff

/-- An object's text does not depend on the order its members were given in (the
property collision register R5 asks of a hand-written writer). -/
theorem objectText_perm {ms ms' : List (String × String)} (h : ms.Perm ms') :
    objectText ms = objectText ms' := by
  have hn : (ms.map Prod.fst).Nodup ↔ (ms'.map Prod.fst).Nodup := (h.map Prod.fst).nodup_iff
  unfold objectText
  by_cases hd : (ms.map Prod.fst).Nodup
  · have h2 := (adjacentKeysDistinct_sortMembers ms').mpr (hn.mp hd)
    simp only [sortMembers_perm hd h, h2, ite_true]
  · have h1 : adjacentKeysDistinct (sortMembers ms) = false := by
      cases e : adjacentKeysDistinct (sortMembers ms)
      · rfl
      · exact absurd ((adjacentKeysDistinct_sortMembers ms).mp e) hd
    have h2 : adjacentKeysDistinct (sortMembers ms') = false := by
      cases e : adjacentKeysDistinct (sortMembers ms')
      · rfl
      · exact absurd (hn.mpr ((adjacentKeysDistinct_sortMembers ms').mp e)) hd
    simp only [h1, h2, Bool.false_eq_true, ite_false]

/-- Members given in two orders are refused alike or written as two orders of one list
of members. -/
theorem canonicalJsonMembers_perm {l₁ l₂ : List (String × Value)} (h : l₁.Perm l₂) :
    (Value.canonicalJsonMembers l₁ = none ∧ Value.canonicalJsonMembers l₂ = none) ∨
      ∃ p q, Value.canonicalJsonMembers l₁ = some p ∧ Value.canonicalJsonMembers l₂ = some q ∧
        p.Perm q := by
  induction h with
  | nil => exact .inr ⟨[], [], rfl, rfl, .nil⟩
  | cons x _ ih =>
    obtain ⟨k, v⟩ := x
    simp only [Value.canonicalJsonMembers]
    cases hv : v.canonicalJson with
    | none => exact .inl ⟨rfl, rfl⟩
    | some t =>
      rcases ih with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hpq⟩
      · exact .inl ⟨by simp [h1], by simp [h2]⟩
      · exact .inr ⟨(k, t) :: p, (k, t) :: q, by simp [h1], by simp [h2], hpq.cons _⟩
  | swap x y l =>
    obtain ⟨k1, v1⟩ := x
    obtain ⟨k2, v2⟩ := y
    simp only [Value.canonicalJsonMembers]
    cases v1.canonicalJson <;> cases v2.canonicalJson <;>
      cases Value.canonicalJsonMembers l <;> simp
    exact .swap _ _ _
  | trans _ _ ih1 ih2 =>
    rcases ih1 with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hpq⟩ <;>
      rcases ih2 with ⟨h2', h3⟩ | ⟨q', r, h2', h3, hqr⟩
    · exact .inl ⟨h1, h3⟩
    · simp [h2] at h2'
    · simp [h2] at h2'
    · rw [h2] at h2'
      cases h2'
      exact .inr ⟨p, r, h1, h3, hpq.trans hqr⟩

/-- An object's canonical JSON does not depend on the order its members were given in:
the property collision register R5 asks of the hand-written writer, since `Lean.Json`
reorders keys on its own terms. -/
theorem canonicalJson_obj_perm {ms ms' : List (String × Value)} (h : ms.Perm ms') :
    (Value.obj ms).canonicalJson = (Value.obj ms').canonicalJson := by
  simp only [Value.canonicalJson]
  rcases canonicalJsonMembers_perm h with ⟨h1, h2⟩ | ⟨p, q, h1, h2, hpq⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact objectText_perm hpq

/-! Numbers: the twelve-digit form reads the value, not its spelling. -/

theorem digitsOf_ten_mul {n : Nat} (h : 0 < n) :
    (digitsOf (10 * n)).length = (digitsOf n).length + 1 := by
  have := Nat.toDigits_append_toDigits (b := 10) (n := n) (d := 0) (by decide) h (by decide)
  simp only [Nat.add_zero] at this
  simp only [digitsOf, ← this, List.length_append, Nat.toDigits_zero]
  rfl

theorem atLeastPow_scale (a b : Nat) (e : Int) :
    atLeastPow (10 * a) (10 * b) e = atLeastPow a b e := by
  unfold atLeastPow
  split
  · simp only [decide_eq_decide, Nat.mul_assoc]
    exact Nat.mul_le_mul_left_iff (by decide)
  · simp only [decide_eq_decide, Nat.mul_assoc]
    exact Nat.mul_le_mul_left_iff (by decide)

theorem decimalExponent_scale {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    decimalExponent (10 * a) (10 * b) = decimalExponent a b := by
  unfold decimalExponent exponentBelow
  rw [digitsOf_ten_mul ha, digitsOf_ten_mul hb, atLeastPow_scale]
  have : ((((digitsOf a).length + 1 : Nat) : Int) - (((digitsOf b).length + 1 : Nat) : Int)) =
      ((digitsOf a).length : Int) - ((digitsOf b).length : Int) := by omega
  rw [this]

theorem scaleBy_scale (a b : Nat) (k : Int) :
    scaleBy (10 * a) (10 * b) k = (10 * (scaleBy a b k).1, 10 * (scaleBy a b k).2) := by
  unfold scaleBy
  split <;> simp [Nat.mul_assoc]

theorem roundHalfEven_scale (n d : Nat) : roundHalfEven (10 * n) (10 * d) = roundHalfEven n d := by
  unfold roundHalfEven
  rw [Nat.mul_div_mul_left _ _ (by decide), Nat.mul_mod_mul_left]
  have h1 : decide (10 * d < 2 * (10 * (n % d))) = decide (d < 2 * (n % d)) := by
    simp only [decide_eq_decide]; omega
  have h2 : (2 * (10 * (n % d)) == 10 * d) = (2 * (n % d) == d) := by
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
  simp only [h1, h2]

theorem roundSignificant_scale (p : Nat) {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    roundSignificant p (10 * a) (10 * b) = roundSignificant p a b := by
  unfold roundSignificant roundAt
  rw [decimalExponent_scale ha hb, scaleBy_scale, roundHalfEven_scale]

theorem ratioText_scale (negative : Bool) (a b : Nat) :
    ratioText negative (10 * a) (10 * b) = ratioText negative a b := by
  unfold ratioText
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have h1 : ¬(10 * a = 0 ∨ 10 * b = 0) := by omega
  have h2 : ¬(a = 0 ∨ b = 0) := by omega
  simp only [h1, h2, ite_false, roundSignificant_scale _ (Nat.pos_of_ne_zero ha)
    (Nat.pos_of_ne_zero hb)]

/-- A decimal and its spelling with one more zero (`3` and `3.0`, `2.5e-7` and
`25e-8`) have one text: the twelve-digit form is a function of the value. -/
theorem Decimal.text_respell (m e : Int) :
    (Decimal.mk (10 * m) (e - 1)).text = (Decimal.mk m e).text := by
  have hs : decide (10 * m < 0) = decide (m < 0) := decide_eq_decide.mpr (by omega)
  have hm : (10 * m).natAbs = 10 * m.natAbs := by
    rw [Int.natAbs_mul]; rfl
  unfold Decimal.text Decimal.magnitude
  simp only [hs, hm]
  by_cases he : 1 ≤ e
  · have h1 : 0 ≤ e - 1 := by omega
    have h2 : 0 ≤ e := by omega
    have hp : e.toNat = (e - 1).toNat + 1 := by omega
    simp only [h1, h2, ite_true, hp, Nat.pow_succ]
    rw [Nat.mul_comm (10 ^ _) 10, ← Nat.mul_assoc, Nat.mul_comm m.natAbs 10]
  · have h1 : ¬ 0 ≤ e - 1 := by omega
    have hk : (-(e - 1)).toNat = (-e).toNat + 1 := by omega
    simp only [h1, ite_false, hk, Nat.pow_succ]
    rw [Nat.mul_comm (10 ^ _) 10]
    by_cases h0 : 0 ≤ e
    · have : e = 0 := by omega
      subst this
      simpa using ratioText_scale (decide (m < 0)) m.natAbs 1
    · simp only [h0, ite_false]
      exact ratioText_scale _ m.natAbs (10 ^ (-e).toNat)

/-- The canonical JSON of a number reads its value, not its spelling. -/
theorem canonicalJson_num_respell (m e : Int) :
    (Value.num ⟨10 * m, e - 1⟩).canonicalJson = (Value.num ⟨m, e⟩).canonicalJson := by
  simp only [Value.canonicalJson, Decimal.text_respell]

/-- A key given twice is refused, wherever it stands. -/
theorem objectText_duplicate (k a b : String) (rest : List (String × String)) :
    objectText ((k, a) :: (k, b) :: rest) = none := by
  have : adjacentKeysDistinct (sortMembers ((k, a) :: (k, b) :: rest)) = false := by
    cases e : adjacentKeysDistinct (sortMembers ((k, a) :: (k, b) :: rest))
    · rfl
    · have := (adjacentKeysDistinct_sortMembers _).mp e
      simp at this
  simp [objectText, this]

end Principia.Canonical
