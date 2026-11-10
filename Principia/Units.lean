import Principia.Dimension
import Principia.Decimal
import Principia.Exact
import Principia.Zone.Text

/-!
# Units

The unit grammar, its closed catalogue and the four unit functions of v1's tpc_units
0.1.1 (tpm_units 0.2.0: the grammar and catalogue, UNIT at zone entry,
KIND): `unit_parse`, `unit_scale`, `unit_matches` (C-32) and
`normalize_measurement`. The three functions that go on to the strike rule
(`mm_contradicts_units`, `lm_contradicts_units`, `sr8_scale_factor_units`) are in
`Principia.UnitsStrike`, with how they meet a power of π.

Grammar: `UNIT := "1" | token (" " token)*`, single ASCII spaces; `token := [prefix]
symbol [exponent]`, `exponent := -?[0-9]{1,4}`. A token's exponent applies to the
prefixed symbol: `cm2` is (0.01 m)^2. An absent exponent is 1; a zero exponent drops the
token. Tokens of one prefixed symbol merge, their exponents adding. Every merged exponent
and every exponent of the resulting DIMENSION lies within -9999..9999.

Canonical spelling: tokens sorted by the symbol's place in the catalogue, then by the
prefix's power of ten (a bare symbol counts 0); exponent 1 not written; `1` when none
remain. Only spelling is canonical: `km m` is `m km`, never `1e3 m2`.

KIND: the exponents of angle (rad, deg, arcmin, arcsec count 1; sr, lm, lx count
2), Hz, Bq, Gy and Sv, written `rad2 Hz-1`, or `none`. Two values are compared only when
DIMENSION and KIND agree.

Numbers. v1 computed a unit's scale in IEEE doubles, token by token, and refused a scale
that is zero or infinite as a double, even when only a partial product left the range
(`Qm11 qm11`), and a normalized value that is infinite. Here every scale and value is
exact, a rational times a power of π (`Principia.Exact`), and v1's refusals are kept,
decided on the exact value before it is formed (`Exact.Product.range`); where that departs
from v1's answers (its printed roundings, and `Qm11 qm11`) the departure is recorded
beside v1's corpus (the divergence list of the units corpus).

Refusals are `Except.error reason`, never raised; a reason quotes its input with hidden
characters escaped (zone schemas 6.3, see `escape`).
-/

namespace Principia.Units

/-! ## The catalogue -/

/-- A symbol's factor to coherent SI, exact by definition. -/
inductive Factor where
  /-- `mantissa × 10^exponent`. -/
  | dec (mantissa : Nat) (exponent : Int)
  /-- π divided by a whole number: deg, arcmin, arcsec. -/
  | piOver (n : Nat)
  deriving DecidableEq, Repr

/-- A catalogue row: the symbol, its exponents over L M T I TH N J, its factor, and
whether it takes a prefix. -/
structure Symbol where
  spell : String
  dims : List Int
  factor : Factor
  prefixable : Bool
  deriving Repr

/-- The closed catalogue, in canonical order (v1's `CATALOGUE`): SI base with the gram in
place of the kilogram, so that kg is k + g; SI dimensionless; SI derived with special
names (degree Celsius excluded, being affine); SI Table 8 units with an exactly defined
value. v1 wrote the decimal factors as strings: g "1e-3", min "60", h "3600", d "86400",
au "149597870700", ha "1e4", L "1e-3", t "1e3", eV "1.602176634e-19". -/
def catalogue : List Symbol := [
  ⟨"m",      [1, 0, 0, 0, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"g",      [0, 1, 0, 0, 0, 0, 0],    .dec 1 (-3), true⟩,
  ⟨"s",      [0, 0, 1, 0, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"A",      [0, 0, 0, 1, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"K",      [0, 0, 0, 0, 1, 0, 0],    .dec 1 0, true⟩,
  ⟨"mol",    [0, 0, 0, 0, 0, 1, 0],    .dec 1 0, true⟩,
  ⟨"cd",     [0, 0, 0, 0, 0, 0, 1],    .dec 1 0, true⟩,
  ⟨"rad",    [0, 0, 0, 0, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"sr",     [0, 0, 0, 0, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"Hz",     [0, 0, -1, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"N",      [1, 1, -2, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"Pa",     [-1, 1, -2, 0, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"J",      [2, 1, -2, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"W",      [2, 1, -3, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"C",      [0, 0, 1, 1, 0, 0, 0],    .dec 1 0, true⟩,
  ⟨"V",      [2, 1, -3, -1, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"F",      [-2, -1, 4, 2, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"Ohm",    [2, 1, -3, -2, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"S",      [-2, -1, 3, 2, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"Wb",     [2, 1, -2, -1, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"T",      [0, 1, -2, -1, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"H",      [2, 1, -2, -2, 0, 0, 0],  .dec 1 0, true⟩,
  ⟨"lm",     [0, 0, 0, 0, 0, 0, 1],    .dec 1 0, true⟩,
  ⟨"lx",     [-2, 0, 0, 0, 0, 0, 1],   .dec 1 0, true⟩,
  ⟨"Bq",     [0, 0, -1, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"Gy",     [2, 0, -2, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"Sv",     [2, 0, -2, 0, 0, 0, 0],   .dec 1 0, true⟩,
  ⟨"kat",    [0, 0, -1, 0, 0, 1, 0],   .dec 1 0, true⟩,
  ⟨"min",    [0, 0, 1, 0, 0, 0, 0],    .dec 60 0, false⟩,
  ⟨"h",      [0, 0, 1, 0, 0, 0, 0],    .dec 3600 0, false⟩,
  ⟨"d",      [0, 0, 1, 0, 0, 0, 0],    .dec 86400 0, false⟩,
  ⟨"au",     [1, 0, 0, 0, 0, 0, 0],    .dec 149597870700 0, false⟩,
  ⟨"deg",    [0, 0, 0, 0, 0, 0, 0],    .piOver 180, false⟩,
  ⟨"arcmin", [0, 0, 0, 0, 0, 0, 0],    .piOver 10800, false⟩,
  ⟨"arcsec", [0, 0, 0, 0, 0, 0, 0],    .piOver 648000, true⟩,
  ⟨"ha",     [2, 0, 0, 0, 0, 0, 0],    .dec 1 4, false⟩,
  ⟨"L",      [3, 0, 0, 0, 0, 0, 0],    .dec 1 (-3), true⟩,
  ⟨"t",      [0, 1, 0, 0, 0, 0, 0],    .dec 1 3, true⟩,
  ⟨"eV",     [2, 1, -2, 0, 0, 0, 0],   .dec 1602176634 (-28), true⟩]

/-- The 24 SI prefixes and their powers of ten, ASCII (`u` for micro), in v1's order
(`PREFIXES`). Not prefixable: min, h, d (the SI Brochure forbids prefixes on the non-SI
units of time), ha (already prefixed), au, deg, arcmin. -/
def prefixes : List (String × Int) := [
  ("q", -30), ("r", -27), ("y", -24), ("z", -21), ("a", -18), ("f", -15),
  ("p", -12), ("n", -9), ("u", -6), ("m", -3), ("c", -2), ("d", -1),
  ("da", 1), ("h", 2), ("k", 3), ("M", 6), ("G", 9), ("T", 12),
  ("P", 15), ("E", 18), ("Z", 21), ("Y", 24), ("R", 27), ("Q", 30)]

/-- The symbols refused on purpose, with the reason the refusal states (v1's
`REFUSED_UNITS`). -/
def refusedSymbols : List (String × String) := [
  ("degC", "an offset scale, not a ratio"),
  ("Da", "a measured value; the conversion would carry an uncertainty"),
  ("Np", "a logarithmic scale"), ("B", "a logarithmic scale"),
  ("dB", "a logarithmic scale")]

/-- The KIND bases, in order (v1's `KIND_BASES`). -/
def kindBases : List String := ["rad", "Hz", "Bq", "Gy", "Sv"]

/-- Each symbol's KIND contribution over `kindBases` (v1's `KIND_OF`); every other symbol
contributes none. -/
def kindOf : List (String × List Int) := [
  ("rad", [1, 0, 0, 0, 0]), ("deg", [1, 0, 0, 0, 0]), ("arcmin", [1, 0, 0, 0, 0]),
  ("arcsec", [1, 0, 0, 0, 0]), ("sr", [2, 0, 0, 0, 0]), ("lm", [2, 0, 0, 0, 0]),
  ("lx", [2, 0, 0, 0, 0]), ("Hz", [0, 1, 0, 0, 0]), ("Bq", [0, 0, 1, 0, 0]),
  ("Gy", [0, 0, 0, 1, 0]), ("Sv", [0, 0, 0, 0, 1])]

/-- A token's reading: a prefix (an index into `prefixes`) or none, and a symbol (an
index into `catalogue`). -/
structure Reading where
  pre : Option Nat
  sym : Nat
  deriving DecidableEq, Repr

/-- A catalogue row by index (the default row is never reached by a reading). -/
def symbolAt (i : Nat) : Symbol := catalogue.getD i ⟨"", [], .dec 1 0, false⟩

/-- A prefix by index. -/
def prefixAt (j : Nat) : String × Int := prefixes.getD j ("", 0)

/-- The prefix's power of ten; a bare symbol counts 0. -/
def Reading.power (r : Reading) : Int :=
  match r.pre with
  | some j => (prefixAt j).2
  | none => 0

/-- A reading's letters: the prefix, then the symbol. -/
def Reading.spell (r : Reading) : String :=
  (match r.pre with
    | some j => (prefixAt j).1
    | none => "") ++ (symbolAt r.sym).spell

/-- The catalogue index of a symbol spelled exactly so. -/
def symbolIndex? (cs : List Char) : Option Nat :=
  catalogue.findIdx? fun e => e.spell.toList == cs

/-- Every reading of a token's letters as a prefix and a symbol (v1's `_readings`): the
bare symbol first, then each prefix in order; only a prefixable symbol takes one. -/
def readings (cs : List Char) : List Reading :=
  let bare := match symbolIndex? cs with
    | some i => [⟨none, i⟩]
    | none => []
  bare ++ (List.range prefixes.length).filterMap fun j =>
    let p := (prefixAt j).1.toList
    if p.isPrefixOf cs then
      match symbolIndex? (cs.drop p.length) with
      | some i => if (symbolAt i).prefixable then some ⟨some j, i⟩ else none
      | none => none
    else none

/-! ## The ambiguity check

v1 asserted when loaded that the catalogue spells 807 token strings, each in one way only,
none of them a refused symbol. Here the same facts are theorems, checked by the Lean
kernel when the library is built. Each spelling is mapped to a number (its characters in
base 128 after a leading 1); the numbers are merge-sorted and checked strictly increasing,
which makes them, and so the spellings, pairwise distinct. -/

/-- Every reading the catalogue allows: each symbol bare, and each prefixable symbol under
each prefix. -/
def allReadings : List Reading :=
  (List.range catalogue.length).flatMap fun i =>
    ⟨none, i⟩ :: if (symbolAt i).prefixable then
      (List.range prefixes.length).map fun j => ⟨some j, i⟩
    else []

/-- A spelling as a number. -/
def spellKey (s : String) : Nat := s.toList.foldl (fun acc c => acc * 128 + c.toNat) 1

/-- Strictly increasing. -/
def strictly : List Nat → Bool
  | a :: b :: r => decide (a < b) && strictly (b :: r)
  | _ => true

/-- Merge two lists in `fuel` steps at most; out of fuel, the rest is appended. -/
def mergeFuel : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeFuel f xs (y :: ys) else y :: mergeFuel f (x :: xs) ys

/-- Merge neighbouring runs. -/
def mergePairs : List (List Nat) → List (List Nat)
  | a :: b :: r => mergeFuel (a.length + b.length) a b :: mergePairs r
  | [a] => [a]
  | [] => []

/-- Merge runs until one is left, in `fuel` rounds at most; out of fuel, the runs are
concatenated. -/
def mergeRuns : Nat → List (List Nat) → List Nat
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [l] => l
  | f + 1, a :: b :: r => mergeRuns f (mergePairs (a :: b :: r))

/-- A merge sort written by structural recursion, so that the kernel can run it. Whatever
the fuel, the result is a permutation of the input; enough fuel also sorts it, and the
check below fails if it does not. -/
def sortFuel (l : List Nat) : List Nat := mergeRuns l.length (l.map fun a => [a])

theorem mergeFuel_perm : ∀ (f : Nat) (xs ys : List Nat), (mergeFuel f xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by simp [mergeFuel]
  | f + 1, x :: xs, y :: ys => by
    unfold mergeFuel
    split
    · exact (mergeFuel_perm f xs (y :: ys)).cons x
    · exact ((mergeFuel_perm f (x :: xs) ys).cons y).trans List.perm_middle.symm

theorem mergePairs_perm : ∀ ls : List (List Nat), (mergePairs ls).flatten.Perm ls.flatten
  | a :: b :: r => by
    simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
    exact (mergeFuel_perm _ a b).append (mergePairs_perm r)
  | [_] => List.Perm.refl _
  | [] => List.Perm.refl _

theorem mergeRuns_perm : ∀ (f : Nat) (ls : List (List Nat)), (mergeRuns f ls).Perm ls.flatten
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => by simp [mergeRuns]
  | f + 1, a :: b :: r => (mergeRuns_perm f _).trans (mergePairs_perm _)

theorem flatten_map_singleton : ∀ l : List Nat, (l.map fun a => [a]).flatten = l
  | [] => rfl
  | a :: l => by simp [List.flatten_cons, flatten_map_singleton l]

theorem sortFuel_perm (l : List Nat) : (sortFuel l).Perm l := by
  have h := mergeRuns_perm l.length (l.map fun a => [a])
  rw [flatten_map_singleton] at h
  exact h

theorem strictly_lt : ∀ {a : Nat} {l : List Nat}, strictly (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: r, h, x, hx => by
    simp only [strictly, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (strictly_lt h.2 x hx)

theorem strictly_nodup : ∀ {l : List Nat}, strictly l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    refine List.nodup_cons.mpr ⟨fun ha => Nat.lt_irrefl a (strictly_lt h a ha), ?_⟩
    apply strictly_nodup
    cases l with
    | nil => rfl
    | cons b r =>
      simp only [strictly, Bool.and_eq_true] at h
      exact h.2

/-- 807 token strings, as v1 counts them (`TOKEN_COUNT`); a catalogue edit that changes
the count must change this theorem. -/
theorem allReadings_length : allReadings.length = 807 := by decide +kernel

theorem allReadings_keys_sorted :
    strictly (sortFuel ((allReadings.map Reading.spell).map spellKey)) = true := by
  decide +kernel

/-- Every token string is spelled by one reading only (v1's `_assert_unambiguous`): `cd`
is the candela, `TT` the teratesla, `hPa` the hectopascal and `ha` the hectare. -/
theorem allReadings_unambiguous : (allReadings.map Reading.spell).Nodup :=
  List.Pairwise.of_map spellKey (fun _ _ h e => h (congrArg spellKey e))
    ((sortFuel_perm _).nodup_iff.mp (strictly_nodup allReadings_keys_sorted))

theorem allReadings_keys_not_refused :
    allReadings.all (fun r => !((refusedSymbols.map fun p => spellKey p.1).contains
      (spellKey r.spell))) = true := by
  decide +kernel

/-- No token string is a refused symbol. -/
theorem allReadings_not_refused :
    ∀ r ∈ allReadings, ∀ p ∈ refusedSymbols, r.spell ≠ p.1 := by
  intro r hr p hp he
  have h := List.all_eq_true.mp allReadings_keys_not_refused r hr
  have hm : spellKey r.spell ∈ refusedSymbols.map fun p => spellKey p.1 :=
    List.mem_map.mpr ⟨p, hp, by rw [he]⟩
  simp [hm] at h

/-! ## Reading a UNIT -/

/-- A token's letters and exponent (`([A-Za-z]+)(-?[0-9]{1,4})?`); an absent exponent is
1. -/
def readUnitToken (cs : List Char) : Option (List Char × Int) :=
  let (letters, rest) := cs.span Char.isAlpha
  if letters = [] then none
  else if rest = [] then some (letters, 1)
  else (Dimension.readExp rest).map fun n => (letters, n)

/-- The reason a refused symbol is refused. -/
def refusedReason (cs : List Char) : Option String :=
  (refusedSymbols.find? fun p => p.1.toList == cs).map (·.2)

/-- The first prefix, in v1's order, under which the rest of the letters gives an
answer. -/
def underPrefix (letters : List Char) (f : List Char → Option String) : Option String :=
  prefixes.findSome? fun p =>
    if p.1.toList.isPrefixOf letters then f (letters.drop p.1.length) else none

/-- Why letters with no reading are refused, in v1's words and order: a refused symbol
under a prefix, a symbol that takes no prefix, or no unit symbol at all. -/
def noReading (u : String) (letters : List Char) : String :=
  let refusedUnder := underPrefix letters fun rest =>
    (refusedReason rest).map fun why => s!"{String.ofList rest} is refused, {why}"
  let noPrefix := underPrefix letters fun rest =>
    (symbolIndex? rest).map fun _ => s!"{String.ofList rest} takes no prefix"
  match refusedUnder, noPrefix with
  | some what, _ => s!"UNIT {u}: {what}"
  | none, some what => s!"UNIT {u}: {what}"
  | none, none => s!"UNIT {u}: {String.ofList letters} is not a unit symbol"

/-- Add an exponent to a reading's entry, or append the reading. -/
def addReading : List (Reading × Int) → Reading → Int → List (Reading × Int)
  | [], r, e => [(r, e)]
  | (r', e') :: rest, r, e =>
    if r' = r then (r', e' + e) :: rest else (r', e') :: addReading rest r e

/-- Read the tokens in order, merging those of one prefixed symbol; the first token that
does not read gives the refusal. -/
def mergeTokens (u : String) :
    List (List Char) → List (Reading × Int) → Except String (List (Reading × Int))
  | [], acc => .ok acc
  | tok :: toks, acc =>
    match readUnitToken tok with
    | none => .error s!"UNIT {u} is not a unit"
    | some (letters, ex) =>
      match refusedReason letters with
      | some why => .error s!"UNIT {u}: {String.ofList letters} is refused, {why}"
      | none =>
        match readings letters with
        | [] => .error (noReading u letters)
        | r :: _ => mergeTokens u toks (addReading acc r ex)

/-- Each base's exponent in the DIMENSION of merged tokens. -/
def dimExps (items : List (Reading × Int)) : Dimension.Exponents :=
  fun b => (items.map fun t => (symbolAt t.1.sym).dims.getD b.index 0 * t.2).sum

/-- Canonical order: the symbol's place in the catalogue, then the prefix's power. -/
def canonLe (a b : Reading × Int) : Bool :=
  decide (a.1.sym < b.1.sym) || (a.1.sym == b.1.sym && decide (a.1.power ≤ b.1.power))

/-- A UNIT's tokens, merged, without zero exponents, in canonical order; or the reason it
is refused, before escaping (v1's `_tokens`). -/
def tokens (u : String) : Except String (List (Reading × Int)) :=
  if u = "" then .error s!"UNIT {u} is not a unit"
  else if u = "1" then .ok []
  else
    match mergeTokens u (u.toList.splitOn ' ') [] with
    | .error r => .error r
    | .ok merged =>
      let items := (merged.filter fun t => t.2 != 0).mergeSort canonLe
      if items.any (fun t => decide (Dimension.expMax < t.2.natAbs)) ||
          !Dimension.inRange (dimExps items) then
        .error s!"UNIT {u}: an exponent is out of range"
      else .ok items

/-- The canonical spelling of merged tokens; exponent 1 is not written. -/
def spelling (items : List (Reading × Int)) : String :=
  if items.isEmpty then "1"
  else " ".intercalate (items.map fun t =>
    t.1.spell ++ if t.2 = 1 then "" else toString t.2)

/-- The KIND of merged tokens: `rad2 Hz-1`, or `none`. -/
def kind (items : List (Reading × Int)) : String :=
  let contribution (s : String) (j : Nat) : Int :=
    ((kindOf.find? (·.1 == s)).map (·.2.getD j 0)).getD 0
  let sums := (List.range kindBases.length).map fun j =>
    (items.map fun t => contribution (symbolAt t.1.sym).spell j * t.2).sum
  let toks := ((kindBases.zip sums).filter (·.2 != 0)).map fun p => p.1 ++ toString p.2
  if toks.isEmpty then "none" else " ".intercalate toks

/-! ## The scale to coherent SI -/

/-- A symbol's factor, unevaluated. -/
def Factor.product : Factor → Exact.Product
  | .dec m e => (Exact.Product.nat m).mul (Exact.Product.ten e)
  | .piOver n => { den := [(n, 1)], pi := 1 }

/-- The prime-free parts of every scale: 2, 3 and 5, and the two factors of the
astronomical unit's and the electronvolt's values that are left when 2, 3 and 5 are
divided out. Every factor of the catalogue is a product of their powers
(`catalogue_factors_atoms`), and no two of them share a factor (`atoms_coprime`), so the
powers with a positive exponent over those with a negative one are a fraction in lowest
terms. -/
def atoms : List Nat := [2, 3, 5, 498659569, 89009813]

/-- How many times `a` divides `n`, and what is left, in at most `fuel` divisions. -/
def divideOut (a : Nat) : Nat → Nat → Nat × Nat
  | 0, n => (0, n)
  | fuel + 1, n =>
    if 1 < a && n != 0 && n % a == 0 then
      let (k, r) := divideOut a fuel (n / a)
      (k + 1, r)
    else (0, n)

/-- A whole number's exponents over `atoms`, when it is a product of their powers: each
divided out in turn, no more often than the number has bits. -/
def atomExps? (n : Nat) : Option (List Int) :=
  let (ks, rest) := atoms.foldl (fun (acc : List Int × Nat) a =>
    let (k, r) := divideOut a (Nat.log2 acc.2 + 1) acc.2
    (acc.1 ++ [(k : Int)], r)) ([], n)
  if rest = 1 then some ks else none

/-- Exponents over `atoms`, added. -/
def addExps (a b : List Int) : List Int := List.zipWith (· + ·) a b

/-- Exponents over `atoms`, multiplied by `k`. -/
def scaleExps (k : Int) (a : List Int) : List Int := a.map (k * ·)

/-- The exponents of one. -/
def noExps : List Int := atoms.map fun _ => 0

/-- The exponents of ten. -/
def tenExps : List Int := [1, 0, 1, 0, 0]

/-- A symbol's factor over `atoms`: its exponents, and its power of π. -/
def Factor.exps : Factor → List Int × Int
  | .dec m e => (addExps ((atomExps? m).getD noExps) (scaleExps e tenExps), 0)
  | .piOver n => (scaleExps (-1) ((atomExps? n).getD noExps), 1)

/-- A merged token's factor over `atoms`, the prefix's power of ten times the symbol's
factor, raised to the token's exponent. -/
def tokenExps (t : Reading × Int) : List Int × Int :=
  let (fs, p) := (symbolAt t.1.sym).factor.exps
  (scaleExps t.2 (addExps (scaleExps t.1.power tenExps) fs), p * t.2)

/-- The powers of `atoms` of the given exponents, and of π, unevaluated and in lowest
terms. -/
def ofExps (es : List Int) (pi : Int) : Exact.Product :=
  { num := (atoms.zip es).filterMap fun (a, k) => if 0 < k then some (a, k.toNat) else none,
    den := (atoms.zip es).filterMap fun (a, k) => if k < 0 then some (a, (-k).toNat) else none,
    pi := pi }

/-- The scale of merged tokens to coherent SI, unevaluated: per token, the prefix's power
of ten times the symbol's factor, raised to the token's exponent; the product over the
tokens, its exponents over `atoms` added first, so that the scale is held in lowest terms
and no larger number is ever formed. Exact, so neither the order of the product nor the
size of a partial product matters (v1 multiplied doubles in canonical order, and refused
a partial product that left the range). -/
def scaleProduct (items : List (Reading × Int)) : Exact.Product :=
  let (es, pi) := items.foldl (fun (acc : List Int × Int) t =>
    let (fs, p) := tokenExps t
    (addExps acc.1 fs, acc.2 + p)) (noExps, 0)
  ofExps es pi

/-- No two of `atoms` share a factor. -/
theorem atoms_coprime : atoms.Pairwise (fun a b => Nat.gcd a b = 1) := by decide

/-- Every factor of the catalogue is a product of powers of `atoms`. -/
theorem catalogue_factors_atoms :
    catalogue.all (fun s => match s.factor with
      | .dec m _ => (atomExps? m).isSome
      | .piOver n => (atomExps? n).isSome) = true := by decide +kernel

/-- Each of the 807 token strings, at exponent 1, has the scale its prefix's power of ten
times its symbol's factor gives: the factors over `atoms` are the catalogue's. -/
theorem readings_scale :
    allReadings.all (fun r => (scaleProduct [(r, 1)]).value ==
      ((Exact.Product.ten r.power).mul (symbolAt r.sym).factor.product).value) = true := by
  decide +kernel

/-- The scale of merged tokens, evaluated. -/
def scaleOf (items : List (Reading × Int)) : Exact := (scaleProduct items).value

/-- A decimal's absolute value, unevaluated: its digits times a power of ten. -/
def decimalProduct (p : Decimal.Parts) : Exact.Product :=
  (Exact.Product.nat (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0)).mul
    (Exact.Product.ten (p.ex - p.fp.length))

/-! ## Escaping a reason -/

/-- v1's `_disallowed`, the zones' (`Principia.Zone.disallowed`): every code point of
Unicode general category C but TAB and LF, and U+2028 and U+2029, at Unicode 15.1.0
(the Declarer's choice of Unicode version). -/
def escapes (c : Char) : Bool := Zone.disallowed c

/-- Four or more upper-case hexadecimal digits (`%04X`). -/
def hex4 (n : Nat) : String :=
  let ds := (Nat.toDigits 16 n).map Char.toUpper
  String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

/-- A reason with every escaped code point written `<U+XXXX>` (v1's `_show`). -/
def escape (msg : String) : String :=
  String.join (msg.toList.map fun c =>
    if escapes c then "<U+" ++ hex4 c.toNat ++ ">" else c.toString)

/-! ## The four functions -/

/-- A UNIT read: its canonical spelling, its canonical DIMENSION and its KIND. -/
structure ParsedUnit where
  spelling : String
  dimension : String
  kind : String
  deriving DecidableEq, Repr

/-- A measurement normalized to coherent SI: the value, its uncertainty, the DIMENSION
and the KIND. -/
structure Measurement where
  x : Exact
  u : Exact
  dimension : String
  kind : String
  deriving DecidableEq, Repr

/-- An argument as JSON gives it: a string, or `none` for any other value, which a reason
quotes as `?` (v1's `_q`). -/
abbrev Arg := Option String

/-- The tokens of a UNIT argument. -/
def tokensOf : Arg → Except String (List (Reading × Int))
  | some u => tokens u
  | none => .error "UNIT ? is not a unit"

/-- `unit_parse`: the canonical spelling, DIMENSION and KIND of a UNIT. -/
def unitParseArg (u : Arg) : Except String ParsedUnit :=
  match tokensOf u with
  | .error r => .error (escape r)
  | .ok items =>
    .ok { spelling := spelling items, dimension := Dimension.canon (dimExps items),
          kind := kind items }

/-- `unit_scale`'s checks, in v1's order: the UNIT reads, and its scale is neither zero
nor infinite as a double; the scale is given unevaluated. -/
def scaleChecks (u : Arg) : Except String Exact.Product :=
  match tokensOf u with
  | .error r => .error (escape r)
  | .ok items =>
    let f := scaleProduct items
    if f.range == .inside then .ok f
    else .error (escape s!"UNIT {u.getD "?"} has no finite scale")

/-- `unit_scale`: the factor from a UNIT to coherent SI, exact. A scale that is zero or
infinite as a double is refused, as v1 refuses it. -/
def unitScaleArg (u : Arg) : Except String Exact :=
  (scaleChecks u).map Exact.Product.value

/-- `unit_matches`, C-32: whether a UNIT is commensurable with a DIMENSION. A UNIT that
does not read is refused first. -/
def unitMatchesArg (u d : Arg) : Except String Bool :=
  match unitParseArg u with
  | .error r => .error r
  | .ok p =>
    match d with
    | none => .error (escape "DIMENSION ? is not a dimension")
    | some d =>
      match Dimension.normalize d with
      | some c => .ok (p.dimension == c)
      | none =>
        if Dimension.outOfRange d then
          .error (escape s!"DIMENSION {d}: an exponent is out of range")
        else .error (escape s!"DIMENSION {d} is not a dimension")

/-- What `normalize_measurement`'s checks leave: the value and the uncertainty, exact,
the merged tokens, and the scale, unevaluated. -/
structure Checked where
  x : Rat
  u : Rat
  items : List (Reading × Int)
  scale : Exact.Product

/-- `normalize_measurement`'s checks, in v1's order: VALUE, UNCERTAINTY, its sign, UNIT,
the scale (zero or infinite as a double), then the scaled values (infinite as a double;
a value too small for a double is kept, exact, where v1 made it zero). -/
def normalizeChecks (v unc u : Arg) : Except String Checked :=
  let parts (a : Arg) := a.bind fun s => Decimal.readParts s.toList
  match parts v, parts unc, v.bind Decimal.value, unc.bind Decimal.value with
  | some pv, some pu, some x, some su =>
    if su < 0 then .error (escape s!"UNCERTAINTY {unc.getD "?"} is negative")
    else
      match tokensOf u with
      | .error r => .error (escape r)
      | .ok items =>
        let uName := u.getD "?"
        let f := scaleProduct items
        if f.range != .inside then .error (escape s!"UNIT {uName} has no finite scale")
        else if (f.mul (decimalProduct pv)).range == .infinite ||
            (f.mul (decimalProduct pu)).range == .infinite then
          .error (escape s!"VALUE {v.getD "?"} in UNIT {uName} is not a finite double")
        else .ok { x := x, u := su, items := items, scale := f }
  | none, _, _, _ | _, _, none, _ => .error (escape s!"VALUE {v.getD "?"} is not a decimal")
  | _, _, _, _ => .error (escape s!"UNCERTAINTY {unc.getD "?"} is not a decimal")

/-- The measurement the checks passed: the value and the uncertainty times the scale, the
DIMENSION and the KIND. -/
def Checked.measurement (c : Checked) : Measurement :=
  let fe := c.scale.value
  { x := fe.scale c.x, u := fe.scale c.u, dimension := Dimension.canon (dimExps c.items),
    kind := kind c.items }

/-- `normalize_measurement`: a VALUE and its UNCERTAINTY, decimal strings, in a UNIT,
scaled to coherent SI, once `normalizeChecks` has passed them. -/
def normalizeMeasurementArg (v unc u : Arg) : Except String Measurement :=
  (normalizeChecks v unc u).map Checked.measurement

/-- `unit_parse` of a string. -/
def unitParse (u : String) : Except String ParsedUnit := unitParseArg (some u)

/-- `unit_scale` of a string. -/
def unitScale (u : String) : Except String Exact := unitScaleArg (some u)

/-- `unit_matches` of two strings. -/
def unitMatches (u d : String) : Except String Bool := unitMatchesArg (some u) (some d)

/-- `normalize_measurement` of three strings. -/
def normalizeMeasurement (v unc u : String) : Except String Measurement :=
  normalizeMeasurementArg (some v) (some unc) (some u)

/-! ## Results as v1 wrote them

v1 returned a list, `["OK", ...]` or `["REFUSED", reason]`, and compared results through
its canonical form: the items joined by commas, in brackets. Numbers here are exact
(`Exact.render`), where v1 printed a double to twelve significant digits. -/

/-- A result in v1's bracket form. -/
def bracket {α : Type} (items : α → List String) : Except String α → String
  | .ok a => "[" ++ ",".intercalate ("OK" :: items a) ++ "]"
  | .error r => "[REFUSED," ++ r ++ "]"

/-- A read UNIT's items. -/
def ParsedUnit.items (p : ParsedUnit) : List String := [p.spelling, p.dimension, p.kind]

/-- A normalized measurement's items. -/
def Measurement.items (m : Measurement) : List String :=
  [m.x.render, m.u.render, m.dimension, m.kind]

end Principia.Units
