import Principia.Unicode.Tables

/-!
# Unicode: NFC, NFD and the general category, at Unicode 15.1.0

The Declarer's choice of Unicode version: text is normalized as version 1 normalizes
it, with `unicodedata.normalize("NFC", ...)` at Unicode 15.1.0, the version of version 1's
Python, and a code point's general category is version 1's `unicodedata.category`. Both read
`Principia.Unicode.Tables`, which a generator script writes from Unicode's own
data files (kept with the vectors); each table is a text parsed once, when first used.

The normalization is the Unicode Standard's (chapter 3, sections 3.11 and 3.12; Unicode Standard Annex 15):

* `decompose`: each code point's full canonical decomposition, a Hangul syllable's by
  Unicode's arithmetic and every other from the table;
* `reorder`, the canonical ordering: each run of non-starters (canonical combining class not
  0) sorted stably by class, the starters left where they are;
* `compose`, for NFC, the canonical composition: each code point composed with the last
  starter before it when nothing between them blocks it and the pair has a primary
  composite, a Hangul syllable's by arithmetic and every other from the table, which leaves
  out the code points excluded from composition (Full_Composition_Exclusion).

Each lookup first compares the code point with the least code point its table reaches (the
generator writes these floors): ASCII and Latin-1 up to U+00BF never reach a table.

Lean proves that the canonical ordering is a permutation that leaves every run of
non-starters in increasing order of class (`reorder_perm`, `reorder_ordered`, so NFD's
result is canonically ordered, `nfd_ordered`), that NFC and NFD leave ASCII text, and every
text below U+00C0, unchanged (`nfc_ascii`, `nfd_ascii`), and that every Hangul syllable
composes back from its parts (`hangul_compose_lv`, `hangul_compose_lvt`). the Unicode test runner runs all of
Unicode 15.1.0's normalization test data and compares the general category, the combining
class and the decomposition of every code point with Unicode's character database.
-/

namespace Principia.Unicode

open Tables

/-! ## Reading the tables -/

/-- An upper-case hexadecimal numeral's value; `none` when it is empty or holds another
character. -/
def hexValue? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c && c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
    else none) (some 0)

/-- `START-END` or `CP`: the first and last code point. -/
def span? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "-" with
  | [a] => (hexValue? a).map fun n => (n, n)
  | [a, b] => do pure ((← hexValue? a), (← hexValue? b))
  | _ => none

/-- A table text's items, each read by `f`. An item that does not read is dropped;
the Unicode test runner checks that none is, each table's count being the generator's. -/
def items {α : Type} (text : String) (f : String → Option α) : Array α :=
  ((text.splitOn ";").filterMap f).toArray

/-- The entry of `arr` whose range `[lo x, hi x]` holds `n`, by binary search over ranges
that are disjoint and in increasing order (the Unicode test runner checks each table's). -/
def search {β : Type} (arr : Array β) (lo hi : β → Nat) (n : Nat) : Option β :=
  go 0 arr.size
where
  go (a b : Nat) : Option β :=
    if _h : a < b then
      match arr[(a + b) / 2]? with
      | none => none
      | some x =>
        if n < lo x then go a ((a + b) / 2)
        else if hi x < n then go ((a + b) / 2 + 1) b
        else some x
    else none
  termination_by b - a
  decreasing_by all_goals omega

/-! ## The general category -/

/-- Unicode's 30 general categories (Unicode Standard Annex 44, section 5.7.1). -/
inductive GeneralCategory where
  | lu | ll | lt | lm | lo
  | mn | mc | me
  | nd | nl | no
  | pc | pd | ps | pe | pi | pf | po
  | sm | sc | sk | so
  | zs | zl | zp
  | cc | cf | cs | co | cn
  deriving DecidableEq, Repr, Inhabited

namespace GeneralCategory

/-- The category's two-letter code, as Unicode's character database and `unicodedata.category` write it. -/
def code : GeneralCategory → String
  | .lu => "Lu" | .ll => "Ll" | .lt => "Lt" | .lm => "Lm" | .lo => "Lo"
  | .mn => "Mn" | .mc => "Mc" | .me => "Me"
  | .nd => "Nd" | .nl => "Nl" | .no => "No"
  | .pc => "Pc" | .pd => "Pd" | .ps => "Ps" | .pe => "Pe" | .pi => "Pi" | .pf => "Pf"
  | .po => "Po"
  | .sm => "Sm" | .sc => "Sc" | .sk => "Sk" | .so => "So"
  | .zs => "Zs" | .zl => "Zl" | .zp => "Zp"
  | .cc => "Cc" | .cf => "Cf" | .cs => "Cs" | .co => "Co" | .cn => "Cn"

/-- Every category, in the order of Unicode Standard Annex 44. -/
def all : List GeneralCategory :=
  [.lu, .ll, .lt, .lm, .lo, .mn, .mc, .me, .nd, .nl, .no, .pc, .pd, .ps, .pe, .pi, .pf, .po,
   .sm, .sc, .sk, .so, .zs, .zl, .zp, .cc, .cf, .cs, .co, .cn]

/-- The category a two-letter code names. -/
def ofCode? (s : String) : Option GeneralCategory := all.find? (·.code == s)

/-- The major class, the code's first letter: L, M, N, P, S, Z or C. -/
def major : GeneralCategory → Char
  | .lu | .ll | .lt | .lm | .lo => 'L'
  | .mn | .mc | .me => 'M'
  | .nd | .nl | .no => 'N'
  | .pc | .pd | .ps | .pe | .pi | .pf | .po => 'P'
  | .sm | .sc | .sk | .so => 'S'
  | .zs | .zl | .zp => 'Z'
  | .cc | .cf | .cs | .co | .cn => 'C'

/-- Each code reads back to its category. -/
theorem ofCode?_code (g : GeneralCategory) : ofCode? g.code = some g := by
  cases g <;> decide

/-- The major class is the code's first letter, as version 1 reads it (`category(ch)[0]`). -/
theorem major_code (g : GeneralCategory) : g.code.toList.head? = some g.major := by
  cases g <;> decide

end GeneralCategory

/-- `generalCategoryText` read: `(first, last, category)`, in increasing order. -/
def categoryRuns : Array (Nat × Nat × GeneralCategory) :=
  items generalCategoryText fun s =>
    match s.splitOn ":" with
    | [r, g] => do let (a, b) ← span? r; pure (a, b, ← GeneralCategory.ofCode? g)
    | _ => none

/-- The general category of a code point; Cn (unassigned) where no run holds it, past
U+10FFFF too. Surrogates, which no `Char` is, are Cs. -/
def generalCategoryOf (n : Nat) : GeneralCategory :=
  match search categoryRuns (·.1) (·.2.1) n with
  | some (_, _, g) => g
  | none => .cn

/-- v1's `unicodedata.category`. -/
def generalCategory (c : Char) : GeneralCategory := generalCategoryOf c.toNat

/-! ## The canonical combining class -/

/-- `combiningClassText` read: `(first, last, class)`, in increasing order. -/
def combiningRuns : Array (Nat × Nat × Nat) :=
  items combiningClassText fun s =>
    match s.splitOn ":" with
    | [r, k] => do let (a, b) ← span? r; pure (a, b, ← k.toNat?)
    | _ => none

/-- The canonical combining class (v1's `unicodedata.combining`); 0 below the table's floor. -/
def combiningClass (c : Char) : Nat :=
  if c.toNat < combiningFloor then 0
  else match search combiningRuns (·.1) (·.2.1) c.toNat with
    | some (_, _, k) => k
    | none => 0

/-- A non-starter: its canonical combining class is not 0. -/
def nonStarter (c : Char) : Bool := combiningClass c != 0

/-! ## Hangul (the Unicode Standard, section 3.12) -/

def sBase : Nat := 0xAC00
def lBase : Nat := 0x1100
def vBase : Nat := 0x1161
def tBase : Nat := 0x11A7
def lCount : Nat := 19
def vCount : Nat := 21
def tCount : Nat := 28
/-- `vCount * tCount`. -/
def nCount : Nat := 588
/-- `lCount * nCount`. -/
def sCount : Nat := 11172

/-- A precomposed Hangul syllable. -/
def syllable (s : Nat) : Bool := sBase ≤ s && s < sBase + sCount

/-- A syllable's canonical decomposition: its leading consonant and vowel, and its trailing
consonant when it has one. -/
def hangulParts (s : Nat) : List Nat :=
  let i := s - sBase
  let l := lBase + i / nCount
  let v := vBase + i % nCount / tCount
  if i % tCount = 0 then [l, v] else [l, v, tBase + i % tCount]

/-- A pair's Hangul composite: a leading consonant and a vowel, or a syllable without a
trailing consonant and a trailing consonant. -/
def hangulPair? (a b : Nat) : Option Nat :=
  if lBase ≤ a ∧ a < lBase + lCount ∧ vBase ≤ b ∧ b < vBase + vCount then
    some (sBase + ((a - lBase) * vCount + (b - vBase)) * tCount)
  else if sBase ≤ a ∧ a < sBase + sCount ∧ (a - sBase) % tCount = 0 ∧ tBase < b ∧
      b < tBase + tCount then
    some (a + (b - tBase))
  else none

/-- A syllable without a trailing consonant decomposes into its leading consonant and its
vowel, and they compose back into it. -/
theorem hangul_compose_lv (s : Nat) (h₁ : sBase ≤ s) (h₂ : s < sBase + sCount)
    (h : (s - sBase) % tCount = 0) :
    hangulParts s = [lBase + (s - sBase) / nCount, vBase + (s - sBase) % nCount / tCount] ∧
    hangulPair? (lBase + (s - sBase) / nCount) (vBase + (s - sBase) % nCount / tCount) =
      some s := by
  unfold hangulPair? hangulParts
  unfold sBase lBase vBase tBase lCount vCount tCount nCount sCount at *
  refine ⟨by simp [h], ?_⟩
  rw [ite_eq_left (by omega)]
  apply congrArg some
  omega

/-- A syllable with a trailing consonant decomposes into three parts, and they compose back
into it: the vowel onto the leading consonant, then the trailing consonant onto that. -/
theorem hangul_compose_lvt (s : Nat) (h₁ : sBase ≤ s) (h₂ : s < sBase + sCount)
    (h : (s - sBase) % tCount ≠ 0) :
    hangulParts s = [lBase + (s - sBase) / nCount, vBase + (s - sBase) % nCount / tCount,
      tBase + (s - sBase) % tCount] ∧
    (hangulPair? (lBase + (s - sBase) / nCount) (vBase + (s - sBase) % nCount / tCount)).bind
      (hangulPair? · (tBase + (s - sBase) % tCount)) = some s := by
  unfold hangulPair? hangulParts
  unfold sBase lBase vBase tBase lCount vCount tCount nCount sCount at *
  refine ⟨by simp [h], ?_⟩
  rw [ite_eq_left (by omega), Option.bind_some, ite_eq_right (by omega), ite_eq_left (by omega)]
  apply congrArg some
  omega

/-! ## Decomposition -/

/-- An item of `decompositionText`: a code point, a colon, then the code points of its
decomposition. -/
def decompositionItem? (s : String) : Option (Nat × List Char) :=
  match s.splitOn ":" with
  | [c, ds] => do
    let n ← hexValue? c
    let xs ← (ds.splitOn " ").mapM hexValue?
    pure (n, xs.map Char.ofNat)
  | _ => none

/-- `decompositionText` read: each code point and its full canonical decomposition, in
increasing order of code point. -/
def decompositions : Array (Nat × List Char) := items decompositionText decompositionItem?

/-- A code point's full canonical decomposition: itself when it has none. -/
def decompose (c : Char) : List Char :=
  let n := c.toNat
  if n < decompositionFloor then [c]
  else if syllable n then (hangulParts n).map Char.ofNat
  else match search decompositions (·.1) (·.1) n with
    | some (_, ds) => ds
    | none => [c]

/-! ## The canonical ordering -/

/-- A run of non-starters sorted by class; `mergeSort` is stable, so equal classes keep
their order. -/
def sortRun (run : List Char) : List Char :=
  run.mergeSort fun a b => decide (combiningClass a ≤ combiningClass b)

/-- The canonical ordering: each maximal run of non-starters sorted by class. -/
def reorder : List Char → List Char
  | [] => []
  | c :: cs =>
    if nonStarter c then
      sortRun (c :: cs.takeWhile nonStarter) ++ reorder (cs.dropWhile nonStarter)
    else c :: reorder cs
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_cons]
  · have := (List.dropWhile_suffix nonStarter (l := cs)).length_le
    omega
  · omega

/-- Canonically ordered: no non-starter follows a code point of greater class. -/
def canonicallyOrdered : List Char → Bool
  | a :: b :: rest =>
    (combiningClass b == 0 || decide (combiningClass a ≤ combiningClass b)) &&
      canonicallyOrdered (b :: rest)
  | _ => true

/-! ## Composition -/

/-- An item `FIRST SECOND:COMPOSITE` of `compositionText`, keyed by the pair. -/
def compositionItem? (s : String) : Option (Nat × Char) :=
  match s.splitOn ":" with
  | [ab, c] =>
    match ab.splitOn " " with
    | [a, b] => do
      let a ← hexValue? a
      let b ← hexValue? b
      let c ← hexValue? c
      pure (a * 0x110000 + b, Char.ofNat c)
    | _ => none
  | _ => none

/-- `compositionText` read: each pair's key, `first * 0x110000 + second`, and its primary
composite, in increasing order of key. -/
def compositions : Array (Nat × Char) := items compositionText compositionItem?

/-- The primary composite of a pair, if it has one. -/
def composePair? (a b : Char) : Option Char :=
  if b.toNat < compositionSecondFloor then none
  else match hangulPair? a.toNat b.toNat with
    | some n => some (Char.ofNat n)
    | none => (search compositions (·.1) (·.1) (a.toNat * 0x110000 + b.toNat)).map (·.2)

/-- The canonical composition's state: the text before the last starter (reversed), the
last starter as composed so far, and what follows it, not composed (reversed). -/
structure Composing where
  done : List Char := []
  starter : Option Char := none
  after : List Char := []

/-- The text the state stands for. -/
def Composing.text (st : Composing) : List Char :=
  st.done.reverse ++ st.starter.toList ++ st.after.reverse

/-- A code point that does not compose is appended: a starter becomes the last starter. -/
def Composing.push (st : Composing) (c : Char) : Composing :=
  if combiningClass c = 0 then
    { done := st.after ++ st.starter.toList ++ st.done, starter := some c, after := [] }
  else { st with after := c :: st.after }

/-- One code point: composed with the last starter when nothing between them blocks it (a
starter, or a code point of the same or a greater class) and the pair has a primary
composite; appended otherwise. -/
def Composing.step (st : Composing) (c : Char) : Composing :=
  let free := match st.after with
    | [] => true
    | b :: _ => decide (combiningClass b < combiningClass c)
  match st.starter with
  | some s =>
    match (if free then composePair? s c else none) with
    | some x => { st with starter := some x }
    | none => st.push c
  | none => st.push c

/-- The canonical composition of a canonically ordered decomposition. -/
def compose (l : List Char) : List Char := (l.foldl Composing.step {}).text

/-! ## NFD and NFC -/

/-- NFD of a sequence of code points. -/
def nfdList (l : List Char) : List Char := reorder (l.flatMap decompose)

/-- NFC of a sequence of code points. -/
def nfcList (l : List Char) : List Char := compose (nfdList l)

/-- v1's `unicodedata.normalize("NFD", s)`. -/
def nfd (s : String) : String := String.ofList (nfdList s.toList)

/-- v1's `unicodedata.normalize("NFC", s)`. -/
def nfc (s : String) : String := String.ofList (nfcList s.toList)

/-- v1's `unicodedata.is_normalized("NFC", s)`. -/
def isNfc (s : String) : Bool := nfc s == s

/-! ## What Lean proves -/

/-- Below its floor no code point decomposes. -/
theorem decompose_of_lt {c : Char} (h : c.toNat < decompositionFloor) : decompose c = [c] := by
  simp [decompose, h]

/-- Below its floor every code point is a starter. -/
theorem combiningClass_of_lt {c : Char} (h : c.toNat < combiningFloor) :
    combiningClass c = 0 := by
  simp [combiningClass, h]

/-- Below its floor no code point is the second of a composition. -/
theorem composePair?_of_lt {a b : Char} (h : b.toNat < compositionSecondFloor) :
    composePair? a b = none := by
  simp [composePair?, h]

/-- A sorted run is a permutation of the run. -/
theorem sortRun_perm (run : List Char) : (sortRun run).Perm run :=
  List.mergeSort_perm _ _

/-- A sorted run is in increasing order of class, each code point with each after it. -/
theorem sortRun_pairwise (run : List Char) :
    (sortRun run).Pairwise fun a b => decide (combiningClass a ≤ combiningClass b) = true :=
  List.pairwise_mergeSort
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The canonical ordering only moves code points: it is a permutation. -/
theorem reorder_perm (l : List Char) : (reorder l).Perm l := by
  induction l using reorder.induct with
  | case1 => simp [reorder]
  | case2 c cs h ih =>
    rw [reorder, ite_eq_left h]
    have hs := sortRun_perm (c :: cs.takeWhile nonStarter)
    have e : c :: cs = (c :: cs.takeWhile nonStarter) ++ cs.dropWhile nonStarter := by
      simp
    rw [e]
    exact List.Perm.append hs ih
  | case3 c cs h ih =>
    rw [reorder, ite_eq_right h]
    exact List.Perm.cons c ih

/-- In increasing order pairwise, a list is canonically ordered. -/
theorem canonicallyOrdered_of_pairwise {l : List Char}
    (h : l.Pairwise fun a b => decide (combiningClass a ≤ combiningClass b) = true) :
    canonicallyOrdered l = true := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    match rest, h, ih with
    | [], _, _ => rfl
    | b :: rest, h, ih =>
      rw [List.pairwise_cons] at h
      simp only [canonicallyOrdered, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inr (h.1 b (List.mem_cons_self ..)), ih h.2⟩

/-- A canonically ordered list followed by one that starts with a starter is canonically
ordered. -/
theorem canonicallyOrdered_append {l₁ l₂ : List Char} (h₁ : canonicallyOrdered l₁ = true)
    (h₂ : canonicallyOrdered l₂ = true) (hd : ∀ d ∈ l₂.head?, combiningClass d = 0) :
    canonicallyOrdered (l₁ ++ l₂) = true := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a rest ih =>
    match rest, h₁, ih with
    | [], _, _ =>
      match l₂, h₂, hd with
      | [], _, _ => rfl
      | d :: ds, h₂, hd =>
        have : combiningClass d = 0 := hd d rfl
        simp only [List.cons_append, List.nil_append, canonicallyOrdered, Bool.and_eq_true,
          Bool.or_eq_true, beq_iff_eq]
        exact ⟨Or.inl this, h₂⟩
    | b :: rest, h₁, ih =>
      simp only [canonicallyOrdered, Bool.and_eq_true] at h₁
      simp only [List.cons_append, canonicallyOrdered, Bool.and_eq_true] at ih ⊢
      exact ⟨h₁.1, ih h₁.2⟩

/-- A starter followed by a canonically ordered list is canonically ordered. -/
theorem canonicallyOrdered_cons_starter {c : Char} {l : List Char} (hc : combiningClass c = 0)
    (h : canonicallyOrdered l = true) : canonicallyOrdered (c :: l) = true := by
  match l, h with
  | [], _ => rfl
  | b :: rest, h =>
    simp only [canonicallyOrdered, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq, hc, Nat.zero_le, or_true, true_and]
    exact h

/-- The canonical ordering's result starts with the input's first code point when that is a
starter, and with a non-starter only when the input does. -/
theorem reorder_head (l : List Char) (h : ∀ d ∈ l.head?, combiningClass d = 0) :
    ∀ d ∈ (reorder l).head?, combiningClass d = 0 := by
  match l, h with
  | [], _ => simp [reorder]
  | c :: cs, h =>
    have hc : combiningClass c = 0 := h c rfl
    have hn : nonStarter c = false := by simp [nonStarter, hc]
    rw [reorder, ite_eq_right (by simp [hn])]
    intro d hd
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
    exact hd ▸ hc

/-- What follows a run of non-starters starts with a starter. -/
theorem dropWhile_head (cs : List Char) :
    ∀ d ∈ (cs.dropWhile nonStarter).head?, combiningClass d = 0 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    by_cases h : nonStarter c = true
    · rw [List.dropWhile_cons_of_pos h]; exact ih
    · rw [List.dropWhile_cons_of_neg h]
      intro d hd
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
      subst hd
      simpa [nonStarter] using h

/-- The canonical ordering leaves every run of non-starters in increasing order of class. -/
theorem reorder_ordered (l : List Char) : canonicallyOrdered (reorder l) = true := by
  induction l using reorder.induct with
  | case1 => simp [reorder, canonicallyOrdered]
  | case2 c cs h ih =>
    rw [reorder, ite_eq_left h]
    exact canonicallyOrdered_append (canonicallyOrdered_of_pairwise (sortRun_pairwise _)) ih
      (reorder_head _ (dropWhile_head cs))
  | case3 c cs h ih =>
    rw [reorder, ite_eq_right h]
    have hc : combiningClass c = 0 := by simpa [nonStarter] using h
    exact canonicallyOrdered_cons_starter hc ih

/-- NFD's result is canonically ordered. -/
theorem nfd_ordered (s : String) : canonicallyOrdered (nfd s).toList = true := by
  rw [nfd, String.toList_ofList, nfdList]
  exact reorder_ordered _

/-- NFD's result is a permutation of the full decomposition of its input. -/
theorem nfdList_perm (l : List Char) : (nfdList l).Perm (l.flatMap decompose) :=
  reorder_perm _

/-- Code points that do not decompose decompose to themselves, as a sequence. -/
theorem flatMap_decompose {l : List Char} (h : ∀ c ∈ l, c.toNat < decompositionFloor) :
    l.flatMap decompose = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, decompose_of_lt (h c (List.mem_cons_self ..)),
      ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    rfl

/-- A sequence of starters is canonically ordered as it stands. -/
theorem reorder_starters {l : List Char} (h : ∀ c ∈ l, combiningClass c = 0) :
    reorder l = l := by
  induction l with
  | nil => simp [reorder]
  | cons c cs ih =>
    have hc : nonStarter c = false := by simp [nonStarter, h c (List.mem_cons_self ..)]
    rw [reorder, ite_eq_right (by simp [hc]), ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]

/-- A code point that does not compose is appended to the text. -/
theorem Composing.text_push (st : Composing) (c : Char) :
    (st.push c).text = st.text ++ [c] := by
  unfold Composing.push Composing.text
  split
  · cases st.starter <;> simp
  · simp

/-- Code points none of which is ever the second of a composition compose to themselves. -/
theorem foldl_step {l : List Char} (h : ∀ c ∈ l, ∀ s, composePair? s c = none)
    (st : Composing) : (l.foldl Composing.step st).text = st.text ++ l := by
  induction l generalizing st with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    have hc := h c (List.mem_cons_self ..)
    have e : Composing.step st c = st.push c := by
      unfold Composing.step
      cases st.starter <;> simp [hc]
    rw [e, Composing.text_push]
    simp

/-- The canonical composition leaves a sequence none of whose code points is ever the
second of a composition as it is. -/
theorem compose_of_never_second {l : List Char} (h : ∀ c ∈ l, ∀ s, composePair? s c = none) :
    compose l = l := by
  rw [compose, foldl_step h]
  rfl

/-- NFD leaves text below U+00C0 unchanged, ASCII among it. -/
theorem nfdList_of_lt {l : List Char} (h : ∀ c ∈ l, c.toNat < 0xC0) : nfdList l = l := by
  have hd : ∀ c ∈ l, c.toNat < decompositionFloor := fun c hc => by
    have := h c hc; unfold decompositionFloor; omega
  rw [nfdList, flatMap_decompose hd]
  exact reorder_starters fun c hc => combiningClass_of_lt (by
    have := h c hc; unfold combiningFloor; omega)

/-- NFC leaves text below U+00C0 unchanged, ASCII among it. -/
theorem nfcList_of_lt {l : List Char} (h : ∀ c ∈ l, c.toNat < 0xC0) : nfcList l = l := by
  rw [nfcList, nfdList_of_lt h]
  exact compose_of_never_second fun c hc _ => composePair?_of_lt (by
    have := h c hc; unfold compositionSecondFloor; omega)

/-- NFD of ASCII text is the text. -/
theorem nfd_ascii {s : String} (h : ∀ c ∈ s.toList, c.toNat < 0x80) : nfd s = s := by
  rw [nfd, nfdList_of_lt (fun c hc => by have := h c hc; omega), String.ofList_toList]

/-- NFC of ASCII text is the text. -/
theorem nfc_ascii {s : String} (h : ∀ c ∈ s.toList, c.toNat < 0x80) : nfc s = s := by
  rw [nfc, nfcList_of_lt (fun c hc => by have := h c hc; omega), String.ofList_toList]

/-- ASCII text is in NFC. -/
theorem isNfc_ascii {s : String} (h : ∀ c ∈ s.toList, c.toNat < 0x80) : isNfc s = true := by
  simp [isNfc, nfc_ascii h]

end Principia.Unicode
