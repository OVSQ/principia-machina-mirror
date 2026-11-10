/-!
# Dimensions

A DIMENSION is a product of powers of the seven base dimensions, written as tokens
`<BASE><exponent>` separated by single spaces, or `1` for none (zone schemas 5.5; v1's
tpc_zone 0.4.1: `DIM_BASES`, `canon_dimension`, `normalize_dimension`,
`dimension_out_of_range`, `is_canonical_dimension`).

- Accepted: `1`, or tokens over the bases L M T I TH N J in any order, separated by single
  spaces; a base may repeat (its exponents add); an exponent is an optional minus sign and
  one to four ASCII digits, zero and leading zeros allowed.
- Canonical: the bases in that order, each at most once, no zero exponent, no leading
  zero, `1` when none remain. `T-1 L1` is `L1 T-1`; `L1 L-1` is `1`.
- S15: a DIMENSION whose summed exponent for a base leaves -9999..9999 is refused, never
  altered: its canonical token would leave the grammar (`L9999 L1` would be `L10000`).

The reading works on the string's characters, so the theorems at the end can speak about
it: the canonical form reads back to the exponents it was made from, normalization is
idempotent, and what it returns is canonical. These are the PROVED rows of the canonical
form.
-/

namespace Principia.Dimension

/-- The seven base dimensions, in canonical order: length, mass, time, electric current,
thermodynamic temperature, amount of substance, luminous intensity. -/
inductive Base where
  | L | M | T | I | TH | N | J
  deriving DecidableEq, Repr

namespace Base

/-- Every base, in canonical order (v1's `DIM_BASES`). -/
def all : List Base := [L, M, T, I, TH, N, J]

/-- A base's position in the canonical order. -/
def index : Base → Nat
  | L => 0 | M => 1 | T => 2 | I => 3 | TH => 4 | N => 5 | J => 6

/-- A base's spelling. -/
def spell : Base → List Char
  | L => ['L'] | M => ['M'] | T => ['T'] | I => ['I'] | TH => ['T', 'H'] | N => ['N']
  | J => ['J']

theorem mem_all (b : Base) : b ∈ all := by cases b <;> decide

end Base

/-- An exponent for every base. -/
abbrev Exponents := Base → Int

/-- The bound on every exponent of a DIMENSION (S15): four digits. -/
def expMax : Nat := 9999

/-- Every exponent within -9999..9999. -/
def inRange (e : Exponents) : Bool :=
  Base.all.all fun b => decide ((e b).natAbs ≤ expMax)

/-! ## Spelling and reading exponents -/

/-- An exponent's decimal spelling: a minus sign when negative, then the digits of its
absolute value with no leading zero (Python's `str` of an `int`). -/
def expChars (n : Int) : List Char :=
  if n < 0 then '-' :: Nat.toDigits 10 n.natAbs else Nat.toDigits 10 n.natAbs

/-- One to four ASCII digits, read as a number (`[0-9]{1,4}`). -/
def readDigits (ds : List Char) : Option Nat :=
  if ds ≠ [] ∧ ds.length ≤ 4 ∧ ds.all Char.isDigit = true then
    some (Nat.ofDigitChars 10 ds 0)
  else none

/-- An exponent: an optional minus sign, then one to four ASCII digits
(`-?[0-9]{1,4}`). -/
def readExp : List Char → Option Int
  | [] => none
  | c :: ds =>
    if c = '-' then
      match readDigits ds with
      | some k => some (-(k : Int))
      | none => none
    else
      match readDigits (c :: ds) with
      | some k => some (k : Int)
      | none => none

/-! ## Tokens -/

/-- The base at the front of a token, and what follows it. `TH` is tried before `T`, as
v1's pattern `(TH|L|M|T|I|N|J)` does. -/
def readBase : List Char → Option (Base × List Char)
  | 'T' :: 'H' :: r => some (.TH, r)
  | 'L' :: r => some (.L, r)
  | 'M' :: r => some (.M, r)
  | 'T' :: r => some (.T, r)
  | 'I' :: r => some (.I, r)
  | 'N' :: r => some (.N, r)
  | 'J' :: r => some (.J, r)
  | _ => none

/-- One token `<BASE><exponent>` (v1's `_DIM_TOKEN`). -/
def readToken (cs : List Char) : Option (Base × Int) :=
  match readBase cs with
  | some (b, r) => (readExp r).map fun n => (b, n)
  | none => none

/-- A token's spelling. -/
def tokenChars (t : Base × Int) : List Char := t.1.spell ++ expChars t.2

/-- A DIMENSION's tokens in the order written, or `none` when one does not read. `1` has
none; otherwise the pieces between single spaces are the tokens, as Python's
`str.split(" ")` gives them, so a doubled, leading or trailing space leaves an empty
piece, which does not read. -/
def readTokens (cs : List Char) : Option (List (Base × Int)) :=
  if cs = ['1'] then some [] else (cs.splitOn ' ').mapM readToken

/-- A token list's spelling: `1` for none, else the tokens joined by single spaces. -/
def renderChars : List (Base × Int) → List Char
  | [] => ['1']
  | t :: ts => [' '].intercalate ((t :: ts).map tokenChars)

/-! ## The canonical form -/

/-- Each base's summed exponent over a token list; zero for a base not written. -/
def sumTokens (ts : List (Base × Int)) : Exponents :=
  fun b => ((ts.filter fun t => t.1 == b).map (·.2)).sum

/-- The canonical tokens: the bases in order, those with a zero exponent dropped. -/
def canonTokens (e : Exponents) : List (Base × Int) :=
  (Base.all.filter fun b => e b != 0).map fun b => (b, e b)

/-- The canonical DIMENSION of an exponent for every base (v1's `canon_dimension`). -/
def canon (e : Exponents) : String :=
  String.ofList (renderChars (canonTokens e))

/-- Each base's summed exponent, or `none` when a token does not read (v1's
`_dim_sums`). -/
def sums (s : String) : Option Exponents :=
  (readTokens s.toList).map sumTokens

/-- S15: every token reads, but a base's summed exponent leaves -9999..9999 (v1's
`dimension_out_of_range`). -/
def outOfRange (s : String) : Bool :=
  match sums s with
  | some e => !inRange e
  | none => false

/-- The canonical form of a DIMENSION, or `none` when it does not read or a summed
exponent leaves -9999..9999 (v1's `normalize_dimension`). -/
def normalize (s : String) : Option String :=
  match sums s with
  | some e => if inRange e then some (canon e) else none
  | none => none

/-! ## The canonical test -/

/-- A canonical exponent's digits: a first digit 1 to 9, at most four digits
(`[1-9][0-9]{0,3}`). -/
def canonDigits (ds : List Char) : Bool :=
  match ds with
  | [] => false
  | d :: _ => d != '0' && decide (ds.length ≤ 4) && ds.all Char.isDigit

/-- A canonical exponent: an optional minus sign, then canonical digits
(`-?[1-9][0-9]{0,3}`). -/
def canonExp : List Char → Bool
  | [] => false
  | c :: ds => if c = '-' then canonDigits ds else canonDigits (c :: ds)

/-- A canonical token's base (v1's `_DIM_CANON_TOKEN`). -/
def readCanonToken (cs : List Char) : Option Base :=
  match readBase cs with
  | some (b, r) => if canonExp r then some b else none
  | none => none

/-- Bases in strictly increasing canonical order. -/
def increasing : List Base → Bool
  | a :: b :: r => decide (a.index < b.index) && increasing (b :: r)
  | _ => true

/-- True when the DIMENSION is already canonical (v1's `is_canonical_dimension`):
`1`, or canonical tokens whose bases strictly increase. -/
def isCanonical (s : String) : Bool :=
  s.toList = ['1'] ||
    match (s.toList.splitOn ' ').mapM readCanonToken with
    | some bs => increasing bs
    | none => false

/-! ## PROVED: the canonical form -/

/-- The digits of a positive number do not begin with `0`. -/
theorem toDigits_head_ne_zero : ∀ {k : Nat}, 0 < k →
    ∃ d ds, Nat.toDigits 10 k = d :: ds ∧ d ≠ '0'
  | k, hk => by
    by_cases h : k < 10
    · refine ⟨k.digitChar, [], Nat.toDigits_of_lt_base h, ?_⟩
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by
        omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have hdiv : 0 < k / 10 := Nat.div_pos (by omega) (by decide)
      have hlt : k / 10 < k := Nat.div_lt_self hk (by decide)
      obtain ⟨d, ds, hds, hd⟩ := toDigits_head_ne_zero hdiv
      refine ⟨d, ds ++ [(k % 10).digitChar], ?_, hd⟩
      rw [Nat.toDigits_of_base_le (by decide) (by omega), hds]
      rfl
termination_by k => k

theorem isDigit_of_mem_toDigits_ten {c : Char} {k : Nat} (h : c ∈ Nat.toDigits 10 k) :
    c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem all_isDigit_toDigits (k : Nat) : (Nat.toDigits 10 k).all Char.isDigit = true :=
  List.all_eq_true.mpr fun _ h => isDigit_of_mem_toDigits_ten h

theorem length_toDigits_le_four {k : Nat} (h : k ≤ expMax) :
    (Nat.toDigits 10 k).length ≤ 4 :=
  (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by unfold expMax at h; omega)

theorem readDigits_toDigits {k : Nat} (h : k ≤ expMax) :
    readDigits (Nat.toDigits 10 k) = some k := by
  simp [readDigits, length_toDigits_le_four h, all_isDigit_toDigits]

/-- The digits of a number do not begin with a minus sign. -/
theorem toDigits_cons_ne_minus {k : Nat} {c : Char} {ds : List Char}
    (h : Nat.toDigits 10 k = c :: ds) : c ≠ '-' := by
  intro hc
  have := isDigit_of_mem_toDigits_ten (k := k) (c := c) (by rw [h]; exact List.mem_cons_self)
  rw [hc] at this
  exact absurd this (by decide)

/-- An exponent within range reads back from its spelling. -/
theorem readExp_expChars {n : Int} (h : n.natAbs ≤ expMax) : readExp (expChars n) = some n := by
  unfold expChars
  split
  · simp only [readExp, ite_true, readDigits_toDigits h]
    congr 1
    omega
  · obtain ⟨c, ds, hcd⟩ : ∃ c ds, Nat.toDigits 10 n.natAbs = c :: ds := by
      cases hh : Nat.toDigits 10 n.natAbs with
      | nil => exact absurd hh Nat.toDigits_ne_nil
      | cons c ds => exact ⟨c, ds, rfl⟩
    have hc := toDigits_cons_ne_minus hcd
    rw [hcd]
    simp only [readExp, hc, ite_false]
    rw [← hcd, readDigits_toDigits h]
    dsimp only
    congr 1
    omega

/-- An exponent's spelling begins with a minus sign or a digit, never `H`. -/
theorem expChars_cons {n : Int} : ∃ c ds, expChars n = c :: ds ∧ c ≠ 'H' ∧ c ≠ ' ' := by
  unfold expChars
  split
  · exact ⟨'-', _, rfl, by decide, by decide⟩
  · cases hh : Nat.toDigits 10 n.natAbs with
    | nil => exact absurd hh Nat.toDigits_ne_nil
    | cons c ds =>
      have hd := isDigit_of_mem_toDigits_ten (k := n.natAbs) (c := c)
        (by rw [hh]; exact List.mem_cons_self)
      refine ⟨c, ds, rfl, ?_, ?_⟩ <;> intro hc <;> rw [hc] at hd <;> exact absurd hd (by decide)

theorem space_not_mem_expChars (n : Int) : ' ' ∉ expChars n := by
  unfold expChars
  intro h
  split at h
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact absurd (isDigit_of_mem_toDigits_ten h) (by decide)
  · exact absurd (isDigit_of_mem_toDigits_ten h) (by decide)

theorem readBase_spell (b : Base) (n : Int) :
    readBase (b.spell ++ expChars n) = some (b, expChars n) := by
  obtain ⟨c, ds, h, hH, -⟩ := expChars_cons (n := n)
  rw [h]
  cases b <;> simp [Base.spell, readBase, hH]

theorem readToken_tokenChars {t : Base × Int} (h : t.2.natAbs ≤ expMax) :
    readToken (tokenChars t) = some t := by
  obtain ⟨b, n⟩ := t
  simp [readToken, tokenChars, readBase_spell, readExp_expChars h]

theorem space_not_mem_tokenChars (t : Base × Int) : ' ' ∉ tokenChars t := by
  obtain ⟨b, n⟩ := t
  simp only [tokenChars, List.mem_append, not_or]
  exact ⟨by cases b <;> decide, space_not_mem_expChars n⟩

theorem mapM_readToken_map {ts : List (Base × Int)} (h : ∀ t ∈ ts, t.2.natAbs ≤ expMax) :
    (ts.map tokenChars).mapM readToken = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [List.mapM_cons, readToken_tokenChars h.1, ih h.2]

/-- A token list within range reads back from its spelling. -/
theorem readTokens_renderChars {ts : List (Base × Int)} (h : ∀ t ∈ ts, t.2.natAbs ≤ expMax) :
    readTokens (renderChars ts) = some ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have hne : renderChars (t :: ts) ≠ ['1'] := by
      obtain ⟨b, n⟩ := t
      cases ts <;> cases b <;> simp [renderChars, tokenChars, Base.spell, List.intercalate]
    unfold readTokens
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
    simp only [renderChars]
    rw [List.splitOn_intercalate]
    · exact mapM_readToken_map h
    · intro l hl
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hl
      exact space_not_mem_tokenChars u
    · simp

theorem sum_filter_nonzero (e : Exponents) (b : Base) : ∀ l : List Base, l.Nodup →
    (((l.filter fun x => e x != 0).filter fun x => x == b).map e).sum =
      if b ∈ l then e b else 0
  | [], _ => by simp
  | x :: l, hl => by
    have ⟨hx, hl⟩ := List.nodup_cons.mp hl
    have ih := sum_filter_nonzero e b l hl
    by_cases hxb : x = b
    · subst hxb
      rw [ite_eq_right_of_eq_false _ _ (eq_false hx)] at ih
      rw [List.filter_cons, ite_eq_left_of_eq_true _ _ (eq_true List.mem_cons_self)]
      by_cases h0 : e x = 0
      · rw [ite_eq_right_of_eq_false _ _ (by simp [h0]), ih, h0]
      · rw [ite_eq_left_of_eq_true _ _ (by simp [h0]), List.filter_cons,
          ite_eq_left_of_eq_true _ _ (by simp), List.map_cons, List.sum_cons, ih, Int.add_zero]
    · have hmem : (if b ∈ x :: l then e b else 0) = if b ∈ l then e b else 0 := by
        simp [List.mem_cons, Ne.symm hxb]
      rw [hmem, ← ih, List.filter_cons]
      split
      · rw [List.filter_cons, ite_eq_right_of_eq_false _ _ (by simpa using hxb)]
      · rfl

theorem sumTokens_canonTokens (e : Exponents) : sumTokens (canonTokens e) = e := by
  funext b
  have h := sum_filter_nonzero e b Base.all (by decide)
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Base.mem_all b))] at h
  simpa [sumTokens, canonTokens, List.filter_map, List.map_map, Function.comp_def] using h

theorem canonTokens_bound {e : Exponents} (h : inRange e = true) :
    ∀ t ∈ canonTokens e, t.2.natAbs ≤ expMax := by
  intro t ht
  simp only [canonTokens, List.mem_map] at ht
  obtain ⟨b, -, rfl⟩ := ht
  simp only [inRange, List.all_eq_true, decide_eq_true_eq] at h
  exact h b (Base.mem_all b)

/-- The canonical form reads back to the exponents it was made from. -/
theorem sums_canon {e : Exponents} (h : inRange e = true) : sums (canon e) = some e := by
  simp [sums, canon, String.toList_ofList, readTokens_renderChars (canonTokens_bound h),
    sumTokens_canonTokens]

/-- The canonical form is its own canonical form. -/
theorem normalize_canon {e : Exponents} (h : inRange e = true) :
    normalize (canon e) = some (canon e) := by
  simp [normalize, sums_canon h, h]

/-- Normalization is idempotent. -/
theorem normalize_idem {s c : String} (h : normalize s = some c) : normalize c = some c := by
  unfold normalize at h
  split at h
  · split at h
    · cases h
      exact normalize_canon ‹_›
    · cases h
  · cases h

/-! ## PROVED: what normalization returns is canonical -/

theorem canonDigits_toDigits {k : Nat} (h0 : 0 < k) (h : k ≤ expMax) :
    canonDigits (Nat.toDigits 10 k) = true := by
  obtain ⟨d, ds, hds, hd⟩ := toDigits_head_ne_zero h0
  have hlen := length_toDigits_le_four h
  have hall := all_isDigit_toDigits k
  rw [hds] at hlen hall ⊢
  simp only [List.length_cons] at hlen
  simp [canonDigits, hd, hall]
  omega

theorem canonExp_expChars {n : Int} (h0 : n ≠ 0) (h : n.natAbs ≤ expMax) :
    canonExp (expChars n) = true := by
  have hk : 0 < n.natAbs := Int.natAbs_pos.mpr h0
  unfold expChars
  split
  · simp only [canonExp, ite_true]
    exact canonDigits_toDigits hk h
  · obtain ⟨c, ds, hcd⟩ : ∃ c ds, Nat.toDigits 10 n.natAbs = c :: ds := by
      cases hh : Nat.toDigits 10 n.natAbs with
      | nil => exact absurd hh Nat.toDigits_ne_nil
      | cons c ds => exact ⟨c, ds, rfl⟩
    have hc := toDigits_cons_ne_minus hcd
    have := canonDigits_toDigits hk h
    rw [hcd] at this ⊢
    simp only [canonExp, hc, ite_false]
    exact this

theorem readCanonToken_tokenChars {t : Base × Int} (h0 : t.2 ≠ 0) (h : t.2.natAbs ≤ expMax) :
    readCanonToken (tokenChars t) = some t.1 := by
  obtain ⟨b, n⟩ := t
  simp [readCanonToken, tokenChars, readBase_spell, canonExp_expChars h0 h]

theorem increasing_of_pairwise :
    ∀ {l : List Base}, l.Pairwise (fun a b => a.index < b.index) → increasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    have ⟨hab, hr⟩ := List.pairwise_cons.mp h
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hab b List.mem_cons_self, increasing_of_pairwise hr⟩

theorem increasing_canonTokens (e : Exponents) :
    increasing ((canonTokens e).map (·.1)) = true := by
  apply increasing_of_pairwise
  simp only [canonTokens, List.map_map, Function.comp_def, List.map_id']
  exact List.Pairwise.filter _ (by decide)

/-- The canonical form passes the canonical test. -/
theorem isCanonical_canon {e : Exponents} (h : inRange e = true) :
    isCanonical (canon e) = true := by
  have hb := canonTokens_bound h
  have hinc := increasing_canonTokens e
  unfold isCanonical canon
  rw [String.toList_ofList]
  generalize hts : canonTokens e = ts at hb hinc
  have hnz : ∀ t ∈ ts, t.2 ≠ 0 := by
    intro t ht
    rw [← hts] at ht
    simp only [canonTokens, List.mem_map, List.mem_filter] at ht
    obtain ⟨b, ⟨-, hb⟩, rfl⟩ := ht
    simpa using hb
  cases ts with
  | nil => rfl
  | cons t ts =>
    have hmap : ∀ us : List (Base × Int), (∀ u ∈ us, u.2 ≠ 0) →
        (∀ u ∈ us, u.2.natAbs ≤ expMax) →
        (us.map tokenChars).mapM readCanonToken = some (us.map (·.1)) := by
      intro us h0 h1
      induction us with
      | nil => rfl
      | cons u us ih =>
        simp only [List.mem_cons, forall_eq_or_imp] at h0 h1
        simp [List.mapM_cons, readCanonToken_tokenChars h0.1 h1.1, ih h0.2 h1.2]
    simp only [renderChars]
    rw [List.splitOn_intercalate, hmap _ hnz hb]
    · simp only [List.map_cons] at hinc
      simp [hinc]
    · intro l hl
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hl
      exact space_not_mem_tokenChars u
    · simp

/-- What normalization returns passes the canonical test. -/
theorem isCanonical_of_normalize {s c : String} (h : normalize s = some c) :
    isCanonical c = true := by
  unfold normalize at h
  split at h
  · split at h
    · cases h
      exact isCanonical_canon ‹_›
    · cases h
  · cases h

/-! ## PROVED: a canonical DIMENSION is its own canonical form

With `isCanonical_of_normalize`, the canonical test and normalization agree exactly: a
DIMENSION passes v1's `is_canonical_dimension` if and only if `normalize_dimension` returns
it unchanged (`isCanonical_iff`). -/

theorem Base.index_inj {a b : Base} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [Base.index]

theorem readBase_eq {cs r : List Char} {b : Base} (h : readBase cs = some (b, r)) :
    cs = b.spell ++ r := by
  unfold readBase at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> rfl

theorem digitChar_of_isDigit {c : Char} (h : c.isDigit = true) :
    Nat.digitChar (c.toNat - 48) = c := by
  have hc := Char.isDigit_iff_toNat.mp h
  simp only [Char.reduceToNat] at hc
  apply Char.toNat_inj.mp
  rw [Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

theorem ofDigitChars_pos {d : Char} {t : List Char} (hd : d.isDigit = true) (h0 : d ≠ '0') :
    0 < Nat.ofDigitChars 10 (d :: t) 0 := by
  have hc := Char.isDigit_iff_toNat.mp hd
  simp only [Char.reduceToNat] at hc
  have h48 : d.toNat ≠ 48 := fun e => h0 (Char.toNat_inj.mp (by rw [e]; rfl))
  rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero]
  have : 0 < 10 ^ t.length := Nat.pow_pos (by decide)
  have : 0 < 10 ^ t.length * (10 * 0 + (d.toNat - '0'.toNat)) :=
    Nat.mul_pos this (by simp only [Char.reduceToNat]; omega)
  omega

/-- The digits of a number read from digits with no leading zero are those digits; the
induction runs from the last digit, over the reversed list. -/
theorem toDigits_ofDigitChars_rev : ∀ (rl : List Char), rl ≠ [] →
    rl.reverse.all Char.isDigit = true →
    (∀ h : rl.reverse ≠ [], rl.reverse.head h ≠ '0' ∨ rl.reverse.length = 1) →
    Nat.toDigits 10 (Nat.ofDigitChars 10 rl.reverse 0) = rl.reverse
  | [], h => absurd rfl h
  | d :: rinit, _ => by
    have ih := toDigits_ofDigitChars_rev rinit
    generalize hinit : rinit.reverse = init at ih
    simp only [List.reverse_cons, hinit]
    intro hall hhead
    have hall' := List.all_eq_true.mp hall
    have hd : d.isDigit = true := hall' d (by simp)
    have hv : d.toNat - 48 < 10 := by
      have := Char.isDigit_iff_toNat.mp hd
      simp only [Char.reduceToNat] at this
      omega
    cases init with
    | nil =>
      simp only [List.nil_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil,
        Char.reduceToNat, Nat.mul_zero, Nat.zero_add]
      rw [Nat.toDigits_of_lt_base hv, digitChar_of_isDigit hd]
    | cons a t =>
      have hrne : rinit ≠ [] := by
        intro e
        rw [e] at hinit
        simp at hinit
      have hne : a :: t ≠ [] := List.cons_ne_nil a t
      have hallI : (a :: t).all Char.isDigit = true :=
        List.all_eq_true.mpr fun x hx => hall' x (List.mem_append_left _ hx)
      have ha : a ≠ '0' := by
        rcases hhead (by simp) with h | h
        · simpa using h
        · simp at h
      have hheadI : ∀ h : a :: t ≠ [], (a :: t).head h ≠ '0' ∨ (a :: t).length = 1 :=
        fun _ => Or.inl ha
      have hm := ofDigitChars_pos (t := t) (hall' a (by simp)) ha
      rw [Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil,
        ← Nat.toDigits_append_toDigits (by decide) hm (by simp only [Char.reduceToNat]; exact hv),
        ih hrne hallI hheadI]
      simp only [Char.reduceToNat]
      rw [Nat.toDigits_of_lt_base hv, digitChar_of_isDigit hd]

theorem toDigits_ofDigitChars {ds : List Char} (hne : ds ≠ []) (hall : ds.all Char.isDigit = true)
    (hhead : ∀ h : ds ≠ [], ds.head h ≠ '0' ∨ ds.length = 1) :
    Nat.toDigits 10 (Nat.ofDigitChars 10 ds 0) = ds := by
  have := toDigits_ofDigitChars_rev ds.reverse (by simpa using hne)
  simp only [List.reverse_reverse] at this
  exact this hall hhead

/-- Canonical digits are the spelling of a number from 1 to 9999. -/
theorem canonDigits_spec {ds : List Char} (h : canonDigits ds = true) :
    ∃ k, readDigits ds = some k ∧ Nat.toDigits 10 k = ds ∧ 0 < k ∧ k ≤ expMax := by
  cases ds with
  | nil => simp [canonDigits] at h
  | cons d t =>
    simp only [canonDigits, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hd0, hlen⟩, hall⟩ := h
    have hdigit : d.isDigit = true := List.all_eq_true.mp hall d (by simp)
    have hback := toDigits_ofDigitChars (List.cons_ne_nil d t) hall fun _ => Or.inl hd0
    refine ⟨Nat.ofDigitChars 10 (d :: t) 0, ?_, hback, ofDigitChars_pos hdigit hd0, ?_⟩
    · simp only [List.length_cons] at hlen
      simp [readDigits, hall]
      omega
    · have := (Nat.length_toDigits_le_iff (b := 10) (k := 4) (by decide) (by decide)).mp
        (by rw [hback]; exact hlen)
      unfold expMax
      omega

/-- A canonical exponent is the spelling of a nonzero exponent within range. -/
theorem canonExp_spec {r : List Char} (h : canonExp r = true) :
    ∃ n, readExp r = some n ∧ expChars n = r ∧ n ≠ 0 ∧ n.natAbs ≤ expMax := by
  cases r with
  | nil => simp [canonExp] at h
  | cons c ds =>
    by_cases hc : c = '-'
    · subst hc
      simp only [canonExp, ite_true] at h
      obtain ⟨k, hk, hback, hpos, hmax⟩ := canonDigits_spec h
      refine ⟨-(k : Int), ?_, ?_, by omega, by omega⟩
      · simp [readExp, hk]
      · simp only [expChars]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        simp [hback]
    · simp only [canonExp, hc, ite_false] at h
      obtain ⟨k, hk, hback, hpos, hmax⟩ := canonDigits_spec h
      refine ⟨(k : Int), ?_, ?_, by omega, by omega⟩
      · simp only [readExp, hc, ite_false, hk]
      · simp only [expChars]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        simpa using hback

theorem readCanonToken_spec {w : List Char} {b : Base} (h : readCanonToken w = some b) :
    ∃ n, readToken w = some (b, n) ∧ tokenChars (b, n) = w ∧ n ≠ 0 ∧ n.natAbs ≤ expMax := by
  unfold readCanonToken at h
  split at h
  · rename_i b' r hb
    split at h
    · cases h
      obtain ⟨n, hn, hback, h0, hmax⟩ := canonExp_spec ‹_›
      refine ⟨n, ?_, ?_, h0, hmax⟩
      · simp [readToken, hb, hn]
      · rw [readBase_eq hb, tokenChars, hback]
    · cases h
  · cases h

theorem mapM_readCanonToken {ws : List (List Char)} {bs : List Base}
    (h : ws.mapM readCanonToken = some bs) :
    ∃ ts : List (Base × Int), ws.mapM readToken = some ts ∧ ts.map tokenChars = ws ∧
      ts.map (·.1) = bs ∧ ∀ t ∈ ts, t.2 ≠ 0 ∧ t.2.natAbs ≤ expMax := by
  induction ws generalizing bs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, rfl, by simp⟩
  | cons w ws ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    cases hw : readCanonToken w with
    | none => simp [hw] at h
    | some b =>
      cases hws : ws.mapM readCanonToken with
      | none => simp [hw, hws] at h
      | some bs' =>
        simp only [hw, hws, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨n, hn, hback, h0, hmax⟩ := readCanonToken_spec hw
        obtain ⟨ts, hts, hmap, hfst, hbound⟩ := ih hws
        refine ⟨(b, n) :: ts, ?_, ?_, ?_, ?_⟩
        · simp [List.mapM_cons, hn, hts]
        · simp [hback, hmap]
        · simp [hfst]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨h0, hmax⟩
          · exact hbound t ht

theorem pairwise_of_increasing :
    ∀ {l : List Base}, increasing l = true → l.Pairwise (fun a b => a.index < b.index)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_increasing h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx)

/-- A sorted list of bases taken from a sorted list is that list filtered by membership. -/
theorem filter_mem_sorted :
    ∀ {l bs : List Base}, l.Pairwise (fun a b => a.index < b.index) →
      bs.Pairwise (fun a b => a.index < b.index) → (∀ b ∈ bs, b ∈ l) →
      l.filter (fun x => decide (x ∈ bs)) = bs
  | [], bs, _, _, hsub => by
    cases bs with
    | nil => rfl
    | cons c _ => exact absurd (hsub c (by simp)) List.not_mem_nil
  | a :: l, bs, hl, hbs, hsub => by
    have ⟨hal, hl'⟩ := List.pairwise_cons.mp hl
    have hne : ∀ x ∈ l, x ≠ a := fun x hx e => by
      have := hal x hx
      rw [e] at this
      exact Nat.lt_irrefl _ this
    cases bs with
    | nil => simp
    | cons c bs' =>
      have ⟨hcb, hbs'⟩ := List.pairwise_cons.mp hbs
      by_cases hca : c = a
      · subst hca
        have hsub' : ∀ b ∈ bs', b ∈ l := by
          intro b hb
          rcases List.mem_cons.mp (hsub b (by simp [hb])) with rfl | h
          · exact absurd (hcb _ hb) (Nat.lt_irrefl _)
          · exact h
        have hcongr : l.filter (fun x => decide (x ∈ c :: bs')) =
            l.filter (fun x => decide (x ∈ bs')) :=
          List.filter_congr fun x hx => by simp [List.mem_cons, hne x hx]
        rw [List.filter_cons_of_pos (by simp), hcongr, filter_mem_sorted hl' hbs' hsub']
      · have hcl : c ∈ l := by
          rcases List.mem_cons.mp (hsub c (by simp)) with h | h
          · exact absurd h hca
          · exact h
        have hac := hal c hcl
        have hanot : a ∉ c :: bs' := by
          intro ha
          rcases List.mem_cons.mp ha with h | h
          · exact hca h.symm
          · have := hcb a h
            omega
        have hsub' : ∀ b ∈ c :: bs', b ∈ l := by
          intro b hb
          rcases List.mem_cons.mp (hsub b hb) with rfl | h
          · exact absurd hb hanot
          · exact h
        rw [List.filter_cons_of_neg (by simpa using hanot), filter_mem_sorted hl' hbs hsub']

theorem eq_of_nodup_fst : ∀ {ts : List (Base × Int)}, (ts.map (·.1)).Nodup →
    ∀ {u t : Base × Int}, u ∈ ts → t ∈ ts → u.1 = t.1 → u = t
  | [], _, _, _, hu, _, _ => absurd hu List.not_mem_nil
  | x :: ts, hnd, u, t, hu, ht, he => by
    have ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp ht with rfl | ht'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨t, ht', he.symm⟩) hnot
    · exact absurd (show t.1 ∈ ts.map (·.1) from List.mem_map.mpr ⟨u, hu', he⟩) hnot
    · exact eq_of_nodup_fst hnd' hu' ht' he

/-- With distinct bases, each base's sum is its one exponent, or zero. -/
theorem sumTokens_of_nodup :
    ∀ {ts : List (Base × Int)}, (ts.map (·.1)).Nodup →
      ∀ b, sumTokens ts b = ((ts.find? fun t => t.1 == b).map (·.2)).getD 0
  | [], _, b => rfl
  | t :: ts, hnd, b => by
    have ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have ih := sumTokens_of_nodup hnd' b
    simp only [sumTokens] at ih ⊢
    by_cases htb : t.1 = b
    · subst htb
      have h0 : ((ts.filter fun u => u.1 == t.1).map (·.2)).sum = 0 := by
        rw [ih]
        have : (ts.find? fun u => u.1 == t.1) = none := by
          rw [List.find?_eq_none]
          intro u hu he
          exact hnot (List.mem_map.mpr ⟨u, hu, by simpa using he⟩)
        rw [this]
        rfl
      simp [h0]
    · have : (t.1 == b) = false := by simpa using htb
      simp [this, ih]

theorem canonTokens_sumTokens {ts : List (Base × Int)}
    (hinc : (ts.map (·.1)).Pairwise (fun a b => a.index < b.index))
    (h0 : ∀ t ∈ ts, t.2 ≠ 0) : canonTokens (sumTokens ts) = ts := by
  have hnd : (ts.map (·.1)).Nodup :=
    hinc.imp fun h e => by rw [e] at h; exact Nat.lt_irrefl _ h
  have hval : ∀ t ∈ ts, sumTokens ts t.1 = t.2 := by
    intro t ht
    rw [sumTokens_of_nodup hnd]
    have hf : ∀ u ∈ ts, u.1 = t.1 → u = t := by
      intro u hu he
      exact eq_of_nodup_fst hnd hu ht he
    have : (ts.find? fun u => u.1 == t.1) = some t := by
      cases hfind : ts.find? (fun u => u.1 == t.1) with
      | none =>
        rw [List.find?_eq_none] at hfind
        exact absurd (by simp) (hfind t ht)
      | some u =>
        have hu := List.mem_of_find?_eq_some hfind
        have he := List.find?_some hfind
        rw [hf u hu (by simpa using he)]
    rw [this]
    rfl
  have hzero : ∀ b, sumTokens ts b ≠ 0 ↔ b ∈ ts.map (·.1) := by
    intro b
    constructor
    · intro hb
      rw [sumTokens_of_nodup hnd] at hb
      cases hfind : ts.find? (fun u => u.1 == b) with
      | none => rw [hfind] at hb; exact absurd rfl hb
      | some u =>
        have hu := List.mem_of_find?_eq_some hfind
        have he := List.find?_some hfind
        exact List.mem_map.mpr ⟨u, hu, by simpa using he⟩
    · intro hb
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      rw [hval t ht]
      exact h0 t ht
  unfold canonTokens
  have hfilter : (Base.all.filter fun b => sumTokens ts b != 0) =
      Base.all.filter fun x => decide (x ∈ ts.map (·.1)) :=
    List.filter_congr fun b _ => by
      have := hzero b
      by_cases hb : sumTokens ts b = 0 <;> simp_all
  rw [hfilter, filter_mem_sorted (by decide) hinc (fun b _ => Base.mem_all b), List.map_map]
  conv => rhs; rw [← List.map_id ts]
  apply List.map_congr_left
  intro t ht
  simp [hval t ht]

/-- A canonical DIMENSION is its own canonical form. -/
theorem normalize_of_isCanonical {s : String} (h : isCanonical s = true) :
    normalize s = some s := by
  unfold isCanonical at h
  by_cases h1 : s.toList = ['1']
  · have hs : s = String.ofList ['1'] := by rw [← h1, String.ofList_toList]
    subst hs
    decide
  · simp only [h1, decide_false, Bool.false_or] at h
    split at h
    · rename_i bs hbs
      obtain ⟨ts, hts, hmap, hfst, hbound⟩ := mapM_readCanonToken hbs
      have hinc : (ts.map (·.1)).Pairwise (fun a b => a.index < b.index) := by
        rw [hfst]; exact pairwise_of_increasing h
      have hcanon := canonTokens_sumTokens hinc fun t ht => (hbound t ht).1
      have hsums : sums s = some (sumTokens ts) := by
        simp [sums, readTokens, h1, hts]
      have hrange : inRange (sumTokens ts) = true := by
        rw [← hcanon] at hbound
        simp only [inRange, List.all_eq_true, decide_eq_true_eq]
        intro b _
        by_cases hb : sumTokens ts b = 0
        · rw [hb]; unfold expMax; omega
        · have : (b, sumTokens ts b) ∈ canonTokens (sumTokens ts) :=
            List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨Base.mem_all b, by simpa using hb⟩, rfl⟩
          exact (hbound _ this).2
      simp only [normalize, hsums, hrange, ite_true, canon, hcanon]
      congr 1
      cases ts with
      | nil =>
        simp only [List.map_nil] at hmap
        exact absurd hmap.symm (List.splitOn_ne_nil ' ' s.toList)
      | cons t ts' =>
        rw [renderChars, hmap, List.intercalate_splitOn, String.ofList_toList]
    · cases h

/-- The canonical test and normalization agree: a DIMENSION is canonical if and only if
normalization returns it unchanged. -/
theorem isCanonical_iff {s : String} : isCanonical s = true ↔ normalize s = some s :=
  ⟨normalize_of_isCanonical, isCanonical_of_normalize⟩

/-! ## Worked examples from v1's corpus -/

example : normalize "T-1 L1" = some "L1 T-1" := by decide
example : normalize "L1 L-1" = some "1" := by decide
example : normalize "L9999 L1" = none := by decide
example : outOfRange "L9999 L1" = true := by decide
example : isCanonical "M1 L1" = false := by decide
example : isCanonical "L-1 TH1" = true := by decide

end Principia.Dimension
