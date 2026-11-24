import Principia.Dimension

/-!
# Decimals

A VALUE, an UNCERTAINTY and the Criteria Set's K are decimal strings (zone schemas 5.6;
v1's tpc_zone 0.4.1: `canon_decimal`, `_dec_sign`, `_is_pos_finite`).

- Accepted: an optional minus sign, one or more ASCII digits, optionally a point and one
  or more digits, optionally `e` or `E` with an optional sign and one to four digits
  (`-?[0-9]+(\.[0-9]+)?([eE][-+]?[0-9]{1,4})?`). No leading `+`, no bare point.
- Canonical: `0` for zero; otherwise the digits with no leading or trailing zero, a minus
  sign before them when negative, and `e<exponent>` after them when the exponent is not
  zero: `0.050` is `5e-2`, `1500` is `15e2`, `-0` is `0`. String arithmetic only, as in
  v1. Trailing zeros carry no precision here; an UNCERTAINTY carries it.

A decimal's value is exact (`Rat`); v1 parsed it to the nearest IEEE double where it
computed with it. `isPosFinite`, v1's test that a positive decimal's nearest double is
positive and finite, is in `Principia.Exact`, beside the double range's bounds.
-/

namespace Principia.Decimal

/-- A decimal as written: its sign, its integer digits, its fraction digits (possibly
none) and its written exponent (zero when none is written). -/
structure Parts where
  neg : Bool
  ip : List Char
  fp : List Char
  ex : Int
  deriving DecidableEq, Repr

/-- The exponent after `e` or `E`: an optional sign, then one to four digits. -/
def readExponent : List Char → Option Int
  | [] => none
  | c :: ds =>
    if c = '+' then (Dimension.readDigits ds).map Int.ofNat
    else if c = '-' then (Dimension.readDigits ds).map fun k => -(k : Int)
    else (Dimension.readDigits (c :: ds)).map Int.ofNat

/-- What follows the digits: nothing, or an exponent. -/
def readTail : List Char → Option Int
  | [] => some 0
  | c :: r => if c = 'e' || c = 'E' then readExponent r else none

/-- A decimal's parts, or `none` when it does not read. -/
def readParts (cs : List Char) : Option Parts :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (ip, r) := cs.span Char.isDigit
  if ip = [] then none
  else
    match r with
    | '.' :: r' =>
      let (fp, r'') := r'.span Char.isDigit
      if fp = [] then none
      else (readTail r'').map fun ex => { neg, ip, fp, ex }
    | _ => (readTail r).map fun ex => { neg, ip, fp := [], ex }

/-- The digits with leading zeros removed, then the number of trailing zeros. -/
def significant (p : Parts) : List Char × Nat :=
  let ds := (p.ip ++ p.fp).dropWhile (· = '0')
  (ds, (ds.reverse.takeWhile (· = '0')).length)

/-- The canonical spelling of a decimal's parts. -/
def canonChars (p : Parts) : List Char :=
  let (ds, t) := significant p
  if ds = [] then ['0']
  else
    let e : Int := p.ex - p.fp.length + t
    (if p.neg then ['-'] else []) ++ ds.take (ds.length - t) ++
      (if e = 0 then [] else 'e' :: (toString e).toList)

/-- The canonical form of a decimal, or `none` when it does not read (v1's
`canon_decimal`). -/
def canon (s : String) : Option String :=
  (readParts s.toList).map fun p => String.ofList (canonChars p)

/-- -1, 0 or 1 for a decimal's sign; 0 when it does not read (v1's `_dec_sign`). -/
def sign (s : String) : Int :=
  match canon s with
  | none => 0
  | some c => if c = "0" then 0 else if c.startsWith "-" then -1 else 1

/-- A power of ten as an exact rational. -/
def pow10 (e : Int) : Rat := (10 : Rat) ^ e

/-- A decimal's exact value, or `none` when it does not read. -/
def value (s : String) : Option Rat :=
  (readParts s.toList).map fun p =>
    let m : Rat := (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat)
    let v := m * pow10 (p.ex - p.fp.length)
    if p.neg then -v else v

/-! ## Worked examples from v1's corpus -/

example : canon "0.050" = some "5e-2" := by decide
example : canon "1500" = some "15e2" := by decide
example : canon "-1.5E+3" = some "-15e2" := by decide
example : canon "-0" = some "0" := by decide
example : canon "5." = none := by decide
example : canon "+1" = none := by decide

/-! A canonical form need not read again: a written exponent has at most four digits, but
the canonical exponent also counts the fraction digits and the trailing zeros, so it can
pass 9999. v1 accepts such a decimal; S15 bounded only the DIMENSION's exponents. -/
example : canon "0.001e-9999" = some "1e-10002" := by decide
example : canon "1e-10002" = none := by decide

/-! ## The sign and the exact value

`sign` reads a decimal's sign from its canonical spelling; `value` computes its exact value.
The two agree (`sign_of_value`); the canonical form exists exactly when the exact value does
(`canon_isSome_iff`); a decimal that does not read has sign 0 (`value_none_sign`). -/

/-- What `span`'s loop keeps is what it was given, or what passes the test. -/
theorem span_loop_keeps {p : Char → Bool} :
    ∀ (l acc : List Char), ∀ c ∈ (List.span.loop p l acc).1, c ∈ acc ∨ p c = true
  | [], acc, c, h => by simp [List.span.loop] at h; exact .inl h
  | a :: as, acc, c, h => by
    simp only [List.span.loop] at h
    split at h
    · rename_i hp
      rcases span_loop_keeps as (a :: acc) c h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr hp
        · exact .inl h
      · exact .inr h
    · simp at h; exact .inl h

/-- What `span` keeps passes the test, read from its result. -/
theorem span_keeps {l a b : List Char} (h : l.span Char.isDigit = (a, b)) :
    ∀ c ∈ a, c.isDigit = true := by
  intro c hm
  have hm' : c ∈ (l.span Char.isDigit).1 := by rw [h]; exact hm
  rcases span_loop_keeps l [] c hm' with h | h
  · simp at h
  · exact h

/-- A decimal's integer and fraction digits are ASCII digits. -/
theorem readParts_isDigit {cs : List Char} {p : Parts} (h : readParts cs = some p) :
    ∀ c ∈ p.ip ++ p.fp, c.isDigit = true := by
  unfold readParts at h
  repeat' split at h
  all_goals first
    | cases h
    | obtain ⟨ex, -, rfl⟩ := Option.map_eq_some_iff.mp h
      intro c hm
      simp only [List.append_nil, List.mem_append] at hm
      first
        | exact span_keeps (by assumption) c hm
        | rcases hm with hm | hm <;> exact span_keeps (by assumption) c hm

/-- A digit whose value is 0 is `'0'`. -/
theorem digit_value_zero {c : Char} (hd : c.isDigit = true) (h0 : c.toNat - '0'.toNat = 0) :
    c = '0' := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  apply Char.ext
  apply UInt32.toNat_inj.mp
  have h1 : '0'.val.toNat ≤ c.val.toNat := hd.1
  have h2 : c.toNat - '0'.toNat = 0 := h0
  simp only [Char.toNat] at h2
  omega

/-- Digits read as zero exactly when every one is `'0'` and nothing came before them. -/
theorem digits_zero_iff : ∀ (l : List Char) (init : Nat), (∀ c ∈ l, c.isDigit = true) →
    (Nat.ofDigitChars 10 l init = 0 ↔ init = 0 ∧ ∀ c ∈ l, c = '0')
  | [], init, _ => by simp [Nat.ofDigitChars]
  | c :: l, init, hd => by
    have ih := digits_zero_iff l (10 * init + (c.toNat - '0'.toNat))
      (fun c' h => hd c' (List.mem_cons_of_mem _ h))
    simp only [Nat.ofDigitChars, List.foldl_cons] at ih ⊢
    rw [ih]
    have hc := hd c (List.mem_cons_self ..)
    constructor
    · rintro ⟨h0, hl⟩
      refine ⟨by omega, ?_⟩
      intro c' hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact digit_value_zero hc (by omega)
      · exact hl c' hm
    · rintro ⟨rfl, hl⟩
      have := hl c (List.mem_cons_self ..)
      subst this
      exact ⟨by decide, fun c' h => hl c' (List.mem_cons_of_mem _ h)⟩

/-- Dropping the leading zeros leaves nothing exactly when every character is `'0'`. -/
theorem dropZeros_eq_nil : ∀ (l : List Char),
    l.dropWhile (fun c => decide (c = '0')) = [] ↔ ∀ c ∈ l, c = '0'
  | [] => by simp
  | c :: l => by
    have ih := dropZeros_eq_nil l
    by_cases hc : c = '0'
    · subst hc; simp [ih]
    · simp [hc]

/-- A list whose last element fails the test is not all taken by `takeWhile`. -/
theorem takeWhile_snoc_lt {p : Char → Bool} : ∀ {l : List Char} {a : Char},
    p a = false → ((l ++ [a]).takeWhile p).length < (l ++ [a]).length
  | [], a, h => by simp [h]
  | b :: l, a, h => by
    simp only [List.cons_append, List.takeWhile, List.length_cons]
    split
    · simp only [List.length_cons]
      have := takeWhile_snoc_lt (l := l) h
      omega
    · simp

/-- The canonical spelling of a decimal whose digits are not all zero: a minus sign first
exactly when it is negative, and never `0`. -/
theorem canonChars_nonzero {p : Parts} (hd : ∀ c ∈ p.ip ++ p.fp, c.isDigit = true)
    (hne : (significant p).1 ≠ []) :
    canonChars p ≠ ['0'] ∧ (['-'] <+: canonChars p ↔ p.neg = true) := by
  unfold canonChars
  generalize hsig : significant p = sig
  obtain ⟨ds, t⟩ := sig
  rw [hsig] at hne
  simp only at hne ⊢
  simp only [hne, ite_false]
  have hds : ds = (p.ip ++ p.fp).dropWhile (fun c => decide (c = '0')) := by
    unfold significant at hsig; simp only [Prod.mk.injEq] at hsig; exact hsig.1.symm
  have hht : t = (ds.reverse.takeWhile (fun c => decide (c = '0'))).length := by
    unfold significant at hsig; simp only [Prod.mk.injEq] at hsig; rw [← hsig.2, hds]
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have hd0 : d ≠ '0' := by
    have := List.head_dropWhile_not (fun c => decide (c = '0')) (l := p.ip ++ p.fp)
      (by rw [← hds]; simp)
    simp only [← hds, List.head_cons, decide_eq_false_iff_not] at this
    exact this
  have hdig : d.isDigit = true := by
    have hsub : d ∈ p.ip ++ p.fp := by
      have : d ∈ (p.ip ++ p.fp).dropWhile (fun c => decide (c = '0')) := by
        rw [← hds]; exact List.mem_cons_self ..
      have hte := List.takeWhile_append_dropWhile (p := fun c => decide (c = '0'))
        (l := p.ip ++ p.fp)
      rw [← hte]; exact List.mem_append_right _ this
    exact hd d hsub
  have hdm : d ≠ '-' := fun h => by subst h; simp [Char.isDigit] at hdig
  have htl : t < (d :: ds').length := by
    rw [hht, List.reverse_cons]
    have := takeWhile_snoc_lt (p := fun c => decide (c = '0')) (l := ds'.reverse) (a := d)
      (by simp [hd0])
    simpa using this
  obtain ⟨k, hk⟩ : ∃ k, (d :: ds').length - t = k + 1 := ⟨(d :: ds').length - t - 1, by omega⟩
  rw [hk, List.take_succ_cons]
  cases hn : p.neg
  · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
    refine ⟨fun h => hd0 (List.cons.inj h).1, ?_⟩
    simp only [List.cons_prefix_cons, iff_false, not_and]
    intro h; exact absurd h.symm hdm
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine ⟨fun h => by simp at h, ?_⟩
    simp [List.cons_prefix_cons]

/-- **The canonical form exists exactly when the exact value does.** Both read the same
parts, so a decimal has a canonical spelling if and only if it has an exact value. -/
theorem canon_isSome_iff (s : String) : (canon s).isSome ↔ (value s).isSome := by
  simp [canon, value, Option.isSome_map]

/-- **A decimal that does not read has sign 0.** With no exact value there is no canonical
form, and the sign of no canonical form is 0. -/
theorem value_none_sign {s : String} (h : value s = none) : sign s = 0 := by
  unfold value at h
  unfold sign canon
  cases hp : readParts s.toList with
  | none => rfl
  | some p => simp [hp] at h

/-- **The sign agrees with the exact value.** The sign read from a decimal's canonical
spelling is 0, -1 or 1 as its exact value is zero, negative or positive. -/
theorem sign_of_value {s : String} {q : Rat} (h : value s = some q) :
    sign s = if q = 0 then 0 else if q < 0 then -1 else 1 := by
  unfold value at h
  cases hp : readParts s.toList with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst h
    have hd := readParts_isDigit hp
    have hpos : 0 < pow10 (p.ex - p.fp.length) := Rat.zpow_pos (by decide)
    unfold sign canon
    simp only [hp, Option.map_some]
    by_cases hz : (significant p).1 = []
    · have hall : ∀ c ∈ p.ip ++ p.fp, c = '0' := by
        unfold significant at hz; exact (dropZeros_eq_nil _).mp hz
      have hm : Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 = 0 :=
        (digits_zero_iff _ 0 hd).mpr ⟨rfl, hall⟩
      have hc : canonChars p = ['0'] := by
        unfold canonChars
        generalize hsig : significant p = sig at hz
        obtain ⟨ds, t⟩ := sig
        simp only at hz ⊢
        simp [hz]
      rw [hc, hm]
      simp
    · obtain ⟨hn0, hneg⟩ := canonChars_nonzero hd hz
      have hm : Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 ≠ 0 := by
        intro h0
        have := ((digits_zero_iff _ 0 hd).mp h0).2
        exact hz (by unfold significant; exact (dropZeros_eq_nil _).mpr this)
      have hmpos : (0 : Rat) < (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hprod : 0 < ((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
          pow10 (p.ex - p.fp.length) := Rat.mul_pos hmpos hpos
      have hs0 : String.ofList (canonChars p) ≠ "0" := by
        intro h
        apply hn0
        have : String.ofList (canonChars p) = String.ofList ['0'] := h
        exact String.ofList_inj.mp this
      simp only [hs0, ite_false]
      have hsw : (String.ofList (canonChars p)).startsWith "-" = p.neg := by
        cases hn : p.neg
        · rw [String.startsWith_string_eq_false_iff]
          simp only [String.toList_ofList]
          intro h; exact absurd (hneg.mp h) (by simp [hn])
        · rw [String.startsWith_string_iff]
          simp only [String.toList_ofList]
          exact hneg.mpr hn
      rw [hsw]
      cases hn : p.neg
      · have h1 : ¬ ((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            pow10 (p.ex - p.fp.length) = 0 := by grind
        have h2 : ¬ ((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            pow10 (p.ex - p.fp.length) < 0 := by grind
        simp [h1, h2]
      · have h1 : ¬ -(((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            pow10 (p.ex - p.fp.length)) = 0 := by grind
        have h2 : -(((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            pow10 (p.ex - p.fp.length)) < 0 := by grind
        simp [h1, h2]

end Principia.Decimal
