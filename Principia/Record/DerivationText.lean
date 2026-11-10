import Principia.Record.StructuredWire
import Principia.Record.Answer
import Principia.Digest.Injective

/-!
# A DERIVATION's canonical text names one derivation

TPC-RECORD form 1's preimage writes a DERIVATION of `formsShape` as one text field, the
canonical JSON (`cj`, tpm_record_schema 11.4) of `derivationToValue` applied to the
derivation read (`Principia.Record.Check`, `encodeDerivation`). Here the Lean kernel checks
that the field leaves nothing of the derivation out: two derivations with one such text are
one derivation (`cj_derivationToValue_injective`).

The proof has two parts.

* **Canonical JSON tells sorted values apart** (`canonicalJson_prefix`). A value is
  `Sorted` when it holds no decimal number (whose text a respelling keeps,
  `canonicalJson_num_respell`, and which can read as an integer) and every object's keys are
  in strictly increasing code point order, at every depth. Two sorted values whose texts,
  each followed by nothing or by `,`, `]` or `}`, are one character list are one value, and
  what follows them is one: a string's text ends at its closing quote, as no escape writes a
  bare one; an integer's text holds no `,`, `]` or `}`; a list's and an object's elements
  are read in turn, each followed by `,` or the closing bracket.
* **The wire object's text is a sorted value's text** (`canonicalJson_derivationToValue`):
  `sortedValue` writes each object of `derivationToValue` with its members in key order,
  which leaves the canonical text unchanged (`canonicalJson_obj_perm`); `sortedValue` is
  sorted, and it is injective.
-/

namespace Principia.Record

open Principia.Canonical

/-! ## Sorted values -/

mutual
/-- A value with no decimal number and every object's keys in strictly increasing code
point order, at every depth. -/
def sortedV : Value → Prop
  | .num _ => False
  | .arr xs => sortedL xs
  | .obj ms => sortedM ms ∧ (ms.map Prod.fst).Pairwise (· < ·)
  | _ => True

/-- Every element is sorted. -/
def sortedL : List Value → Prop
  | [] => True
  | x :: xs => sortedV x ∧ sortedL xs

/-- Every member's value is sorted. -/
def sortedM : List (String × Value) → Prop
  | [] => True
  | (_, v) :: ms => sortedV v ∧ sortedM ms
end

/-- What may follow a value's text inside a canonical text: nothing, or `,`, `]` or `}`. -/
def Delim (a : List Char) : Prop := ∀ c r, a = c :: r → c = ',' ∨ c = ']' ∨ c = '}'

theorem delim_nil : Delim [] := fun _ _ h => by simp at h

theorem delim_comma (r : List Char) : Delim (',' :: r) := fun _ _ h => by
  simp only [List.cons.injEq] at h; exact .inl h.1.symm

theorem delim_close (r : List Char) : Delim (']' :: r) := fun _ _ h => by
  simp only [List.cons.injEq] at h; exact .inr (.inl h.1.symm)

theorem delim_brace (r : List Char) : Delim ('}' :: r) := fun _ _ h => by
  simp only [List.cons.injEq] at h; exact .inr (.inr h.1.symm)

/-! ## Strings -/

/-- No escape opens with a bare quote. -/
theorem escapeChar_head (c : Char) (r : List Char) (h : escapeChar c = '"' :: r) : False := by
  unfold escapeChar at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.cons.injEq] at h
        rename_i h1 _ _
        exact h1 h.1

/-- Escaped characters followed by a closing quote: the characters and what follows are
told apart. -/
theorem escaped_prefix :
    ∀ {xs ys : List Char} {a b : List Char},
      xs.flatMap escapeChar ++ '"' :: a = ys.flatMap escapeChar ++ '"' :: b → xs = ys ∧ a = b
  | [], [], _, _, h => by simpa using h
  | [], y :: ys, _, _, h => by
    simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons, List.append_assoc] at h
    obtain ⟨r, hr⟩ : ∃ r, escapeChar y = '"' :: r := by
      cases he : escapeChar y with
      | nil => exact absurd he (escapeChar_ne_nil y)
      | cons d r =>
        rw [he, List.cons_append, List.cons.injEq] at h
        exact ⟨r, by rw [h.1]⟩
    exact (escapeChar_head y r hr).elim
  | x :: xs, [], _, _, h => by
    simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons, List.append_assoc] at h
    obtain ⟨r, hr⟩ : ∃ r, escapeChar x = '"' :: r := by
      cases he : escapeChar x with
      | nil => exact absurd he (escapeChar_ne_nil x)
      | cons d r =>
        rw [he, List.cons_append, List.cons.injEq] at h
        exact ⟨r, by rw [← h.1]⟩
    exact (escapeChar_head x r hr).elim
  | x :: xs, y :: ys, _, _, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := escapeChar_prefix h
    obtain ⟨rfl, rfl⟩ := escaped_prefix h'
    exact ⟨rfl, rfl⟩

theorem quote_toList (s : String) :
    (quote s).toList = '"' :: (s.toList.flatMap escapeChar ++ ['"']) := by
  simp [quote]

/-- A quoted string's text, followed by anything, names the string and what follows. -/
theorem quote_prefix {s t : String} {a b : List Char}
    (h : (quote s).toList ++ a = (quote t).toList ++ b) : s = t ∧ a = b := by
  simp only [quote_toList, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
  obtain ⟨h1, h2⟩ := escaped_prefix h
  exact ⟨String.toList_inj.mp h1, h2⟩

/-! ## Integers -/

/-- A character an integer's text holds: `-` or a decimal digit. -/
theorem int_toList_char {n : Int} {c : Char} (h : c ∈ (toString n).toList) :
    c = '-' ∨ c.isDigit = true := by
  simp only [toString, Int.repr_eq_ite] at h
  split at h
  · simp only [Nat.toList_repr] at h
    exact .inr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)
  · simp only [String.toList_append, Nat.toList_repr, Digest.minus_toList, List.cons_append,
      List.nil_append, List.mem_cons] at h
    rcases h with h | h
    · exact .inl h
    · exact .inr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)

/-- A character that is not `-` and no digit. -/
def Plain (c : Char) : Prop := c ≠ '-' ∧ c.isDigit = false

theorem plain_of_delim {c : Char} (h : c = ',' ∨ c = ']' ∨ c = '}') : Plain c := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Two texts of `-` and digits, each followed by nothing or a character that is neither,
are one text, and what follows is one. -/
theorem digits_prefix :
    ∀ {l₁ l₂ a b : List Char}, (∀ c ∈ l₁, c = '-' ∨ c.isDigit = true) →
      (∀ c ∈ l₂, c = '-' ∨ c.isDigit = true) → Delim a → Delim b →
      l₁ ++ a = l₂ ++ b → l₁ = l₂ ∧ a = b
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], c :: _, a, _, _, h₂, ha, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    have hp := plain_of_delim (ha c _ h)
    rcases h₂ c List.mem_cons_self with h' | h'
    · exact absurd h' hp.1
    · rw [hp.2] at h'; exact absurd h' (by decide)
  | c :: _, [], _, b, h₁, _, _, hb, h => by
    simp only [List.nil_append, List.cons_append] at h
    have hp := plain_of_delim (hb c _ h.symm)
    rcases h₁ c List.mem_cons_self with h' | h'
    · exact absurd h' hp.1
    · rw [hp.2] at h'; exact absurd h' (by decide)
  | c :: l₁, d :: l₂, _, _, h₁, h₂, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e1, e2⟩ := digits_prefix (fun x hx => h₁ x (List.mem_cons_of_mem c hx))
      (fun x hx => h₂ x (List.mem_cons_of_mem d hx)) ha hb h.2
    exact ⟨by rw [h.1, e1], e2⟩

/-! ## Lists of texts -/

/-- Texts joined by `,`, then the closing character `e`, then `a`. -/
def joinTail : List (List Char) → Char → List Char → List Char
  | [], e, a => e :: a
  | p :: ps, e, a => ',' :: p ++ joinTail ps e a

/-- Texts joined by `,`, the closing character `e`, then `a`. -/
def joinAll : List (List Char) → Char → List Char → List Char
  | [], e, a => e :: a
  | p :: ps, e, a => p ++ joinTail ps e a

theorem intercalate_joinAll (ps : List (List Char)) (e : Char) (a : List Char) :
    List.intercalate [','] ps ++ e :: a = joinAll ps e a := by
  match ps with
  | [] => rfl
  | [p] => simp [joinAll, joinTail]
  | p :: q :: ps =>
    have ih := intercalate_joinAll (q :: ps) e a
    simp only [List.intercalate_cons_cons, joinAll] at ih ⊢
    simp only [List.append_assoc, List.cons_append, ih, joinTail, List.nil_append]

/-! ## The first character of a value's text -/

/-- The first character of each kind's text. -/
def headOf : Value → Char → Prop
  | .null, c => c = 'n'
  | .bool true, c => c = 't'
  | .bool false, c => c = 'f'
  | .int _, c => c = '-' ∨ c.isDigit = true
  | .num _, _ => True
  | .str _, c => c = '"'
  | .arr _, c => c = '['
  | .obj _, c => c = '{'

/-- A value's text opens with its kind's character. -/
theorem canonicalJson_head (v : Value) (hv : sortedV v) {t : String} (h : v.canonicalJson = some t) :
    ∃ c r, t.toList = c :: r ∧ headOf v c := by
  cases v with
  | null => simp [Value.canonicalJson] at h; subst h; exact ⟨'n', ['u', 'l', 'l'], by decide, rfl⟩
  | bool b =>
    cases b <;> simp [Value.canonicalJson] at h <;> subst h
    · exact ⟨'f', ['a', 'l', 's', 'e'], by decide, rfl⟩
    · exact ⟨'t', ['r', 'u', 'e'], by decide, rfl⟩
  | int n =>
    simp only [Value.canonicalJson, Option.some.injEq] at h; subst h
    cases hl : (toString n).toList with
    | nil =>
      exfalso
      simp only [toString, Int.repr_eq_ite] at hl
      split at hl
      · simp [Nat.toList_repr, Nat.toDigits_ne_nil] at hl
      · simp [String.toList_append, Digest.minus_toList] at hl
    | cons c r => exact ⟨c, r, rfl, int_toList_char (by rw [hl]; exact List.mem_cons_self)⟩
  | num _ => exact hv.elim
  | str s =>
    simp only [Value.canonicalJson, Option.some.injEq] at h; subst h
    exact ⟨_, _, quote_toList s, rfl⟩
  | arr xs =>
    simp only [Value.canonicalJson, Option.map_eq_some_iff] at h
    obtain ⟨parts, _, rfl⟩ := h
    exact ⟨'[', (",".intercalate parts ++ "]").toList,
      by rw [String.append_assoc, String.toList_append]; rfl, rfl⟩
  | obj ms =>
    simp only [Value.canonicalJson, Option.bind_eq_some_iff] at h
    obtain ⟨ps, _, h⟩ := h
    unfold objectText at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨'{', (",".intercalate ((sortMembers ps).map fun m => quote m.1 ++ ":" ++ m.2) ++
        "}").toList, by rw [String.append_assoc, String.toList_append]; rfl, rfl⟩
    · simp at h

/-- No value's text opens with `,`, `]` or `}`. -/
theorem headOf_plain {v : Value} (hv : sortedV v) {c : Char} (h : headOf v c) :
    c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | null => simp only [headOf] at h; subst h; decide
  | bool b => cases b <;> simp only [headOf] at h <;> subst h <;> decide
  | int _ =>
    simp only [headOf] at h
    rcases h with rfl | h
    · decide
    · refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd h (by decide)
  | num _ => exact hv.elim
  | str _ => simp only [headOf] at h; subst h; decide
  | arr _ => simp only [headOf] at h; subst h; decide
  | obj _ => simp only [headOf] at h; subst h; decide

/-- Each member keeps its key. -/
theorem canonicalJsonMembers_fst :
    ∀ {ms : List (String × Value)} {ps : List (String × String)},
      Value.canonicalJsonMembers ms = some ps → ps.map Prod.fst = ms.map Prod.fst
  | [], ps, h => by simp [Value.canonicalJsonMembers] at h; subst h; rfl
  | (k, v) :: ms, ps, h => by
    simp only [Value.canonicalJsonMembers, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t, _, ts, hts, rfl⟩ := h
    simp [canonicalJsonMembers_fst hts]

/-- An array's text. -/
theorem arr_toList {xs : List Value} {t : String} (h : (Value.arr xs).canonicalJson = some t) :
    ∃ ps, Value.canonicalJsonList xs = some ps ∧
      ∀ a, t.toList ++ a = '[' :: joinAll (ps.map String.toList) ']' a := by
  simp only [Value.canonicalJson, Option.map_eq_some_iff] at h
  obtain ⟨ps, hps, rfl⟩ := h
  refine ⟨ps, hps, fun a => ?_⟩
  rw [← intercalate_joinAll]
  simp [String.toList_append, String.toList_intercalate]

/-- The member texts of an object. -/
def memberTexts (ps : List (String × String)) : List (List Char) :=
  ps.map fun m => (quote m.1).toList ++ ':' :: m.2.toList

/-- A sorted object's text: its members in the order given. -/
theorem obj_toList {ms : List (String × Value)} (hk : (ms.map Prod.fst).Pairwise (· < ·))
    {t : String} (h : (Value.obj ms).canonicalJson = some t) :
    ∃ ps, Value.canonicalJsonMembers ms = some ps ∧
      ∀ a, t.toList ++ a = '{' :: joinAll (memberTexts ps) '}' a := by
  simp only [Value.canonicalJson, Option.bind_eq_some_iff] at h
  obtain ⟨ps, hps, h⟩ := h
  have hf := canonicalJsonMembers_fst hps
  have hsorted : ps.Pairwise fun a b => keyLe a b = true := by
    have : (ps.map Prod.fst).Pairwise (· < ·) := hf ▸ hk
    rw [List.pairwise_map] at this
    exact this.imp fun hab => by simp only [keyLe, decide_eq_true_eq]; exact Std.le_of_not_ge fun h' => h' hab
  have hs : sortMembers ps = ps := List.mergeSort_of_pairwise hsorted
  unfold objectText at h
  rw [hs] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨ps, hps, fun a => ?_⟩
    rw [memberTexts, ← intercalate_joinAll]
    simp [String.toList_append, String.toList_intercalate, Function.comp_def]
  · simp at h

theorem canonicalJsonList_cons {x : Value} {xs : List Value} {ps : List String}
    (h : Value.canonicalJsonList (x :: xs) = some ps) :
    ∃ p qs, x.canonicalJson = some p ∧ Value.canonicalJsonList xs = some qs ∧ ps = p :: qs := by
  simp only [Value.canonicalJsonList, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨p, hp, qs, hqs, rfl⟩ := h
  exact ⟨p, qs, hp, hqs, rfl⟩

theorem canonicalJsonMembers_cons {k : String} {v : Value} {ms : List (String × Value)}
    {ps : List (String × String)} (h : Value.canonicalJsonMembers ((k, v) :: ms) = some ps) :
    ∃ p qs, v.canonicalJson = some p ∧ Value.canonicalJsonMembers ms = some qs ∧
      ps = (k, p) :: qs := by
  simp only [Value.canonicalJsonMembers, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨p, hp, qs, hqs, rfl⟩ := h
  exact ⟨p, qs, hp, hqs, rfl⟩

theorem canonicalJsonList_nil {ps : List String} (h : Value.canonicalJsonList [] = some ps) :
    ps = [] := by simp [Value.canonicalJsonList] at h; exact h

theorem canonicalJsonMembers_nil {ps : List (String × String)}
    (h : Value.canonicalJsonMembers [] = some ps) : ps = [] := by
  simp [Value.canonicalJsonMembers] at h; exact h

/-- A text that opens with a value's text never opens with `,`, `]` or `}`. -/
theorem text_head_plain {v : Value} (hv : sortedV v) {t : String} (ht : v.canonicalJson = some t)
    {c : Char} {r a : List Char} (h : t.toList ++ a = c :: r) : c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' := by
  obtain ⟨d, r', hd, hh⟩ := canonicalJson_head v hv ht
  rw [hd, List.cons_append, List.cons.injEq] at h
  exact h.1 ▸ headOf_plain hv hh

/-! ## Canonical JSON tells sorted values apart -/

/-- What follows an element: `,` or the closing character. -/
theorem joinTail_delim (ps : List (List Char)) (a : List Char) {e : Char}
    (he : e = ',' ∨ e = ']' ∨ e = '}') : Delim (joinTail ps e a) := by
  cases ps with
  | nil => intro c r h; simp only [joinTail, List.cons.injEq] at h; exact h.1 ▸ he
  | cons p ps => exact delim_comma _

/-- Only a list's text opens with `[`. -/
theorem head_arr {w : Value} (hw : sortedV w) (h : headOf w '[') : ∃ ys, w = .arr ys := by
  rcases w with _ | (_ | _) | _ | _ | _ | ys | _ <;> simp only [headOf] at h <;>
    first | exact ⟨ys, rfl⟩ | exact hw.elim | exact absurd h (by decide)

/-- Only an object's text opens with `{`. -/
theorem head_obj {w : Value} (hw : sortedV w) (h : headOf w '{') : ∃ ns, w = .obj ns := by
  rcases w with _ | (_ | _) | _ | _ | _ | _ | ns <;> simp only [headOf] at h <;>
    first | exact ⟨ns, rfl⟩ | exact hw.elim | exact absurd h (by decide)

/-- Two texts that open two lists alike open with one character. -/
theorem common_head {v w : Value} (hv : sortedV v) (hw : sortedV w) {t t' : String}
    {a b : List Char} (ht : v.canonicalJson = some t) (ht' : w.canonicalJson = some t')
    (h : t.toList ++ a = t'.toList ++ b) : ∃ c, headOf v c ∧ headOf w c := by
  obtain ⟨c, r, hc, hh⟩ := canonicalJson_head v hv ht
  obtain ⟨c', r', hc', hh'⟩ := canonicalJson_head w hw ht'
  rw [hc, hc', List.cons_append, List.cons_append, List.cons.injEq] at h
  exact ⟨c, hh, h.1 ▸ hh'⟩

/-- Two values of one scalar text: null, a Boolean, an integer or a string. -/
theorem scalar_prefix {v w : Value} (hv : sortedV v) (hw : sortedV w)
    (hs : ∀ xs, v ≠ .arr xs) (hs' : ∀ ms, v ≠ .obj ms) {t t' : String} {a b : List Char}
    (ht : v.canonicalJson = some t) (ht' : w.canonicalJson = some t')
    (ha : Delim a) (hb : Delim b) (h : t.toList ++ a = t'.toList ++ b) : v = w ∧ a = b := by
  obtain ⟨c, h1, h2⟩ := common_head hv hw ht ht' h
  rcases v with _ | (_ | _) | n | x | s | xs | ms <;>
    rcases w with _ | (_ | _) | n' | x' | s' | ys | ns <;>
    simp only [headOf] at h1 h2 <;>
    (try exact hv.elim) <;> (try exact hw.elim) <;>
    (try exact absurd rfl (hs _)) <;> (try exact absurd rfl (hs' _))
  all_goals first
    | (subst h1; exact absurd h2 (by decide))
    | (subst h2; exact absurd h1 (by decide))
    | skip
  all_goals simp only [Value.canonicalJson, Option.some.injEq] at ht ht'
  all_goals subst ht ht'
  · exact ⟨rfl, List.append_cancel_left h⟩
  · exact ⟨rfl, List.append_cancel_left h⟩
  · exact ⟨rfl, List.append_cancel_left h⟩
  · obtain ⟨e1, e2⟩ := digits_prefix (fun c hc => int_toList_char hc)
      (fun c hc => int_toList_char hc) ha hb h
    exact ⟨congrArg _ (Digest.int_toString_inj (String.toList_inj.mp e1)), e2⟩
  · obtain ⟨rfl, rfl⟩ := quote_prefix h
    exact ⟨rfl, rfl⟩

mutual
/-- **Canonical JSON tells sorted values apart**: two sorted values whose texts, each
followed by nothing or by `,`, `]` or `}`, are one character list are one value, and what
follows them is one. -/
theorem canonicalJson_prefix : ∀ (v w : Value), sortedV v → sortedV w →
    ∀ {t t' : String} {a b : List Char}, v.canonicalJson = some t → w.canonicalJson = some t' →
      Delim a → Delim b → t.toList ++ a = t'.toList ++ b → v = w ∧ a = b
  | .arr xs, w, hv, hw, _, _, _, _, ht, ht', _, _, h => by
    obtain ⟨c, h1, h2⟩ := common_head hv hw ht ht' h
    simp only [headOf] at h1; subst h1
    obtain ⟨ys, rfl⟩ := head_arr hw h2
    obtain ⟨ps, hps, ep⟩ := arr_toList ht
    obtain ⟨qs, hqs, eq⟩ := arr_toList ht'
    rw [ep, eq, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := list_prefix xs ys hv hw hps hqs h.2
    exact ⟨rfl, rfl⟩
  | .obj ms, w, hv, hw, _, _, _, _, ht, ht', _, _, h => by
    obtain ⟨c, h1, h2⟩ := common_head hv hw ht ht' h
    simp only [headOf] at h1; subst h1
    obtain ⟨ns, rfl⟩ := head_obj hw h2
    obtain ⟨ps, hps, ep⟩ := obj_toList hv.2 ht
    obtain ⟨qs, hqs, eq⟩ := obj_toList hw.2 ht'
    rw [ep, eq, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := members_prefix ms ns hv.1 hw.1 hps hqs h.2
    exact ⟨rfl, rfl⟩
  | .null, _, hv, hw, _, _, _, _, ht, ht', ha, hb, h =>
    scalar_prefix hv hw (fun _ e => nomatch e) (fun _ e => nomatch e) ht ht' ha hb h
  | .bool _, _, hv, hw, _, _, _, _, ht, ht', ha, hb, h =>
    scalar_prefix hv hw (fun _ e => nomatch e) (fun _ e => nomatch e) ht ht' ha hb h
  | .int _, _, hv, hw, _, _, _, _, ht, ht', ha, hb, h =>
    scalar_prefix hv hw (fun _ e => nomatch e) (fun _ e => nomatch e) ht ht' ha hb h
  | .num _, _, hv, _, _, _, _, _, _, _, _, _, _ => hv.elim
  | .str _, _, hv, hw, _, _, _, _, ht, ht', ha, hb, h =>
    scalar_prefix hv hw (fun _ e => nomatch e) (fun _ e => nomatch e) ht ht' ha hb h

/-- A list's elements, each followed by `,` or `]`. -/
theorem list_prefix : ∀ (xs ys : List Value), sortedL xs → sortedL ys →
    ∀ {ps qs : List String} {a b : List Char}, Value.canonicalJsonList xs = some ps →
      Value.canonicalJsonList ys = some qs →
      joinAll (ps.map String.toList) ']' a = joinAll (qs.map String.toList) ']' b →
      xs = ys ∧ a = b
  | [], [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hp, canonicalJsonList_nil hq] at h
    simp only [List.map_nil, joinAll, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | [], y :: _, _, hy, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hp] at h
    obtain ⟨q, _, hq1, _, rfl⟩ := canonicalJsonList_cons hq
    simp only [List.map_nil, List.map_cons, joinAll] at h
    exact absurd rfl (text_head_plain hy.1 hq1 h.symm).2.1
  | x :: _, [], hx, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hq] at h
    obtain ⟨p, _, hp1, _, rfl⟩ := canonicalJsonList_cons hp
    simp only [List.map_nil, List.map_cons, joinAll] at h
    exact absurd rfl (text_head_plain hx.1 hp1 h).2.1
  | x :: xs, y :: ys, hx, hy, _, _, _, _, hp, hq, h => by
    obtain ⟨p, ps, hp1, hps, rfl⟩ := canonicalJsonList_cons hp
    obtain ⟨q, qs, hq1, hqs, rfl⟩ := canonicalJsonList_cons hq
    simp only [List.map_cons, joinAll] at h
    obtain ⟨rfl, h'⟩ := canonicalJson_prefix x y hx.1 hy.1 hp1 hq1
      (joinTail_delim _ _ (.inr (.inl rfl))) (joinTail_delim _ _ (.inr (.inl rfl))) h
    obtain ⟨rfl, rfl⟩ := list_tail xs ys hx.2 hy.2 hps hqs h'
    exact ⟨rfl, rfl⟩

/-- A list's later elements, each opened by `,`, then `]`. -/
theorem list_tail : ∀ (xs ys : List Value), sortedL xs → sortedL ys →
    ∀ {ps qs : List String} {a b : List Char}, Value.canonicalJsonList xs = some ps →
      Value.canonicalJsonList ys = some qs →
      joinTail (ps.map String.toList) ']' a = joinTail (qs.map String.toList) ']' b →
      xs = ys ∧ a = b
  | [], [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hp, canonicalJsonList_nil hq] at h
    simp only [List.map_nil, joinTail, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | [], _ :: _, _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hp] at h
    obtain ⟨q, _, _, _, rfl⟩ := canonicalJsonList_cons hq
    simp [joinTail] at h
  | _ :: _, [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonList_nil hq] at h
    obtain ⟨p, _, _, _, rfl⟩ := canonicalJsonList_cons hp
    simp [joinTail] at h
  | x :: xs, y :: ys, hx, hy, _, _, _, _, hp, hq, h => by
    obtain ⟨p, ps, hp1, hps, rfl⟩ := canonicalJsonList_cons hp
    obtain ⟨q, qs, hq1, hqs, rfl⟩ := canonicalJsonList_cons hq
    simp only [List.map_cons, joinTail, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h'⟩ := canonicalJson_prefix x y hx.1 hy.1 hp1 hq1
      (joinTail_delim _ _ (.inr (.inl rfl))) (joinTail_delim _ _ (.inr (.inl rfl))) h
    obtain ⟨rfl, rfl⟩ := list_tail xs ys hx.2 hy.2 hps hqs h'
    exact ⟨rfl, rfl⟩

/-- An object's members, each followed by `,` or `}`. -/
theorem members_prefix : ∀ (ms ns : List (String × Value)), sortedM ms → sortedM ns →
    ∀ {ps qs : List (String × String)} {a b : List Char}, Value.canonicalJsonMembers ms = some ps →
      Value.canonicalJsonMembers ns = some qs →
      joinAll (memberTexts ps) '}' a = joinAll (memberTexts qs) '}' b →
      ms = ns ∧ a = b
  | [], [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hp, canonicalJsonMembers_nil hq] at h
    simp only [memberTexts, List.map_nil, joinAll, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | [], (_, _) :: _, _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hp] at h
    obtain ⟨q, _, _, _, rfl⟩ := canonicalJsonMembers_cons hq
    simp [memberTexts, joinAll, quote_toList] at h
  | (_, _) :: _, [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hq] at h
    obtain ⟨p, _, _, _, rfl⟩ := canonicalJsonMembers_cons hp
    simp [memberTexts, joinAll, quote_toList] at h
  | (k, v) :: ms, (k', w) :: ns, hv, hw, _, _, _, _, hp, hq, h => by
    obtain ⟨p, ps, hp1, hps, rfl⟩ := canonicalJsonMembers_cons hp
    obtain ⟨q, qs, hq1, hqs, rfl⟩ := canonicalJsonMembers_cons hq
    simp only [memberTexts, List.map_cons, joinAll, List.append_assoc, List.cons_append] at h
    obtain ⟨rfl, h2⟩ := quote_prefix h
    injection h2 with _ h3
    obtain ⟨rfl, h'⟩ := canonicalJson_prefix v w hv.1 hw.1 hp1 hq1
      (joinTail_delim _ _ (.inr (.inr rfl))) (joinTail_delim _ _ (.inr (.inr rfl))) h3
    obtain ⟨rfl, rfl⟩ := members_tail ms ns hv.2 hw.2 hps hqs h'
    exact ⟨rfl, rfl⟩

/-- An object's later members, each opened by `,`, then `}`. -/
theorem members_tail : ∀ (ms ns : List (String × Value)), sortedM ms → sortedM ns →
    ∀ {ps qs : List (String × String)} {a b : List Char}, Value.canonicalJsonMembers ms = some ps →
      Value.canonicalJsonMembers ns = some qs →
      joinTail (memberTexts ps) '}' a = joinTail (memberTexts qs) '}' b →
      ms = ns ∧ a = b
  | [], [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hp, canonicalJsonMembers_nil hq] at h
    simp only [memberTexts, List.map_nil, joinTail, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | [], (_, _) :: _, _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hp] at h
    obtain ⟨q, _, _, _, rfl⟩ := canonicalJsonMembers_cons hq
    simp [memberTexts, joinTail] at h
  | (_, _) :: _, [], _, _, _, _, _, _, hp, hq, h => by
    rw [canonicalJsonMembers_nil hq] at h
    obtain ⟨p, _, _, _, rfl⟩ := canonicalJsonMembers_cons hp
    simp [memberTexts, joinTail] at h
  | (k, v) :: ms, (k', w) :: ns, hv, hw, _, _, _, _, hp, hq, h => by
    obtain ⟨p, ps, hp1, hps, rfl⟩ := canonicalJsonMembers_cons hp
    obtain ⟨q, qs, hq1, hqs, rfl⟩ := canonicalJsonMembers_cons hq
    simp only [memberTexts, List.map_cons, joinTail, List.append_assoc, List.cons_append,
      List.cons.injEq, true_and] at h
    obtain ⟨rfl, h2⟩ := quote_prefix h
    injection h2 with _ h3
    obtain ⟨rfl, h'⟩ := canonicalJson_prefix v w hv.1 hw.1 hp1 hq1
      (joinTail_delim _ _ (.inr (.inr rfl))) (joinTail_delim _ _ (.inr (.inr rfl))) h3
    obtain ⟨rfl, rfl⟩ := members_tail ms ns hv.2 hw.2 hps hqs h'
    exact ⟨rfl, rfl⟩
end

/-! ## The wire object's text is a sorted value's text -/

/-- A step with its members in key order. -/
def StructuredStep.sortedValue (s : StructuredStep) : Value :=
  match s.cites with
  | .law n => .obj [("EQUATION", .str s.equation), ("FORWARD", .bool s.forward),
      ("LAW", .str n), ("SITE", .str s.site)]
  | .assumption r => .obj [("ASSUMPTION", .str r), ("EQUATION", .str s.equation),
      ("FORWARD", .bool s.forward), ("SITE", .str s.site)]
  | .identity n => .obj [("EQUATION", .str s.equation), ("FORWARD", .bool s.forward),
      ("IDENTITY", .str n), ("SITE", .str s.site)]

/-- A STRUCTURED payload with its members in key order. -/
def sortedStructured (steps : List StructuredStep) (start : StructuredStart) : Value :=
  .obj ((start.toValue?.map fun v => [("START", v)]).getD [] ++
    [("STEPS", .arr (steps.map StructuredStep.sortedValue))])

/-- An attachment with its members in key order. -/
def Attachment.sortedValue : Attachment → Value
  | .structured steps start => sortedStructured steps start
  | .kernelProof p => kernelToValue p

/-- A DERIVATION's wire object with every object's members in key order. -/
def sortedDerivation : Derivation → Value
  | .prose n text att =>
    .obj ((att.map fun a => [("ATTACHMENT", a.sortedValue)]).getD [] ++
      [("STEPS", .int n), ("TEXT", .str text)])
  | .structured steps start => sortedStructured steps start
  | .kernelProof p => kernelToValue p

theorem StructuredStep.canonicalJson_sortedValue (s : StructuredStep) :
    s.toValue.canonicalJson = s.sortedValue.canonicalJson := by
  obtain ⟨e, c, site, fwd⟩ := s
  cases c <;> apply canonicalJson_obj_perm <;>
    simp only [StepCitation.member]
  · exact .cons _ (List.perm_middle (l₁ := [_, _]) (l₂ := []))
  · exact (List.Perm.swap _ _ _).trans (.cons _ (.cons _ (List.Perm.swap _ _ _)))
  · exact .cons _ (List.perm_middle (l₁ := [_, _]) (l₂ := []))

theorem canonicalJsonList_sortedValue (steps : List StructuredStep) :
    Value.canonicalJsonList (steps.map StructuredStep.toValue) =
      Value.canonicalJsonList (steps.map StructuredStep.sortedValue) := by
  induction steps with
  | nil => rfl
  | cons s steps ih =>
    simp only [List.map_cons, Value.canonicalJsonList, s.canonicalJson_sortedValue, ih]

theorem canonicalJson_sortedStructured (steps : List StructuredStep) (start : StructuredStart) :
    (structuredToValue steps start).canonicalJson = (sortedStructured steps start).canonicalJson := by
  cases start <;>
    simp only [structuredToValue, sortedStructured, StructuredStart.toValue?, Option.map,
      Option.getD, List.nil_append, List.cons_append, Value.canonicalJson,
      Value.canonicalJsonMembers, canonicalJsonList_sortedValue]

theorem Attachment.canonicalJson_sortedValue (a : Attachment) :
    a.toValue.canonicalJson = a.sortedValue.canonicalJson := by
  cases a with
  | structured steps start => exact canonicalJson_sortedStructured steps start
  | kernelProof p => rfl

/-- The wire object's text is the sorted value's. -/
theorem canonicalJson_derivationToValue (d : Derivation) :
    (derivationToValue d).canonicalJson = (sortedDerivation d).canonicalJson := by
  cases d with
  | prose n text att =>
    cases att with
    | none => rfl
    | some a =>
      simp only [derivationToValue, sortedDerivation, Option.map, Option.getD]
      rw [canonicalJson_obj_perm (ms' := [("ATTACHMENT", a.toValue), ("STEPS", .int ↑n),
        ("TEXT", .str text)]) (List.perm_middle (l₁ := [_, _]) (l₂ := []))]
      simp only [Value.canonicalJson, Value.canonicalJsonMembers, a.canonicalJson_sortedValue,
        List.cons_append, List.nil_append]
  | structured steps start => exact canonicalJson_sortedStructured steps start
  | kernelProof p => rfl

/-! ## The sorted value is sorted, written, and names the derivation -/

theorem StructuredStep.sortedV_sortedValue (s : StructuredStep) : sortedV s.sortedValue := by
  obtain ⟨e, c, site, fwd⟩ := s
  cases c <;> simp only [StructuredStep.sortedValue, sortedV, sortedM, List.map] <;>
    refine ⟨by simp, by decide⟩

theorem sortedL_sortedValue (steps : List StructuredStep) :
    sortedL (steps.map StructuredStep.sortedValue) := by
  induction steps with
  | nil => trivial
  | cons s steps ih => exact ⟨s.sortedV_sortedValue, ih⟩

theorem sortedV_sortedStructured (steps : List StructuredStep) (start : StructuredStart) :
    sortedV (sortedStructured steps start) := by
  cases start <;>
    simp only [sortedStructured, StructuredStart.toValue?, Option.map, Option.getD,
      List.nil_append, List.cons_append, sortedV, sortedM, List.map] <;>
    refine ⟨by simp [sortedL_sortedValue], by decide⟩

theorem sortedV_sortedDerivation (d : Derivation) : sortedV (sortedDerivation d) := by
  cases d with
  | prose n text att =>
    cases att with
    | none =>
      refine ⟨by simp [sortedV, sortedM], ?_⟩
      simp only [Option.map, Option.getD, List.nil_append, List.map]
      decide
    | some a =>
      refine ⟨⟨?_, by simp [sortedV, sortedM]⟩, ?_⟩
      rotate_left
      · simp only [Option.map, Option.getD, List.cons_append,
          List.nil_append, List.map]
        decide
      cases a with
      | structured steps start => exact sortedV_sortedStructured steps start
      | kernelProof p => exact ⟨by simp [sortedV, sortedM], by simp⟩
  | structured steps start => exact sortedV_sortedStructured steps start
  | kernelProof p => exact ⟨by simp [sortedV, sortedM], by simp⟩

theorem StructuredStep.sortedValue_injective {s s' : StructuredStep}
    (h : s.sortedValue = s'.sortedValue) : s = s' := by
  obtain ⟨e, c, site, fwd⟩ := s
  obtain ⟨e', c', site', fwd'⟩ := s'
  cases c <;> cases c' <;> simp_all [StructuredStep.sortedValue]

theorem map_sortedValue_injective :
    ∀ {xs ys : List StructuredStep},
      xs.map StructuredStep.sortedValue = ys.map StructuredStep.sortedValue → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [StructuredStep.sortedValue_injective h.1, map_sortedValue_injective h.2]

theorem sortedStructured_injective {steps steps' : List StructuredStep}
    {start start' : StructuredStart}
    (h : sortedStructured steps start = sortedStructured steps' start') :
    steps = steps' ∧ start = start' := by
  cases start <;> cases start' <;>
    simp [sortedStructured, StructuredStart.toValue?] at h <;>
    first
    | exact ⟨map_sortedValue_injective h, rfl⟩
    | exact ⟨map_sortedValue_injective h.2, by rw [h.1]⟩
    | skip

theorem sortedStructured_ne_kernel (steps : List StructuredStep) (start : StructuredStart)
    (p : String) : sortedStructured steps start ≠ kernelToValue p := by
  cases start <;> simp [sortedStructured, StructuredStart.toValue?, kernelToValue]

theorem Attachment.sortedValue_injective {a a' : Attachment}
    (h : a.sortedValue = a'.sortedValue) : a = a' := by
  cases a with
  | structured steps start =>
    cases a' with
    | structured steps' start' =>
      obtain ⟨rfl, rfl⟩ := sortedStructured_injective h
      rfl
    | kernelProof p => exact absurd h (sortedStructured_ne_kernel _ _ _)
  | kernelProof p =>
    cases a' with
    | structured steps' start' => exact absurd h.symm (sortedStructured_ne_kernel _ _ _)
    | kernelProof p' => simp [Attachment.sortedValue, kernelToValue] at h; rw [h]

/-- The sorted value names the derivation. -/
theorem sortedDerivation_injective {d d' : Derivation}
    (h : sortedDerivation d = sortedDerivation d') : d = d' := by
  cases d with
  | prose n t att =>
    cases d' with
    | prose n' t' att' =>
      cases att <;> cases att' <;> simp [sortedDerivation] at h
      · obtain ⟨hn, rfl⟩ := h
        have : n = n' := by omega
        rw [this]
      · obtain ⟨ha, hn, rfl⟩ := h
        have : n = n' := by omega
        rw [this, Attachment.sortedValue_injective ha]
    | structured steps start =>
      cases att <;> cases start <;>
        simp [sortedDerivation, sortedStructured, StructuredStart.toValue?] at h
    | kernelProof p => cases att <;> simp [sortedDerivation, kernelToValue] at h
  | structured steps start =>
    cases d' with
    | prose n' t' att' =>
      cases att' <;> cases start <;>
        simp [sortedDerivation, sortedStructured, StructuredStart.toValue?] at h
    | structured steps' start' =>
      obtain ⟨rfl, rfl⟩ := sortedStructured_injective h
      rfl
    | kernelProof p => exact absurd h (sortedStructured_ne_kernel _ _ _)
  | kernelProof p =>
    cases d' with
    | prose n' t' att' => cases att' <;> simp [sortedDerivation, kernelToValue] at h
    | structured steps' start' => exact absurd h.symm (sortedStructured_ne_kernel _ _ _)
    | kernelProof p' => simp [sortedDerivation, kernelToValue] at h; rw [h]

theorem Attachment.toValue_isSome (a : Attachment) : a.toValue.canonicalJson.isSome := by
  cases a with
  | structured steps start => exact structuredToValue_canonicalJson_isSome steps start
  | kernelProof p =>
    exact canonicalJson_obj_isSome (by simp [Value.canonicalJson]) (by simp)

/-- Every DERIVATION's wire object is written. -/
theorem derivationToValue_isSome (d : Derivation) : (derivationToValue d).canonicalJson.isSome := by
  cases d with
  | prose n text att =>
    cases att with
    | none =>
      exact canonicalJson_obj_isSome (by simp [Value.canonicalJson]) (by
        simp only [Option.map, Option.getD, List.append_nil, List.map]; decide)
    | some a =>
      refine canonicalJson_obj_isSome ?_ (by simp only [Option.map, Option.getD,
        List.cons_append, List.nil_append, List.map]; decide)
      simp only [Option.map, Option.getD, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro m (rfl | rfl | rfl)
      · rfl
      · rfl
      · exact a.toValue_isSome
  | structured steps start => exact structuredToValue_canonicalJson_isSome steps start
  | kernelProof p =>
    exact canonicalJson_obj_isSome (by simp [Value.canonicalJson]) (by simp)

/-- **A DERIVATION's canonical text names one derivation**: two derivations whose wire
objects have one canonical JSON text are one derivation, its form, its steps, its START, its
attachment and its PROOF included. -/
theorem cj_derivationToValue_injective {d d' : Derivation}
    (h : cj (derivationToValue d) = cj (derivationToValue d')) : d = d' := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (derivationToValue_isSome d)
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (derivationToValue_isSome d')
  simp only [cj, ht, ht', Option.getD_some] at h
  subst h
  rw [canonicalJson_derivationToValue] at ht ht'
  exact sortedDerivation_injective (canonicalJson_prefix _ _ (sortedV_sortedDerivation d)
    (sortedV_sortedDerivation d') ht ht' delim_nil delim_nil rfl).1

end Principia.Record
