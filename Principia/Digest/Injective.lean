import Principia.Digest

/-!
# A preimage stands for one field list (SC5)

The Research Assembly's PROVED class (SC5) names "digest preimage injectivity for every digest form",
and TPS 2.5.10 and 2.5.11 state it: "one byte sequence stands for one ordered field list",
and the type tag "makes the encoding injective over every tree, validated or not". Here the
Lean kernel checks it for each form a PMA digest is taken over:

* `preimage_injective`: the netstring encoding of a list of texts (`Digest.preimage`). Two
  lists with one preimage are the same list: the same number of texts, each the same text.
* `preimageFields_bytes` and `preimageFields_injective`: a field list (`Digest.Field`, a text
  or an integer). A preimage gives every field's bytes; two field lists with one preimage
  whose fields are of the same kinds, position by position, are the same list. The kinds are
  the producer's to fix: a text "10" and the integer 10 have one preimage
  (`preimageFields_int_text`), as in v1.
* `preimageDigests_injective` and `preimageResearchAssembly_injective`: the combination rule
  (TPS 2.5.3) over a list of digests, and D(RAS) over the three zones' digests.
* `Tree.preimage_injective`: the type-tagged tree encoding of a zone (TPS 2.5.11), over every
  tree, validated or not.

What is proved is the encoding, which is all that is SHA-256's input: that a digest is never
the digest of two different preimages is SHA-256's collision resistance, which no proof here
claims.

The proof reads a preimage as its characters: a netstring is its length's decimal digits, a
colon and its text, and the digits hold no colon, so the first colon ends them; the length is
then a count of UTF-8 bytes, and of two texts of one byte count that begin one list, neither
can be a longer prefix, since every character has at least one byte.
-/

namespace Principia.Digest

/-! ## One netstring -/

theorem colon_toList : (":" : String).toList = [':'] := by decide

theorem minus_toList : ("-" : String).toList = ['-'] := by decide

/-- A netstring's characters: the decimal digits of its text's UTF-8 byte count, a colon,
the text. -/
theorem netstring_toList (s : String) :
    (netstring s).toList = Nat.toDigits 10 s.utf8ByteSize ++ ':' :: s.toList := by
  simp only [netstring, String.toList_append, toString, Nat.toList_repr, colon_toList]
  simp

/-- No netstring is empty. -/
theorem netstring_ne_empty (s : String) : netstring s ≠ "" := fun h => by
  have := congrArg String.toList h
  rw [netstring_toList] at this
  simp at this

/-- Two lists that hold a separator, neither before it, split alike at it. -/
theorem split_at_first {c : Char} :
    ∀ {l₁ l₂ r₁ r₂ : List Char}, c ∉ l₁ → c ∉ l₂ → l₁ ++ c :: r₁ = l₂ ++ c :: r₂ →
      l₁ = l₂ ∧ r₁ = r₂
  | [], [], _, _, _, _, h => by simpa using h
  | [], _ :: _, _, _, _, h₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | _ :: _, [], _, _, h₁, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₁
  | a :: _, b :: _, _, _, h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    have ih := split_at_first (fun m => h₁ (List.mem_cons_of_mem a m))
      (fun m => h₂ (List.mem_cons_of_mem b m)) h.2
    exact ⟨by rw [h.1, ih.1], ih.2⟩

/-- A number's decimal digits give the number back. -/
theorem toDigits_ten_inj {n m : Nat} (h : Nat.toDigits 10 n = Nat.toDigits 10 m) : n = m := by
  rw [← Nat.ofDigitChars_ten_toDigits (n := n), ← Nat.ofDigitChars_ten_toDigits (n := m), h]

/-- A natural number's text gives the number back. -/
theorem nat_toString_inj {n m : Nat} (h : toString n = toString m) : n = m := by
  apply toDigits_ten_inj
  have := congrArg String.toList h
  simpa [toString, Nat.toList_repr] using this

/-- A character that is not a decimal digit is in no number's digits. -/
theorem not_mem_toDigits {c : Char} (hc : c.isDigit = false) {n : Nat} :
    c ∉ Nat.toDigits 10 n := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  rw [hc] at this
  exact Bool.false_ne_true this

/-- An integer's text gives the integer back: a negative one opens with `-`, which is no
digit. -/
theorem int_toString_inj {a b : Int} (h : toString a = toString b) : a = b := by
  have h' := congrArg String.toList h
  simp only [toString, Int.repr_eq_ite] at h'
  split at h' <;> split at h'
  · simp only [Nat.toList_repr] at h'
    have := toDigits_ten_inj h'
    omega
  · simp only [String.toList_append, Nat.toList_repr, minus_toList, List.cons_append,
      List.nil_append] at h'
    exact absurd (h' ▸ List.mem_cons_self) (not_mem_toDigits (by decide))
  · simp only [String.toList_append, Nat.toList_repr, minus_toList, List.cons_append,
      List.nil_append] at h'
    exact absurd (h'.symm ▸ List.mem_cons_self) (not_mem_toDigits (by decide))
  · simp only [String.toList_append, Nat.toList_repr, minus_toList, List.cons_append,
      List.nil_append, List.cons.injEq, true_and] at h'
    have := toDigits_ten_inj h'
    omega

/-- Of two texts of one UTF-8 byte count that begin one list of characters, each is the
other: a longer one would add characters of no bytes. -/
theorem prefix_of_byteSize {s t : String} {r₁ r₂ : List Char}
    (hs : s.utf8ByteSize = t.utf8ByteSize) (h : s.toList ++ r₁ = t.toList ++ r₂) :
    s = t ∧ r₁ = r₂ := by
  rcases List.append_eq_append_iff.mp h with ⟨as, ht, hr⟩ | ⟨bs, hs', hr⟩
  · have ht' : t = s ++ String.ofList as := String.toList_injective (by
      simp [String.toList_append, ht])
    have h0 : (String.ofList as).utf8ByteSize = 0 := by
      rw [ht', String.utf8ByteSize_append] at hs; omega
    have has : as = [] := by
      have := String.utf8ByteSize_eq_zero_iff.mp h0
      rw [← String.toList_ofList (l := as), this]; rfl
    subst has
    exact ⟨by simpa using ht'.symm, by simpa using hr⟩
  · have hs'' : s = t ++ String.ofList bs := String.toList_injective (by
      simp [String.toList_append, hs'])
    have h0 : (String.ofList bs).utf8ByteSize = 0 := by
      rw [hs'', String.utf8ByteSize_append] at hs; omega
    have hbs : bs = [] := by
      have := String.utf8ByteSize_eq_zero_iff.mp h0
      rw [← String.toList_ofList (l := bs), this]; rfl
    subst hbs
    exact ⟨by simpa using hs'', by simpa using hr.symm⟩

/-- A netstring that begins a list of characters is read off it alone: its text and what
follows are determined. -/
theorem netstring_append_inj {x y : String} {r₁ r₂ : List Char}
    (h : (netstring x).toList ++ r₁ = (netstring y).toList ++ r₂) : x = y ∧ r₁ = r₂ := by
  rw [netstring_toList, netstring_toList] at h
  simp only [List.append_assoc, List.cons_append] at h
  have ⟨hd, hr⟩ := split_at_first (not_mem_toDigits (by decide))
    (not_mem_toDigits (by decide)) h
  exact prefix_of_byteSize (toDigits_ten_inj hd) hr

/-! ## A list of texts (`preimage`) -/

/-- A preimage's characters: its netstrings' characters in order. -/
theorem preimage_toList (xs : List String) :
    (preimage xs).toList = (xs.map netstring).flatMap String.toList := by
  simp [preimage, String.toList_join]

/-- **SC5.** One preimage stands for one list of texts (TPS 2.5.10). -/
theorem preimage_injective : ∀ {xs ys : List String}, preimage xs = preimage ys → xs = ys
  | [], [], _ => rfl
  | [], y :: _, h => by
    have := congrArg String.toList h
    simp [preimage_toList] at this
    exact absurd this.1 (netstring_ne_empty y)
  | x :: _, [], h => by
    have := congrArg String.toList h
    simp [preimage_toList] at this
    exact absurd this.1 (netstring_ne_empty x)
  | x :: xs, y :: ys, h => by
    have h' := congrArg String.toList h
    simp only [preimage_toList, List.map_cons, List.flatMap_cons] at h'
    have ⟨hxy, hr⟩ := netstring_append_inj h'
    have hrest : preimage xs = preimage ys := String.toList_injective (by
      rw [preimage_toList, preimage_toList]; exact hr)
    rw [hxy, preimage_injective hrest]

theorem preimage_inj {xs ys : List String} : preimage xs = preimage ys ↔ xs = ys :=
  ⟨preimage_injective, fun h => h ▸ rfl⟩

/-! ## A field list (`preimageFields`) -/

/-- A field's kind: an integer, or a text. -/
def Field.isInt : Field → Bool
  | .text _ => false
  | .int _ => true

/-- A preimage gives every field's bytes. -/
theorem preimageFields_bytes {a b : List Field} (h : preimageFields a = preimageFields b) :
    a.map Field.bytes = b.map Field.bytes :=
  preimage_injective h

/-- Two fields of one kind with the same bytes are the same field. -/
theorem Field.bytes_inj : ∀ {f g : Field}, f.isInt = g.isInt → f.bytes = g.bytes → f = g
  | .text _, .text _, _, h => by simp only [Field.bytes] at h; rw [h]
  | .int _, .int _, _, h => by simp only [Field.bytes] at h; rw [int_toString_inj h]
  | .text _, .int _, hk, _ | .int _, .text _, hk, _ => by simp [Field.isInt] at hk

/-- **SC5.** Two field lists with one preimage, whose fields are of the same kinds position by
position, are the same field list. -/
theorem preimageFields_injective : ∀ {a b : List Field}, a.map Field.isInt = b.map Field.isInt →
    preimageFields a = preimageFields b → a = b
  | a, b, hk, h => by
    have hb := preimageFields_bytes h
    clear h
    induction a generalizing b with
    | nil => cases b with
      | nil => rfl
      | cons _ _ => simp at hk
    | cons f a ih => cases b with
      | nil => simp at hk
      | cons g b =>
        simp only [List.map_cons, List.cons.injEq] at hk hb
        rw [Field.bytes_inj hk.1 hb.1, ih _ hk.2 hb.2]

/-! ## The combination rule and D(RAS) -/

/-- **SC5.** Two lists of digests with one preimage are the same list (TPS 2.5.3). -/
theorem preimageDigests_injective {xs ys : List String} {p : String}
    (hx : preimageDigests xs = some p) (hy : preimageDigests ys = some p) : xs = ys := by
  unfold preimageDigests at hx hy
  split at hx <;> split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hx hy
  exact preimage_injective (hx.trans hy.symm)

/-- **SC5.** D(RAS)'s preimage gives the three zones' digests back, each in its place. -/
theorem preimageResearchAssembly_injective {a b c a' b' c' p : String}
    (h : preimageResearchAssembly a b c = some p)
    (h' : preimageResearchAssembly a' b' c' = some p) :
    a = a' ∧ b = b' ∧ c = c' := by
  have := preimageDigests_injective h h'
  simp only [List.cons.injEq, and_true] at this
  exact this

/-! ## The tree encoding (TPS 2.5.11) -/

/-- A string's join over a list's head. -/
theorem join_cons (a : String) (l : List String) : String.join (a :: l) = a ++ String.join l :=
  String.toList_injective (by simp [String.toList_join, String.toList_append])

/-- A list's children are the netstrings of their encodings: `preimage` over them. -/
theorem Tree.childrenPreimage_eq (xs : List Tree) :
    Tree.childrenPreimage xs = Digest.preimage (xs.map Tree.preimage) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Tree.childrenPreimage, ih, Digest.preimage, List.map_cons, List.map_map, join_cons]

theorem Tree.preimage_text (s : String) : (Tree.text s).preimage.toList = 's' :: s.toList := by
  simp only [Tree.preimage, String.toList_append]; rfl

theorem Tree.preimage_int (n : Int) :
    (Tree.int n).preimage.toList = 'i' :: (toString n).toList := by
  simp only [Tree.preimage, String.toList_append]; rfl

theorem Tree.preimage_list (xs : List Tree) :
    (Tree.list xs).preimage.toList = 'l' :: (Digest.preimage (xs.map Tree.preimage)).toList := by
  simp only [Tree.preimage, String.toList_append, Tree.childrenPreimage_eq]; rfl

mutual
/-- **SC5.** One encoding stands for one tree (TPS 2.5.11): its tag gives the node's kind, a
text its text, an integer its integer, a list its children. -/
theorem Tree.preimage_injective : ∀ {a b : Tree}, a.preimage = b.preimage → a = b
  | .text s, .text t, h => by
    have := congrArg String.toList h
    simp only [Tree.preimage_text, List.cons.injEq, true_and] at this
    rw [String.toList_injective this]
  | .int n, .int m, h => by
    have := congrArg String.toList h
    simp only [Tree.preimage_int, List.cons.injEq, true_and] at this
    rw [int_toString_inj (String.toList_injective this)]
  | .list xs, .list ys, h => by
    have := congrArg String.toList h
    simp only [Tree.preimage_list, List.cons.injEq, true_and] at this
    rw [Tree.preimages_injective (Digest.preimage_injective (String.toList_injective this))]
  | .text _, .int _, h | .text _, .list _, h | .int _, .text _, h | .int _, .list _, h
  | .list _, .text _, h | .list _, .int _, h => by
    have := congrArg String.toList h
    simp [Tree.preimage_text, Tree.preimage_int, Tree.preimage_list] at this

/-- Trees whose encodings agree, position by position, are the same trees. -/
theorem Tree.preimages_injective : ∀ {xs ys : List Tree},
    xs.map Tree.preimage = ys.map Tree.preimage → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Tree.preimage_injective h.1, Tree.preimages_injective h.2]
end

end Principia.Digest
