import Principia.Provision.Expand

/-!
# One selection, one expansion

TPS 5.22.7: "Terms are composed in ID order, then term order, then name order, whatever the
order of selection, so one selection gives one EQUATION and one D(TPK)." Proved here: once the
claims are read, reordering them changes nothing in the expansion (`expandRun_perm`). The
claims are read each on its own, then checked for an ID given twice and put in ID order; each
step is indifferent to the order they came in, which the lemmas below state.
-/

namespace Principia.Provision

open Principia.Zone (Value Entry)

/-- `≤` on strings, as the sorts decide it, is transitive. -/
theorem strLe_trans (a b c : String) :
    decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
  simp only [decide_eq_true_eq]
  exact String.le_trans

/-- `≤` on strings is total. -/
theorem strLe_total (a b : String) : (decide (a ≤ b) || decide (b ≤ a)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

/-- Strings sorted are in code point order. -/
theorem sortStrs_sorted (xs : List String) : (sortStrs xs).Pairwise fun a b => a ≤ b := by
  have := List.pairwise_mergeSort strLe_trans strLe_total xs
  simp only [decide_eq_true_eq] at this
  exact this

/-- Strings sorted do not depend on the order they were given in. -/
theorem sortStrs_perm {xs ys : List String} (h : xs.Perm ys) : sortStrs xs = sortStrs ys := by
  have p : (sortStrs xs).Perm (sortStrs ys) :=
    (List.mergeSort_perm xs _).trans (h.trans (List.mergeSort_perm ys _).symm)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => String.le_antisymm hab hba)
    (sortStrs_sorted xs) (sortStrs_sorted ys) p

/-- The least name given twice does not depend on the order of the names. -/
theorem leastDup_perm {xs ys : List String} (h : xs.Perm ys) : leastDup xs = leastDup ys := by
  unfold leastDup
  have hf : (xs.filter fun x => decide (xs.count x ≥ 2)).Perm (ys.filter fun y => decide (ys.count y ≥ 2)) := by
    have : (fun x => decide (xs.count x ≥ 2)) = (fun y => decide (ys.count y ≥ 2)) := by
      funext x; rw [h.count_eq]
    rw [this]
    exact h.filter _
  rw [sortStrs_perm hf]

/-- A list in which no element occurs twice has distinct elements. -/
theorem nodup_of_count_lt_two : ∀ {xs : List String}, (∀ a ∈ xs, xs.count a < 2) → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.nodup_cons]
    constructor
    · intro hx
      have h1 := h x List.mem_cons_self
      rw [List.count_cons_self] at h1
      have h2 : 0 < xs.count x := List.count_pos_iff.mpr hx
      omega
    · apply nodup_of_count_lt_two
      intro a ha
      have h1 := h a (List.mem_cons_of_mem _ ha)
      rw [List.count_cons] at h1
      split at h1 <;> omega

/-- No name given twice: the names are distinct. -/
theorem nodup_of_leastDup {xs : List String} (h : leastDup xs = none) : xs.Nodup := by
  unfold leastDup at h
  have he : sortStrs (xs.filter fun x => decide (xs.count x ≥ 2)) = [] := List.head?_eq_none_iff.mp h
  have hp : (xs.filter fun x => decide (xs.count x ≥ 2)).Perm [] := by
    have := List.mergeSort_perm (xs.filter fun x => decide (xs.count x ≥ 2)) (fun a b => decide (a ≤ b))
    unfold sortStrs at he
    rw [he] at this
    exact this.symm
  have hf := List.perm_nil.mp hp
  apply nodup_of_count_lt_two
  intro a ha
  have : ¬ (xs.count a ≥ 2) := by
    intro hc
    have : a ∈ xs.filter (fun x => decide (xs.count x ≥ 2)) := List.mem_filter.mpr ⟨ha, by simpa using hc⟩
    rw [hf] at this; simp at this
  omega

/-- The claims from the `i`-th on are read exactly when none has a problem, and then they
are each claim's fields, whatever their places. -/
theorem readClaimList_ok : ∀ (xs : List Value) (i : Nat) (out : List Claim),
    readClaimList i xs = .ok out ↔ (∀ c ∈ xs, claimProblem c = none) ∧ out = xs.map claimValue
  | [], i, out => by
    simp only [readClaimList, Except.ok.injEq, List.not_mem_nil, false_imp_iff, implies_true,
      List.map_nil, true_and]
    exact eq_comm
  | c :: cs, i, out => by
    have ih := readClaimList_ok cs (i + 1)
    simp only [readClaimList, List.mem_cons, forall_eq_or_imp, List.map_cons, readClaim]
    cases hp : claimProblem c with
    | some p =>
      simp [refuse, throw, throwThe, MonadExceptOf.throw]
    | none =>
      simp only [pure, Except.pure, true_and]
      cases hr : readClaimList (i + 1) cs with
      | error e =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro hall _
        have := (ih (cs.map claimValue)).mpr ⟨hall, rfl⟩
        rw [hr] at this; cases this
      | ok rest =>
        simp only [Except.ok.injEq]
        have ih' := (ih rest).mp hr
        constructor
        · intro h; subst h; exact ⟨ih'.1, by rw [ih'.2]⟩
        · rintro ⟨_, hout⟩
          rw [hout, ih'.2]

/-- Among claims with distinct IDs, an ID names one claim. -/
theorem eq_of_id_eq {cs : List Claim} (hd : (cs.map (·.id)).Nodup) {a b : Claim} (ha : a ∈ cs)
    (hb : b ∈ cs) (hk : a.id = b.id) : a = b := by
  induction cs with
  | nil => simp at ha
  | cons c rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, hk.symm⟩ hd.1
    · exact absurd ⟨a, ha, hk⟩ hd.1
    · exact ih hd.2 ha hb

/-- Claims with distinct IDs, sorted, do not depend on the order they were given in. -/
theorem sortClaims_perm {cs cs' : List Claim} (hd : (cs.map (·.id)).Nodup) (h : cs.Perm cs') :
    sortClaims cs = sortClaims cs' := by
  have le_trans : ∀ a b c : Claim, decide (a.id ≤ b.id) = true → decide (b.id ≤ c.id) = true →
      decide (a.id ≤ c.id) = true := fun a b c => strLe_trans a.id b.id c.id
  have le_total : ∀ a b : Claim, (decide (a.id ≤ b.id) || decide (b.id ≤ a.id)) = true :=
    fun a b => strLe_total a.id b.id
  have sorted (l : List Claim) : (sortClaims l).Pairwise fun a b => a.id ≤ b.id := by
    have := List.pairwise_mergeSort le_trans le_total l
    simp only [decide_eq_true_eq] at this
    exact this
  have p : (sortClaims cs).Perm (sortClaims cs') :=
    (List.mergeSort_perm cs _).trans (h.trans (List.mergeSort_perm cs' _).symm)
  apply List.Perm.eq_of_pairwise _ (sorted cs) (sorted cs') p
  intro a b ha hb hab hba
  have ha' : a ∈ cs := (List.mergeSort_perm cs _).subset ha
  have hb' : b ∈ cs := h.symm.subset ((List.mergeSort_perm cs' _).subset hb)
  exact eq_of_id_eq hd ha' hb' (String.le_antisymm hab hba)

/-- Claims read in one order are read, alike, in any other. -/
theorem readClaims_perm {xs ys : List Value} (hp : xs.Perm ys) {cls : List Claim}
    (h : readClaims (.arr xs) = .ok cls) : readClaims (.arr ys) = .ok cls := by
  simp only [readClaims] at h ⊢
  cases hx : readClaimList 1 xs with
  | error e => simp only [hx] at h; cases h
  | ok out =>
    simp only [hx] at h
    obtain ⟨hall, hout⟩ := (readClaimList_ok xs 1 out).mp hx
    have hy : readClaimList 1 ys = .ok (ys.map claimValue) :=
      (readClaimList_ok ys 1 _).mpr ⟨fun c hc => hall c (hp.symm.subset hc), rfl⟩
    simp only [hy]
    have hperm : out.Perm (ys.map claimValue) := hout ▸ hp.map claimValue
    have hids : (out.map (·.id)).Perm ((ys.map claimValue).map (·.id)) := hperm.map _
    cases hd : leastDup (out.map (·.id)) with
    | some d => simp only [hd] at h; cases h
    | none =>
      simp only [hd, Except.ok.injEq] at h
      rw [← leastDup_perm hids, hd]
      simp only [Except.ok.injEq]
      rw [← h]
      exact (sortClaims_perm (nodup_of_leastDup hd) hperm).symm

/-- One selection, one expansion (TPS 5.22.7): once the claims are read, the expansion does not
depend on the order they were selected in, and so neither does its D(TPK). -/
theorem expandRun_perm (D : DigestHook) (draft textsV : Value) {xs ys : List Value}
    (hp : xs.Perm ys) {cls : List Claim} (h : readClaims (.arr xs) = .ok cls) :
    expandRun D draft (.arr xs) textsV = expandRun D draft (.arr ys) textsV := by
  simp only [expandRun, h, readClaims_perm hp h]

/-- A pair is refused when either one's EXCLUDES matches the other (TPS 5.22.3): the refusal
does not depend on which of the two is named first. -/
theorem excludesPair_comm (a b : Provision) : excludesPair a b = excludesPair b a := by
  unfold excludesPair
  exact Bool.or_comm _ _

/-- Two texts of different (ID, VERSION) are found alike in either order. -/
theorem textOf?_swap {M B : Provision} (h : (M.id, M.version) ≠ (B.id, B.version)) :
    textOf? [M, B] = textOf? [B, M] := by
  funext i v
  simp only [textOf?, List.find?]
  by_cases hm : (M.id == i && M.version == v) = true <;> by_cases hb : (B.id == i && B.version == v) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hm hb
    exact absurd (by rw [hm.1, hm.2, hb.1, hb.2]) h
  · simp [hm, hb]
  · simp [hm, hb]
  · simp [hm, hb]

/-- The two orders of selection `module_check` tries for a pair give one expansion, so its
verdict "TWO SELECTION ORDERS GIVE TWO D(TPK)" never arises (TPS 5.22.11). -/
theorem pair_orders_agree (D : DigestHook) (d : Entry) (tpk : Value) {M B : Provision} {ca cb : Claim}
    (hid : ca.id ≠ cb.id) (hMB : (M.id, M.version) ≠ (B.id, B.version)) :
    expandWith D d tpk (sortClaims [ca, cb]) (textOf? [M, B]) =
      expandWith D d tpk (sortClaims [cb, ca]) (textOf? [B, M]) := by
  have hs : sortClaims [ca, cb] = sortClaims [cb, ca] :=
    sortClaims_perm (by simp [hid]) (List.Perm.swap cb ca [])
  rw [hs, textOf?_swap hMB]

end Principia.Provision
