import Principia.Canonical
import Principia.Identity

/-!
# The EXCLUSION LIST and the MODEL MAP on a month's raw rows (TPS 5.19.5)

The EXCLUSION LIST is applied, matching whole tokens without regard to case, to the raw rows
at ingestion, before anything else, and again to the canonical identifiers after the MODEL
MAP. A row the MODEL MAP does not cover is UNMAPPED: held out and counted. The page's text is
checked the same way: it names no excluded model.

**The token rule.** v1's TOKEN RULE (TPS 5.20.11) is the sources' only statement of a whole
token, and its two general clauses are taken here:

* TK0: every invisible format character (Unicode category Cf) is removed from the text and
  the pattern before matching;
* TK1: a match counts only where the character before it and the character after it, in the
  text so cleaned, are not a letter or a digit (Unicode categories L and N, Unicode 15.1.0's
  tables, `Principia.Unicode.generalCategory`); the start and the end of the text count as
  such a character.

TK2 to TK11 concern numbers in a quote and are not taken. Case is folded in ASCII only
(`Char.toLower`: `A` to `Z`), the floor 5.19.5 leaves; a letter outside ASCII is matched as it
is written. A position is a code point's index in the text as given, Cf characters counted.

**The canonical form.** A raw row is a JSON object whose members are texts and numbers, with
the texts `model` and `config`. The MODEL MAP is the form `family_of` reads
(`Principia.Identity.checkMap`): a row is mapped when its `model`, in NFC, is a map row's
name. Its canonical identifiers are the model and the configuration in NFC and the map row's
family, server and quantization in NFC. A kept row's answer holds the model, the
configuration, the family and the raw row.
-/

namespace Principia.Cluster.Screen

open Principia.Canonical (Value)

/-! ## The token rule -/

/-- TK0: an invisible format character, Unicode category Cf. -/
def invisible (c : Char) : Bool := Unicode.generalCategory c == .cf

/-- TK1: a letter or a digit, Unicode categories L and N. -/
def wordChar (c : Char) : Bool :=
  let m := (Unicode.generalCategory c).major
  m == 'L' || m == 'N'

/-- The text as matched: Cf characters removed, ASCII case folded, each character beside its
code point's index in the text as given. -/
def prepare (t : String) : List (Char × Nat) :=
  (t.toList.zipIdx.filter fun (c, _) => !invisible c).map fun (c, i) => (c.toLower, i)

/-- A pattern as matched: Cf characters removed, ASCII case folded. -/
def pattern (p : String) : List Char := (p.toList.filter fun c => !invisible c).map Char.toLower

/-- A side of a match: the start or the end of the text, or a character not a letter or a
digit. -/
def boundary : Option Char → Bool
  | none => true
  | some c => !wordChar c

/-- What follows the pattern `p` at the head of `l`, when `l` begins with it. -/
def afterPrefix : List Char → List (Char × Nat) → Option (List (Char × Nat))
  | [], l => some l
  | _ :: _, [] => none
  | a :: p, (c, _) :: l => if a == c then afterPrefix p l else none

/-- The pattern `p` matches as a whole token at the head of `l`, `prev` the character before. -/
def matchAt (p : List Char) (prev : Option Char) (l : List (Char × Nat)) : Bool :=
  boundary prev &&
    match afterPrefix p l with
    | some r => boundary (r.head?.map (·.1))
    | none => false

/-- The first position at which a pattern matches, scanning from the head of `l`. -/
def firstHit (ps : List (List Char)) : Option Char → List (Char × Nat) → Option Nat
  | _, [] => none
  | prev, (c, i) :: rest =>
    if ps.any (fun p => matchAt p prev ((c, i) :: rest)) then some i
    else firstHit ps (some c) rest

/-- The first position of the text `t` at which a pattern of the list matches. -/
def hit (ps : List (List Char)) (t : String) : Option Nat := firstHit ps none (prepare t)

/-- The text names an excluded token. -/
def names (ps : List (List Char)) (t : String) : Bool := (hit ps t).isSome

/-- The character before a split of the prepared text: the last of `pre`, else `prev`. -/
def prevOf (prev : Option Char) (pre : List (Char × Nat)) : Option Char :=
  match pre.getLast? with
  | some x => some x.1
  | none => prev

/-- The text names an excluded token: at some split of its prepared characters a pattern
of the list matches as a whole token. -/
def Names (ps : List (List Char)) (t : String) : Prop :=
  ∃ pre post, prepare t = pre ++ post ∧ post ≠ [] ∧
    ∃ p ∈ ps, matchAt p (prevOf none pre) post = true

theorem prevOf_cons (prev : Option Char) (x : Char × Nat) (pre : List (Char × Nat)) :
    prevOf prev (x :: pre) = prevOf (some x.1) pre := by
  unfold prevOf
  rw [List.getLast?_cons]
  cases h : pre.getLast? <;> simp

/-- Where the scan finds nothing, no pattern matches at any split. -/
theorem firstHit_none {ps : List (List Char)} :
    ∀ {prev : Option Char} {l : List (Char × Nat)}, firstHit ps prev l = none →
      ∀ pre post, l = pre ++ post → post ≠ [] → ∀ p ∈ ps, matchAt p (prevOf prev pre) post = false
  | _, [], _, pre, post, hl, hp, _, _ => by
    exact absurd (List.append_eq_nil_iff.mp hl.symm).2 hp
  | prev, (c, i) :: rest, h, pre, post, hl, hp, p, hmem => by
    unfold firstHit at h
    split at h
    · cases h
    · rename_i hany
      cases pre with
      | nil =>
        simp only [List.nil_append] at hl
        subst hl
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
        exact hany p hmem
      | cons x pre' =>
        simp only [List.cons_append, List.cons.injEq] at hl
        obtain ⟨hx, hr⟩ := hl
        subst hx
        rw [prevOf_cons]
        exact firstHit_none h pre' post hr hp p hmem

/-- `hit` answers no position only for a text that names no excluded token. -/
theorem not_names_of_hit_none {ps : List (List Char)} {t : String} (h : hit ps t = none) :
    ¬ Names ps t := by
  rintro ⟨pre, post, hl, hp, p, hmem, hm⟩
  have := firstHit_none h pre post hl hp p hmem
  simp_all

/-! ## The raw rows -/

/-- A raw row: its members, each a text or a number. -/
abbrev Raw := List (String × Value)

/-- A raw row's texts: every member's name and every text member's value. -/
def rawTexts (r : Raw) : List String :=
  r.flatMap fun (k, v) => match v with
    | .str s => [k, s]
    | _ => [k]

/-- A text member of a raw row, or the empty text. -/
def textOf (r : Raw) (key : String) : String :=
  match r.lookup key with
  | some (.str s) => s
  | _ => ""

/-- A kept row in canonical form. -/
structure Kept where
  /-- The model, in NFC. -/
  model : String
  /-- The configuration, in NFC. -/
  config : String
  /-- The MODEL MAP row's family, in NFC. -/
  family : String
  /-- The raw row as given. -/
  row : Raw

/-- The texts a kept row's answer carries. -/
def keptTexts (k : Kept) : List String := k.model :: k.config :: k.family :: rawTexts k.row

/-- What becomes of one raw row. -/
inductive Verdict where
  /-- Excluded at ingestion. -/
  | ingestion
  /-- Excluded after the MODEL MAP. -/
  | afterMap
  /-- UNMAPPED. -/
  | unmapped
  /-- Kept, in canonical form. -/
  | kept (k : Kept)

/-- One raw row through the EXCLUSION LIST, the MODEL MAP and the EXCLUSION LIST again. -/
def classify (ps : List (List Char)) (map : List (String × Identity.MapRow)) (r : Raw) : Verdict :=
  if (rawTexts r).any (names ps) then .ingestion
  else
    let m := Unicode.nfc (textOf r "model")
    let c := Unicode.nfc (textOf r "config")
    match Identity.findRow m map with
    | none => .unmapped
    | some mr =>
      let fam := Unicode.nfc mr.family
      let ids := [m, c, fam] ++ (mr.server.map Unicode.nfc).toList ++
        (mr.quantization.map Unicode.nfc).toList
      if ids.any (names ps) then .afterMap else .kept ⟨m, c, fam, r⟩

/-- The screen's answer: the kept rows and the three counts. -/
structure Answer where
  /-- The kept rows, in the order given. -/
  kept : List Kept
  /-- The rows excluded at ingestion. -/
  ingestion : Nat
  /-- The rows excluded after the MODEL MAP. -/
  afterMap : Nat
  /-- The rows UNMAPPED. -/
  unmapped : Nat

/-- The verdicts counted, the kept rows in order. -/
def tally : List Verdict → Answer
  | [] => ⟨[], 0, 0, 0⟩
  | v :: vs =>
    let a := tally vs
    match v with
    | .ingestion => { a with ingestion := a.ingestion + 1 }
    | .afterMap => { a with afterMap := a.afterMap + 1 }
    | .unmapped => { a with unmapped := a.unmapped + 1 }
    | .kept k => { a with kept := k :: a.kept }

/-- `cluster_screen`: every raw row classified and counted. -/
def screen (ps : List (List Char)) (map : List (String × Identity.MapRow)) (rows : List Raw) :
    Answer :=
  tally (rows.map (classify ps map))

/-! ## Its laws -/

theorem tally_adds (vs : List Verdict) :
    (tally vs).kept.length + (tally vs).ingestion + (tally vs).afterMap + (tally vs).unmapped =
      vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v <;> simp only [tally, List.length_cons] <;> omega

/-- The kept rows and the three counts add up to the rows given. -/
theorem screen_adds (ps : List (List Char)) (map : List (String × Identity.MapRow))
    (rows : List Raw) :
    (screen ps map rows).kept.length + (screen ps map rows).ingestion +
      (screen ps map rows).afterMap + (screen ps map rows).unmapped = rows.length := by
  unfold screen
  rw [tally_adds, List.length_map]

theorem mem_tally_kept {k : Kept} : ∀ {vs : List Verdict}, k ∈ (tally vs).kept → Verdict.kept k ∈ vs
  | [], h => by simp [tally] at h
  | v :: vs, h => by
    cases v with
    | ingestion => exact List.mem_cons_of_mem _ (mem_tally_kept h)
    | afterMap => exact List.mem_cons_of_mem _ (mem_tally_kept h)
    | unmapped => exact List.mem_cons_of_mem _ (mem_tally_kept h)
    | kept k' =>
      simp only [tally, List.mem_cons] at h
      rcases h with h | h
      · subst h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_tally_kept h)

theorem classify_kept {ps : List (List Char)} {map : List (String × Identity.MapRow)} {r : Raw}
    {k : Kept} (h : classify ps map r = .kept k) : ∀ s ∈ keptTexts k, names ps s = false := by
  unfold classify at h
  split at h
  · cases h
  · rename_i hraw
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hids
        cases h
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hraw hids
        intro s hs
        simp only [keptTexts, List.mem_cons] at hs
        rcases hs with hs | hs | hs | hs
        · exact hids s (by simp [hs])
        · exact hids s (by simp [hs])
        · exact hids s (by simp [hs])
        · exact hraw s hs

/-- No kept row, and no canonical identifier in the answer, names a token the list matches. -/
theorem screen_kept_clean (ps : List (List Char)) (map : List (String × Identity.MapRow))
    (rows : List Raw) (k : Kept) (hk : k ∈ (screen ps map rows).kept) :
    ∀ s ∈ keptTexts k, ¬ Names ps s := by
  have hv := mem_tally_kept hk
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hv
  intro s hs
  have hn := classify_kept hr s hs
  apply not_names_of_hit_none
  simpa [names] using hn

/-! ## The page's text -/

/-- `cluster_text_check`: the first position at which the page's text names an excluded
token, or none. -/
def textCheck (ps : List (List Char)) (t : String) : Option Nat := hit ps t

/-- The check accepts a text only if no token of it matches. -/
theorem textCheck_sound (ps : List (List Char)) (t : String) (h : textCheck ps t = none) :
    ¬ Names ps t :=
  not_names_of_hit_none h

end Principia.Cluster.Screen
