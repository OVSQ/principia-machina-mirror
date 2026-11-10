import Principia.Zone.Text
import Principia.Zone.Fields
import Principia.StartingSet
import Principia.Correspondence
import Principia.Criteria

/-!
# The zones: Starting Set, Correspondence Table, Criteria Set

The three zones' well-formedness checks, ported from v1's `tpc_zone` 0.5.1
(schema 0.5.0): `Principia.StartingSet.wellFormed` (fundamental test T1),
`Principia.Correspondence.wellFormed`, `Principia.Criteria.wellFormed`, with
`Principia.Criteria.canonicalTerm`. Shared: the text rules (`Principia.Zone.Text`)
and the field checks (`Principia.Zone.Fields`). Corpus: the zones' corpus,
run by the zones' test runner.

Text is judged with Unicode 15.1.0's general category and NFC, as v1 judged it
(`Principia.Zone.Text`). The zones' preimages and digests, the Research Assembly's digest
and the successor classes are `Principia.Zone.Preimage` (v1's canonical serialization;
SHA-256, the Declarer's choice). Declared forms are read by `Principia.Form`.
-/

namespace Principia.Zone

/-! ## The owed verdict's guarantees

Nothing the Calculator cannot judge is ever passed: a zone with a form field whose reading
the declared-form grammar owes is owed by each of the three checks. Reading a form is never
owed, so no zone is owed for its text or its forms (`owedOf_eq_none`): every zone is
judged. -/

/-- A zone with a form field whose reading the grammar owes is owed. -/
theorem owedOf_isSome_of_formOwed {zone : Value} (h : (formOwedOf zone).isSome) :
    (owedOf zone).isSome := by
  simpa [owedOf] using h

/-- Reading a form field is never owed: it is read or refused, as v1 read it, after NFC. -/
theorem parseField_not_owed (f text : String) (w : Form.Owed) :
    Form.parseField f text ≠ .owed w := by
  unfold Form.parseField Form.parseForm
  split
  · simp only [Form.parse]
    split
    · simp [Form.Answer.map, Form.Answer.escaped]
    · unfold Form.Answer.ofExcept
      split <;> simp [Form.Answer.map, Form.Answer.escaped]
  · simp [Form.refuse]

/-- No zone is owed: Unicode's tables are the Calculator's, and no form field's
reading is owed, so each of the three checks judges every zone. -/
theorem owedOf_eq_none (zone : Value) : owedOf zone = none := by
  unfold owedOf formOwedOf
  rw [List.findSome?_eq_none_iff]
  rintro ⟨k, v⟩ _
  by_cases hk : formFields.contains k = true
  · simp only [hk, ite_true]
    cases h : Form.parseField k v with
    | owed w => exact absurd h (parseField_not_owed k v w)
    | ok _ => rfl
    | refused _ => rfl
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]

/-- An owed zone is never passed by the Starting Set's check. -/
theorem StartingSet.not_passes_of_owed {units : UnitHook} {tpk : Value}
    (h : (owedOf tpk).isSome) : (StartingSet.wellFormed units tpk).passes = false := by
  unfold StartingSet.wellFormed
  cases ho : owedOf tpk with
  | none => simp [ho] at h
  | some o => simp [Verdict.passes]

/-- An owed table is never passed by the Correspondence Table's check. -/
theorem Correspondence.not_passes_of_owed {units : UnitHook} {trm tpk : Value}
    (h : (owedOf trm).isSome) : (Correspondence.wellFormed units trm tpk).passes = false := by
  unfold Correspondence.wellFormed
  cases ho : owedOf trm with
  | none => simp [ho] at h
  | some o => simp [Verdict.passes]

/-- An owed Criteria Set is never passed by its check. -/
theorem Criteria.not_passes_of_owed {units : UnitHook} {tms : Value}
    (h : (owedOf tms).isSome) : (Criteria.wellFormed units tms).passes = false := by
  unfold Criteria.wellFormed
  cases ho : owedOf tms with
  | none => simp [ho] at h
  | some o => simp [Verdict.passes]

end Principia.Zone
