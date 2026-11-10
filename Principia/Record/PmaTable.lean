import Principia.Canonical
import Principia.Record.Table
import Principia.Record.Derivation

/-!
# The PMA table: the rows PMA adds beside version 1's record table

Version 1's record table (`Principia.Record.Table.tableText`) is carried byte for byte, so a
field PMA adds cannot join its text. The PMA table is a second table of the same shape
(`Principia.Record.Table.Table`, its `FIELD` rows `FieldRow`), read beside version 1's by the
record check, the preimage and the views (`Principia.Record.Check`).

Its one row: `FIELD RESULT DERIVATION_CLASS ENUM ONE R TPX D - ENUM=DERIVATION_CLASS`.
DERIVATION_CLASS is written by Custos (version 1's writer word TPX) at landing: absent at the
push (REC-07 when present), required on a RESULT at LANDED (REC-43 when absent or when its
value is not one of the three check classes), and inside the record digest (`D`): the
`TPC-RECORD` form 1 field list carries it after version 1's fields. Its values are the wire
words of `Principia.Record.DerivationClass`, INSPECTION, MECHANICAL and PROVED, taken from
the type itself, so the table and the type cannot disagree.
-/

namespace Principia.Record.PmaTable

open Principia.Record.Table
open Principia.Canonical (Value)

/-- The PMA enumeration DERIVATION_CLASS: the wire words of `DerivationClass`, in its order. -/
def derivationClassWords : List String :=
  (WireWord.members : List DerivationClass).map WireWord.toWire

/-- The PMA row DERIVATION_CLASS of a RESULT, in version 1's `FIELD` columns. -/
def derivationClassRow : FieldRow :=
  { name := "DERIVATION_CLASS", type := "ENUM", card := "ONE", req := "R", writer := "TPX",
    dig := "D", default := "-", cons := ["ENUM=DERIVATION_CLASS"] }

/-- The PMA table: its enumeration and its rows, keyed as version 1's table keys them. -/
def pmaTable : Table :=
  { enums := [("DERIVATION_CLASS", derivationClassWords)],
    fields := [("RESULT", [derivationClassRow])] }

/-- The PMA rows of a class (none for a class PMA adds nothing to). -/
def pmaFieldsOf (cls : String) : List FieldRow := (pmaTable.fields.lookup cls).getD []

/-- The values of a PMA enumeration. -/
def pmaEnumValues (name : String) : List String := (pmaTable.enums.lookup name).getD []

/-- A value a PMA row accepts: a string among the values of its enumeration, which bears
the row's name (`ENUM=DERIVATION_CLASS` on the row DERIVATION_CLASS). -/
def rowValueOk (f : FieldRow) (v : Value) : Bool :=
  match v with
  | .str s => (pmaEnumValues f.name).contains s
  | _ => false

/-- The words of DERIVATION_CLASS are INSPECTION, MECHANICAL and PROVED. -/
theorem derivationClassWords_eq :
    derivationClassWords = ["INSPECTION", "MECHANICAL", "PROVED"] := rfl

/-- A RESULT has exactly one PMA row, DERIVATION_CLASS; no other class has any. -/
theorem pmaFieldsOf_result : pmaFieldsOf "RESULT" = [derivationClassRow] := rfl

/-- Every PMA row is DERIVATION_CLASS. -/
theorem pmaFieldsOf_name (cv : String) (f : FieldRow) (h : f ∈ pmaFieldsOf cv) :
    f.name = "DERIVATION_CLASS" := by
  unfold pmaFieldsOf pmaTable at h
  by_cases hc : cv = "RESULT"
  · subst hc
    simp [List.lookup] at h
    subst h
    rfl
  · have hb : (cv == "RESULT") = false := by simp [hc]
    simp [List.lookup, hb] at h

/-- **Every DERIVATION_CLASS the row accepts is a check class**: the value reads as a
`DerivationClass` and is that class's wire word. -/
theorem rowValueOk_derivationClass (v : Value) (h : rowValueOk derivationClassRow v = true) :
    ∃ s c, v = .str s ∧ WireWord.ofWire? s = some (c : DerivationClass) := by
  cases v with
  | str s =>
    refine ⟨s, ?_⟩
    have hm : s = "INSPECTION" ∨ s = "MECHANICAL" ∨ s = "PROVED" := by
      simpa [rowValueOk, derivationClassRow, pmaEnumValues, pmaTable,
        derivationClassWords_eq] using h
    rcases hm with rfl | rfl | rfl
    · exact ⟨.inspection, rfl, by decide⟩
    · exact ⟨.mechanical, rfl, by decide⟩
    · exact ⟨.proved, rfl, by decide⟩
  | _ => simp [rowValueOk] at h

/-- Every check class's wire word is accepted by the row. -/
theorem rowValueOk_toWire (c : DerivationClass) :
    rowValueOk derivationClassRow (.str (WireWord.toWire c)) = true := by
  cases c <;> decide

end Principia.Record.PmaTable
