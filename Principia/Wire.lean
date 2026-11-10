/-!
# Wire words

Rule R1 of the collision register: a wire name keeps its capital spelling (JSON
keys, page text, prose: `RESULT`, `NOT GRADED`, `KERNEL`); its Lean name is a
lowerCamel word that is not a keyword (`result`, `notGraded`, `kernelProof`).
Each closed enumeration of the record table maps its constructors to their wire
words one to one. The class `WireWord` carries the map and one fact per
enumeration, that reading a member's spelling gives the member back; the round
trip in both directions, injectivity and completeness follow here, once, for
every enumeration.

A wire word is compared byte for byte: no case folding, no trimming, no
normalization (v1's ENUM type, tpm_record_schema 0.3.1, 2.10).
-/

namespace Principia

/-- Read a wire word against a list of members: the first member whose spelling
is the word, byte for byte; `none` when no member spells it. -/
def readWire {α : Type} (members : List α) (toWire : α → String) (s : String) :
    Option α :=
  members.find? (fun a => toWire a == s)

/-- A closed enumeration whose members have capital wire spellings (R1). -/
class WireWord (α : Type) where
  /-- Every member, in the table's order. -/
  members : List α
  /-- The member's wire spelling. -/
  toWire : α → String
  /-- Reading a member's spelling gives the member back. -/
  read_toWire : ∀ a, readWire members toWire (toWire a) = some a

namespace WireWord

variable {α : Type} [WireWord α]

/-- Read a wire word: the member it spells, or `none`. -/
def ofWire? (s : String) : Option α :=
  readWire (members : List α) toWire s

/-- Round trip, Lean to wire to Lean. -/
theorem ofWire?_toWire (a : α) : ofWire? (toWire a) = some a :=
  read_toWire a

/-- Round trip, wire to Lean to wire: a word that reads as a member is that
member's spelling, so no other spelling is accepted. -/
theorem toWire_of_ofWire? {s : String} {a : α} (h : ofWire? s = some a) :
    toWire a = s := by
  unfold ofWire? readWire at h
  have hb := List.find?_some (p := fun x => toWire x == s) h
  exact beq_iff_eq.mp hb

/-- No two members share a wire word. -/
theorem toWire_injective {a b : α} (h : toWire a = toWire b) : a = b := by
  have ha : ofWire? (toWire a) = some a := ofWire?_toWire a
  rw [h, ofWire?_toWire] at ha
  exact (Option.some.inj ha).symm

/-- Every value of the type is listed among the members. -/
theorem mem_members (a : α) : a ∈ (members : List α) :=
  List.mem_of_find?_eq_some (ofWire?_toWire a)

end WireWord

end Principia
