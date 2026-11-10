import Principia.Canonical
import Principia.Record.Derivation

/-!
# The wire form of a STRUCTURED payload

A STRUCTURED derivation's payload (`Derivation.structured`, and an `Attachment` of that
form) as a JSON value, written through the hand-written canonical serializer
(`Principia.Canonical.Value.canonicalJson`, tpm_record_schema 0.3.1 section 11.4) and read
back from a value the hand-written reader gives (`Principia.Canonical.readText`). No text
here passes through `Lean.Json` (collision register R5). The spelling is provisional, as
the step's fields are (section 10 of the record types' design note, question 5 there):

* **The payload**, an object: `STEPS`, the steps in order, a list; and `START`, the
  start, absent when the derivation starts from `e = e` for the RESULT's EQUATION's left
  side, so that each payload has one spelling.
* **A start**, an object of one member: `LAW` (a NAME of the Starting Set), `ASSUMPTION`
  (an ASSUMPTION record's identifier) or `EXPRESSION` (an expression in the declared-form
  grammar), a string.
* **A step**, an object of four members: `EQUATION`, the equation it leads to, a string;
  one of `LAW`, `ASSUMPTION` or `IDENTITY`, what it cites or applies, a string; `SITE`,
  its side and path, a string (empty when the record does not say, which the checker
  refuses as `no-site`); `FORWARD`, its direction, a boolean. Every member is always
  written, so a step has one spelling.

The reader is structural: it takes any value the writer could have written and refuses
anything else with the place and a word (`not-an-object`, `unknown-member`,
`repeated-member`, `missing`, `not-a-string`, `not-a-boolean`, `not-a-list`,
`no-citation`, `several-citations`, `no-start`, `several-starts`). What the texts say (an
EQUATION, a SITE, an identity's name) is the checker's to read
(`Principia.StructuredCheck.readStructured`). Reading what the writer wrote gives the
payload back (`structuredOfValue_structuredToValue`, a part of SC5's round trip), and the
writer never refuses a payload (`structuredToValue_canonicalJson_isSome`).

The DERIVATION sum around the payload is shape-discriminated, every member
written: PROSE `{STEPS: integer, TEXT, ATTACHMENT?}`, the attachment a STRUCTURED payload
or a KERNEL payload; STRUCTURED `{STEPS: list, START?}`, the payload above; KERNEL
`{PROOF: text}`. Members of two forms together (`START` or a list `STEPS` beside `TEXT`,
`ATTACHMENT` or an integer `STEPS`; `PROOF` beside any other) are refused, `mixed-forms`;
an object with none of them, `no-form`. `derivationOfValue` reads it, refusing with the
words above and `not-a-count STEPS` (a negative step count) and `not-an-integer-or-a-list
STEPS`, an attachment's refusal placed under `ATTACHMENT: `; `derivationToValue` writes it,
and reading what it wrote gives the derivation back
(`derivationOfValue_derivationToValue`).
-/

namespace Principia.Record

open Principia.Canonical (Value)

/-! ## Writing -/

/-- A citation as the member of a step that carries it. -/
def StepCitation.member : StepCitation → String × Value
  | .law n => ("LAW", .str n)
  | .assumption r => ("ASSUMPTION", .str r)
  | .identity n => ("IDENTITY", .str n)

/-- A step as a wire object. -/
def StructuredStep.toValue (s : StructuredStep) : Value :=
  .obj [("EQUATION", .str s.equation), s.cites.member, ("SITE", .str s.site),
    ("FORWARD", .bool s.forward)]

/-- A start as a wire object; `none` for the start a payload leaves unwritten. -/
def StructuredStart.toValue? : StructuredStart → Option Value
  | .lhs => none
  | .law n => some (.obj [("LAW", .str n)])
  | .assumption r => some (.obj [("ASSUMPTION", .str r)])
  | .refl e => some (.obj [("EXPRESSION", .str e)])

/-- A STRUCTURED payload as a wire object. -/
def structuredToValue (steps : List StructuredStep) (start : StructuredStart) : Value :=
  .obj ((start.toValue?.map fun v => [("START", v)]).getD [] ++
    [("STEPS", .arr (steps.map StructuredStep.toValue))])

/-- A STRUCTURED payload's canonical JSON text. -/
def structuredText (steps : List StructuredStep) (start : StructuredStart) : Option String :=
  (structuredToValue steps start).canonicalJson

/-! ## Reading -/

/-- Whether no key occurs twice. -/
def keysDistinct : List String → Bool
  | [] => true
  | k :: ks => !ks.contains k && keysDistinct ks

/-- An object's members, when it is an object whose keys are among `allowed`, none twice. -/
def wireMembers (allowed : List String) : Value → Except String (List (String × Value))
  | .obj ms =>
    match ms.find? (fun m => !allowed.contains m.1) with
    | some m => .error ("unknown-member " ++ m.1)
    | none => if keysDistinct (ms.map (·.1)) then .ok ms else .error "repeated-member"
  | _ => .error "not-an-object"

/-- The string member `k`. -/
def wireString (ms : List (String × Value)) (k : String) : Except String String :=
  match ms.lookup k with
  | some (.str s) => .ok s
  | some _ => .error ("not-a-string " ++ k)
  | none => .error ("missing " ++ k)

/-- The one member among `keys` an object holds, with its key; `none` when it holds no
such member, `some none` when it holds several. -/
def oneOf (ms : List (String × Value)) (keys : List String) : Option (Option String) :=
  match keys.filter (fun k => (ms.lookup k).isSome) with
  | [] => none
  | [k] => some (some k)
  | _ => some none

/-- A step's citation from its members. -/
def readCitation (ms : List (String × Value)) : Except String StepCitation :=
  match oneOf ms ["ASSUMPTION", "IDENTITY", "LAW"] with
  | none => .error "no-citation"
  | some none => .error "several-citations"
  | some (some k) => do
    let n ← wireString ms k
    if k == "LAW" then pure (.law n)
    else if k == "ASSUMPTION" then pure (.assumption n)
    else pure (.identity n)

/-- A step from its wire object. -/
def StructuredStep.ofValue (v : Value) : Except String StructuredStep := do
  let ms ← wireMembers ["ASSUMPTION", "EQUATION", "FORWARD", "IDENTITY", "LAW", "SITE"] v
  let equation ← wireString ms "EQUATION"
  let cites ← readCitation ms
  let site ← wireString ms "SITE"
  let forward ← match ms.lookup "FORWARD" with
    | some (.bool b) => pure b
    | some _ => throw "not-a-boolean FORWARD"
    | none => throw "missing FORWARD"
  pure { equation, cites, site, forward }

/-- A start from its wire object. -/
def StructuredStart.ofValue (v : Value) : Except String StructuredStart := do
  let ms ← wireMembers ["ASSUMPTION", "EXPRESSION", "LAW"] v
  match oneOf ms ["ASSUMPTION", "EXPRESSION", "LAW"] with
  | none => throw "no-start"
  | some none => throw "several-starts"
  | some (some k) => do
    let n ← wireString ms k
    if k == "LAW" then pure (.law n)
    else if k == "ASSUMPTION" then pure (.assumption n)
    else pure (.refl n)

/-- The steps in order, numbered from `i`; the first that does not read, with its number. -/
def readWireSteps : List Value → Nat → Except String (List StructuredStep)
  | [], _ => .ok []
  | v :: vs, i =>
    match StructuredStep.ofValue v with
    | .error w => .error ("step " ++ toString i ++ ": " ++ w)
    | .ok s => match readWireSteps vs (i + 1) with
      | .error w => .error w
      | .ok ss => .ok (s :: ss)

/-- A STRUCTURED payload from its wire object: the steps and the start. -/
def structuredOfValue (v : Value) : Except String (List StructuredStep × StructuredStart) := do
  let ms ← wireMembers ["START", "STEPS"] v
  let start ← match ms.lookup "START" with
    | none => pure .lhs
    | some s => match StructuredStart.ofValue s with
      | .ok st => pure st
      | .error w => throw ("START: " ++ w)
  let steps ← match ms.lookup "STEPS" with
    | some (.arr xs) => readWireSteps xs 1
    | some _ => throw "not-a-list STEPS"
    | none => throw "missing STEPS"
  pure (steps, start)

/-! ## The round trip -/

theorem StructuredStep.ofValue_toValue (s : StructuredStep) :
    StructuredStep.ofValue s.toValue = .ok s := by
  obtain ⟨e, c, site, fwd⟩ := s
  cases c <;>
    simp [StructuredStep.ofValue, StructuredStep.toValue, StepCitation.member, wireMembers,
      keysDistinct, wireString, readCitation, oneOf, List.lookup, bind, Except.bind, pure,
      Except.pure]

theorem StructuredStart.ofValue_toValue {st : StructuredStart} {v : Value}
    (h : st.toValue? = some v) : StructuredStart.ofValue v = .ok st := by
  cases st <;> simp [StructuredStart.toValue?] at h <;> subst h <;>
    simp [StructuredStart.ofValue, wireMembers, keysDistinct, wireString, oneOf, List.lookup,
      bind, Except.bind, pure, Except.pure]

theorem readWireSteps_map (steps : List StructuredStep) (i : Nat) :
    readWireSteps (steps.map StructuredStep.toValue) i = .ok steps := by
  induction steps generalizing i with
  | nil => rfl
  | cons s ss ih => simp [readWireSteps, StructuredStep.ofValue_toValue, ih]

/-- **The round trip.** Reading a payload's wire object gives the payload back: its steps,
each with its equation, citation, site and direction, and its start. -/
theorem structuredOfValue_structuredToValue (steps : List StructuredStep)
    (start : StructuredStart) :
    structuredOfValue (structuredToValue steps start) = .ok (steps, start) := by
  cases h : start.toValue? with
  | none =>
    cases start <;> simp [StructuredStart.toValue?] at h
    simp [structuredOfValue, structuredToValue, StructuredStart.toValue?, wireMembers,
      keysDistinct, List.lookup, readWireSteps_map, bind, Except.bind, pure, Except.pure]
  | some v =>
    have hv := StructuredStart.ofValue_toValue h
    simp [structuredOfValue, structuredToValue, h, wireMembers, keysDistinct, List.lookup,
      readWireSteps_map, hv, bind, Except.bind, pure, Except.pure]

/-! ## The DERIVATION sum -/

/-- A KERNEL payload as a wire object. -/
def kernelToValue (proof : String) : Value := .obj [("PROOF", .str proof)]

/-- An attachment as a wire object: its STRUCTURED or KERNEL payload. -/
def Attachment.toValue : Attachment → Value
  | .structured steps start => structuredToValue steps start
  | .kernelProof p => kernelToValue p

/-- A DERIVATION as a wire object, by its form's shape. -/
def derivationToValue : Derivation → Value
  | .prose n text att =>
    .obj ([("STEPS", .int n), ("TEXT", .str text)] ++
      (att.map fun a => [("ATTACHMENT", a.toValue)]).getD [])
  | .structured steps start => structuredToValue steps start
  | .kernelProof p => kernelToValue p

/-- A KERNEL payload from its wire object: `{PROOF}`. -/
def kernelOfValue (v : Value) : Except String String := do
  let ms ← wireMembers ["PROOF"] v
  wireString ms "PROOF"

/-- An attachment from its wire object: a KERNEL payload when it holds `PROOF`, else a
STRUCTURED payload. -/
def attachmentOfValue (v : Value) : Except String Attachment :=
  match v with
  | .obj ms =>
    if (ms.lookup "PROOF").isSome then
      match kernelOfValue v with
      | .ok p => .ok (.kernelProof p)
      | .error w => .error w
    else
      match structuredOfValue v with
      | .ok (steps, start) => .ok (.structured steps start)
      | .error w => .error w
  | _ => .error "not-an-object"

/-- A PROSE derivation from its wire object: `{STEPS: integer, TEXT, ATTACHMENT?}`. -/
def proseOfValue (v : Value) : Except String Derivation := do
  let ms ← wireMembers ["ATTACHMENT", "STEPS", "TEXT"] v
  let n ← match ms.lookup "STEPS" with
    | some (.int n) => if 0 ≤ n then pure n.toNat else throw "not-a-count STEPS"
    | some _ => throw "not-an-integer-or-a-list STEPS"
    | none => throw "missing STEPS"
  let text ← wireString ms "TEXT"
  let att ← match ms.lookup "ATTACHMENT" with
    | none => pure none
    | some a => match attachmentOfValue a with
      | .ok x => pure (some x)
      | .error w => throw ("ATTACHMENT: " ++ w)
  pure (.prose n text att)

/-- The forms whose own members an object holds: PROSE's `TEXT`, `ATTACHMENT` or an
integer `STEPS`; STRUCTURED's `START` or a list `STEPS`; KERNEL's `PROOF`. -/
def formsHeld (ms : List (String × Value)) : List DerivationForm :=
  let steps := ms.lookup "STEPS"
  let prose := (ms.lookup "TEXT").isSome || (ms.lookup "ATTACHMENT").isSome ||
    (match steps with | some (.int _) => true | _ => false)
  let structured := (ms.lookup "START").isSome ||
    (match steps with | some (.arr _) => true | _ => false)
  let kernel := (ms.lookup "PROOF").isSome
  (if prose then [.prose] else []) ++ (if structured then [.structured] else []) ++
    (if kernel then [.kernelProof] else [])

/-- A DERIVATION from its wire object, its form told by its shape. -/
def derivationOfValue (v : Value) : Except String Derivation :=
  match v with
  | .obj ms =>
    match formsHeld ms with
    | [.prose] => proseOfValue v
    | [.structured] =>
      match structuredOfValue v with
      | .ok (steps, start) => .ok (.structured steps start)
      | .error w => .error w
    | [.kernelProof] =>
      match kernelOfValue v with
      | .ok p => .ok (.kernelProof p)
      | .error w => .error w
    | [] => if (ms.lookup "STEPS").isSome then .error "not-an-integer-or-a-list STEPS"
      else .error "no-form"
    | _ => .error "mixed-forms"
  | _ => .error "not-an-object"

/-! ## The writer never refuses -/

theorem canonicalJsonList_isSome {xs : List Value} (h : ∀ x ∈ xs, x.canonicalJson.isSome) :
    (Value.canonicalJsonList xs).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp (ih fun y hy => h y (by simp [hy]))
    simp [Value.canonicalJsonList, ht, hts]

theorem canonicalJsonMembers_keys {ms : List (String × Value)}
    (h : ∀ m ∈ ms, m.2.canonicalJson.isSome) :
    ∃ ts, Value.canonicalJsonMembers ms = some ts ∧ ts.map (·.1) = ms.map (·.1) := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨k, v⟩ := m
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h (k, v) (by simp))
    obtain ⟨ts, hts, hk⟩ := ih fun y hy => h y (by simp [hy])
    exact ⟨(k, t) :: ts, by simp [Value.canonicalJsonMembers, ht, hts], by simp [hk]⟩

/-- An object whose members' values are all written and whose keys are distinct is
written. -/
theorem canonicalJson_obj_isSome {ms : List (String × Value)}
    (h : ∀ m ∈ ms, m.2.canonicalJson.isSome) (hd : (ms.map (·.1)).Nodup) :
    (Value.obj ms).canonicalJson.isSome := by
  obtain ⟨ts, hts, hk⟩ := canonicalJsonMembers_keys h
  have hd' : (ts.map Prod.fst).Nodup := by
    have : ts.map Prod.fst = ms.map (·.1) := hk
    rw [this]; exact hd
  have ha := (Principia.Canonical.adjacentKeysDistinct_sortMembers ts).mpr hd'
  simp [Value.canonicalJson, hts, Principia.Canonical.objectText, ha]

theorem StructuredStep.toValue_canonicalJson_isSome (s : StructuredStep) :
    s.toValue.canonicalJson.isSome := by
  obtain ⟨e, c, site, fwd⟩ := s
  cases c <;>
    exact canonicalJson_obj_isSome
      (by simp [StepCitation.member, Value.canonicalJson])
      (by simp [StepCitation.member])

/-- **The writer never refuses a payload**: every STRUCTURED payload has a canonical
JSON text. -/
theorem structuredToValue_canonicalJson_isSome (steps : List StructuredStep)
    (start : StructuredStart) : (structuredToValue steps start).canonicalJson.isSome := by
  have hsteps : (Value.canonicalJsonList (steps.map StructuredStep.toValue)).isSome :=
    canonicalJsonList_isSome fun x hx => by
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
      exact s.toValue_canonicalJson_isSome
  cases start <;>
    exact canonicalJson_obj_isSome
      (by simp [StructuredStart.toValue?, Value.canonicalJson, hsteps, Value.canonicalJsonMembers,
        Principia.Canonical.objectText, Principia.Canonical.sortMembers,
        Principia.Canonical.adjacentKeysDistinct])
      (by simp [StructuredStart.toValue?])

/-! ## The DERIVATION sum's round trip -/

theorem kernelOfValue_kernelToValue (p : String) : kernelOfValue (kernelToValue p) = .ok p := by
  simp [kernelOfValue, kernelToValue, wireMembers, keysDistinct, wireString, List.lookup, bind,
    Except.bind]

theorem structuredToValue_lookup_proof (steps : List StructuredStep) (start : StructuredStart) :
    ∃ ms, structuredToValue steps start = .obj ms ∧ ms.lookup "PROOF" = none ∧
      ms.lookup "TEXT" = none ∧ ms.lookup "ATTACHMENT" = none ∧
      ms.lookup "STEPS" = some (.arr (steps.map StructuredStep.toValue)) := by
  cases start <;> simp [structuredToValue, StructuredStart.toValue?, List.lookup] <;>
    refine ⟨?_, ?_, ?_⟩ <;> intro a b h <;> rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

theorem attachmentOfValue_toValue (a : Attachment) : attachmentOfValue a.toValue = .ok a := by
  cases a with
  | structured steps start =>
    obtain ⟨ms, hv, hp, -, -, -⟩ := structuredToValue_lookup_proof steps start
    have h := structuredOfValue_structuredToValue steps start
    rw [hv] at h
    simp [attachmentOfValue, Attachment.toValue, hv, hp, h]
  | kernelProof p =>
    simp [attachmentOfValue, Attachment.toValue, kernelToValue, List.lookup, kernelOfValue,
      wireMembers, keysDistinct, wireString, bind, Except.bind]

/-- **The sum's round trip.** Reading a DERIVATION's wire object gives the derivation back:
its form, and the payload of each form, the attachment included. -/
theorem derivationOfValue_derivationToValue (d : Derivation) :
    derivationOfValue (derivationToValue d) = .ok d := by
  cases d with
  | prose n text att =>
    cases att with
    | none =>
      simp [derivationOfValue, derivationToValue, formsHeld, List.lookup, proseOfValue,
        wireMembers, keysDistinct, wireString, bind, Except.bind, pure, Except.pure]
    | some a =>
      simp [derivationOfValue, derivationToValue, formsHeld, List.lookup, proseOfValue,
        wireMembers, keysDistinct, wireString, attachmentOfValue_toValue, bind, Except.bind,
        pure, Except.pure]
  | structured steps start =>
    obtain ⟨ms, hv, hp, ht, ha, hs⟩ := structuredToValue_lookup_proof steps start
    have h := structuredOfValue_structuredToValue steps start
    rw [hv] at h
    simp [derivationOfValue, derivationToValue, hv, formsHeld, hp, ht, ha, hs, h]
  | kernelProof p =>
    simp [derivationOfValue, derivationToValue, kernelToValue, formsHeld, List.lookup,
      kernelOfValue, wireMembers, keysDistinct, wireString, bind, Except.bind]

end Principia.Record
