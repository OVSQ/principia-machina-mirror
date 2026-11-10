import Principia.Zone
import Principia.Form
import Principia.Units
import Principia.Digest

/-!
# The zones' preimages and digests, and the successor classes

v1's `tpc_zone` 0.5.1 canonical serialization (schema 0.5.0; TPS 2.5.9) and the
successor classes (TPS 2.1.5): `_entry_list`, `_sorted_entries`, `_tree_tpk`, `_tree_trm`,
`_tree_tms`, `_node`, `zone_preimage`, `d_tpk`, `d_trm`, `d_tms`, `d_tfk_of` and
`classify_successor`. This is the one implementation: the Provision functions take D(TPK) and
`_entry_list` from here, as v1's `tpc_module` took them from `tpc_zone`, and the record check
takes the zones' digests from here.

A zone's preimage is a tree of texts, integers and lists (`Principia.Digest.Tree`), written as
the type-tagged netstring, every text put through v1's `_text` first (line endings as LF, then
NFC at Unicode 15.1.0; `Principia.Zone.text`). Each entry's fields come in its kind's order,
normalized as v1 normalized them: a set field (REFS, OVER, BEARS) sorted, a KEY's terms in their
canonical spelling, a yardstick's limiting cases sorted by DOMAIN, a DIMENSION, a decimal, a
UNIT and a form in their canonical spellings; the entries of a list are sorted by NAME (the
inventory by ENVIRONMENT_QUANTITY). A digest is SHA-256 over the preimage's UTF-8 bytes, in
lowercase hexadecimal (`Principia.Digest.ofPreimage`, `Principia.Sha256`), and D(TFK) combines the three zones' digests in the order TPK, TrM, TMS
(`Principia.Digest.combineDigests`).

Digests are defined over well-formed zones: v1's custodian ran the zone checks first, and v1's
serializer raised on a value it cannot write (a field that does not normalize, a boolean, a
number with a fraction, null, an object, a missing part). Here such a zone is refused, the
refusal naming what it met (`Fault`); no case of v1's corpus reaches one.
-/

namespace Principia.Zone

open Principia.Digest (Tree)

/-! ## A field's value, normalized (v1 `_entry_list`) -/

/-- A field's value as v1's `_entry_list` leaves it. -/
inductive Norm where
  /-- A tree of texts, integers and lists; its texts are put through `_text` when the tree is
  written (`canonicalTree`). -/
  | tree (t : Tree)
  /-- v1's None: a DIMENSION, a decimal, a UNIT or a form with no canonical spelling. -/
  | none
  /-- A value v1's serializer cannot write: what it is. -/
  | unwritable (what : String)
  deriving BEq, Repr, Inhabited

/-- What a value is, for a refusal. -/
def Value.kindWord : Value → String
  | .null => "null"
  | .bool _ => "a boolean"
  | .int _ => "an integer"
  | .real => "a number with a fraction"
  | .str _ => "a text"
  | .arr _ => "a list"
  | .obj _ => "an object"

mutual
/-- v1's `_node` of a value as given: a text, an integer, or a list of them. -/
def valueTree : Value → Except String Tree
  | .str s => .ok (.text s)
  | .int n => .ok (.int n)
  | .arr xs => (valueTrees xs).map .list
  | v => .error v.kindWord
/-- Each value of a list as its tree. -/
def valueTrees : List Value → Except String (List Tree)
  | [] => .ok []
  | x :: xs => do pure ((← valueTree x) :: (← valueTrees xs))
end

/-- A value as given, its tree, or what it is when v1's `_node` would raise on it. -/
def asGiven (v : Value) : Norm :=
  match valueTree v with
  | .ok t => .tree t
  | .error w => .unwritable w

/-- The texts of a list value, when it is a list of texts. -/
def textList? : Value → Option (List String)
  | .arr xs => xs.mapM fun | .str s => some s | _ => Option.none
  | _ => Option.none

/-- Texts in code point order (Python's `sorted`). -/
def sortTexts (xs : List String) : List String := xs.mergeSort fun a b => decide (a ≤ b)

/-- A limiting case's fields (v1 `LIM_FIELDS`). -/
def limitingFields : List String := ["DOMAIN", "KEY"]

/-- The fields whose value is a canonical spelling of a text: v1's DIM, DEC, UNIT and FORM
fields, each normalized by its own grammar, `none` when it has no canonical spelling. -/
def spellingOf (f : String) (s : String) : Option (Option String) :=
  if f == "DIMENSION" then some (Dimension.normalize s)
  else if decFields.contains f then some (Decimal.canon s)
  else if f == "UNIT" then some ((Units.unitParse s).toOption.map (·.spelling))
  else match Form.Mode.ofField? f with
    | some m =>
      some (match Form.parseForm s m with
        | .ok c => some c
        | _ => Option.none)
    | Option.none => Option.none

/-- A field's value written as v1's flat entry list writes it: the field's name, then its
value. -/
def entryTree (fs : List (String × Norm)) : Except String Tree := do
  let mut out : List Tree := []
  for (f, n) in fs do
    match n with
    | .tree t => out := out ++ [.text f, t]
    | .none => throw ("field " ++ f ++ " has no canonical form")
    | .unwritable w => throw ("field " ++ f ++ " holds " ++ w)
  pure (.list out)

/-- One field's value, normalized (the `elif` chain of v1's `_entry_list`): a set field's
texts sorted after `_text`; a KEY's terms each in its canonical spelling after `_text`; the
limiting cases sorted by DOMAIN after `_text`, each its own entry list; a DIMENSION, a decimal,
a UNIT or a form in its canonical spelling; any other value as given. -/
def normField (f : String) (v : Value) : Norm :=
  if setFields.contains f then
    match textList? v with
    | some xs => .tree (.list ((sortTexts (xs.map text)).map .text))
    | Option.none => .unwritable ("a " ++ f ++ " that is not a list of texts")
  else if seqFields.contains f then
    match textList? v with
    | some xs => .tree (.list (xs.map fun x => .text (Criteria.canonicalTerm (text x))))
    | Option.none => .unwritable ("a " ++ f ++ " that is not a list of texts")
  else if objListFields.contains f then
    let cases? : Option (List Entry) := match v with
      | .arr xs => xs.mapM fun | .obj e => some e | _ => Option.none
      | _ => Option.none
    match cases? with
    | Option.none => .unwritable ("a " ++ f ++ " that is not a list of objects")
    | some cs =>
      let keyed := cs.map fun c => (text ((getStr? c "DOMAIN").getD ""), c)
      let sorted := keyed.mergeSort fun a b => decide (a.1 ≤ b.1)
      let entries := sorted.mapM fun (_, c) =>
        entryTree (limitingFields.filterMap fun g => (get? c g).map fun w => (g, normLimiting g w))
      match entries with
      | .ok ts => .tree (.list ts)
      | .error w => .unwritable ("a limiting case whose " ++ w)
  else
    match v with
    | .str s =>
      match spellingOf f s with
      | some (some c) => .tree (.text c)
      | some Option.none => .none
      | Option.none => .tree (.text s)
    | _ =>
      match spellingOf f "" with
      | some _ => .none
      | Option.none => asGiven v
where
  /-- A limiting case's field: its DOMAIN as given, its KEY's terms canonical. -/
  normLimiting (g : String) (w : Value) : Norm :=
    if seqFields.contains g then
      match textList? w with
      | some xs => .tree (.list (xs.map fun x => .text (Criteria.canonicalTerm (text x))))
      | Option.none => .unwritable ("a " ++ g ++ " that is not a list of texts")
    else asGiven w

/-- v1's `_entry_list(e, fields)`: the fields present, in the order given, each normalized. -/
def entryList (e : Entry) (fields : List String) : List (String × Norm) :=
  fields.filterMap fun f => (get? e f).map fun v => (f, normField f v)

/-! ## The trees (v1 `_tree_tpk`, `_tree_trm`, `_tree_tms`) -/

/-- Why a zone has no preimage: what v1's serializer would have raised on. -/
abbrev Fault := String

/-- The schema's version, the second item of every zone's tree. -/
def schemaVersion : String := "0.5.0"

/-- The objects of a list value, or the fault. -/
def objectsOf (what : String) : Value → Except Fault (List Entry)
  | .arr xs => xs.mapM fun
    | .obj e => .ok e
    | v => .error (what ++ " holds " ++ v.kindWord ++ ", not an object")
  | v => .error (what ++ " is " ++ v.kindWord ++ ", not a list")

/-- v1's `_sorted_entries(lst, fields, keyfield)`: each entry's list, the entries sorted by
the key field's text after `_text` (a stable sort, as Python's). -/
def sortedEntries (what : String) (lst : Value) (fields : List String) (key : String := "NAME") :
    Except Fault Tree := do
  let es ← objectsOf what lst
  let keyed ← es.mapM fun e => match getStr? e key with
    | some s => .ok (text s, e)
    | Option.none => .error (what ++ ": an entry has no text " ++ key)
  let sorted := keyed.mergeSort fun a b => decide (a.1 ≤ b.1)
  let lists ← sorted.mapM fun (_, e) => entryTree (entryList e fields)
  pure (.list lists)

/-- An object's member, or the fault naming it (v1's `obj[k]`). -/
def member (what : String) (v : Value) (k : String) : Except Fault Value :=
  match v with
  | .obj e => match get? e k with
    | some x => .ok x
    | Option.none => .error (what ++ " has no " ++ k)
  | _ => .error (what ++ " is " ++ v.kindWord ++ ", not an object")

/-- A list member, `[]` when absent (v1's `obj.get(k, [])`). -/
def memberOr (e : Entry) (k : String) : Value := (get? e k).getD (.arr [])

/-- A PARAMETERS object with its defaults set where absent (v1's `setdefault`). -/
def withDefaults (pm : Entry) (defaults : List (String × String)) : Entry :=
  defaults.foldl (fun acc (k, d) => if has acc k then acc else acc ++ [(k, .str d)]) pm

/-- An object's members, or the fault. -/
def objectOf (what : String) : Value → Except Fault Entry
  | .obj e => .ok e
  | v => .error (what ++ " is " ++ v.kindWord ++ ", not an object")

/-- v1's `_tree_tpk`: "TPK", the schema's version, the PARAMETERS part (D_VARIABLES ONE when
absent), then each kind's entries sorted by NAME. -/
def tpkTree (tpk : Value) : Except Fault Tree := do
  let z ← objectOf "the TPK" tpk
  let pm ← objectOf "the TPK's PARAMETERS" ((get? z "PARAMETERS").getD (.obj []))
  let pm := withDefaults pm [("D_VARIABLES", "ONE")]
  let params ← entryTree (entryList pm ["D_VARIABLES"])
  let mut parts : List Tree := [.text "TPK", .text schemaVersion, .list [.text "PARAMETERS", params]]
  for kind in StartingSet.kinds do
    let (req, opt) := StartingSet.kindFields kind
    let entries ← sortedEntries ("the TPK's " ++ kind) (memberOr z kind) (req ++ opt)
    parts := parts ++ [.list [.text kind, entries]]
  pure (.list parts)

/-- v1's `_tree_trm`: "TrM", the schema's version, the HEADER's three parts (the inventory
sorted by ENVIRONMENT_QUANTITY, the SIGNATURE and the TRANSFORMATIONS by NAME), then the
ENTRIES sorted by NAME. -/
def trmTree (trm : Value) : Except Fault Tree := do
  let h ← member "the TrM" trm "HEADER"
  let inv ← member "the TrM's HEADER" h "ENVIRONMENT_INVENTORY"
  let sig ← member "the TrM's HEADER" h "SIGNATURE"
  let trf ← member "the TrM's HEADER" h "TRANSFORMATIONS"
  let ents ← member "the TrM" trm "ENTRIES"
  let (sreq, sopt) := Correspondence.signatureFields
  let invTree ← sortedEntries "the ENVIRONMENT_INVENTORY" inv Correspondence.inventoryFields
    "ENVIRONMENT_QUANTITY"
  let sigTree ← sortedEntries "the SIGNATURE" sig (sreq ++ sopt)
  let trfTree ← sortedEntries "the TRANSFORMATIONS" trf Correspondence.transformationFields
  let entTree ← sortedEntries "the ENTRIES" ents Correspondence.entryFields
  pure (.list [.text "TrM", .text schemaVersion,
    .list [.text "HEADER", .list [.text "ENVIRONMENT_INVENTORY", invTree],
      .list [.text "SIGNATURE", sigTree], .list [.text "TRANSFORMATIONS", trfTree]],
    .list [.text "ENTRIES", entTree]])

/-- A Criteria Set constant's fields (v1 `TMSC_FIELDS`). -/
def constantFields : List String := ["NAME", "VALUE"]

/-- A yardstick's fields (v1 `YARD_FIELDS`). -/
def yardstickFields : List String := ["NAME", "KEY", "LIMITING"]

/-- v1's `_tree_tms`: "TMS", the schema's version, the PARAMETERS (IC2_POLICY GAP,
PROMOTION_FLOOR F2 and STRUCTURE_CHECK ON when absent), then the CONSTANTS and
the YARDSTICKS sorted by NAME. -/
def tmsTree (tms : Value) : Except Fault Tree := do
  let pm ← objectOf "the TMS's PARAMETERS" (← member "the TMS" tms "PARAMETERS")
  let pm := withDefaults pm
    [("IC2_POLICY", "GAP"), ("PROMOTION_FLOOR", "F2"), ("STRUCTURE_CHECK", "ON")]
  let z ← objectOf "the TMS" tms
  let params ← entryTree (entryList pm (Criteria.paramFields.1 ++ Criteria.paramFields.2))
  let consts ← sortedEntries "the CONSTANTS" (memberOr z "CONSTANTS") constantFields
  let yards ← sortedEntries "the YARDSTICKS" (memberOr z "YARDSTICKS") yardstickFields
  pure (.list [.text "TMS", .text schemaVersion, .list [.text "PARAMETERS", params],
    .list [.text "CONSTANTS", consts], .list [.text "YARDSTICKS", yards]])

/-! ## The preimages and the digests (v1 `_node`, `zone_preimage`, `d_tpk`, `d_trm`, `d_tms`,
`d_tfk_of`) -/

mutual
/-- v1's `_node`'s texts: every text of a tree put through `_text`. -/
def canonicalTree : Tree → Tree
  | .text s => .text (text s)
  | .int n => .int n
  | .list xs => .list (canonicalTrees xs)
/-- Each tree of a list, its texts through `_text`. -/
def canonicalTrees : List Tree → List Tree
  | [] => []
  | x :: xs => canonicalTree x :: canonicalTrees xs
end

/-- v1's `_node` of a tree: its texts through `_text`, then the type-tagged netstring. -/
def node (t : Tree) : String := (canonicalTree t).preimage

/-- The three zones, by the names v1's `zone_preimage` takes. -/
inductive ZoneName where
  | tpk | trm | tms
  deriving DecidableEq, Repr

/-- `TPK`, `TrM` or `TMS`. -/
def ZoneName.ofString? : String → Option ZoneName
  | "TPK" => some .tpk
  | "TrM" => some .trm
  | "TMS" => some .tms
  | _ => Option.none

/-- A zone's tree. -/
def ZoneName.tree : ZoneName → Value → Except Fault Tree
  | .tpk => tpkTree
  | .trm => trmTree
  | .tms => tmsTree

/-- v1's `zone_preimage(zone, value)`: the exact preimage of one zone, as text. -/
def zonePreimage (zone : ZoneName) (value : Value) : Except Fault String :=
  node <$> zone.tree value

/-- A zone's digest: SHA-256 over its preimage, in lowercase hexadecimal. -/
def zoneDigest (zone : ZoneName) (value : Value) : Except Fault String :=
  Digest.ofPreimage <$> zonePreimage zone value

/-- v1's `d_tpk`. -/
def dTpk (tpk : Value) : Except Fault String := zoneDigest .tpk tpk

/-- v1's `d_trm`. -/
def dTrm (trm : Value) : Except Fault String := zoneDigest .trm trm

/-- v1's `d_tms`. -/
def dTms (tms : Value) : Except Fault String := zoneDigest .tms tms

/-- v1's `d_tfk_of(tfk)`: D(TFK) of a whole Research Assembly `{"TPK", "TrM", "TMS"}`, its
three zones' digests combined in that order. -/
def dTfkOf (tfk : Value) : Except Fault String := do
  let p ← dTpk (← member "the TFK" tfk "TPK")
  let r ← dTrm (← member "the TFK" tfk "TrM")
  let m ← dTms (← member "the TFK" tfk "TMS")
  match Digest.combineDigests [p, r, m] with
  | some d => pure d
  | Option.none => throw "a zone's digest is not 64 lowercase hexadecimal characters"

/-! ## The successor classes (TPS 2.1.5; v1 `classify_successor`) -/

/-- How a successor Research Assembly differs from its predecessor. -/
inductive Successor where
  /-- The three zones' digests are equal. -/
  | identical
  /-- D(TPK) and D(TrM) equal, D(TMS) moved. -/
  | yardstickOnly
  /-- D(TPK) equal, D(TrM) moved. -/
  | correspondenceChanged
  /-- D(TPK) moved. -/
  | kernelChanged
  deriving DecidableEq, Repr

/-- v1's word for a successor class. -/
def Successor.word : Successor → String
  | .identical => "IDENTICAL"
  | .yardstickOnly => "YARDSTICK_ONLY"
  | .correspondenceChanged => "CORRESPONDENCE_CHANGED"
  | .kernelChanged => "KERNEL_CHANGED"

/-- The class given the three digest comparisons, in v1's order: the Starting Set first,
then the Correspondence Table, then the Criteria Set. -/
def Successor.ofMoves (tpk trm tms : Bool) : Successor :=
  if tpk then .kernelChanged
  else if trm then .correspondenceChanged
  else if tms then .yardstickOnly
  else .identical

/-- v1's `classify_successor(a, b)`: each Research Assembly's zones digested and compared, in
order (a zone of `b` is digested only when the earlier zones agree, as v1 digests them). -/
def classifySuccessor (a b : Value) : Except Fault Successor := do
  let zone (v : Value) (k : String) := member "the TFK" v k
  if (← dTpk (← zone a "TPK")) != (← dTpk (← zone b "TPK")) then return .kernelChanged
  if (← dTrm (← zone a "TrM")) != (← dTrm (← zone b "TrM")) then
    return .correspondenceChanged
  if (← dTms (← zone a "TMS")) != (← dTms (← zone b "TMS")) then return .yardstickOnly
  return .identical

/-! ## What Lean proves -/

/-- A zone's digest is SHA-256 of its preimage. -/
theorem zoneDigest_eq (zone : ZoneName) (v : Value) :
    zoneDigest zone v = Digest.ofPreimage <$> zonePreimage zone v := rfl

/-- Every zone digest is 64 characters. -/
theorem zoneDigest_length {zone : ZoneName} {v : Value} {d : String}
    (h : zoneDigest zone v = .ok d) : d.length = 64 := by
  unfold zoneDigest at h
  cases hp : zonePreimage zone v with
  | error e => simp [hp, Functor.map, Except.map] at h
  | ok p =>
    simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
    rw [← h]
    exact Digest.ofPreimage_length p

/-- A Research Assembly is IDENTICAL to itself, whenever its zones have digests. -/
theorem classifySuccessor_self (a : Value) :
    classifySuccessor a a = .ok .identical ∨ ∃ f, classifySuccessor a a = .error f := by
  unfold classifySuccessor
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals first
    | exact Or.inr ⟨_, rfl⟩
    | exact Or.inl rfl
    | simp_all

/-- The successor class is the class of the three moves (`Successor.ofMoves`), whenever the
six zones have digests. -/
theorem classifySuccessor_ofMoves {a b ta tb ra rb ma mb : Value} {pa pb qa qb sa sb : String}
    (hta : member "the TFK" a "TPK" = .ok ta) (htb : member "the TFK" b "TPK" = .ok tb)
    (hra : member "the TFK" a "TrM" = .ok ra) (hrb : member "the TFK" b "TrM" = .ok rb)
    (hma : member "the TFK" a "TMS" = .ok ma) (hmb : member "the TFK" b "TMS" = .ok mb)
    (hpa : dTpk ta = .ok pa) (hpb : dTpk tb = .ok pb) (hqa : dTrm ra = .ok qa)
    (hqb : dTrm rb = .ok qb) (hsa : dTms ma = .ok sa) (hsb : dTms mb = .ok sb) :
    classifySuccessor a b = .ok (Successor.ofMoves (pa != pb) (qa != qb) (sa != sb)) := by
  unfold classifySuccessor Successor.ofMoves
  simp only [bind, Except.bind, pure, Except.pure, hta, htb, hra, hrb, hma, hmb, hpa, hpb, hqa,
    hqb, hsa, hsb]
  by_cases h1 : (pa != pb) = true
  · simp [h1]
  · by_cases h2 : (qa != qb) = true
    · simp [h1, h2]
    · by_cases h3 : (sa != sb) = true
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]

/-- A text's node is its tag `s` and its text through `_text`. -/
theorem node_text (s : String) : node (.text s) = "s" ++ text s := by
  simp [node, canonicalTree, Digest.Tree.preimage]

end Principia.Zone
