import Principia.Strike
import Principia.Zone
import Principia.Units
import Principia.Canonical
import Principia.Form.Arithmetic

/-!
# SR3's scope and the CONDITIONS of a comparison

The strike rule's functions that read the zones and the register's records, ported from
v1's `tpc_strike` (TPC-PY 0.3.0):

* `sr3Scope` (v1 `sr3_scope`): whether SR3's M-M and L-M tests and SR8's scale
  factor run mechanically over a QUANTITY (its DOF FIXed in the Starting Set) or are
  listed for row 21's inspection (TPS 4.4.13 and 4.2.13 as staged).
* `conditionsOf`, `comparisonSet`, `sr8Groups` (v1 `conditions_of`, `comparison_set`,
  `sr8_groups`; tpm_record_functions 0.2.0, section 9): a record's CONDITIONS
  (the SITUATION assumptions of its closure, and its AT points in coherent SI), the pairs
  SR3 compares, and the groups SR8 scales.

They read their inputs as JSON gives them, malformed ones included, and never fail: every
fault is a refusal with v1's words. `sr3Scope` reads the Research Assembly as the zones do
(`Principia.Zone.Value`); the other three read the register as canonical JSON writes it
(`Principia.Canonical.Value`), since their refusals quote the input in that form, and they
hand the Research Assembly to `sr3Scope` through `toZoneValue`.

A message escapes the code points v1 escaped, by Unicode 15.1.0's general category
(`Principia.Zone.disallowed`). Owed, never answered: an AT point
whose coherent-SI value carries a power of π, whose twelve-digit text needs π's digits
(v1 wrote its double; under the Calculator's exact default it does not round π).

v1's AT value is `canon_decimal(canon(v))`: the coherent-SI value in the twelve-digit form,
then canonical. Here `canon` is the canonical serialization's (`Canonical.ratioText`), one
rounding of the exact value, so two points equal to twelve digits compare equal, as in v1.

Vectors: the corpora of `sr3Scope` and of the conditions, run by the strike tests.
-/

namespace Principia.Strike

/-! ## The Research Assembly as the zones read it -/

mutual
/-- A canonical JSON value as the zones read it: a number with a fraction or an exponent
is v1's float, which the zones keep as `real`. -/
def toZoneValue : Canonical.Value → Zone.Value
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .num _ => .real
  | .str s => .str s
  | .arr xs => .arr (toZoneList xs)
  | .obj ms => .obj (toZoneMembers ms)

/-- Each element as the zones read it. -/
def toZoneList : List Canonical.Value → List Zone.Value
  | [] => []
  | x :: xs => toZoneValue x :: toZoneList xs

/-- Each member as the zones read it. -/
def toZoneMembers : List (String × Canonical.Value) → List (String × Zone.Value)
  | [] => []
  | (k, v) :: ms => (k, toZoneValue v) :: toZoneMembers ms
end

/-- A message with every code point v1 escapes written `<U+XXXX>`. `alsoTabLf`: v1's
`_cshow` (the register functions' messages) escapes TAB and LF too, every code point of
general category C; its `_show` (the zones' and `sr3_scope`'s) does not. -/
def showMessage (alsoTabLf : Bool) (s : String) : String :=
  String.join (s.toList.map fun c =>
    if Zone.disallowed c || (alsoTabLf && (c == '\t' || c == '\n'))
    then "<" ++ Zone.codePoint c ++ ">" else c.toString)

/-! ## sr3_scope -/

/-- `sr3_scope`'s answer for a QUANTITY. -/
inductive Sr3Scope where
  /-- The entry's DOF is the TARGET of a CONSTRAINT whose ACTION is FIX. -/
  | mechanical
  /-- The entry exists and no FIX constraint targets its DOF. -/
  | inspection
  deriving DecidableEq, Repr, Inhabited

/-- v1's word for the scope. -/
def Sr3Scope.toV1 : Sr3Scope → String
  | .mechanical => "MECHANICAL"
  | .inspection => "INSPECTION"

/-- v1's `_sr3_field`: `none` when the entry's field holds a string; else the problem. -/
def sr3Field (tag : String) (e : Zone.Entry) (f : String) : Option String :=
  match Zone.get? e f with
  | none => some (tag ++ ": missing field " ++ f)
  | some (.str _) => none
  | some _ => some (tag ++ ": field " ++ f ++ " has the wrong type")

/-- The first problem of a list of entries' fields, each entry tagged by its NAME. -/
def sr3Fields (kind : String) (fields : List String) : List Zone.Entry → Option String
  | [] => none
  | e :: es =>
    match fields.findSome? (sr3Field (kind ++ ":" ++ Zone.nameOf e) e) with
    | some p => some p
    | none => sr3Fields kind fields es

/-- The objects of a list, or `none` when one member is not an object. -/
def objects : List Zone.Value → Option (List Zone.Entry)
  | [] => some []
  | .obj e :: xs => (objects xs).map (e :: ·)
  | _ :: _ => none

/-- `sr3_scope` with its refusal unescaped: what is read, in v1's order, the first problem
refusing. The QUANTITY; the Research Assembly; the Correspondence Table and its ENTRIES,
each entry's NAME and DOF (every entry, before the answer); the QUANTITY resolved; the
Starting Set and its CONSTRAINT kind (absent: none), each constraint's TARGET and ACTION
(every constraint). A FIX counts only as ACTION `FIX` with TARGET the entry's DOF. -/
def sr3ScopeRaw (tfk quantity : Zone.Value) : Except String Sr3Scope := do
  let q ← match quantity with
    | .str s => if Zone.isIdent s then pure s else throw "QUANTITY is not an identifier"
    | _ => throw "QUANTITY is not an identifier"
  let some tfkE := (match tfk with | .obj e => some e | _ => none)
    | throw "TFK is not an object"
  let some trm := (match Zone.get? tfkE "TrM" with | some (.obj e) => some e | _ => none)
    | throw "TrM: zone is not an object"
  let some ents := Zone.get? trm "ENTRIES" | throw "TrM: missing part ENTRIES"
  let some entList := (match ents with | .arr xs => some xs | _ => none)
    | throw "TrM ENTRIES is not a list"
  let some es := objects entList | throw "TrM ENTRIES: entry is not an object"
  if let some p := sr3Fields "ENTRY" ["NAME", "DOF"] es then throw p
  let found := es.filterMap fun e =>
    if Zone.getStr? e "NAME" == some q then Zone.getStr? e "DOF" else none
  let dof ← match found with
    | [] => throw ("QUANTITY " ++ q ++ " names no TrM entry")
    | [d] => pure d
    | _ => throw ("TrM: duplicate entry name " ++ q)
  let some tpk := (match Zone.get? tfkE "TPK" with | some (.obj e) => some e | _ => none)
    | throw "TPK: zone is not an object"
  let some consList := (match (Zone.get? tpk "CONSTRAINT").getD (.arr []) with
      | .arr xs => some xs | _ => none)
    | throw "TPK kind CONSTRAINT is not a list"
  let some cons := objects consList | throw "TPK kind CONSTRAINT: entry is not an object"
  if let some p := sr3Fields "CONSTRAINT" ["TARGET", "ACTION"] cons then throw p
  let fixed := cons.any fun c =>
    Zone.getStr? c "ACTION" == some "FIX" && Zone.getStr? c "TARGET" == some dof
  pure (if fixed then .mechanical else .inspection)

/-- v1's `sr3_scope`: the scope, or a refusal with its reason escaped (v1's `_show`). -/
def sr3Scope (tfk quantity : Zone.Value) : Except String Sr3Scope :=
  (sr3ScopeRaw tfk quantity).mapError (showMessage false)

/-! ## The register's records -/

/-- A record of the register: its members. -/
abbrev Rec := List (String × Canonical.Value)

/-- A member of a record. -/
def field (r : Rec) (k : String) : Option Canonical.Value := r.lookup k

/-- Whether a member holds the string `s`. -/
def fieldIs (r : Rec) (k s : String) : Bool :=
  match field r k with
  | some (.str t) => t == s
  | _ => false

/-- v1's `_cmembers`: the strings of a list, or none. -/
def strMembers : Option Canonical.Value → List String
  | some (.arr xs) => xs.filterMap fun | .str s => some s | _ => none
  | _ => []

/-- v1's `_ckeyed`: the keyed members of a register, in order, or `none` when `records`
is not one: a list whose members are objects with a string ID, no ID twice, or list-form
records, which are passed over. -/
def keyedOf : Canonical.Value → Option (List (String × Rec))
  | .arr xs =>
    xs.foldlM (fun acc x => match x with
      | .obj r => match field r "ID" with
        | some (.str i) => if (acc.lookup i).isSome then none else some (acc ++ [(i, r)])
        | _ => none
      | .arr _ => some acc
      | _ => none) []
  | _ => none

/-! ## Results -/

/-- A refusal of the register functions: one `[code, field, message]` (tpc_record's
form), its message escaped as v1's `_cshow` writes it. -/
structure Refusal where
  code : String
  fieldName : String
  message : String
  deriving DecidableEq, Repr

/-- A register function's answer: a result, a refusal, or owed. -/
inductive Answer (α : Type) where
  | ok (a : α)
  | refused (r : Refusal)
  | owed (why : String)
  deriving Repr

/-- A refusal whose message is escaped (v1's `_cshow`). -/
def refuse {α : Type} (code : String) (msg : String) : Answer α :=
  .refused ⟨code, "-", showMessage true msg⟩

/-- An input value as a message slot: its canonical JSON, `none` when an object at some
depth holds a key twice (no JSON reader gives one). -/
def jsonText (v : Canonical.Value) : Option String := v.canonicalJson

/-- v1's `_cbad`: REC-50, the argument shown as canonical JSON. -/
def refuseBad {α : Type} (argument : String) (v : Canonical.Value) (what : String) : Answer α :=
  match jsonText v with
  | some t => refuse "REC-50" (argument ++ " " ++ t ++ " is not " ++ what)
  | none => .owed "an argument holds an object with a key twice"

/-- v1's `_cv`: a string as given, any other value as its canonical JSON. -/
def slotText (v : Canonical.Value) : Option String :=
  match v with
  | .str s => some s
  | _ => jsonText v

/-! ## CONDITIONS -/

/-- An AT point in coherent SI: the DOF, the canonical decimal of the value, the KIND. -/
structure Point where
  dof : String
  value : String
  kind : String
  deriving DecidableEq, Repr

/-- A record's CONDITIONS: the SITUATION assumptions of its closure, sorted, and its AT
points, sorted. -/
structure Conditions where
  situations : List String
  points : List Point
  deriving DecidableEq, Repr

/-- Points in v1's list order: by DOF, then value, then KIND, each in code point order. -/
def pointLe (a b : Point) : Bool :=
  decide (a.dof < b.dof) || (a.dof == b.dof &&
    (decide (a.value < b.value) || (a.value == b.value && decide (a.kind ≤ b.kind))))

/-- An AT point's value as v1 wrote it: `canon_decimal(canon(v))`, the coherent-SI value
in the twelve-digit form, then canonical. A value carrying a power of π takes its twelve
digits from bounds on π (`Form.twelve`); `none` only when 4096 bits do not settle them. -/
def pointValue (x : Exact) : Option String :=
  if x.pi ≠ 0 then (Form.twelve x).bind Decimal.canon
  else Decimal.canon (Canonical.ratioText (x.coef < 0) x.coef.num.natAbs x.coef.den)

/-- One AT point: the DOF and the normalized value, or `none` when it does not normalize;
owed when its value carries π and 4096 bits do not settle its twelve digits. -/
def readPoint (q : Canonical.Value) : Except String (Option Point) :=
  match q with
  | .obj m =>
    match field m "DOF" with
    | some (.str dof) =>
      let arg (k : String) : Units.Arg := match field m k with
        | some (.str s) => some s
        | _ => none
      match Units.normalizeMeasurementArg (arg "VALUE") (some "0") (arg "UNIT") with
      | .error _ => .ok none
      | .ok n =>
        match pointValue n.x with
        | some v => .ok (some ⟨dof, v, n.kind⟩)
        | none => .error ("an AT point's value in coherent SI carries a power of pi: its " ++
            "twelve digits are not settled by bounds on pi of up to 4096 bits")
    | _ => .ok none
  | _ => .ok none

/-- The AT points in order, v1's loop: the first that does not read or normalize ends it
(`none`, refused), the first carrying π ends it owed. -/
def readPoints : List Canonical.Value → Except String (Option (List Point))
  | [] => .ok (some [])
  | q :: qs =>
    match readPoint q with
    | .error w => .error w
    | .ok none => .ok none
    | .ok (some p) => (readPoints qs).map (·.map (p :: ·))

/-- v1's `_cconditions`: the CONDITIONS of a RESULT or a VERIFICATION of the register. A
VERIFICATION takes its TARGET's situations (RD-RS-36) with its own AT. -/
def conditionsAt (keyed : List (String × Rec)) (rec : Rec) :
    Answer Conditions := Id.run do
  let base : Option Rec :=
    if fieldIs rec "CLASS" "VERIFICATION" then
      match field rec "TARGET" with
      | some (.str t) => keyed.lookup t
      | _ => none
    else some rec
  let view : Records := keyed.map fun (k, r) =>
    (k, { assumptions := strMembers (field r "ASSUMPTIONS"),
          cites := (strMembers (field r "CITES")).filter fun c => (keyed.lookup c).isSome,
          steps := 0 })
  let baseId : Option String := base.bind fun b => match field b "ID" with
    | some (.str i) => some i
    | _ => none
  let closure := (baseId.bind (assumptionClosure · view)).getD []
  let situations := (closure.filter fun a => match keyed.lookup a with
      | some r => fieldIs r "CLASS" "ASSUMPTION" && (field r "SITUATION").isSome
      | none => false).mergeSort idLe
  let at_ := (field rec "AT").getD (.arr [])
  let bad : Answer Conditions := refuseBad "AT" at_ "a list of points that normalize"
  match at_ with
  | .arr qs =>
    match readPoints qs with
    | .error why => return .owed why
    | .ok (some pts) => return .ok ⟨situations, pts.mergeSort pointLe⟩
    | .ok none => return bad
  | _ => return bad

/-- v1's `conditions_of` (9.1): the CONDITIONS of a RESULT or a VERIFICATION of the
register. Refused: REC-50 (not a register), REC-52 (not in it), REC-73 (another class). -/
def conditionsOf (records id : Canonical.Value) : Answer Conditions :=
  match keyedOf records with
  | none => refuseBad "records" records "a register"
  | some keyed =>
    let missing : Answer Conditions := match slotText id with
      | some t => refuse "REC-52" ("record " ++ t ++ " is not in the register")
      | none => .owed "an argument holds an object with a key twice"
    match id with
    | .str i =>
      match keyed.lookup i with
      | none => missing
      | some rec =>
        if fieldIs rec "CLASS" "RESULT" || fieldIs rec "CLASS" "VERIFICATION" then
          conditionsAt keyed rec
        else refuse "REC-73" "conditions_of reads a RESULT or a VERIFICATION"
    | _ => missing

/-! ## comparison_set and sr8_groups -/

/-- v1's `_cscope`: the keyed register, the status words, and whether the QUANTITY's DOF
is FIXed. Refused: REC-50 (records, words), REC-74 (a QUANTITY that is no entry), REC-39
(a Research Assembly `sr3_scope` cannot read). -/
def scopeOf (records words tfk quantity : Canonical.Value) :
    Answer (List (String × Rec) × List (String × String) × Bool) :=
  match keyedOf records with
  | none => refuseBad "records" records "a register"
  | some keyed =>
    let ws : Option (List (String × String)) := match words with
      | .obj ms => ms.mapM fun (k, v) => match v with
        | .str s => some (k, s)
        | _ => none
      | _ => none
    match ws with
    | none => refuseBad "words" words "a map of status words"
    | some ws =>
      let notEntry : Answer (List (String × Rec) × List (String × String) × Bool) :=
        match slotText quantity with
        | some t => refuse "REC-74" ("quantity " ++ t ++ " is not an entry of the TrM")
        | none => .owed "an argument holds an object with a key twice"
      match quantity with
      | .str _ =>
        match sr3ScopeRaw (toZoneValue tfk) (toZoneValue quantity) with
        | .ok sc => .ok (keyed, ws, sc == .mechanical)
        | .error r =>
          if r.startsWith "QUANTITY " then notEntry
          else refuse "REC-39" "the TFK is not readable"
      | _ => notEntry

/-- A record stands: its status word, `NOT GRADED` when absent, is PROVISIONAL or
ESTABLISHED. -/
def standing (ws : List (String × String)) (rid : String) : Bool :=
  let w := (ws.lookup rid).getD "NOT GRADED"
  w == "PROVISIONAL" || w == "ESTABLISHED"

/-- v1's `_cmembers_of`: the standing RESULTs naming the QUANTITY, REGIME M, and with
`withL` REGIME L carrying a VALUE; in code point order. -/
def membersOf (keyed : List (String × Rec)) (ws : List (String × String)) (quantity : String)
    (withL : Bool) : List String :=
  ((keyed.map (·.1)).mergeSort idLe).filter fun rid =>
    match keyed.lookup rid with
    | none => false
    | some r =>
      fieldIs r "CLASS" "RESULT" && fieldIs r "QUANTITY" quantity && standing ws rid &&
        (fieldIs r "REGIME" "M" ||
          (withL && fieldIs r "REGIME" "L" && (field r "VALUE").isSome))

/-- The CONDITIONS of each record, in order, or the first refusal. -/
def conditionsAll (keyed : List (String × Rec)) :
    List String → Answer (List (String × Conditions))
  | [] => .ok []
  | rid :: rest =>
    match keyed.lookup rid with
    | none => .ok []
    | some rec =>
      match conditionsAt keyed rec with
      | .ok c =>
        match conditionsAll keyed rest with
        | .ok cs => .ok ((rid, c) :: cs)
        | .refused r => .refused r
        | .owed w => .owed w
      | .refused r => .refused r
      | .owed w => .owed w

/-- How SR3 compares a pair of equal CONDITIONS. -/
inductive CompareMode where
  /-- Equal but for a point's KIND: no test; the row-43 audit block. -/
  | convention
  /-- Tested: the entry's DOF FIXed, or a non-empty AT. -/
  | test
  /-- Listed for row 21's inspection. -/
  | inspect
  deriving DecidableEq, Repr, Inhabited

/-- v1's word for the mode. -/
def CompareMode.toV1 : CompareMode → String
  | .convention => "CONVENTION"
  | .test => "TEST"
  | .inspect => "INSPECT"

/-- The DOF and value of each point, its KIND left out. -/
def withoutKind (ps : List Point) : List (String × String) := ps.map fun p => (p.dof, p.value)

/-- Whether the register's record `rid` is of REGIME L. -/
def regimeL (keyed : List (String × Rec)) (rid : String) : Bool :=
  ((keyed.lookup rid).map (fieldIs · "REGIME" "L")).getD false

/-- The mode of a pair, or `none` when SR3 does not compare it: two L records, or
CONDITIONS that differ in a situation, a DOF or a value. -/
def pairMode (isL : String → Bool) (fixed : Bool) (a : String) (ca : Conditions)
    (b : String) (cb : Conditions) : Option CompareMode :=
  if isL a && isL b then none
  else if ca.situations != cb.situations ||
      withoutKind ca.points != withoutKind cb.points then none
  else if ca.points != cb.points then some .convention
  else if fixed || !ca.points.isEmpty then some .test
  else some .inspect

/-- Every pair `i < j` of the records, in order, with its mode. -/
def comparePairs (isL : String → Bool) (fixed : Bool) :
    List (String × Conditions) → List (String × String × CompareMode)
  | [] => []
  | (a, ca) :: rest =>
    rest.filterMap (fun (b, cb) => (pairMode isL fixed a ca b cb).map fun m => (a, b, m)) ++
      comparePairs isL fixed rest

/-- A value free of π is written as before: the twelve-digit form of the exact rational. -/
theorem pointValue_of_pi_zero {x : Exact} (h : x.pi = 0) :
    pointValue x = Decimal.canon (Canonical.ratioText (x.coef < 0) x.coef.num.natAbs x.coef.den) := by
  simp [pointValue, h]

/-- No pair of two L records is ever compared (SR3: never L-L). -/
theorem comparePairs_not_both_L (isL : String → Bool) (fixed : Bool) :
    ∀ (cs : List (String × Conditions)) {a b : String} {m : CompareMode},
      (a, b, m) ∈ comparePairs isL fixed cs → ¬ (isL a = true ∧ isL b = true)
  | [], _, _, _, h => by simp [comparePairs] at h
  | (x, cx) :: rest, a, b, m, h => by
    simp only [comparePairs, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨y, cy⟩, _, m', hm, he⟩ | h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      intro ⟨ha, hb⟩
      simp [pairMode, ha, hb] at hm
    · exact comparePairs_not_both_L isL fixed rest h

/-- v1's `comparison_set` (9.2): the pairs SR3 compares among the standing RESULTs of the
QUANTITY (M, and L carrying a VALUE; never two L records) whose CONDITIONS are equal, each
with its mode. Refused: REC-39, REC-50, REC-74. -/
def comparisonSet (records words tfk quantity : Canonical.Value) :
    Answer (List (String × String × CompareMode)) :=
  match scopeOf records words tfk quantity, quantity with
  | .refused r, _ => .refused r
  | .owed w, _ => .owed w
  | .ok (keyed, ws, fixed), q =>
    let q := match q with | .str s => s | _ => ""
    let ids := membersOf keyed ws q true
    match conditionsAll keyed ids with
    | .refused r => .refused r
    | .owed w => .owed w
    | .ok cond =>
      .ok (comparePairs (regimeL keyed) fixed cond)

/-- SR8's mode for a group: tested, or listed for inspection. -/
inductive GroupMode where
  | test
  | inspect
  deriving DecidableEq, Repr, Inhabited

/-- v1's word for the mode. -/
def GroupMode.toV1 : GroupMode → String
  | .test => "TEST"
  | .inspect => "INSPECT"

/-- Records into groups of equal CONDITIONS, in order of each group's first record. -/
def groupBy : List (String × Conditions) → List (Conditions × List String) →
    List (Conditions × List String)
  | [], gs => gs
  | (rid, c) :: rest, gs =>
    if gs.any (·.1 == c) then
      groupBy rest (gs.map fun g => if g.1 == c then (g.1, g.2 ++ [rid]) else g)
    else groupBy rest (gs ++ [(c, [rid])])

/-- v1's `sr8_groups` (9.3): the standing M RESULTs of the QUANTITY grouped by equal
CONDITIONS (a convention splits a group), each group's records in code point order and
the groups in order of their first; TEST when the entry's DOF is FIXed or the group's
points are not empty, INSPECT otherwise. Refused: REC-39, REC-50, REC-74. -/
def sr8Groups (records words tfk quantity : Canonical.Value) :
    Answer (List (GroupMode × List String)) :=
  match scopeOf records words tfk quantity, quantity with
  | .refused r, _ => .refused r
  | .owed w, _ => .owed w
  | .ok (keyed, ws, fixed), q =>
    let q := match q with | .str s => s | _ => ""
    match conditionsAll keyed (membersOf keyed ws q false) with
    | .refused r => .refused r
    | .owed w => .owed w
    | .ok cond =>
      .ok ((groupBy cond []).map fun (c, ids) =>
        (if fixed || !c.points.isEmpty then .test else .inspect, ids))

/-- The pairs of an answer built from `comparePairs` are never two L records. -/
theorem comparePairs_answer {isL : String → Bool} {fixed : Bool}
    {x : Answer (List (String × Conditions))} {ps : List (String × String × CompareMode)}
    (h : (match x with
      | .refused r => .refused r
      | .owed w => .owed w
      | .ok cond => .ok (comparePairs isL fixed cond)) = Answer.ok ps) :
    ∀ {a b : String} {m : CompareMode}, (a, b, m) ∈ ps → ¬ (isL a = true ∧ isL b = true) := by
  cases x with
  | ok cond =>
    simp only [Answer.ok.injEq] at h
    subst h
    exact fun hm => comparePairs_not_both_L _ _ _ hm
  | refused r => simp at h
  | owed w => simp at h

/-- A refusal is never a result. -/
theorem refuse_ne_ok {α : Type} {code msg : String} {a : α} :
    (refuse code msg : Answer α) ≠ .ok a := by
  simp [refuse]

/-- REC-50 is never a result. -/
theorem refuseBad_ne_ok {α : Type} {arg what : String} {v : Canonical.Value} {a : α} :
    (refuseBad arg v what : Answer α) ≠ .ok a := by
  unfold refuseBad
  split
  · exact refuse_ne_ok
  · simp

/-- When `_cscope` answers, its keyed register is the register's own (`keyedOf`). -/
theorem scopeOf_keyed {records words tfk quantity : Canonical.Value}
    {k : List (String × Rec)} {w : List (String × String)} {f : Bool}
    (h : scopeOf records words tfk quantity = .ok (k, w, f)) : keyedOf records = some k := by
  unfold scopeOf at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | exact absurd h refuseBad_ne_ok
    | exact absurd h refuse_ne_ok
    | (simp at h; done)
    | (simp only [Answer.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -, -⟩ := h
       assumption)

/-- `comparison_set` never pairs two L records of the register, on any input (SR3: an
L-L contradiction is the derivation's, never a comparison). -/
theorem comparisonSet_not_both_L {records words tfk quantity : Canonical.Value}
    {keyed : List (String × Rec)} (hk : keyedOf records = some keyed)
    {ps : List (String × String × CompareMode)}
    (h : comparisonSet records words tfk quantity = .ok ps) :
    ∀ {a b : String} {m : CompareMode}, (a, b, m) ∈ ps →
      ¬ (regimeL keyed a = true ∧ regimeL keyed b = true) := by
  unfold comparisonSet at h
  split at h
  all_goals first
    | contradiction
    | (rename_i hs
       have := scopeOf_keyed hs
       rw [hk, Option.some.injEq] at this
       subst this
       intro a b m hm
       exact comparePairs_answer h hm)

/-- The QUANTITY is read first: one that is not an identifier string is refused whatever
the Research Assembly. -/
theorem sr3ScopeRaw_quantity {tfk quantity : Zone.Value}
    (h : ∀ s, quantity = .str s → Zone.isIdent s = false) :
    sr3ScopeRaw tfk quantity = .error "QUANTITY is not an identifier" := by
  unfold sr3ScopeRaw
  cases quantity with
  | str s => simp [h s rfl]; rfl
  | _ => rfl

/-! ## v1's result lists, as canonical JSON writes them -/

/-- A refusal as tpc_record wrote it: `["REFUSED", [[code, field, message]]]`. -/
def Refusal.toValue (r : Refusal) : Canonical.Value :=
  .arr [.str "REFUSED", .arr [.arr [.str r.code, .str r.fieldName, .str r.message]]]

/-- An answer as v1 wrote it, `["OK", result]` or the refusal; `none` when owed. -/
def Answer.toValue {α : Type} (f : α → Canonical.Value) : Answer α → Option Canonical.Value
  | .ok a => some (.arr [.str "OK", f a])
  | .refused r => some r.toValue
  | .owed _ => none

/-- Strings as a list value. -/
def strs (xs : List String) : Canonical.Value := .arr (xs.map .str)

/-- CONDITIONS as v1 wrote them: `[situations, [[DOF, value, KIND], ...]]`. -/
def Conditions.toValue (c : Conditions) : Canonical.Value :=
  .arr [strs c.situations, .arr (c.points.map fun p => strs [p.dof, p.value, p.kind])]

/-- The pairs as v1 wrote them: `[[id1, id2, mode], ...]`. -/
def pairsValue (ps : List (String × String × CompareMode)) : Canonical.Value :=
  .arr (ps.map fun (a, b, m) => strs [a, b, m.toV1])

/-- The groups as v1 wrote them: `[[mode, [ids]], ...]`. -/
def groupsValue (gs : List (GroupMode × List String)) : Canonical.Value :=
  .arr (gs.map fun (m, ids) => .arr [.str m.toV1, strs ids])

end Principia.Strike
