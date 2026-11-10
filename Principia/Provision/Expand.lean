import Principia.Provision.Text
import Principia.Provision.Preimage
import Principia.Eom

/-!
# Binding and expansion

v1's `module_bind` and `module_expand` (tpm_module_spec 0.2.0 6.3, 6.4; TPS 5.22.7). A claim
names a Provision's ID, VERSION and digest, binds each of its slots to names of the draft's
Starting Set of the slot's kind and DIMENSION, gives each AUTHOR parameter a value (or `{}`,
symbolic) and answers the questions raised. The expansion writes the Provision's entries
into the Starting Set and composes its terms into laws the Starting Set already has:

* a CONSTANT for each parameter, its value declared, overridden, the author's, or symbolic;
  an ASSUMPTION and a BOUNDARY for each of the text's, every `{SLOT}` filled with its names;
* each TERM goes into the one law the structure check's MAP names as the equation of motion
  of the bound DOF, which carries ROLE `EOM(<DOF>)` and has exactly one side of the
  equation-of-motion shape: the term is added on the other side, with its sign, and the
  law's STATEMENT gains `; with <LABEL>: <term>`;
* a term aimed at a FIXED DOF is dropped where the answer to `FIXED:<DOF>` is YES, and one
  ASSUMPTION states the balancing constraint force; NO is refused;
* terms are composed in ID order, then term order, then name order, whatever the order of
  selection; an entry two Provisions write identically is written once, written differently
  or named as an entry of the author's own it is refused.

The structure check is the Calculator's (`Principia.Eom`), T1 the zones'
(`Principia.StartingSet`), the forms the declared forms' (`Principia.Form`).
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-! ## Claims and texts (5.1, 5.2) -/

/-- A claim: one Provision chosen for a draft, with its binding, values and answers. -/
structure Claim where
  id : String
  version : String
  digest : String
  bind : Entry
  values : Entry
  answers : Entry
  deriving Repr, Inhabited

/-- `ID VERSION`. -/
def Claim.cv (c : Claim) : String := c.id ++ " " ++ c.version

/-- The fields of a claim. -/
def claimFields : List String := ["ID", "VERSION", "DIGEST", "BIND", "VALUES", "ANSWERS"]

/-- v1's `_fields` as a problem: the first unknown field (in code point order), then the
first required one missing, each message a function of the tag. -/
def fieldsProblem (o : Entry) (req : List String) (opt : List String := []) : Option (String → String) :=
  match (keysOf o).find? (fun k => !(req.contains k || opt.contains k)) with
  | some k => some fun tag => tag ++ ": unknown field " ++ k
  | none => (req.find? (fun f => !has o f)).map fun f tag => tag ++ ": missing field " ++ f

/-- A field holding a string that passes a test. -/
def strField (c : Entry) (f : String) (p : String → Bool) : Bool :=
  match get? c f with
  | some (.str s) => p s
  | _ => false

/-- A field holding an object whose every member's value passes a test. -/
def objField (c : Entry) (f : String) (p : Value → Bool) : Bool :=
  match get? c f with
  | some (.obj o) => o.all fun (_, x) => p x
  | _ => false

/-- The first problem of one claim, its message a function of the claim's tag (v1's checks
of 5.1, in v1's order), or none. -/
def claimProblem : Value → Option (String → String)
  | .obj c =>
    match fieldsProblem c claimFields with
    | some p => some p
    | none =>
      if !strField c "ID" isProvisionId then some (· ++ ": ID is not a module ID")
      else if !strField c "VERSION" isVersion then some (· ++ ": VERSION is not a version")
      else if !strField c "DIGEST" isDigest then some (· ++ ": DIGEST is not a digest")
      else if !objField c "BIND" (fun x => (strList? x).isSome) then some (· ++ ": field BIND has the wrong type")
      else if !objField c "VALUES" (fun | .obj _ => true | _ => false) then
        some (· ++ ": field VALUES has the wrong type")
      else if !objField c "ANSWERS" (fun | .str _ => true | _ => false) then
        some (· ++ ": field ANSWERS has the wrong type")
      else none
  | _ => some (· ++ ": not an object")

/-- An object field, or empty. -/
def objOf (c : Entry) (f : String) : Entry :=
  match get? c f with
  | some (.obj o) => o
  | _ => []

/-- A claim's fields, once `claimProblem` has found none. -/
def claimValue : Value → Claim
  | .obj c => ⟨(getStr? c "ID").getD "", (getStr? c "VERSION").getD "", (getStr? c "DIGEST").getD "",
      objOf c "BIND", objOf c "VALUES", objOf c "ANSWERS"⟩
  | _ => default

/-- One claim, at its 1-based place in the list. -/
def readClaim (i : Nat) (cv : Value) : Run Claim :=
  match claimProblem cv with
  | some p => refuse (p s!"CLAIM {i}")
  | none => pure (claimValue cv)

/-- The claims from the `i`-th on. -/
def readClaimList : Nat → List Value → Run (List Claim)
  | _, [] => .ok []
  | i, c :: cs =>
    match readClaim i c with
    | .error e => .error e
    | .ok x =>
      match readClaimList (i + 1) cs with
      | .error e => .error e
      | .ok rest => .ok (x :: rest)

/-- Claims in code point order of their IDs (stable). -/
def sortClaims (cs : List Claim) : List Claim := cs.mergeSort fun a b => decide (a.id ≤ b.id)

/-- v1's `_claims`: each claim read, no ID twice, then in ID order. -/
def readClaims (claims : Value) : Run (List Claim) :=
  match claims with
  | .arr xs =>
    match readClaimList 1 xs with
    | .error e => .error e
    | .ok out =>
      match leastDup (out.map (·.id)) with
      | some d => .error (.refused ("CLAIMS: duplicate module " ++ d))
      | none => .ok (sortClaims out)
  | _ => .error (.refused "CLAIMS: not a list")

/-- The text of an (ID, VERSION). -/
def textOf? (texts : List Provision) (id version : String) : Option Provision :=
  texts.find? fun M => M.id == id && M.version == version

/-- The texts given, as the expansion reads them: the text of an (ID, VERSION), if given. -/
abbrev Texts := String → String → Option Provision

/-- Pairs in code point order. -/
def pairLe (a b : String × String) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- v1's `_modules`: every text read, none twice. -/
def readTexts (textsV : Value) : Run (List Provision) := do
  let some ts := strList? textsV | refuse "MODULES: not a list of texts"
  let mut out : List Provision := []
  let mut i := 0
  for t in ts do
    i := i + 1
    match parseText (.str t) with
    | .ok M => out := out ++ [M]
    | .error (.refused m) => refuse (s!"MODULES {i}: " ++ m)
    | .error (.owed w) => owe w
  let pairs := (out.map fun M => (M.id, M.version)).mergeSort pairLe
  let rec dup : List (String × String) → Option (String × String)
    | a :: b :: r => if a == b then some a else dup (b :: r)
    | _ => none
  if let some (id, v) := dup pairs then refuse ("MODULES: duplicate text of " ++ id ++ " " ++ v)
  pure out

/-- v1's `_claim_texts`: each claim has its text, and its DIGEST is the text's. -/
def claimTexts (D : DigestHook) (cls : List Claim) (find : Texts) : Run Unit := do
  for c in cls do
    let some M := find c.id c.version | refuse ("CLAIM " ++ c.cv ++ ": no module text")
    if c.digest != (← M.digest D) then refuse ("CLAIM " ++ c.cv ++ ": DIGEST does not match the module text")

/-- Either one's EXCLUDES matches the other's ID (TPS 5.22.3). -/
def excludesPair (a b : Provision) : Bool :=
  a.excludes.any (idMatches · b.id) || b.excludes.any (idMatches · a.id)

/-- v1's `_excludes`: no two claims exclude each other. -/
def checkExcludes (cls : List Claim) (find : Texts) : Run Unit := do
  let ms := cls.filterMap fun c => find c.id c.version
  let rec go : List Provision → Run Unit
    | [] => pure ()
    | a :: rest => do
      for b in rest do
        if excludesPair a b then
          refuse ("CLAIMS: " ++ a.cv ++ " and " ++ b.cv ++ " exclude each other (EXCLUDES)")
      go rest
  go ms

/-! ## The binding (6.3) -/

/-- A parameter's row: its name, how it is supplied (DECLARED, OVERRIDDEN, AUTHOR, SYMBOLIC)
and its value, unit and uncertainty, where given. -/
structure ParamRow where
  name : String
  supply : String
  value : Option String
  unit : Option String
  uncertainty : Option String
  deriving DecidableEq, Repr, Inhabited

/-- The entries of a kind of the Starting Set that are objects. -/
def tpkEntries (tpk : Value) (kind : String) : List Entry :=
  match tpk with
  | .obj z => kindEntries z kind
  | _ => []

/-- v1's `_bind`: each slot bound to names of its kind and DIMENSION, no name in two slots;
each parameter's row. -/
def bindRows (M : Provision) (tpk : Value) (bind values : Value) :
    Run (List (String × List String) × List ParamRow) := do
  let .obj b := bind | refuse "BIND: not an object"
  for k in keysOf b do
    unless M.slots.any (·.slot == k) do refuse ("BIND: unknown slot " ++ k)
  for s in M.slots do
    unless has b s.slot do refuse ("BIND: slot " ++ s.slot ++ " is not bound")
  let mut bound : List (String × List String) := []
  for s in M.slots do
    let sl := s.slot
    let some names := strList? (field b sl) | refuse ("BIND: slot " ++ sl ++ " has the wrong type")
    unless s.min ≤ names.length && names.length ≤ s.max do
      refuse s!"BIND: slot {sl} takes from {s.min} to {s.max} names, not {names.length}"
    unless strictlySorted names do
      refuse ("BIND: slot " ++ sl ++ ": the names are not in code point order without repeats")
    let entries := tpkEntries tpk s.entryKind
    for n in names do
      let some e := entries.reverse.find? (getStr? · "NAME" == some n)
        | refuse ("BIND: slot " ++ sl ++ ": " ++ n ++ " is not a " ++ s.entryKind ++ " of the TPK")
      let d := (getStr? e "DIMENSION").bind Dimension.normalize
      if d != some s.dim then
        refuse ("BIND: slot " ++ sl ++ ": " ++ n ++ " has dimension " ++ d.getD "None" ++ ", not " ++ s.dim)
    bound := bound ++ [(sl, names)]
  let allNames := bound.flatMap (·.2)
  let two := sortStrs (allNames.eraseDups.filter fun n => (bound.filter (·.2.contains n)).length > 1)
  if let n :: _ := two then
    let where_ := (bound.filter (·.2.contains n)).map (·.1)
    refuse ("BIND: " ++ n ++ " is bound to two slots, " ++ where_.getD 0 "" ++ " and " ++ where_.getD 1 "")
  let .obj vs := values | refuse "VALUES: not an object"
  for k in keysOf vs do
    unless M.params.any (·.name == k) do refuse ("VALUES: unknown parameter " ++ k)
  let mut rows : List ParamRow := []
  for p in M.params do
    let n := p.name
    let tag := "VALUES: " ++ n
    if p.supply == "DECLARED" then
      match get? vs n with
      | none => rows := rows ++ [⟨n, "DECLARED", p.value, p.unit, p.uncertainty⟩]
      | some x =>
        if p.overridable == some "NO" then refuse (tag ++ " is not OVERRIDABLE")
        valueObject tag x p.dim
        let .obj o := x | refuse (tag ++ " has the wrong type")
        if o.isEmpty then refuse (tag ++ ": an override needs VALUE and UNIT")
        rows := rows ++ [⟨n, "OVERRIDDEN", getStr? o "VALUE", getStr? o "UNIT", getStr? o "UNCERTAINTY"⟩]
    else
      match get? vs n with
      | none => refuse (tag ++ " is author supplied: give a value, or {} for a symbolic constant")
      | some (.obj []) => rows := rows ++ [⟨n, "SYMBOLIC", none, none, none⟩]
      | some x =>
        valueObject tag x p.dim
        let .obj o := x | refuse (tag ++ " has the wrong type")
        rows := rows ++ [⟨n, "AUTHOR", getStr? o "VALUE", getStr? o "UNIT", getStr? o "UNCERTAINTY"⟩]
  pure (bound, rows)

/-- What `module_bind` answers: each slot's names and each parameter's row. -/
structure Bound where
  slots : List (String × List String)
  params : List ParamRow
  deriving DecidableEq, Repr

/-- v1's `_t1` over a draft's Starting Set: its first problem, or none. -/
def baseT1 (tpk : Value) : Run Unit := do
  if let some p ← t1First tpk then refuse ("BASE: the TPK fails T1: " ++ p)

/-- v1's `module_bind`. -/
def bind (tpk text bindV values : Value) : Answer Bound :=
  finish do
    let M ← parseText text
    baseT1 tpk
    let (s, r) ← bindRows M tpk bindV values
    pure ⟨s, r⟩

/-! ## The expansion (6.4) -/

/-- An expression without its enclosing parentheses. -/
def strip (e : Form.Expr) : Form.Expr := e.strip

/-- v1's `_factors`: a side's factors above and below the line. -/
def factors : Form.Expr → List Form.Expr × List Form.Expr
  | .paren e | .neg e => factors e
  | .bin .mul l r => let (a, b) := factors l; let (c, d) := factors r; (a ++ c, b ++ d)
  | .bin .div l r => let (a, b) := factors l; (a, b ++ [r])
  | e => ([e], [])

/-- Whether a factor is a D. -/
def isDeriv : Form.Expr → Bool
  | .deriv _ _ _ => true
  | _ => false

/-- v1's `_shaped`: the equation-of-motion shape of a side for `q` (6.4 S7 b): exactly one D
above the line, a derivative of `q`, and every other factor of constants only. -/
def shaped (side : Form.Expr) (q : String) (consts : List String) : Bool :=
  let (num, den) := factors side
  match num.filter isDeriv with
  | [.deriv x _ _] =>
    x == q && ((num.filter (!isDeriv ·)) ++ den).all fun f => (identsOf f.names).all consts.contains
  | _ => false

/-- v1's `_expand_template` (S9): the template with its scalar slots renamed and its sums
replaced, each by the parenthesized sum of its EACH over the slot's names. -/
def templateMap (M : Provision) (rename : List (String × String)) (members : List (String × List String)) :
    String → Option Form.Expr := fun x =>
  match rename.lookup x with
  | some n => some (.ident n)
  | none =>
    match M.sums.find? (·.name == x) with
    | some s =>
      let each := strip s.each
      let ts := ((members.lookup s.over).getD []).map fun q =>
        exprSubst (fun y => if y == s.over then some (.ident q) else none) each
      match ts with
      | t :: rest => some (.paren (rest.foldl (fun acc u => .bin .add acc u) t))
      | [] => none
    | none => none

/-- v1's `_fill`: each `{SLOT}` replaced by its names joined with `, `. -/
def fill (s : String) (members : List (String × List String)) : String :=
  let rec go : Nat → List Char → List Char
    | 0, _ => []
    | _ + 1, [] => []
    | f + 1, '{' :: rest =>
      match rest.findIdx? (· == '}') with
      | some j =>
        let x := String.ofList (rest.take j)
        (", ".intercalate ((members.lookup x).getD [])).toList ++ go f (rest.drop (j + 1))
      | none => '{' :: go f rest
    | f + 1, c :: rest => c :: go f rest
  String.ofList (go (s.length + 1) s.toList)

/-- Replace a field of an entry in place, or add it at the end. -/
def setField (e : Entry) (f : String) (v : Value) : Entry :=
  if has e f then e.map fun (k, x) => if k == f then (k, v) else (k, x) else e ++ [(f, v)]

/-- A term received by a law: its sign, its text, its text wrapped for a sum, its label. -/
structure Received where
  sign : String
  text : String
  wrapped : String
  label : String
  deriving Repr, Inhabited

/-- The expansion: the expanded draft, the laws composed, the entries written with their
sources, and the terms dropped on FIXED DOFs. -/
structure Expansion where
  draft : Entry
  tpk : Value
  composed : List (String × String)
  emitted : List (String × String × List String)
  dropped : List (String × String)
  deriving Repr, Inhabited

/-- The structure check's MAP of a Starting Set: each DOF's label and law. -/
def eomMapOf (tpk : Value) : Run (List (String × String × String)) :=
  match Eom.readTfk Eom.FormHook.calculator (.obj [("TPK", tpk)]) with
  | .error (.refused r) => refuse ("EXPAND: the structure check refuses the TPK: " ++ r)
  | .error (.owed why) => owe (.exact why)
  | .ok K =>
    match Eom.analyse K K.laws with
    | some (R, _, _, _) => pure R.map
    | none => refuse "EXPAND: the structure check refuses the TPK: internal: no assignment in a part that has one"

/-- The draft checked: an object of the three zones holding a Starting Set that passes T1. -/
def checkDraft (draft : Value) : Run (Entry × Value) := do
  let .obj d := draft | refuse "DRAFT: not an object"
  for k in keysOf d do
    unless ["TPK", "TrM", "TMS"].contains k do refuse ("DRAFT: unknown zone " ++ k)
  let some tpk := get? d "TPK" | refuse "DRAFT: missing zone TPK"
  baseT1 tpk
  pure (d, tpk)

/-- The questions a claim's answers may answer, and its checks (6.4 S7 a). -/
def checkAnswerWords (cv : String) (ans : Entry) : Run Unit := do
  for k in keysOf ans do
    unless isAnswerKey k do refuse ("CLAIM " ++ cv ++ ": answer " ++ k ++ " is not a question")
    match get? ans k with
    | some (.str "YES") | some (.str "NO") => pure ()
    | _ => refuse ("CLAIM " ++ cv ++ ": answer " ++ k ++ " is not YES or NO")

/-- The INTERACTS_WITH questions a claim raises: those whose WITH matches another claim. -/
def raisedQuestions (M : Provision) (c : Claim) (ids : List String) : List Question :=
  M.questions.filter fun qd => ids.any fun o => o != c.id && idMatches qd.withPattern o

/-- The expansion after the draft, the texts and the claims are read (v1's `_expand` from
`_claim_texts` on). -/
def expandWith (D : DigestHook) (d : Entry) (tpk : Value) (cls : List Claim) (find : Texts) :
    Run Expansion := do
  claimTexts D cls find
  checkExcludes cls find
  let pairs ← cls.mapM fun c => do
    let some M := find c.id c.version | refuse ("CLAIM " ++ c.cv ++ ": no module text")
    match bindRows M tpk (.obj c.bind) (.obj c.values) with
    | .ok br => pure (c, M, br)
    | .error (.refused m) => refuse ("CLAIM " ++ c.cv ++ ": " ++ m)
    | .error (.owed w) => owe w
  let mp ← if pairs.any (fun (_, M, _) => !M.terms.isEmpty) then eomMapOf tpk else pure []
  let laws := tpkEntries tpk "LAW"
  let consts := (tpkEntries tpk "CONSTANT").filterMap (getStr? · "NAME")
  let ids := cls.map (·.id)
  -- S7: the terms placed, the questions raised and answered
  let mut receiving : List (String × List Received) := []
  let mut dside : List (String × Nat) := []
  let mut perDropped : List (List String) := []
  let mut droppedAll : List (String × String) := []
  for (c, M, (bound, _)) in pairs do
    let cv := c.cv
    let ans := c.answers
    checkAnswerWords cv ans
    let mut raised : List String := []
    let mut dropped : List String := []
    let mut i := 0
    for t in M.terms do
      i := i + 1
      for q in (bound.lookup t.target).getD [] do
        let (label, lname) := ((mp.find? (·.1 == q)).map (·.2)).getD ("NO LAW", "")
        let pre := "CLAIM " ++ cv ++ s!": TERM {i}: "
        if label == "DETERMINED" then
          let L := ((laws.reverse.find? (getStr? · "NAME" == some lname))).getD []
          let role := get? L "ROLE"
          let roleOk := match role with
            | some (.str r) => r == "EOM(" ++ q ++ ")"
            | _ => false
          if !roleOk then
            let roleText := match role with
              | some (.str r) => r
              | _ => "None"
            refuse (pre ++ q ++ "'s equation of motion LAW " ++ lname ++ " has ROLE " ++ roleText ++
              ", not EOM(" ++ q ++ ")")
          let sides : List Bool ← match getStr? L "EQUATION" with
            | some eq =>
              match Form.formTree eq .equation with
              | .ok (.eq l r) => pure [shaped l q consts, shaped r q consts]
              | .owed (.exact w) => owe (.exact w)
              | _ => pure [false, false]
            | none => pure [false, false]
          if (sides.filter id).length != 1 then
            refuse (pre ++ "LAW " ++ lname ++ " has no single side of the equation-of-motion shape for " ++ q)
          dside := (dside.filter (·.1 != lname)) ++ [(lname, if sides.getD 0 false then 0 else 1)]
          let rename := (M.slots.filter (·.max == 1)).filterMap (fun s =>
            ((bound.lookup s.slot).bind List.head?).map fun n => (s.slot, n))
          let rename := (rename.filter (·.1 != t.target)) ++ [(t.target, q)]
          let tree := exprSubst (templateMap M rename bound) t.expr
          let e := (Form.Tree.expr tree).print
          let w := match strip tree with
            | .bin .add _ _ | .bin .sub _ _ => "(" ++ e ++ ")"
            | _ => e
          let prev := (receiving.lookup lname).getD []
          receiving := (receiving.filter (·.1 != lname)) ++ [(lname, prev ++ [⟨t.sign, e, w, t.label⟩])]
        else if label == "FIXED" then
          let key := "FIXED:" ++ q
          raised := raised ++ [key]
          match get? ans key with
          | none =>
            refuse ("CLAIM " ++ cv ++ ": question FIXED:" ++ q ++ " is not answered (" ++ q ++
              " is FIXED: does a constraint force balance the forces this module adds along it?)")
          | some (.str "NO") =>
            refuse (pre ++ q ++ " is FIXED and the answer to FIXED:" ++ q ++ " is NO: a force " ++
              "along a fixed DOF with no constraint force balancing it contradicts the constraint")
          | _ => pure ()
          unless dropped.contains q do dropped := dropped ++ [q]
        else if label == "REMOVED" then
          refuse (pre ++ q ++ " is REMOVED; no module is bound to a removed DOF")
        else if label == "INPUT" then
          refuse (pre ++ q ++ " is an INPUT DOF and has no equation of motion")
        else if label == "INDEPENDENT" then
          refuse (pre ++ q ++ " is the independent variable")
        else if label == "UNDER" || label == "OVER" then
          refuse (pre ++ q ++ "'s equation of motion is not determined (" ++ label ++
            "); resolve it, then bind the module")
        else
          refuse (pre ++ q ++ " has no equation of motion (" ++ label ++ "); write it, then bind the module")
    for qd in raisedQuestions M c ids do
      raised := raised ++ [qd.qid]
      unless has ans qd.qid do refuse ("CLAIM " ++ cv ++ ": question " ++ qd.qid ++ " is not answered")
    for k in keysOf ans do
      unless raised.contains k do refuse ("CLAIM " ++ cv ++ ": answer " ++ k ++ " answers no question raised")
    perDropped := perDropped ++ [dropped]
    droppedAll := droppedAll ++ dropped.map (cv, ·)
  -- S8: the entries written
  let baseNames := StartingSet.kinds.flatMap fun kind => (tpkEntries tpk kind).filterMap (getStr? · "NAME")
  let mut emitted : List (String × Entry × List String) := []
  for ((c, M, (bound, rows)), dropped) in pairs.zip perDropped do
    let cv := c.cv
    let rename := (M.slots.filter (·.max == 1)).filterMap (fun s =>
      ((bound.lookup s.slot).bind List.head?).map fun n => (s.slot, n))
    let mut out : List (String × Entry) := []
    for r in rows do
      let dim := ((M.paramOf? r.name).map (·.dim)).getD ""
      let e : Entry := [("NAME", .str r.name), ("DIMENSION", .str dim)] ++
        ([("VALUE", r.value), ("UNIT", r.unit), ("UNCERTAINTY", r.uncertainty)].filterMap fun (f, x) =>
          x.map fun s => (f, .str s))
      out := out ++ [("CONSTANT", e)]
    for a in M.assumptions do
      let refs := sortedSet (a.refs.flatMap fun x => (bound.lookup x).getD [x])
      out := out ++ [("ASSUMPTION", [("NAME", .str a.name), ("PROPOSITION", .str (fill a.proposition bound)),
        ("REFS", .arr (refs.map .str))])]
    for bd in M.boundaries do
      let tree := predSubst (templateMap M rename bound) bd.condition
      out := out ++ [("BOUNDARY", [("NAME", .str bd.name), ("PREDICATE", .str (fill bd.predicate bound)),
        ("REFS", .arr ((identsOf tree.names).map .str)), ("CONDITION", .str (Form.Tree.pred tree).print)])]
    for q in dropped do
      out := out ++ [("ASSUMPTION", [("NAME", .str ("fixed_" ++ q ++ "_balanced")),
        ("PROPOSITION", .str ("a constraint force along " ++ q ++ " balances every other force along " ++ q)),
        ("REFS", .arr [.str q])])]
    for (kind, e) in out do
      let n := (getStr? e "NAME").getD ""
      if baseNames.contains n then
        refuse ("EXPAND: " ++ cv ++ " emits " ++ kind ++ " " ++ n ++ ", but the TPK already has an entry named " ++ n)
      match emitted.find? (fun (_, e0, _) => getStr? e0 "NAME" == some n) with
      | some (_, e0, src) =>
        let k0 := (emitted.find? (fun (_, e1, _) => getStr? e1 "NAME" == some n)).map (·.1)
        let fs := kindFieldList kind
        if k0 != some kind || Zone.entryList e0 fs != Zone.entryList e fs then
          refuse ("EXPAND: " ++ src.headD "" ++ " and " ++ cv ++ " both emit " ++ n ++ ", differently")
        emitted := emitted.map fun (k1, e1, s1) =>
          if getStr? e1 "NAME" == some n then (k1, e1, s1 ++ [cv]) else (k1, e1, s1)
      | none => emitted := emitted ++ [(kind, e, [cv])]
  -- S10: the laws composed
  let mut composed : List (String × String) := []
  let mut newLaws : List (String × Entry) := []
  for L in laws do
    let some ln := getStr? L "NAME" | continue
    let some terms := receiving.lookup ln | continue
    let canon ← match Form.parseForm ((getStr? L "EQUATION").getD "") .equation with
      | .ok c => pure c
      | .refused r => refuse ("internal: LAW " ++ ln ++ ": " ++ r)
      | .owed (.exact w) => owe (.exact w)
    let sides := canon.splitOn "="
    let ds := (dside.lookup ln).getD 0
    let f := sides.getD (1 - ds) ""
    let force := if f == "0" then
        match terms with
        | t1 :: rest => (if t1.sign == "+" then t1.text else "-" ++ t1.wrapped) ++
            String.join (rest.map fun t => t.sign ++ t.wrapped)
        | [] => f
      else f ++ String.join (terms.map fun t => t.sign ++ t.wrapped)
    let new := if ds == 0 then sides.getD 0 "" ++ "=" ++ force else force ++ "=" ++ sides.getD 1 ""
    let eq ← match Form.parseForm new .equation with
      | .ok c => pure c
      | .refused r => refuse ("EXPAND: LAW " ++ ln ++ ": the composed EQUATION is refused: " ++ r)
      | .owed (.exact w) => owe (.exact w)
    let refs ← match Form.formNames eq .equation with
      | .ok ns => pure ns
      | .refused r => refuse ("internal: LAW " ++ ln ++ ": " ++ r)
      | .owed (.exact w) => owe (.exact w)
    let statement := (getStr? L "STATEMENT").getD "" ++
      String.join (terms.map fun t => "; with " ++ t.label ++ ": " ++ t.sign ++ t.wrapped)
    let L2 := setField (setField (setField L "EQUATION" (.str eq)) "REFS" (.arr (refs.map .str)))
      "STATEMENT" (.str statement)
    newLaws := newLaws ++ [(ln, L2)]
    composed := composed ++ [(ln, eq)]
  -- S11: the result
  let z : Entry := match tpk with
    | .obj z => z
    | _ => []
  let mut outTpk : Entry := z.map fun (k, v) =>
    if k == "LAW" then
      match v with
      | .arr xs => (k, .arr (xs.map fun x => match x with
          | .obj e => match getStr? e "NAME" with
            | some n => match newLaws.lookup n with
              | some L2 => .obj L2
              | none => x
            | none => x
          | _ => x))
      | _ => (k, v)
    else (k, v)
  for kind in StartingSet.kinds do
    let add := (emitted.filter (·.1 == kind)).map fun (_, e, _) => Value.obj e
    unless add.isEmpty do
      let cur := match get? outTpk kind with
        | some (.arr xs) => xs
        | _ => []
      outTpk := setField outTpk kind (.arr (cur ++ add))
  let xd := setField d "TPK" (.obj outTpk)
  pure { draft := xd, tpk := .obj outTpk, composed,
         emitted := emitted.map (fun (k, e, src) => (k, (getStr? e "NAME").getD "", src)),
         dropped := droppedAll }

/-- v1's `_expand`: the draft, the texts and the claims read, then expanded. -/
def expandRun (D : DigestHook) (draft claims textsV : Value) : Run Expansion := do
  let (d, tpk) ← checkDraft draft
  let texts ← readTexts textsV
  let cls ← readClaims claims
  expandWith D d tpk cls (textOf? texts)

/-- What `module_expand` answers (6.4 RENDER): D(TPK) of the expanded Starting Set, the laws
composed, the entries written with their sources, the terms dropped. -/
structure Rendered where
  dTpk : String
  composed : List (String × String)
  emitted : List (String × String × List String)
  dropped : List (String × String)
  deriving DecidableEq, Repr

/-- v1's `module_expand`, as v1's corpus renders it. -/
def expand (D : DigestHook) (draft claims textsV : Value) : Answer Rendered :=
  finish do
    let x ← expandRun D draft claims textsV
    pure ⟨← dTpk D x.tpk, x.composed, x.emitted, x.dropped⟩

end Principia.Provision
