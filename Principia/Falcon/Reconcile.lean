import Principia.Digest
import Principia.Falcon.Canon

/-!
# The falcon reconciliation

v1's `tpc_falcon` 0.2.0: `falcon_reconcile(outputs, quotes, schema)`, the
comparison of a falcon's outputs item by item (RL1 to RL7 in v1's text): each output
validated against the FALCON KIND's output schema (a MALFORMED one is reissued, never a
disagreement); then each MECHANICAL item AGREED, settled by a QUOTE that alone passes,
waiting for a THIRD assignee, settled by a strict MAJORITY, or UNRESOLVED; INSPECTION items
shown, never matched; a row carried by one output SINGLE; and the disposition.

Values are compared in their canonical forms (`falconCanon`), so a text value is in NFC
first, at Unicode 15.1.0. A row's key is the netstring of its key
columns' canonical values (`Principia.Digest.preimage`, v1's `_netstring`, not a digest).

`checkSchema` is v1's `_check_schema`, which the output schema's canonical text
(`Principia.Falcon.Schema`) also applies.
-/

namespace Principia.Falcon.Reconcile

open Principia.Canonical (Value)
open Principia.Falcon

/-- The schema's field specs, when it holds a list. -/
def fieldSpecs (schema : Value) : List Members :=
  match schema with
  | .obj ms => match field? ms "fields" with
    | some (.arr fs) => fs.filterMap members?
    | _ => []
  | _ => []

/-- v1's `_check_schema`: true when it raises nothing. -/
def checkSchema (schema : Value) : Bool :=
  match schema with
  | .obj ms =>
    keysAre ms ["class", "narrow", "fields"] ["confidential"] &&
      (match field? ms "class" with
        | some (.str "FINDINGS") | some (.str "PATCH") | some (.str "SURVEY") => true
        | _ => false) &&
      (match field? ms "narrow" with
        | some (.bool _) => true
        | _ => false) &&
      (match field? ms "confidential" with
        | none | some (.bool _) => true
        | _ => false) &&
      (match field? ms "fields" with
        | some (.arr fs@(_ :: _)) =>
          fs.all (specOk · true) &&
            distinct (fs.filterMap fun f => match f with
              | .obj fm => strField? fm "name"
              | _ => none)
        | _ => false)
  | _ => false

/-- A member that is `true`. -/
def isTrue : Option Value → Bool
  | some (.bool true) => true
  | _ => false

/-- A member that is the string `s`. -/
def isStr (s : String) : Option Value → Bool
  | some (.str t) => t == s
  | _ => false

/-- A field's name. -/
def nameOf (f : Members) : String := (strField? f "name").getD ""

/-- A field's type. -/
def typeOf (f : Members) : String := (strField? f "type").getD ""

/-- A rows field's columns. -/
def columnsOf (f : Members) : List Members :=
  match field? f "columns" with
  | some (.arr cs) => cs.filterMap members?
  | _ => []

/-- A rows field's key columns. -/
def keyOf (f : Members) : List String := (strings? ((field? f "key").getD .null)).getD []

/-- A field's canonical values in one output: one value, or rows by their key. -/
inductive Canon where
  | one (v : String)
  | rows (rs : List (String × List (String × String)))

/-- Why an output is not usable, or its values and its IV count. -/
abbrev Checked := Except String (List (String × Canon) × Nat)

/-- A canonical form, a refusal giving the field's name as the reason. -/
def canonOf (field : String) (v : Value) (spec : Members) : Except Fault (Except String String) :=
  match falconCanon v (.obj spec) with
  | .ok c => .ok (.ok c)
  | .error (.refused _) => .ok (.error field)

/-- One rows field of an output (v1's `_validate`, the rows part). -/
def rowsOf (f : Members) (v : Value) : Except Fault (Except String Canon) := do
  let nm := nameOf f
  match v with
  | .arr rows =>
    let cols := columnsOf f
    let cnames := cols.map nameOf
    let mut acc : List (String × List (String × String)) := []
    for row in rows do
      if !keysAreV row cnames [] then return .error nm
      let rm := (members? row).getD []
      let mut cv : List (String × String) := []
      for c in cols do
        match ← canonOf nm ((field? rm (nameOf c)).getD .null) c with
        | .ok x => cv := cv ++ [(nameOf c, x)]
        | .error r => return .error r
      let kenc := Digest.preimage ((keyOf f).map fun k => (cv.lookup k).getD "")
      if acc.any (·.1 == kenc) then return .error nm
      acc := acc ++ [(kenc, cv)]
    return .ok (.rows acc)
  | _ => return .error nm

/-- v1's `_validate(out, schema)`: `ok (values, iv)` when usable, else the reason. -/
def validate (fields : List Members) (status : String) (result : Value) :
    Except Fault Checked := do
  if status == "OVERDUE" then return .error "OVERDUE"
  match result with
  | .null => return .error "refusal"
  | .obj rm =>
    if !keysAre rm (fields.map nameOf) ["IV"] then return .error "shape"
    let iv ← match field? rm "IV" with
      | none => pure (some 0)
      | some v => pure ((strings? v).map List.length)
    let some iv := iv | return .error "IV"
    let mut vals : List (String × Canon) := []
    for f in fields do
      let v := (field? rm (nameOf f)).getD .null
      if typeOf f != "rows" then
        match ← canonOf (nameOf f) v f with
        | .ok c => vals := vals ++ [(nameOf f, .one c)]
        | .error r => return .error r
      else
        match ← rowsOf f v with
        | .ok c => vals := vals ++ [(nameOf f, c)]
        | .error r => return .error r
    return .ok (vals, iv)
  | _ => return .error "shape"

/-- An item of the comparison: its id, its kind, the value it settles on, its detail, and
the voters' values with their quote outcomes. -/
structure Item where
  id : String
  kind : String
  value : Option String
  detail : String
  votes : List (Nat × String × String)

/-- The reconciliation's result (v1's dict). -/
structure Reconciled where
  outputs : List (String × Option String × Nat)
  reissue : List Nat
  items : List Item
  disposition : String
  single : String

/-- An item's votes: the voters and their canonical values. -/
abbrev Voters := List (Nat × String)

/-- v1's RL3 to RL6 for one item with its spec. -/
def judgeItem (nout : Nat) (quotes : List Members) (iid : String) (spec : Members)
    (voters : Voters) : Item :=
  let quoted := isTrue (field? spec "quote")
  let vq := voters.map fun (i, v) =>
    (i, v, if quoted then
      (match (quotes[i]?.bind (field? · iid)) with
        | some (.str q) => q
        | _ => "UNKNOWN")
      else "-")
  let detail := toString voters.length
  if isStr "INSPECTION" (field? spec "class") then
    { id := iid, kind := "INSPECTION", value := none, detail, votes := vq }
  else
    let distinctVals := (voters.map (·.2)).eraseDups
    let count (v : String) := (voters.filter (·.2 == v)).length
    if distinctVals.length == 1 then
      { id := iid, kind := "AGREED", value := (voters.head?.map (·.2)), detail, votes := [] }
    else
      let passers := ((vq.filter (·.2.2 == "PASS")).map (·.2.1)).eraseDups
      if quoted && passers.length == 1 then
        { id := iid, kind := "QUOTE", value := passers.head?, detail, votes := vq }
      else if nout == 2 then
        { id := iid, kind := "SPLIT", value := none, detail, votes := vq }
      else
        match (distinctVals.mergeSort (· ≤ ·)).find? (fun v => voters.length < 2 * count v) with
        | some w =>
          { id := iid, kind := "MAJORITY", value := some w,
            detail := s!"{count w}/{voters.length}", votes := vq }
        | none => { id := iid, kind := "UNRESOLVED", value := none, detail, votes := vq }

/-- The canonical value of a one-value field in an output. -/
def oneValue (vals : List (String × Canon)) (nm : String) : String :=
  match vals.lookup nm with
  | some (.one v) => v
  | _ => ""

/-- The rows of a rows field in an output. -/
def rowsValue (vals : List (String × Canon)) (nm : String) : List (String × List (String × String)) :=
  match vals.lookup nm with
  | some (.rows rs) => rs
  | _ => []

/-- v1's RL2: the items, fields in schema order, a rows field's rows in key order. -/
def items (fields : List Members) (quotes : List Members) (vals : List (List (String × Canon))) :
    List Item :=
  let nout := vals.length
  let outs := List.range nout
  fields.flatMap fun f =>
    let nm := nameOf f
    if typeOf f != "rows" then
      [judgeItem nout quotes nm f (outs.map fun i => (i, oneValue (vals.getD i []) nm))]
    else
      let keys := ((outs.flatMap fun i => (rowsValue (vals.getD i []) nm).map (·.1)).eraseDups).mergeSort
        (· ≤ ·)
      keys.flatMap fun kenc =>
        let rid := nm ++ "[" ++ kenc ++ "]"
        let carriers := outs.filter fun i => ((rowsValue (vals.getD i []) nm).lookup kenc).isSome
        match carriers with
        | [c] => [{ id := rid, kind := "SINGLE", value := none, detail := toString c, votes := [] }]
        | _ =>
          ((columnsOf f).filter fun c => !(keyOf f).contains (nameOf c)).map fun c =>
            judgeItem nout quotes (rid ++ "." ++ nameOf c) c (carriers.map fun i =>
              (i, ((((rowsValue (vals.getD i []) nm).lookup kenc).getD []).lookup (nameOf c)).getD ""))

/-- An output as v1's check accepts it: account, status, result. -/
def outputOf (v : Value) : Option (String × String × Value) := do
  if !keysAreV v ["account", "status", "result"] [] then none
  let ms ← members? v
  let account ← strField? ms "account"
  if account == "" then none
  let status ← strField? ms "status"
  if status != "RETURNED" && status != "OVERDUE" then none
  let result := (field? ms "result").getD .null
  if status == "OVERDUE" then
    match result with
    | .null => pure ()
    | _ => none
  return (account, status, result)

/-- A quotes entry: an object whose every value is PASS, FAIL or UNKNOWN. -/
def quotesOf (v : Value) : Option Members :=
  match v with
  | .obj ms =>
    if ms.all (fun (_, q) => match q with
        | .str "PASS" | .str "FAIL" | .str "UNKNOWN" => true
        | _ => false) then some ms else none
  | _ => none

/-- v1's `falcon_reconcile(outputs, quotes, schema)`. -/
def falconReconcile (outputs quotes schema : Value) : Result Reconciled := do
  if !checkSchema schema then refuse "schema"
  let fields := fieldSpecs schema
  let some outs := (match outputs with
      | .arr os => if os.length < 2 then none else os.mapM outputOf
      | _ => none) | refuse "outputs"
  if !distinct (outs.map (·.1)) then refuse "outputs"
  let some qs := (match quotes with
      | .arr qs => if qs.length != outs.length then none else qs.mapM quotesOf
      | _ => none) | refuse "quotes"
  let checked ← outs.mapM fun (_, status, result) => validate fields status result
  let outLines := (outs.zip checked).map fun ((a, _), c) => match c with
    | .ok (_, iv) => (a, none, iv)
    | .error r => (a, some r, 0)
  let bad := ((List.range outs.length).zip checked).filterMap fun (i, c) => match c with
    | .error _ => some i
    | .ok _ => none
  let base : Reconciled :=
    { outputs := outLines, reissue := [], items := [], disposition := "", single := "" }
  if !bad.isEmpty then return { base with disposition := "REISSUE", reissue := bad }
  let vals := checked.map fun c => match c with
    | .ok (v, _) => v
    | .error _ => []
  let its := items fields qs vals
  let kinds := its.map (·.kind)
  let sm := (members? schema).getD []
  let conf := isTrue (field? sm "confidential")
  let narrow := isTrue (field? sm "narrow")
  let disp :=
    if kinds.contains "SPLIT" then "THIRD"
    else if kinds.contains "SINGLE" && !narrow && !conf then "NARROW"
    else if isStr "FINDINGS" (field? sm "class") then
      (if conf then "PRIVATE REPORT" else "REPORTED")
    else "AWAITING APPROVAL"
  let single :=
    if !kinds.contains "SINGLE" then "-"
    else if disp == "THIRD" then "wait"
    else if narrow || conf then "mark"
    else "narrow"
  return { base with items := its, disposition := disp, single := single }

/-- v1's `render_reconcile`. -/
def renderReconcile (d : Reconciled) : String :=
  let outs := ((List.range d.outputs.length).zip d.outputs).map fun (i, (a, reason, iv)) =>
    match reason with
    | none => s!"output|{i}|{esc a}|OK|iv={iv}"
    | some "OVERDUE" => s!"output|{i}|{esc a}|OVERDUE"
    | some r => s!"output|{i}|{esc a}|MALFORMED|{r}"
  if d.disposition == "REISSUE" then
    "\n".intercalate (outs ++ ["disposition|REISSUE|" ++ ",".intercalate (d.reissue.map toString)])
  else
    let itemLines := d.items.flatMap fun it =>
      s!"item|{esc it.id}|{it.kind}|{match it.value with | some v => esc v | none => "-"}|{it.detail}" ::
        it.votes.map fun (i, v, q) => s!"value|{esc it.id}|{i}|{esc v}|{q}"
    let tally (k : String) := (d.items.filter (·.kind == k)).length
    let summary := "summary|" ++ "|".intercalate
      (["AGREED", "QUOTE", "MAJORITY", "SPLIT", "UNRESOLVED", "INSPECTION", "SINGLE"].map
        fun k => s!"{k.toLower}={tally k}")
    "\n".intercalate (outs ++ itemLines ++ [summary,
      s!"disposition|{d.disposition}|single={d.single}"])

end Principia.Falcon.Reconcile
