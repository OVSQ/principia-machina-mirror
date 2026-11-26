import Tests.Calculator.Common

/-!
The Calculator's runners of the family `falcon`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The falcons through `pcalc falcon` -/

/-- v1's names of the falcon functions in `falcon_corpus.json` and `falcon_hand.json`
(`run_case`), and the Calculator's: v1's names of the functions themselves. -/
def falconFunctions : List (String × String) :=
  [("canon", "falcon_canon"), ("draw", "falcon_draw"), ("hop", "source_hop"),
   ("qcheck", "quote_check"), ("qmatch", "falcon_quote_match"),
   ("reconcile", "falcon_reconcile"), ("schema_canon", "falcon_schema_canon"),
   ("schema_digest", "falcon_schema_digest"), ("source", "source_match"),
   ("stage", "sponsor_stage"), ("stop", "falcon_stop")]

/-- `falcon_corpus.json` (949 cases) and `falcon_hand.json`: every case's `args` through
`falcon <function>`, each giving v1's text, or v1's word as a refusal's detail; a case of the
corpus that `falcon_corpus.owed.json` lists is answered `OWED` (it lists none). -/
def runFalconCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← (← arr (← field (← readJson "vectors/falcon_corpus.owed.json") "owed")).mapM
    (str · "name")
  for path in ["vectors/falcon_corpus.json", "vectors/falcon_hand.json"] do
    for c in ← v1Cases path do
      let name ← memberStr c "name"
      let expected ← memberStr c "expected"
      let some fn := falconFunctions.lookup (← memberStr c "fn")
        | throw (IO.userError s!"{path} {name}: unknown function")
      let some args := member c "args" | throw (IO.userError s!"{path} {name}: no args")
      let got := respondTo "falcon" fn args
      let ok := if path == "vectors/falcon_corpus.json" && owed.contains name then
          match got with
          | .error r => r.code == .owed
          | .ok _ => false
        else
          match got with
          | .ok (.str text) => text == expected
          | .error r => r.code == .badArgument && "ERROR:" ++ r.detail == expected
          | _ => false
      t ← t.check ok s!"falcon {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `n` copies of a character. -/
def copies (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-- A text field's spec. -/
def textSpec : Value :=
  .obj [("name", .str "a"), ("type", .str "text"), ("class", .str "MECHANICAL")]

/-- A `falcon_canon` request of a text value, its strings holding `n` characters in all. -/
def canonOfTexts (n : Nat) : Value :=
  let base := Falcon.textChars (.obj [("value", .str ""), ("spec", textSpec)])
  .obj [("value", .str (copies (n - base) 'a')), ("spec", textSpec)]

/-- A draw's candidate. -/
def falconCandidate (i : Nat) : Value :=
  .obj [("account", .str s!"a{i}"), ("sponsor", .str s!"s{i}"), ("family", .str "f"),
    ("snapshot", .str "x"), ("tier", .bool false), ("good_standing", .bool true),
    ("sandbox", .bool false), ("over_cap", .bool false), ("window", .int 0),
    ("ontime", .int 0), ("assigned", .int 0)]

/-- A draw of two from `m` candidates, `kept` of them kept and `prior` other accounts. -/
def falconDraw (m kept prior : Nat) : Value :=
  .obj [("candidates", .arr ((List.range m).map falconCandidate)), ("n", .int 2),
    ("state", .obj [("kept", strs ((List.range kept).map fun i => s!"a{i}")),
      ("prior", strs ((List.range prior).map fun i => s!"p{i}")), ("drafted", .int 0),
      ("now", .int 0), ("falcon_wait", .int 1)]),
    ("r", .str "0123456789abcdef0123456789abcdef")]

/-- A text field, MECHANICAL. -/
def textField (name : String) : Value :=
  .obj [("name", .str name), ("type", .str "text"), ("class", .str "MECHANICAL")]

/-- A schema of the fields given. -/
def falconSchema (fields : List Value) : Value :=
  .obj [("class", .str "SURVEY"), ("narrow", .bool false), ("fields", .arr fields)]

/-- A schema of one rows field `r`, keyed by its column `k`, with the other columns
named. -/
def rowsSchema (columns : List String) : Value :=
  falconSchema [.obj [("name", .str "r"), ("type", .str "rows"), ("class", .str "MECHANICAL"),
    ("key", strs ["k"]), ("columns", .arr (textField "k" :: columns.map textField))]]

/-- An enum field of `n` values. -/
def enumField (name : String) (n : Nat) : Value :=
  .obj [("name", .str name), ("type", .str "enum"), ("class", .str "MECHANICAL"),
    ("values", strs ((List.range n).map fun i => s!"v{i}"))]

/-- `n` outputs of a one-text-field schema `f`. -/
def flatOutputs (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("account", .str s!"a{i}"),
    ("status", .str "RETURNED"), ("result", .obj [("f", .str "x")])])

/-- A reconciliation of `n` outputs and `q` quotes entries over the schema of one text
field `f`. -/
def flatReconcile (n q : Nat) : Value :=
  .obj [("outputs", flatOutputs n), ("quotes", .arr ((List.range q).map fun _ => .obj [])),
    ("schema", falconSchema [textField "f"])]

/-- A reconciliation of two outputs over `rowsSchema ["c"]`, each holding `rows` rows of
distinct keys, and `outcomes` quote outcomes in each quotes entry. -/
def rowsReconcile (rows outcomes : Nat) : Value :=
  let out (o : Nat) : Value := .obj [("account", .str s!"a{o}"), ("status", .str "RETURNED"),
    ("result", .obj [("r", .arr ((List.range rows).map fun i =>
      .obj [("k", .str s!"{i}"), ("c", .str "x")]))])]
  .obj [("outputs", .arr [out 0, out 1]),
    ("quotes", .arr ((List.range 2).map fun _ =>
      .obj ((List.range outcomes).map fun i => (s!"q{i}", .str "PASS")))),
    ("schema", rowsSchema ["c"])]

/-- Two outputs of one row each, keyed by 3354 characters, over 99 columns whose votes
split: the item lines' identifiers and values hold 999,900 characters and `extra` more,
the first column's second value holding them. -/
def itemsReconcile (extra : Nat) : Value :=
  let names := (List.range 99).map fun j => s!"c{j / 10}{j % 10}"
  let out (o : Nat) : Value := .obj [("account", .str s!"a{o}"), ("status", .str "RETURNED"),
    ("result", .obj [("r", .arr [.obj (("k", .str (copies 3354 'k')) ::
      names.map fun c => (c, .str (if o == 1 && c == "c00" then "1" ++ copies extra 'x'
        else toString o)))])])]
  .obj [("outputs", .arr [out 0, out 1]), ("quotes", .arr [.obj [], .obj []]),
    ("schema", rowsSchema names)]

/-- A `falcon_validate` request over the fields of `schema`, RETURNED with `result`. -/
def validateOf (schema result : Value) : Value :=
  .obj [("fields", Falcon.memberOf schema "fields"), ("status", .str "RETURNED"),
    ("result", result)]

/-- A result of `rows` rows of distinct keys over `rowsSchema ["c"]`. -/
def rowsValidate (rows : Nat) : Value :=
  validateOf (rowsSchema ["c"]) (.obj [("r", .arr ((List.range rows).map fun i =>
    .obj [("k", .str s!"{i}"), ("c", .str "x")]))])

/-- A result of one row keyed by 9888 characters, over 99 columns besides its key, the first
of them holding `e` characters: its value lines' identifiers and values hold 999,984
characters and `e` more. -/
def linesValidate (e : Nat) : Value :=
  let names := (List.range 99).map fun j => s!"c{j / 10}{j % 10}"
  validateOf (rowsSchema names) (.obj [("r", .arr [.obj (("k", .str (copies 9888 'k')) ::
    names.map fun c => (c, .str (if c == "c00" then copies e 'x' else "x")))])])

/-- A source list of `marks` CODE HOST marks holding `templates` templates in all, then
`entries` EXACT entries. -/
def falconSources (marks templates entries : Nat) : Value :=
  .arr ((List.range marks).map (fun i => .arr (.str "CODE HOST" :: .str s!"h{i}.org" ::
      if i == 0 then (List.range templates).map fun j => .str s!"/o{j}/*/" else [])) ++
    (List.range entries).map fun i => .arr [.str "EXACT", .str s!"https://a.org/{i}"])

/-- `n` events of a sponsor's stage. -/
def stageEvents (n : Nat) : Value :=
  .obj [("events", .arr ((List.range n).map fun i =>
      .arr [.str "LANDED", .int ((i * 86400 : Nat) : Int), .str "a"])),
    ("as_of", .int 253402300799),
    ("thresholds", .obj [("blocks", .int 1000000), ("dates", .int 1), ("span_days", .int 0),
      ("dormant_days", .int 1)])]

/-- `n` records of a stop: falcons issued and finished in turn. -/
def stopCounts (n : Nat) : Value :=
  .obj [("counts", .arr ((List.range n).map fun i =>
      if i % 2 == 0 then .arr [.str "ISSUED", .str s!"f{i / 2}"]
      else .arr [.str "FINISHED", .str s!"f{i / 2}", .int 1, .int 0, .int 0])),
    ("limits", .obj [("breaker", .str "1"), ("window", .int 1000)])]

/-- The falcons' bounds, each at the bound and one past it, and the item lines' count of the
case built at that bound. -/
def runFalconBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let ones (n : Nat) : Value := .str (copies n '1')
  let quoteMatch (v q : Nat) : Value := .obj [("value", ones v), ("quote", ones q)]
  let quoteCheck (p q v : Nat) : Value := .obj [("page", ones p), ("quote", ones q), ("value", ones v)]
  let maxS := Falcon.maxSearch
  let fieldsOf (n : Nat) : List Value := (List.range n).map fun i => textField s!"f{i}"
  let columnsOf (n : Nat) : List String := (List.range n).map fun i => s!"c{i}"
  let cases : List (String × String × Value × Bool) := [
    ("strings at 200,000 characters", "falcon_canon", canonOfTexts Falcon.maxTexts, false),
    ("strings past 200,000 characters", "falcon_canon", canonOfTexts (Falcon.maxTexts + 1), true),
    ("a value sought at the search bound", "falcon_quote_match", quoteMatch 20 (maxS / 20), false),
    ("a value sought past the search bound", "falcon_quote_match", quoteMatch 20 (maxS / 20 + 1), true),
    ("a quote sought in a page at the search bound", "quote_check", quoteCheck (maxS / 20) 20 1, false),
    ("a quote sought in a page past the search bound", "quote_check", quoteCheck (maxS / 20 + 1) 20 1, true),
    ("a value sought in a quote at the search bound", "quote_check", quoteCheck 1000 1000 (maxS / 1000), false),
    ("a value sought in a quote past the search bound", "quote_check", quoteCheck 1000 1000 (maxS / 1000 + 1), true),
    ("candidates at 100", "falcon_draw", falconDraw 100 0 0, false),
    ("candidates past 100", "falcon_draw", falconDraw 101 0 0, true),
    ("kept accounts at 100", "falcon_draw", falconDraw 100 100 0, false),
    ("kept accounts past 100", "falcon_draw", falconDraw 100 101 0, true),
    ("prior assignees at 1000", "falcon_draw", falconDraw 100 0 1000, false),
    ("prior assignees past 1000", "falcon_draw", falconDraw 100 0 1001, true),
    ("fields at 100", "falcon_schema_canon", .obj [("schema", falconSchema (fieldsOf 100))], false),
    ("fields past 100", "falcon_schema_digest", .obj [("schema", falconSchema (fieldsOf 101))], true),
    ("columns at 100", "falcon_schema_canon", .obj [("schema", rowsSchema (columnsOf 99))], false),
    ("columns past 100", "falcon_schema_canon", .obj [("schema", rowsSchema (columnsOf 100))], true),
    ("enum values at 1000", "falcon_schema_canon",
      .obj [("schema", falconSchema [enumField "e" 600, enumField "g" 400])], false),
    ("enum values past 1000", "falcon_schema_canon",
      .obj [("schema", falconSchema [enumField "e" 600, enumField "g" 401])], true),
    ("a spec's enum values past 1000", "falcon_canon",
      .obj [("value", .str "v0"), ("spec", enumField "e" 1001)], true),
    ("a schema's string at 100 characters", "falcon_schema_canon",
      .obj [("schema", falconSchema [textField (copies 100 'f')])], false),
    ("a schema's string past 100 characters", "falcon_reconcile",
      .obj [("outputs", flatOutputs 2), ("quotes", .arr [.obj [], .obj []]),
        ("schema", falconSchema [textField (copies 101 'f')])], true),
    ("outputs at 10", "falcon_reconcile", flatReconcile 10 10, false),
    ("outputs past 10", "falcon_reconcile", flatReconcile 11 11, true),
    ("quotes entries past 10", "falcon_reconcile", flatReconcile 10 11, true),
    ("rows at 1000", "falcon_reconcile", rowsReconcile 500 0, false),
    ("rows past 1000", "falcon_reconcile", rowsReconcile 501 0, true),
    ("quote outcomes at 1000", "falcon_reconcile", rowsReconcile 2 500, false),
    ("quote outcomes past 1000", "falcon_reconcile", rowsReconcile 2 501, true),
    ("item lines at 1,000,000 characters", "falcon_reconcile", itemsReconcile 100, false),
    ("item lines past 1,000,000 characters", "falcon_reconcile", itemsReconcile 101, true),
    ("rows in a result at 1000", "falcon_validate", rowsValidate 1000, false),
    ("rows in a result past 1000", "falcon_validate", rowsValidate 1001, true),
    ("a result's fields past 100", "falcon_validate",
      validateOf (falconSchema (fieldsOf 101)) (.obj []), true),
    ("value lines at 1,000,000 characters", "falcon_validate", linesValidate 16, false),
    ("value lines past 1,000,000 characters", "falcon_validate", linesValidate 17, true),
    ("events at 10,000", "sponsor_stage", stageEvents 10000, false),
    ("events past 10,000", "sponsor_stage", stageEvents 10001, true),
    ("count records at 10,000", "falcon_stop", stopCounts 10000, false),
    ("count records past 10,000", "falcon_stop", stopCounts 10001, true),
    ("source entries at 1000", "source_match",
      .obj [("cited", .str "https://a.org/1"), ("sources", falconSources 1 0 999)], false),
    ("source entries past 1000", "source_match",
      .obj [("cited", .str "https://a.org/1"), ("sources", falconSources 1 0 1000)], true),
    ("templates at 1000", "source_hop",
      .obj [("hop", .str "https://a.org/1"), ("matched", .int 1),
        ("sources", falconSources 2 1000 1)], false),
    ("templates past 1000", "source_hop",
      .obj [("hop", .str "https://a.org/1"), ("matched", .int 1),
        ("sources", falconSources 2 1001 1)], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "falcon" fn request
    t ← t.check (boundRefusal got == refused)
      s!"falcon {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The item lines' case is built at the bound exactly, and answered there.
  let atBound := match itemsReconcile 100 with
    | .obj [("outputs", o), ("quotes", q), ("schema", s)] =>
      match Principia.Falcon.Reconcile.falconReconcile o q s with
      | .ok d => Falcon.itemChars d
      | .error _ => 0
    | _ => 0
  t ← t.check (atBound == Falcon.maxItemText)
    s!"falcon_reconcile: the item lines' case holds {atBound} characters, not {Falcon.maxItemText}"
  -- The value lines' case is built at the bound exactly, and answered there.
  let linesAt := match linesValidate 16 with
    | .obj [("fields", f), ("status", st), ("result", r)] =>
      match Falcon.falconValidate f st r with
      | .ok c => Falcon.validateChars c
      | .error _ => 0
    | _ => 0
  t ← t.check (linesAt == Falcon.maxItemText)
    s!"falcon_validate: the value lines' case holds {linesAt} characters, not {Falcon.maxItemText}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Falcon

open Tests.Calculator

/-- `falcon_validate.json`: one output checked against its kind's output schema, every
case's `args` through `falcon falcon_validate`, each giving v1's text, or v1's word as a
refusal's detail; none owed. -/
def runFalconValidate : IO (Nat × Nat) :=
  runTextCalls "falcon" "vectors/falcon_validate.json" [] [("validate", "falcon_validate")]
    (respondTo "falcon")

/-- The family `falcon`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc falcon (falcon_corpus, falcon_hand)", runFalconCalls),
  ("pcalc falcon (falcon_validate)", runFalconValidate),
  ("pcalc falcon bounds", runFalconBounds),
]

end Tests.Calculator.Falcon
