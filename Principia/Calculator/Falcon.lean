import Principia.Calculator.Interface
import Principia.Falcon

/-!
# Family `falcon`: the falcons

v1's `tpc_falcon` 0.2.0 (`Principia.Falcon`), one function each, by v1's function names, its
arguments named as v1's `run_case` names them:
* `falcon_canon {"value", "spec"}`: a field value's canonical form under its field spec.
* `falcon_draw {"candidates", "n", "state", "r"}`: the falcon draw.
* `falcon_quote_match {"value", "quote", "affix"?, "scale"?, "accounting"?}`: the TOKEN RULE's
  match of a value in a quote.
* `falcon_reconcile {"outputs", "quotes", "schema"}`: the reconciliation of a falcon's outputs.
* `falcon_schema_canon {"schema"}` and `falcon_schema_digest {"schema"}`: the output schema's
  canonical text and its SHA-256 digest.
* `falcon_stop {"counts", "limits"}`: the per-kind stop.
* `quote_check {"page", "quote", "value", "affix"?, "scale"?, "accounting"?}`: the QUOTE
  CHECK over a page's text (`page` `null`: UNKNOWN).
* `source_hop {"hop", "matched", "sources"}`: a redirect hop matched again.
* `source_match {"cited", "sources"}`: the source entry a citation falls under.
* `sponsor_stage {"events", "as_of", "thresholds"}`: a sponsor's stage.

An argument v1 read with `get` may be absent: `affix` and `scale` absent or `null` are none;
`accounting` absent is false, and any other value is checked as v1 checked it. Every value is
given to v1's function as it was read: a number with a fraction or an exponent is v1's float,
one without v1's integer. The answer is v1's text of the result (`render_canon`,
`render_draw`, `render_quote`, ...). A request v1 refused is refused with v1's word as the
detail (`BAD_ARGUMENT`), the checks made in v1's order. Every answer is computed: text in NFC
with Unicode 15.1.0's tables and the digests in SHA-256, as in v1, so none is refused `OWED`.
No answer forms an exact fraction: counts, times and shares are integers, a share compared by
cross-multiplication as v1 compared it, so the bound on an exact value has nothing to bound
here.

## Bounds, measured

Times are of `pcalc` on one request, the best of three runs, for the slowest shape found at
each bound. A request is read as the reader bounds it, at most 1 MiB nested at most 64 levels;
one past a bound below is refused (`BAD_ARGUMENT`, "the Calculator's bound").
* Texts: the strings of a request, keys included, hold at most `maxTexts` characters in all.
  Text is put in NFC, whose canonical ordering sorts each run of combining marks: one run of
  199,900 marks takes 0.9 s, 199,900 characters that NFC turns into three each 0.74 s.
* The QUOTE CHECK compares the text sought with the text searched at each position of the
  latter: the characters of the one times those of the other, a value in a quote and a quote
  in a page, are at most `maxSearch`. A page of 199,000 characters that NFC turns into three
  each, its quote of 10, takes 1.2 s; ordinary text of the same lengths, 0.2 s.
* `falcon_draw`: at most `maxCandidates` candidates and as many kept accounts, and `maxPrior`
  prior assignees. The draw weighs every set of `n` eligible accounts against the kept ones:
  three drawn from 80 eligible of 100 candidates, 20 kept, take 0.57 s.
* Schemas and specs: at most `maxFields` fields, `maxColumns` columns in all, `maxValues` enum
  values in all and `maxSchemaText` characters in a string (a name, an enum value, an affix,
  a scale), each name and value checked against those before it: 0.06 s.
* `falcon_reconcile`: at most `maxOutputs` outputs and as many quotes entries, `maxRows` rows
  in all the outputs, and `maxQuoteItems` quote outcomes in all: two outputs of 200 rows of
  100 columns, 1,000 quote outcomes, take 0.74 s. A row's key and its field's name stand in
  the line of each of its columns and of each vote, so the item lines' identifiers and values
  are counted before the answer is written, at most `maxItemText` characters: a key of 45,000
  characters over 100 columns is refused in 0.04 s.
* `sponsor_stage` and `falcon_stop`: at most `maxEvents` events or records, each landed day,
  suspended agent and falcon checked against those before it: 10,000 take 0.51 s and 0.78 s.
* `source_match` and `source_hop`: at most `maxSources` entries and CODE HOST marks, and
  `maxTemplates` templates in all, each PREFIX entry on a CODE HOST tried against its
  templates: 999 such entries and 1,000 templates take 0.15 s.
-/

namespace Principia.Calculator.Falcon

open Principia.Canonical
open Principia.Falcon (Result Fault)

/-! ## The family's bounds, measured -/

/-- The most characters the strings of a request hold in all, keys included. -/
def maxTexts : Nat := 200000

/-- The most a QUOTE CHECK compares: the characters of the text sought times those of the
text searched. -/
def maxSearch : Nat := 2000000

/-- The most candidates a draw weighs, and the most kept accounts. -/
def maxCandidates : Nat := 100

/-- The most prior assignees a draw's state holds. -/
def maxPrior : Nat := 1000

/-- The most fields of a schema. -/
def maxFields : Nat := 100

/-- The most columns of a schema's rows fields, in all. -/
def maxColumns : Nat := 100

/-- The most enum values of a schema or a spec, in all. -/
def maxValues : Nat := 1000

/-- The most characters of a string of a schema or a spec: its names, enum values, affixes
and scales. -/
def maxSchemaText : Nat := 100

/-- The most outputs a reconciliation compares. -/
def maxOutputs : Nat := 10

/-- The most rows the outputs of a reconciliation hold, in all. -/
def maxRows : Nat := 1000

/-- The most quote outcomes the quotes of a reconciliation hold, in all. -/
def maxQuoteItems : Nat := 1000

/-- The most characters of a reconciliation's item lines, their identifiers and values: a
row's key and its field's name stand in the line of each of its columns and each vote. -/
def maxItemText : Nat := 1000000

/-- The most events of a sponsor's stage, and the most records of a stop. -/
def maxEvents : Nat := 10000

/-- The most entries and CODE HOST marks of a source list. -/
def maxSources : Nat := 1000

/-- The most templates the CODE HOST marks of a source list hold, in all. -/
def maxTemplates : Nat := 1000

/-! ## Measuring a request -/

/-- The characters of every string of a value, keys included. -/
def textChars : Value → Nat
  | .str s => s.length
  | .arr vs => listChars vs
  | .obj ms => membersChars ms
  | _ => 0
where
  listChars : List Value → Nat
    | [] => 0
    | v :: rest => textChars v + listChars rest
  membersChars : List (String × Value) → Nat
    | [] => 0
    | (k, v) :: rest => k.length + textChars v + membersChars rest

/-- The characters of the longest string of a value, keys included. -/
def longestText : Value → Nat
  | .str s => s.length
  | .arr vs => listLongest vs
  | .obj ms => membersLongest ms
  | _ => 0
where
  listLongest : List Value → Nat
    | [] => 0
    | v :: rest => max (longestText v) (listLongest rest)
  membersLongest : List (String × Value) → Nat
    | [] => 0
    | (k, v) :: rest => max k.length (max (longestText v) (membersLongest rest))

/-- The number of entries of a list or an object, `0` for anything else. -/
def entries : Value → Nat
  | .arr xs => xs.length
  | .obj ms => ms.length
  | _ => 0

/-- The member `k` of an object, `null` for anything else or when absent. -/
def memberOf (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => (ms.lookup k).getD .null
  | _ => .null

/-- The entries of a list, none for anything else. -/
def listOf : Value → List Value
  | .arr xs => xs
  | _ => []

/-- The members' values of an object, none for anything else. -/
def valuesOf : Value → List Value
  | .obj ms => ms.map (·.2)
  | _ => []

/-- A count within its bound: at most `n` of `what`. -/
def within (what : String) (n count : Nat) : Except Refusal Unit :=
  if n < count then badArgument s!"more than {n} {what} (the Calculator's bound)"
  else .ok ()

/-- The request's strings within `maxTexts`. -/
def textsWithin (v : Value) : Except Refusal Unit :=
  if maxTexts < textChars v then
    badArgument s!"the request's strings hold more than {maxTexts} characters in all (the Calculator's bound)"
  else .ok ()

/-- The characters of a string, `0` for anything else. -/
def charsOf : Value → Nat
  | .str s => s.length
  | _ => 0

/-- A QUOTE CHECK's search within `maxSearch`: the text sought in the text searched. -/
def searchWithin (sought searched : Value) : Except Refusal Unit :=
  if maxSearch < charsOf sought * charsOf searched then
    badArgument s!"the characters of a text sought times those of the text searched are more than {maxSearch} (the Calculator's bound)"
  else .ok ()

/-- A field spec's enum values. -/
def specValues (f : Value) : Nat := entries (memberOf f "values")

/-- A schema's fields, columns, enum values and strings within their bounds; `fields` is
the list of field specs (a schema's, or a single spec). -/
def specsWithin (fields : List Value) : Except Refusal Unit := do
  within "fields in the schema" maxFields fields.length
  if fields.any (maxSchemaText < longestText ·) then
    badArgument s!"a string of the schema holds more than {maxSchemaText} characters (the Calculator's bound)"
  let columns := fields.flatMap fun f => listOf (memberOf f "columns")
  within "columns in the schema" maxColumns columns.length
  within "enum values in the schema" maxValues
    ((fields.map specValues).sum + (columns.map specValues).sum)

/-- A schema within the bounds on its fields, columns and enum values. -/
def schemaWithin (schema : Value) : Except Refusal Unit :=
  specsWithin (listOf (memberOf schema "fields"))

/-- The characters of a reconciliation's item lines, before escaping: each item's identifier
in its line and in each vote's line, its value and the votes' values. -/
def itemChars (d : Principia.Falcon.Reconcile.Reconciled) : Nat :=
  (d.items.map fun it => it.id.length * (1 + it.votes.length) +
    (it.value.map String.length).getD 0 + (it.votes.map fun (_, v, _) => v.length).sum).sum

/-! ## The calls -/

/-- An answer as `pcalc` gives it: v1's text, or v1's word as a refusal. -/
def answer {α : Type} (render : α → String) : Result α → Except Refusal Value
  | .ok a => .ok (.str (render a))
  | .error (.refused w) => badArgument w

/-- `affix`, `scale` and `accounting` as v1's `get` read them: `affix` and `scale` absent or
`null` are none, `accounting` absent is false. -/
def flags (ms : List (String × Value)) : Value × Value × Value :=
  ((optional ms "affix").getD .null, (optional ms "scale").getD .null,
    (ms.lookup "accounting").getD (.bool false))

/-- The family's functions. -/
def calls : Family := [
  ("falcon_canon", fun v => do
    let ms ← membersOf ["value", "spec"] v
    let value ← needed ms "value"
    let spec ← needed ms "spec"
    textsWithin v
    specsWithin [spec]
    answer Principia.Falcon.renderCanon (Principia.Falcon.falconCanon value spec)),
  ("falcon_draw", fun v => do
    let ms ← membersOf ["candidates", "n", "state", "r"] v
    let candidates ← needed ms "candidates"
    let n ← needed ms "n"
    let state ← needed ms "state"
    let r ← needed ms "r"
    textsWithin v
    within "candidates" maxCandidates (listOf candidates).length
    within "kept accounts" maxCandidates (listOf (memberOf state "kept")).length
    within "prior assignees" maxPrior (listOf (memberOf state "prior")).length
    answer Principia.Falcon.Draw.renderDraw (Principia.Falcon.Draw.falconDraw candidates n state r)),
  ("falcon_quote_match", fun v => do
    let ms ← membersOf ["value", "quote", "affix", "scale", "accounting"] v
    let value ← needed ms "value"
    let quote ← needed ms "quote"
    textsWithin v
    searchWithin value quote
    let (affix, scale, accounting) := flags ms
    answer Principia.Falcon.Quote.renderQuote
      (Principia.Falcon.Quote.quoteMatch value quote affix scale accounting)),
  ("falcon_reconcile", fun v => do
    let ms ← membersOf ["outputs", "quotes", "schema"] v
    let outputs ← needed ms "outputs"
    let quotes ← needed ms "quotes"
    let schema ← needed ms "schema"
    textsWithin v
    schemaWithin schema
    within "outputs" maxOutputs (listOf outputs).length
    within "quotes entries" maxOutputs (listOf quotes).length
    within "rows in the outputs" maxRows
      ((listOf outputs).map fun o =>
        ((valuesOf (memberOf o "result")).map fun x => (listOf x).length).sum).sum
    within "quote outcomes in the quotes" maxQuoteItems ((listOf quotes).map entries).sum
    match Principia.Falcon.Reconcile.falconReconcile outputs quotes schema with
    | .ok d =>
      if maxItemText < itemChars d then
        badArgument s!"the item lines would hold more than {maxItemText} characters (the Calculator's bound)"
      pure (.str (Principia.Falcon.Reconcile.renderReconcile d))
    | .error (.refused w) => badArgument w),
  ("falcon_schema_canon", fun v => do
    let schema ← argument1 "schema" v
    textsWithin v
    schemaWithin schema
    answer Principia.Falcon.Schema.renderCanonText (Principia.Falcon.Schema.schemaCanon schema)),
  ("falcon_schema_digest", fun v => do
    let schema ← argument1 "schema" v
    textsWithin v
    schemaWithin schema
    answer Principia.Falcon.Schema.renderDigest (Principia.Falcon.Schema.schemaDigest schema)),
  ("falcon_stop", fun v => do
    let (counts, limits) ← argument2 "counts" "limits" v
    textsWithin v
    within "count records" maxEvents (listOf counts).length
    answer Principia.Falcon.Stop.renderStop (Principia.Falcon.Stop.falconStop counts limits)),
  ("quote_check", fun v => do
    let ms ← membersOf ["page", "quote", "value", "affix", "scale", "accounting"] v
    let page ← needed ms "page"
    let quote ← needed ms "quote"
    let value ← needed ms "value"
    textsWithin v
    searchWithin quote page
    searchWithin value quote
    let (affix, scale, accounting) := flags ms
    answer Principia.Falcon.Quote.renderQuote
      (Principia.Falcon.Quote.quoteCheck page quote value affix scale accounting)),
  ("source_hop", fun v => do
    let (hop, matched, sources) ← argument3 "hop" "matched" "sources" v
    sourcesWithin v sources
    answer Principia.Falcon.Source.renderHop
      (Principia.Falcon.Source.sourceHop hop matched sources)),
  ("source_match", fun v => do
    let (cited, sources) ← argument2 "cited" "sources" v
    sourcesWithin v sources
    answer Principia.Falcon.Source.renderSource
      (Principia.Falcon.Source.sourceMatch cited sources)),
  ("sponsor_stage", fun v => do
    let (events, asOf, thresholds) ← argument3 "events" "as_of" "thresholds" v
    textsWithin v
    within "events" maxEvents (listOf events).length
    answer Principia.Falcon.Stage.renderStage
      (Principia.Falcon.Stage.sponsorStage events asOf thresholds)),
]
where
  /-- A source list within its bounds: its entries and marks, and the marks' templates. -/
  sourcesWithin (v sources : Value) : Except Refusal Unit := do
    textsWithin v
    within "source entries" maxSources (listOf sources).length
    within "templates in the CODE HOST marks" maxTemplates
      ((listOf sources).map fun e => match e with
        | .arr (.str "CODE HOST" :: _ :: tps) => tps.length
        | _ => 0).sum

end Principia.Calculator.Falcon
