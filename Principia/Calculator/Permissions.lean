import Principia.Calculator.Interface
import Principia.Permissions

/-!
# Family `permissions`: the permission table on the command line

`Principia.Permissions.permits` as a JSON family beside the word arm `pcalc permits`
(the Declarer's choice): Custos's permission hook reads a table generated from it.
* `permits {"asker", "class", "op", "context"}`: `"PERMITTED"` or `"REFUSED"`, the word the
  word arm answers for the same words. `asker` is an asker's word (`DECLARER`, `OPERATOR`,
  `INITIATOR`, `SPONSOR`, `PUBLIC`, `HOLDER`, `COWORKER`, or `AGENT` for an agent account in
  no lock state), `class` a page class's, `op` an operation's, and `context` the list of the
  word arm's context words (`OPEN`, `CLOSED`, `LISTED`, `NAMED` and a DOSSIER READ word,
  `QUEUE HEAD`, `REAUTHENTICATED`; `Permissions.readContext`), empty for none.
* `domain {}`: the finite domain, so that a table generator iterates it from this one
  residence: `{"askers", "classes", "ops", "contexts"}`, the askers' 8 words, the 40 page
  classes' and the 6 operations' in the table's order, and the 96 contexts as word lists:
  each policy (none, `OPEN`, `CLOSED`), on the access list or not, the title naming the
  asker under each DOSSIER READ or not, at the queue head or not, re-authenticated or not.
  Every context Custos can know reads as exactly one of them (the Calculator's
  tests check the 96 are distinct and complete).
* `table {}`: the whole table in one answer, so that Custos's permission hook
  reads it from a file generated from this residence (`scripts/permits_table.py`):
  `{"cells", "contexts"}`, `contexts` the domain's 96 contexts and `cells` an object by
  asker word, then page class word, then operation word, of the 96 answer words in the
  contexts' order. `table_lookup_eq_permits`: every cell is the answer `permits` gives on
  its asker, class, operation and context, read as the word arm reads them (9 askers,
  40 classes, 6 operations, 96 contexts: 207,360 cells).

Bounds: reading the words is linear in the request, which the reader bounds at 1 MiB; the
table is a fixed lookup. The slowest accepted request measured, `permits` with 116,496
context words (a request of 1 MiB), took 0.13 s on the command line.
-/

namespace Principia.Calculator.Permissions

open Principia.Canonical
open Principia.Permissions
open Principia.Parameters (DossierRead)

/-- The words of every member of an enumeration, in its order. -/
def words (α : Type) [WireWord α] : Value :=
  .arr ((WireWord.members : List α).map fun a => .str (WireWord.toWire a))

/-- Every context, as the word arm's words, in the order the domain lists them. -/
def contextDomain : List (List String) := Id.run do
  let mut out : Array (List String) := #[]
  for policy in [none, some AccessPolicy.openAccess, some AccessPolicy.closedAccess] do
    for listed in [false, true] do
      for named in [none, some DossierRead.userOnly, some DossierRead.userAndAgent,
          some DossierRead.neither] do
        for head in [false, true] do
          for reauth in [false, true] do
            out := out.push (
              (policy.map WireWord.toWire).toList ++
              (if listed then ["LISTED"] else []) ++
              (match named with
                | some d => ["NAMED", WireWord.toWire d]
                | none => []) ++
              (if head then ["QUEUE HEAD"] else []) ++
              (if reauth then ["REAUTHENTICATED"] else []))
  return out.toList

/-- A request's words read as the word arm reads them. -/
def requestOf (v : Value) : Except Refusal Request := do
  let ms ← membersOf ["asker", "class", "op", "context"] v
  let actor ← asWord Actor "an asker" (← needed ms "asker")
  let pageClass ← asWord PageClass "a page class" (← needed ms "class")
  let op ← asWord Op "an operation" (← needed ms "op")
  let ws ← asStrings "context" (← needed ms "context")
  match readContext ws {} with
  | some context => pure { actor, pageClass, op, context }
  | none => badArgument "context is not a list of the context words"

/-- The answer word on a context's words, read as the word arm reads them; a list that does
not read (none of the domain's, `Tests/Calculator.lean`) answers `REFUSED`. -/
def cellOn (a : Actor) (c : PageClass) (op : Op) (ws : List String) : String :=
  match readContext ws {} with
  | some context => ({ actor := a, pageClass := c, op, context } : Request).answer
  | none => "REFUSED"

/-- A cell read from words is `permits` on the context they read as. -/
theorem cellOn_eq_permits {a : Actor} {c : PageClass} {op : Op} {ws : List String}
    {ctx : PageContext} (h : readContext ws {} = some ctx) :
    cellOn a c op ws = if permits a c op ctx then "PERMITTED" else "REFUSED" := by
  simp [cellOn, h, Request.answer]

/-- The table's cells: by asker, page class, operation and context, in the domain's orders. -/
def cells : List (List (List (List String))) :=
  (WireWord.members : List Actor).map fun a =>
    (WireWord.members : List PageClass).map fun c =>
      (WireWord.members : List Op).map fun op =>
        contextDomain.map (cellOn a c op)

/-- The cell at the domain's indices: asker, page class, operation, context. -/
def lookup (ia ic io ix : Nat) : Option String := do
  let classes ← cells[ia]?
  let ops ← classes[ic]?
  let answers ← ops[io]?
  answers[ix]?

/-- Every cell of the table equals `permits` on its arguments: the asker, class and
operation at its indices and the context the domain lists at its index. -/
theorem table_lookup_eq_permits {ia ic io ix : Nat} {a : Actor} {c : PageClass} {op : Op}
    {ws : List String}
    (ha : (WireWord.members : List Actor)[ia]? = some a)
    (hc : (WireWord.members : List PageClass)[ic]? = some c)
    (ho : (WireWord.members : List Op)[io]? = some op)
    (hw : contextDomain[ix]? = some ws) :
    lookup ia ic io ix = some (cellOn a c op ws) := by
  simp only [lookup, cells, List.getElem?_map, ha, hc, ho, hw, Option.map_some,
    Option.bind_eq_bind, Option.bind_some]

/-- The table as the family answers it: `cells` rendered under the domain's words. -/
def tableValue : Value :=
  .obj [("cells", .obj (((WireWord.members : List Actor).zip cells).map fun (a, byClass) =>
      (WireWord.toWire a, .obj (((WireWord.members : List PageClass).zip byClass).map
        fun (c, byOp) => (WireWord.toWire c, .obj (((WireWord.members : List Op).zip byOp).map
          fun (op, answers) => (WireWord.toWire op, .arr (answers.map .str)))))))),
    ("contexts", .arr (contextDomain.map fun ws => .arr (ws.map .str)))]

/-- The family's functions. -/
def calls : Family := [
  ("domain", fun v => do
    let _ ← arguments [] v
    pure (.obj [("askers", words Actor), ("classes", words PageClass), ("ops", words Op),
      ("contexts", .arr (contextDomain.map fun ws => .arr (ws.map .str)))])),
  ("permits", fun v => do pure (.str (← requestOf v).answer)),
  ("table", fun v => do
    let _ ← arguments [] v
    pure tableValue),
]

end Principia.Calculator.Permissions
