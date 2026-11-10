import Principia.Provision.Check
import Principia.Canonical

/-!
# The answers as v1 wrote them

Each Provision function's answer as v1's list (tpm_module_spec 2.3, 6.4 RENDER):
`["OK", ...]` with the function's parts, or `["REFUSED", reason]`. An owed answer has no such
value: the Calculator does not answer it.
-/

namespace Principia.Provision

open Principia.Canonical (Value)

/-- Strings as a list. -/
def strsV (xs : List String) : Value := .arr (xs.map .str)

/-- An answer as v1's value, or `none` when it is owed. -/
def Answer.toValue? {α : Type} (f : α → List Value) : Answer α → Option Value
  | .ok a => some (.arr (.str "OK" :: f a))
  | .refused r => some (.arr [.str "REFUSED", .str r])
  | .owed _ => none

/-- `module_parse`'s parts. -/
def Parsed.parts (p : Parsed) : List Value :=
  [.str p.id, .str p.version,
   .arr (p.slots.map fun (s, k, d, mn, mx) => .arr [.str s, .str k, .str d, .int mn, .int mx]),
   .arr (p.params.map fun (n, s, d) => strsV [n, s, d]),
   .arr (p.sums.map fun (n, o, c) => strsV [n, o, c]),
   .arr (p.terms.map fun (t, s, c) => strsV [t, s, c]),
   strsV p.assumptions,
   .arr (p.boundaries.map fun (n, c) => strsV [n, c]),
   strsV p.excludes,
   .arr (p.questions.map fun (w, q) => strsV [w, q]),
   strsV p.bindings]

/-- `module_digest`'s part. -/
def digestParts (d : String) : List Value := [.str d]

/-- `module_bind`'s parts. -/
def Bound.parts (b : Bound) : List Value :=
  [.arr (b.slots.map fun (s, ns) => .arr [.str "SLOT", .str s, strsV ns]),
   .arr (b.params.map fun r => strsV ["PARAMETER", r.name, r.supply, r.value.getD "", r.unit.getD "",
     r.uncertainty.getD ""])]

/-- `module_expand`'s parts, as v1's corpus renders them. -/
def Rendered.parts (r : Rendered) : List Value :=
  [strsV ["D(TPK)", r.dTpk],
   .arr [.str "COMPOSED", .arr (r.composed.map fun (l, e) => strsV [l, e])],
   .arr [.str "EMITTED", .arr (r.emitted.map fun (k, n, src) => .arr [.str k, .str n, strsV src])],
   .arr [.str "DROPPED", .arr (r.dropped.map fun (c, q) => strsV [c, q])]]

/-- `catalogue_state`'s parts. -/
def CatalogueState.parts (s : CatalogueState) : List Value :=
  [.arr [.str "VERSIONS", .arr (s.versions.map fun (i, v, d, st, dt, n) => strsV [i, v, d, st.word, dt, n])],
   .arr [.str "OFFERED", .arr (s.offered.map fun (i, v, d) => strsV [i, v, d])],
   .arr [.str "STATES", .arr (s.states.map fun (n, d) => .arr [.int n, .str d])]]

/-- `interview_check`'s parts. -/
def InterviewAnswer.parts (a : InterviewAnswer) : List Value :=
  [.arr [.str "ASK", .arr (a.ask.map fun (i, v, d) => strsV [i, v, d])],
   .arr [.str "CLAIMS", .arr (a.claims.map fun (i, v, w) => strsV [i, v, w.word])]]

/-- `not_included_lines`'s part. -/
def linesParts (ls : List (String × String)) : List Value :=
  [.arr (ls.map fun (s, l) => strsV [s, l])]

/-- `module_verify`'s parts. -/
def Verified.parts (r : Verified) : List Value :=
  [.str (if r.matched then "MATCH" else "MISMATCH"), .str r.want, .str r.got,
   .arr (r.claims.map fun (i, v, st) => strsV [i, v, st.word])]

/-- A claim's status row. -/
def ClaimStatus.row (i v : String) : ClaimStatus → Value
  | .offered => strsV [i, v, "OFFERED"]
  | .noneOffered => strsV [i, v, "SUPERSEDED", "NONE OFFERED"]
  | .superseded s w => strsV [i, v, "SUPERSEDED", s, w]
  | .retired d => strsV [i, v, "RETIRED", d]
  | .withdrawn d n => strsV [i, v, "WITHDRAWN", d, n]

/-- `draft_module_status`'s parts. -/
def DraftStatus.parts (s : DraftStatus) : List Value :=
  [.arr [.str "CLAIMS", .arr (s.claims.map fun (i, v, c) => c.row i v)],
   .arr [.str "GATE", strsV s.gate]]

/-- `module_use_view`'s parts. -/
def UseView.parts (u : UseView) : List Value :=
  [.arr [.str "ROWS", .arr (u.rows.map fun (i, v, p, st) => strsV [i, v, p, st.word])],
   .arr [.str "UWCS ON WITHDRAWN", .int u.onWithdrawn]]

/-- A row of `module_check`. -/
def CheckRow.toValue : CheckRow → Value
  | .digest d => strsV ["DIGEST", d]
  | .references v => strsV ["REFERENCES", v]
  | .binding n v => strsV ["BINDING", n, v]
  | .pairExcluded i v => strsV ["PAIR", i, v, "EXCLUDED"]
  | .pair i v b w => strsV ["PAIR", i, v, b, w]
  | .sharedParameter a b c d n => strsV ["SHARED PARAMETER", a, b, c, d, n]
  | .atomicity xs => .arr [.str "ATOMICITY", strsV xs]

/-- `module_check`'s parts. -/
def Checked.parts (c : Checked) : List Value :=
  [.str (if c.pass then "PASS" else "FAIL"), .arr (c.rows.map CheckRow.toValue)]

end Principia.Provision
