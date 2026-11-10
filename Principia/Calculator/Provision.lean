import Principia.Calculator.Interface
import Principia.Provision

/-!
# Family `provision`: Provisions

Version 1's eleven Provision functions, one function each, its arguments named as v1's
`run_case` names them, each of which v1 read with `get`, so that any may be absent or
`null`:
* `module_parse {"text"}` and `module_digest {"text"}`: a Provision's text read and checked,
  and its digest.
* `module_bind {"tpk", "text", "bind", "values"}`: a Provision's slots bound to names of a
  Starting Set, and each parameter's row.
* `module_expand {"draft", "claims", "modules"}`: a draft expanded by its claims.
* `module_verify {"base", "claims", "modules", "lines", "draft"}`: the re-expansion at the
  final pass.
* `interview_check {"answer", "claims", "lines", "modules", "carried", "modified"}` and
  `not_included_lines` (the same arguments): the interview, and the NOT INCLUDED lines of the
  check page.
* `catalogue_state {"lines"}`: the catalogue that the declaring lines declare.
* `module_check {"text", "act", "date", "lines", "modules"}`: the checks before a declaring
  act.
* `draft_module_status {"base", "claims", "modules", "lines"}`: each claim's status on a
  draft.
* `module_use_view {"certificates", "lines"}`: the certificates that use each declared
  version.

A request's value is read as version 1 read its JSON: a number written with a fraction or an
exponent is a float, which every field refuses; a Provision's text, a string, is read by the
Provision reader, strictly and in NFC. The answer is version 1's value, `["OK", ...]` or
`["REFUSED", reason]`, its refusals values as version 1 wrote them (exit code 0). Every
digest is SHA-256, so none is owed. An answer the Calculator does not compute is refused
`OWED`, its detail saying what is owed: the checks before a declaring act run the
fundamental tests on each test binding's expansion, and a value there that the Calculator's
exact bounds do not settle (a value exactly zero but not known so) leaves the verdict owed,
how such a value is answered being not yet chosen.

Bounds, measured on the Calculator's command line, each with the slowest request found
within it (CPU time, on a machine shared with other work). A request is refused past any of
them, before anything is computed.
* At most `maxTexts` texts in `modules`, holding at most `maxTextsBytes` in all with the text
  `module_check` checks: that check digests and expands its text again for each test binding
  and each Provision given, as version 1 did. Eight test bindings paired with four other
  Provisions in 64 KiB, the text's 32 PROPOSITIONs nested 128 deep, take 1.4 s.
* Every Starting Set a request carries, its own and each test binding's in each text: at
  most `maxEntries` entries of each kind, `maxRefs` names in each REFS, `maxForm` code points
  in each EQUATION and CONDITION and `maxProposition` in each PROPOSITION and PREDICATE; at
  most `maxEntriesInAll` entries in all. A text's PROPOSITIONs and PREDICATEs hold at most
  `maxProposition` code points, as written and once each slot is filled with the names
  bound to it. Version 1's check of a PROPOSITION's atomicity costs its length times its
  nesting, and filling multiplies a text's few characters by the names bound: 32 such
  PROPOSITIONs, unbounded, took 15.9 s to check; one of 40,000 words, 17.8 s. A draft at
  these bounds re-expanded for four superseded claims takes 1.7 s; verified with its base,
  1.2 s; bound, 0.5 s.
* At most `maxPlacements` term placements, each term on each name its target is bound to:
  each reads the law it is composed into, as version 1's did; eight claims of 256 placements
  on laws of 4096 code points took 2.7 s.
* At most `maxLines` declaring lines (each act checks the catalogue so far: 256 take 0.14 s,
  1024 took 2.5 s), `maxClaims` claims, `maxRounds` rounds of the answer, `maxListed` claims
  carried and Provisions modified (the interview at these bounds: 0.11 s), and
  `maxCertificates` certificates naming at most `maxUsed` Provisions (0.23 s).
* The structure check of a draft's equations of motion runs over its DOFs and laws, at most
  `maxEntries` of each: a draft of 61 unknowns and 62 laws, every law naming every unknown,
  takes 0.11 s.
-/

namespace Principia.Calculator.Provision

open Principia.Canonical
open Principia.Provision (Answer Owed)

/-- A request's value as version 1's reader gave it to the Provision functions. -/
def zone (v : Value) : Zone.Value := Principia.Strike.toZoneValue v

/-- The request's members, each named in `names`, any of them absent or `null`. -/
def read (names : List String) (v : Value) : Except Refusal (String → Zone.Value) := do
  let ms ← membersOf names v
  pure fun k => ((ms.lookup k).map zone).getD .null

/-- An owed answer's detail, in plain words: what is owed, and what it waits on. -/
def owedDetail : Owed → String
  | .digest => "the answer is owed: it needs a digest the Calculator does not compute"
  | .exact what =>
    "the answer is owed: the Calculator's exact bounds do not settle a value it meets (" ++ what ++
      "), and how such a value is answered is not yet chosen"

/-- An answer as `pcalc` gives it: version 1's value, or the refusal `OWED`. -/
def answer {α : Type} (parts : α → List Value) : Answer α → Except Refusal Value
  | .ok a => .ok (.arr (.str "OK" :: parts a))
  | .refused r => .ok (.arr [.str "REFUSED", .str r])
  | .owed w => .error ⟨.owed, owedDetail w⟩

/-- The digests: SHA-256. -/
def D : Principia.Provision.DigestHook := Principia.Provision.DigestHook.calculator

/-! ## The family's bounds, measured -/

/-- The most texts `modules` holds. -/
def maxTexts : Nat := 8

/-- The most UTF-8 bytes the texts of a request hold in all, where the function takes
`modules` (the text `module_check` checks counted with them). -/
def maxTextsBytes : Nat := 65536

/-- The most entries each kind of a Starting Set holds. -/
def maxEntries : Nat := 64

/-- The most entries the Starting Sets of a request hold in all: its own, and every test
binding's of every text it gives. -/
def maxEntriesInAll : Nat := 1024

/-- The most names a Starting Set entry's REFS lists. -/
def maxRefs : Nat := 128

/-- The most code points a Starting Set's EQUATION or CONDITION holds. -/
def maxForm : Nat := 16384

/-- The most code points a PROPOSITION or PREDICATE holds: a Starting Set's, a text's, and
one a text writes once its slots are filled. -/
def maxProposition : Nat := 256

/-- The most declaring lines `lines` holds. -/
def maxLines : Nat := 256

/-- The most terms a request's claims place, each term on each name its target is bound
to, in all; and the most each test binding of a text `module_check` checks places. Each
placement reads the law it is composed into. -/
def maxPlacements : Nat := 64

/-- The most claims `claims` holds. -/
def maxClaims : Nat := 8

/-- The most rounds the answer holds. -/
def maxRounds : Nat := 64

/-- The most claims `carried` holds, and the most Provisions `modified` names. -/
def maxListed : Nat := 64

/-- The most certificates `certificates` holds. -/
def maxCertificates : Nat := 1024

/-- The most Provisions the certificates' MODULES_USED name in all. -/
def maxUsed : Nat := 4096

/-- The member `k` of an object, `null` for anything else or when absent. -/
def memberOf (v : Zone.Value) (k : String) : Zone.Value :=
  match v with
  | .obj ms => (ms.lookup k).getD .null
  | _ => .null

/-- A list's entries, none for anything else. -/
def itemsOf : Zone.Value → List Zone.Value
  | .arr xs => xs
  | _ => []

/-- A list within a bound; anything else is left to the function. -/
def listWithin (what : String) (n : Nat) (v : Zone.Value) : Except Refusal Unit :=
  atMost what n (itemsOf v)

/-- A string field within a bound of code points; anything else is left to the function. -/
def fieldWithin (what field : String) (n : Nat) (e : Zone.Value) : Except Refusal Unit :=
  match memberOf e field with
  | .str s =>
    if n < s.length then
      badArgument s!"{what} holds a {field} of more than {n} code points (the Calculator's bound)"
    else pure ()
  | _ => pure ()

/-- A Starting Set within the bounds on each kind, each REFS, each form and each
PROPOSITION: the number of its entries. -/
def startingSetWithin (what : String) (tpk : Zone.Value) : Except Refusal Nat := do
  let mut n := 0
  for kind in StartingSet.kinds do
    let es := itemsOf (memberOf tpk kind)
    atMost s!"{what}'s {kind}" maxEntries es
    for e in es do
      listWithin s!"a REFS of {what}" maxRefs (memberOf e "REFS")
      fieldWithin what "EQUATION" maxForm e
      fieldWithin what "CONDITION" maxForm e
      fieldWithin what "PROPOSITION" maxProposition e
      fieldWithin what "PREDICATE" maxProposition e
    n := n + es.length
  pure n

/-- The most names a slot takes, version 1's bound on a PREREQUISITE's MAX: a BIND that gives
a slot more is refused before anything is filled. -/
def slotNames : Nat := 16

/-- A BIND's slots and their names, as the expansion fills a text with them; a slot given
something else, or more names than any slot takes, fills nothing. -/
def membersOf' (bind : Zone.Value) : List (String × List String) :=
  match bind with
  | .obj ms => ms.filterMap fun (k, v) =>
    match Principia.Provision.strList? v with
    | some ns => if ns.length ≤ slotNames then some (k, ns) else none
    | none => none
  | _ => []

/-- A text's length once each `{SLOT}` in it is filled with the names bound to the slot,
joined by a comma and a space, as the expansion fills it. -/
def filledLength (s : String) (members : List (String × List String)) : Nat :=
  go (s.length + 1) s.toList
where
  /-- The length from here on. -/
  go : Nat → List Char → Nat
    | 0, _ => 0
    | _ + 1, [] => 0
    | f + 1, '{' :: rest =>
      match rest.findIdx? (· == '}') with
      | some j =>
        let ns := (members.lookup (String.ofList (rest.take j))).getD []
        (ns.map String.length).sum + 2 * (ns.length - 1) + go f (rest.drop (j + 1))
      | none => 1 + go f rest
    | f + 1, _ :: rest => 1 + go f rest

/-- A text, as the bounds read it: its ID, its PROPOSITIONs and PREDICATEs, each test
binding's BIND, and the entries of its test bindings' Starting Sets. -/
structure TextRead where
  id : String
  /-- Each TERM's TARGET. -/
  targets : List String
  written : List String
  binds : List Zone.Value
  entries : Nat

/-- A text within the bounds on its test bindings' Starting Sets and on the PROPOSITIONs and
PREDICATEs it writes, before they are filled. A text that does not read, or is longer than
the reader takes, is left to the function, which refuses it as version 1 did. -/
def textWithin (t : String) : Except Refusal (Option TextRead) := do
  if Principia.Provision.maxBytes < t.utf8ByteSize then return none
  let some m := Principia.Provision.readJson t | return none
  let mut written : List String := []
  for (part, field) in [("ASSUMPTIONS", "PROPOSITION"), ("BOUNDARIES", "PREDICATE")] do
    for a in itemsOf (memberOf m part) do
      fieldWithin "a text" field maxProposition a
      if let .str p := memberOf a field then written := p :: written
  let mut n := 0
  let mut binds : List Zone.Value := []
  for b in itemsOf (memberOf m "TEST_BINDINGS") do
    n := n + (← startingSetWithin "a test binding's TPK" (memberOf b "TPK"))
    binds := memberOf b "BIND" :: binds
  let id := match memberOf m "ID" with
    | .str i => i
    | _ => ""
  let targets := (itemsOf (memberOf m "TERMS")).filterMap fun e =>
    match memberOf e "TARGET" with
    | .str x => some x
    | _ => none
  pure (some ⟨id, targets, written.reverse, binds.reverse, n⟩)

/-- The terms a text places under a BIND, each on each name its target is bound to. -/
def placements (r : TextRead) (bind : Zone.Value) : Nat :=
  let ms := membersOf' bind
  (r.targets.map fun x => ((ms.lookup x).getD []).length).sum

/-- What a text writes, filled by a BIND, within `maxProposition` code points. -/
def filledWithin (r : TextRead) (bind : Zone.Value) : Except Refusal Unit := do
  let ms := membersOf' bind
  for p in r.written do
    if maxProposition < filledLength p ms then
      badArgument s!"a PROPOSITION or PREDICATE of {r.id}, its slots filled, holds more than {maxProposition} code points (the Calculator's bound)"

/-- The strings of a list. -/
def stringsOf (v : Zone.Value) : List String :=
  (itemsOf v).filterMap fun | .str s => some s | _ => none

/-- A request within the family's bounds, its members as the functions read them;
`withText`: the text `text` counts with `modules`, as `module_check` reads both, and each
text is filled by its own test bindings; `expands`: the claims fill and place what their
texts write, as the functions that expand a draft read them. -/
def withinBounds (withText expands : Bool) (g : String → Zone.Value) : Except Refusal Unit := do
  listWithin "lines" maxLines (g "lines")
  listWithin "claims" maxClaims (g "claims")
  listWithin "the answer's rounds" maxRounds (g "answer")
  listWithin "carried" maxListed (g "carried")
  listWithin "modified" maxListed (g "modified")
  listWithin "certificates" maxCertificates (g "certificates")
  let used := (itemsOf (g "certificates")).foldl (fun n c => n + (itemsOf (memberOf c "MODULES_USED")).length) 0
  if maxUsed < used then
    badArgument s!"the certificates name more than {maxUsed} Provisions in all (the Calculator's bound)"
  listWithin "modules" maxTexts (g "modules")
  let given := stringsOf (g "modules")
  let own := match g "text" with
    | .str t => [t]
    | _ => []
  if !given.isEmpty || withText then
    let counted := given ++ (if withText then own else [])
    if maxTextsBytes < (counted.map String.utf8ByteSize).sum then
      badArgument s!"the texts hold more than {maxTextsBytes} bytes in all (the Calculator's bound)"
  let mut n := 0
  n := n + (← startingSetWithin "tpk" (g "tpk"))
  n := n + (← startingSetWithin "the draft's TPK" (memberOf (g "draft") "TPK"))
  n := n + (← startingSetWithin "the base's TPK" (memberOf (g "base") "TPK"))
  let mut texts : List TextRead := []
  for t in given ++ own do
    if let some r ← textWithin t then
      n := n + r.entries
      texts := r :: texts
  if maxEntriesInAll < n then
    badArgument s!"the Starting Sets hold more than {maxEntriesInAll} entries in all (the Calculator's bound)"
  -- What the expansions write: each text filled by its own test bindings where they are
  -- expanded (`module_check`), and by each claim's BIND, for every text of its ID.
  if withText then
    for r in texts do
      for b in r.binds do
        filledWithin r b
        if maxPlacements < placements r b then
          badArgument s!"a test binding of {r.id} places more than {maxPlacements} terms (the Calculator's bound)"
  let mut placed := 0
  for c in if expands then itemsOf (g "claims") else [] do
    let cid := match memberOf c "ID" with
      | .str i => i
      | _ => ""
    let mut most := 0
    for r in texts do
      if r.id == cid then
        filledWithin r (memberOf c "BIND")
        most := max most (placements r (memberOf c "BIND"))
    placed := placed + most
  if maxPlacements < placed then
    badArgument s!"the claims place more than {maxPlacements} terms in all (the Calculator's bound)"

/-- A request's members, read and within the bounds. -/
def readWithin (names : List String) (v : Value) : Except Refusal (String → Zone.Value) := do
  let g ← read names v
  withinBounds (names.contains "text" && names.contains "modules")
    (names.contains "draft" || names.contains "base") g
  pure g

/-- The family's functions. -/
def calls : Family := [
  ("catalogue_state", fun v => do
    let g ← readWithin ["lines"] v
    answer Principia.Provision.CatalogueState.parts (Principia.Provision.catalogueState D (g "lines"))),
  ("draft_module_status", fun v => do
    let g ← readWithin ["base", "claims", "modules", "lines"] v
    answer Principia.Provision.DraftStatus.parts
      (Principia.Provision.draftStatus D (g "base") (g "claims") (g "modules") (g "lines"))),
  ("interview_check", fun v => do
    let g ← readWithin ["answer", "claims", "lines", "modules", "carried", "modified"] v
    answer Principia.Provision.InterviewAnswer.parts
      (Principia.Provision.interviewCheck D (g "answer") (g "claims") (g "lines") (g "modules")
        (g "carried") (g "modified"))),
  ("module_bind", fun v => do
    let g ← readWithin ["tpk", "text", "bind", "values"] v
    answer Principia.Provision.Bound.parts
      (Principia.Provision.bind (g "tpk") (g "text") (g "bind") (g "values"))),
  ("module_check", fun v => do
    let g ← readWithin ["text", "act", "date", "lines", "modules"] v
    answer Principia.Provision.Checked.parts
      (Principia.Provision.check D (g "text") (g "act") (g "date") (g "lines") (g "modules"))),
  ("module_digest", fun v => do
    let g ← readWithin ["text"] v
    answer Principia.Provision.digestParts (Principia.Provision.digest D (g "text"))),
  ("module_expand", fun v => do
    let g ← readWithin ["draft", "claims", "modules"] v
    answer Principia.Provision.Rendered.parts
      (Principia.Provision.expand D (g "draft") (g "claims") (g "modules"))),
  ("module_parse", fun v => do
    let g ← readWithin ["text"] v
    answer Principia.Provision.Parsed.parts (Principia.Provision.parse (g "text"))),
  ("module_use_view", fun v => do
    let g ← readWithin ["certificates", "lines"] v
    answer Principia.Provision.UseView.parts
      (Principia.Provision.useView (g "certificates") (g "lines"))),
  ("module_verify", fun v => do
    let g ← readWithin ["base", "claims", "modules", "lines", "draft"] v
    answer Principia.Provision.Verified.parts
      (Principia.Provision.verify D (g "base") (g "claims") (g "modules") (g "lines") (g "draft"))),
  ("not_included_lines", fun v => do
    let g ← readWithin ["answer", "claims", "lines", "modules", "carried", "modified"] v
    answer Principia.Provision.linesParts
      (Principia.Provision.notIncludedLines D (g "answer") (g "claims") (g "lines") (g "modules")
        (g "carried") (g "modified"))),
]

end Principia.Calculator.Provision
