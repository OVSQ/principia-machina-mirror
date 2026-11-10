import Principia
import Lean.Data.Json

/-!
The runner for `vectors/permissions.json`: `Principia.Permissions.permits`, the wire
words of its enumerations, and the request `pcalc permits` reads. `Lean.Json` reads
inputs only (collision register R5).

Case shapes:
* `{"function": "wire", "enum", "members"}`: the enumeration's wire words in order, each
  spelled as R1 asks and read back; `{"function": "wire", "enum", "word", "reads"}`: a
  word that must not read (or must).
* `{"function": "permits", "actor", "class", "context"?, "permitted"}`: one table cell;
  every operation is checked, permitted exactly when listed.
* `{"function": "permits", "actor", "class", "op", "context"?, "expected"}`: one operation.
* `{"function": "group", "role", "group"}`: the role's MediaWiki group, `Role.group`;
  every role has one such case.
* `{"function": "request", "args", "request", "expected"?}`: the request `pcalc permits`
  reads from those words (`{"actor", "class", "op", "context"}`, or `null` when they do
  not read as one) and its verdict, a Bool; the answer printed is `PERMITTED` exactly
  when the verdict is true.

A context is an object of optional fields: `policy` (`OPEN` or `CLOSED`), `listed`,
`named` (a DOSSIER READ word), `queue_head`, `reauthenticated`; any other key is a defect
of the corpus.
-/

namespace Tests.Permissions

open Lean Principia Principia.Permissions
open Principia.Parameters (DossierRead)

/-- Passing and failing checks. -/
structure Count where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr with what was checked. -/
def Count.check (t : Count) (ok : Bool) (what : String) : IO Count := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL permissions: {what}"
    return { t with fail := t.fail + 1 }

def jStr (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)
def jBool (j : Json) (k : String) : IO Bool := IO.ofExcept (j.getObjValAs? Bool k)
def jStrs (j : Json) (k : String) : IO (List String) := do
  return (← IO.ofExcept (j.getObjValAs? (Array String) k)).toList

/-- Read a wire word into its enumeration; a word that does not read is a defect of the
corpus. -/
def word (α : Type) [WireWord α] (s : String) : IO α :=
  match (WireWord.ofWire? s : Option α) with
  | some a => pure a
  | none => throw (IO.userError s!"permissions: not a wire word: {repr s}")

def wire {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a

/-- An enumeration's wire map, read through the class. -/
structure WireOps where
  members : List String
  read : String → Option String

def wireOps (α : Type) [WireWord α] : WireOps where
  members := (WireWord.members : List α).map WireWord.toWire
  read s := (WireWord.ofWire? s : Option α).map WireWord.toWire

def wireOpsFor : String → Option WireOps
  | "AccountClass" => some (wireOps AccountClass)
  | "Role" => some (wireOps Role)
  | "LockState" => some (wireOps LockState)
  | "Actor" => some (wireOps Actor)
  | "Op" => some (wireOps Op)
  | "PageClass" => some (wireOps PageClass)
  | "AccessPolicy" => some (wireOps AccessPolicy)
  | "DossierRead" => some (wireOps DossierRead)
  | _ => none

/-- R1's spelling for a wire word: not empty; capitals, digits, `_` and single inner
spaces only. -/
def r1Spelling (s : String) : Bool :=
  !s.isEmpty &&
    s.all (fun ch => ch.isUpper || ch.isDigit || ch == '_' || ch == ' ') &&
    !s.startsWith " " && !s.endsWith " " && (s.splitOn "  ").length == 1

/-- The context of a case: absent, the default (every field refusing). -/
def readCase (c : Json) : IO PageContext := do
  match c.getObjVal? "context" with
  | .error _ => return {}
  | .ok j =>
    let some fields := (match j with | .obj kvs => some kvs | _ => none)
      | throw (IO.userError "permissions: a context is an object")
    let mut ctx : PageContext := {}
    for (k, _) in fields.toArray do
      match k with
      | "policy" => ctx := { ctx with policy := some (← word AccessPolicy (← jStr j k)) }
      | "listed" => ctx := { ctx with onAccessList := ← jBool j k }
      | "named" => ctx := { ctx with namedAccount := some (← word DossierRead (← jStr j k)) }
      | "queue_head" => ctx := { ctx with atQueueHead := ← jBool j k }
      | "reauthenticated" => ctx := { ctx with reauthenticated := ← jBool j k }
      | other => throw (IO.userError s!"permissions: unknown context key {other}")
    return ctx

/-- Run the corpus: (passing, failing) checks. -/
def run : IO (Nat × Nat) := do
  let text ← IO.FS.readFile "vectors/permissions.json"
  let json ← IO.ofExcept (Json.parse text)
  let cases ← IO.ofExcept json.getArr?
  let mut t : Count := {}
  let mut cells : List (String × String) := []
  let mut groups : List String := []
  for c in cases do
    match ← jStr c "function" with
    | "wire" =>
      let e ← jStr c "enum"
      let some ops := wireOpsFor e | throw (IO.userError s!"permissions: unknown enumeration {e}")
      match c.getObjValAs? (Array String) "members" with
      | .ok ms =>
        let ms := ms.toList
        t ← t.check (ops.members == ms) s!"{e} members: expected {repr ms}, got {repr ops.members}"
        t ← t.check (ops.members.eraseDups.length == ops.members.length) s!"{e} members repeat a word"
        for w in ops.members do
          t ← t.check (r1Spelling w) s!"{e} {repr w} is not spelled as R1 asks"
        for w in ms do
          t ← t.check (ops.read w == some w) s!"{e} {repr w} does not read back"
      | .error _ =>
        let w ← jStr c "word"
        let reads ← jBool c "reads"
        let got := ops.read w
        t ← t.check (got.isSome == reads && got.all (· == w))
          s!"{e} {repr w}: expected reads {reads}, got {repr got}"
    | "permits" =>
      let a ← word Actor (← jStr c "actor")
      let k ← word PageClass (← jStr c "class")
      let ctx ← readCase c
      let at_ := s!"{wire a} on {wire k} in {repr ctx}"
      match c.getObjValAs? (Array String) "permitted" with
      | .ok listed =>
        cells := (wire a, wire k) :: cells
        let listed := listed.toList
        for w in listed do
          discard <| word Op w
        t ← t.check (listed.eraseDups.length == listed.length) s!"{at_}: the list repeats"
        for op in (WireWord.members : List Op) do
          let want := listed.contains (wire op)
          t ← t.check (permits a k op ctx == want) s!"{at_}: {wire op} expected {want}"
      | .error _ =>
        let op ← word Op (← jStr c "op")
        let want ← jBool c "expected"
        t ← t.check (permits a k op ctx == want) s!"{at_}: {wire op} expected {want}"
    | "group" =>
      let r ← word Role (← jStr c "role")
      let g ← jStr c "group"
      groups := wire r :: groups
      t ← t.check (r.group == g) s!"group of {wire r}: expected {repr g}, got {repr r.group}"
    | "request" =>
      let args ← jStrs c "args"
      let r ← IO.ofExcept (c.getObjVal? "request")
      match r with
      | .null =>
        t ← t.check (Request.parse? args).isNone s!"request {repr args}: expected no request"
      | _ =>
        let want : Request := {
          actor := ← word Actor (← jStr r "actor")
          pageClass := ← word PageClass (← jStr r "class")
          op := ← word Op (← jStr r "op")
          context := ← readCase r }
        let got := Request.parse? args
        t ← t.check (got == some want) s!"request {repr args}: expected {repr want}, got {repr got}"
        let verdict ← jBool c "expected"
        t ← t.check (permits want.actor want.pageClass want.op want.context == verdict)
          s!"request {repr args}: verdict expected {verdict}"
        t ← t.check (want.answer == if verdict then "PERMITTED" else "REFUSED")
          s!"request {repr args}: answer {repr want.answer}"
    | other => throw (IO.userError s!"permissions: unknown function {other}")
  -- Every asker on every page class has a cell case.
  for k in (WireWord.members : List PageClass) do
    for a in (WireWord.members : List Actor) do
      t ← t.check (cells.contains (wire a, wire k)) s!"no cell case for {wire a} on {wire k}"
  -- Every role has a group case.
  for r in (WireWord.members : List Role) do
    t ← t.check (groups.contains (wire r)) s!"no group case for {wire r}"
  return (t.pass, t.fail)

end Tests.Permissions
