import Tests.Calculator.Common

/-!
The Calculator's runners of the family `permissions`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- A `permits` request of the family. -/
def permitsRequest (asker pageClass op : String) (context : List String) : Value :=
  .obj [("asker", .str asker), ("class", .str pageClass), ("op", .str op),
    ("context", .arr (context.map .str))]

/-- A case's context, an object of `permissions.json`, as the word arm's context words. -/
def contextWordsOf (j : Json) : IO (List String) := do
  match j.getObjVal? "context" with
  | .error _ => pure []
  | .ok ctx =>
    let some kvs := (match ctx with | .obj kvs => some kvs | _ => none)
      | throw (IO.userError "permissions: a context is not an object")
    let mut out : List String := []
    for (k, _) in kvs.toArray do
      match k, ctx.getObjValD k with
      | "policy", .str w => out := out ++ [w]
      | "listed", .bool b => if b then out := out ++ ["LISTED"]
      | "named", .str w => out := out ++ ["NAMED", w]
      | "queue_head", .bool b => if b then out := out ++ ["QUEUE HEAD"]
      | "reauthenticated", .bool b => if b then out := out ++ ["REAUTHENTICATED"]
      | _, _ => throw (IO.userError s!"permissions: a context member {k} that does not read")
    pure out

/-- The request a word of an enumeration of `permissions.json` is given in: an asker's,
a page class's, an operation's, a policy's or a DOSSIER READ's place. -/
def wordRequest (enum w : String) : Option Value :=
  match enum with
  | "Actor" | "Role" | "LockState" | "AccountClass" => some (permitsRequest w "SPECIFICATION" "READ" [])
  | "PageClass" => some (permitsRequest "PUBLIC" w "READ" [])
  | "Op" => some (permitsRequest "PUBLIC" "SPECIFICATION" w [])
  | "AccessPolicy" => some (permitsRequest "PUBLIC" "SPECIFICATION" "READ" [w])
  | "DossierRead" => some (permitsRequest "PUBLIC" "SPECIFICATION" "READ" ["NAMED", w])
  | _ => none

/-- The answer `permits` gives for a verdict. -/
def verdictWord (b : Bool) : Option String :=
  (Value.str (if b then "PERMITTED" else "REFUSED")).canonicalJson

/-- `permissions.json`: every case through `permissions`. A cell is one check per operation;
a word must read exactly when the corpus says so, in its place in a `permits` request; an
enumeration's members are the domain's lists for the asker, the page class and the operation,
and each reads in its place for the others; a request of the word arm is the same words in a
`permits` request, refused `BAD_ARGUMENT` where the word arm reads none. The cases not
given to the family are `AccountClass`'s members (`USER` is the class of an account that asks
in a role, and no asker's word) and the `group` cases (a role's MediaWiki group is the wiki's
name for it, no word of a request). Then the domain's 96 contexts read as 96 distinct contexts,
every one Custos can know. -/
def runPermissionsCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases ← arr (← readJson "vectors/permissions.json")
  let call := respondTo "permissions" "permits"
  let domain ← match respondTo "permissions" "domain" (.obj []) with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"permissions domain: refused {r.detail}")
  let listOf (k : String) : List String := match member domain k with
    | some (.arr xs) => xs.filterMap fun | .str s => some s | _ => none
    | _ => []
  let mut given := 0
  for c in cases do
    let fn ← str c "function"
    match fn with
    | "wire" =>
      let e ← str c "enum"
      match c.getObjValAs? (Array String) "members" with
      | .ok ms =>
        let ms := ms.toList
        match e with
        | "Actor" => t ← t.check (listOf "askers" == ms) s!"permissions domain askers: {listOf "askers"}"
        | "PageClass" => t ← t.check (listOf "classes" == ms) s!"permissions domain classes: {listOf "classes"}"
        | "Op" => t ← t.check (listOf "ops" == ms) s!"permissions domain ops: {listOf "ops"}"
        | "AccountClass" => continue
        | _ =>
          let ok := ms.all fun w => match wordRequest e w with
            | some r => (call r).toOption.isSome
            | none => false
          t ← t.check ok s!"permissions {e} members {ms}: a member does not read in its place"
        given := given + 1
      | .error _ =>
        let w ← str c "word"
        let reads ← IO.ofExcept (c.getObjValAs? Bool "reads")
        let some r := wordRequest e w | throw (IO.userError s!"permissions: unknown enumeration {e}")
        let got := call r
        t ← t.check ((got.toOption.isSome == reads) && (reads || refusalOf got == some .badArgument))
          s!"permissions {e} {repr w}: expected reads {reads}, got {repr (canonOf got)}"
        given := given + 1
    | "permits" =>
      let a ← str c "actor"
      let k ← str c "class"
      let ctx ← contextWordsOf c
      match c.getObjValAs? (Array String) "permitted" with
      | .ok listed =>
        for op in (WireWord.members : List Principia.Permissions.Op) do
          let o := WireWord.toWire op
          let got := canonOf (call (permitsRequest a k o ctx))
          t ← t.check (got == verdictWord (listed.contains o))
            s!"permissions {a} on {k} {o} in {ctx}: got {repr got}"
      | .error _ =>
        let o ← str c "op"
        let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
        let got := canonOf (call (permitsRequest a k o ctx))
        t ← t.check (got == verdictWord want) s!"permissions {a} on {k} {o} in {ctx}: got {repr got}"
      given := given + 1
    | "request" =>
      let args := (← IO.ofExcept (c.getObjValAs? (Array String) "args")).toList
      let named : List (String × Value) :=
        (["asker", "class", "op"].zip args).map fun (k, w) => (k, Value.str w)
      let context : List (String × Value) :=
        if args.length < 3 then [] else [("context", .arr ((args.drop 3).map .str))]
      let r := Value.obj (named ++ context)
      let got := call r
      match c.getObjVal? "request" with
      | .ok .null =>
        t ← t.check (refusalOf got == some .badArgument)
          s!"permissions request {args}: expected BAD_ARGUMENT, got {repr (canonOf got)}"
      | _ =>
        let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
        t ← t.check (canonOf got == verdictWord want) s!"permissions request {args}: got {repr (canonOf got)}"
      given := given + 1
    | "group" => continue
    | f => throw (IO.userError s!"permissions: unknown function {f}")
  -- The domain's contexts: 96, distinct, every context Custos can know.
  let contexts : List (List String) := match member domain "contexts" with
    | some (.arr xs) => xs.map fun
      | .arr ws => ws.filterMap fun | .str s => some s | _ => none
      | _ => []
    | _ => []
  let read := contexts.filterMap (Principia.Permissions.readContext · {})
  let mut every : List Principia.Permissions.PageContext := []
  for policy in [none, some Principia.Permissions.AccessPolicy.openAccess,
      some Principia.Permissions.AccessPolicy.closedAccess] do
    for listed in [false, true] do
      for named in [none, some Principia.Parameters.DossierRead.userOnly,
          some Principia.Parameters.DossierRead.userAndAgent,
          some Principia.Parameters.DossierRead.neither] do
        for head in [false, true] do
          for reauth in [false, true] do
            let ctx : Principia.Permissions.PageContext :=
              { policy := policy, onAccessList := listed, namedAccount := named,
                atQueueHead := head, reauthenticated := reauth }
            every := ctx :: every
  t ← t.check (contexts.length == 96 && read.length == 96 && read.eraseDups.length == 96 &&
      every.all read.contains)
    s!"permissions domain: {contexts.length} contexts, {read.length} read, {read.eraseDups.length} distinct"
  -- The table (`table {}`): its contexts the domain's; every cell of
  -- permissions.json's `permits` cases read from it; and a sample of 2,000 of its 207,360
  -- cells against `permits`, spread over the whole table by a stride coprime with its size.
  let table ← match respondTo "permissions" "table" (.obj []) with
    | .ok v => pure v
    | .error r => throw (IO.userError s!"permissions table: refused {r.detail}")
  let tableContexts : List (List String) := match member table "contexts" with
    | some (.arr xs) => xs.map fun
      | .arr ws => ws.filterMap fun | .str s => some s | _ => none
      | _ => []
    | _ => []
  t ← t.check (tableContexts == contexts) "permissions table: its contexts are not the domain's"
  let tableCells := (member table "cells").getD .null
  let readTable := tableContexts.map (Principia.Permissions.readContext · {})
  let cellAt (a k o : String) (ix : Nat) : Option String := do
    let byClass ← member tableCells a
    let byOp ← member byClass k
    match ← member byOp o with
    | .arr vs => match vs[ix]? with
      | some (.str w) => some w
      | _ => none
    | _ => none
  let cellOf (a k o : String) (ws : List String) : Option String := do
    let ctx ← Principia.Permissions.readContext ws {}
    let ix ← readTable.findIdx? (· == some ctx)
    cellAt a k o ix
  let word (b : Bool) : String := if b then "PERMITTED" else "REFUSED"
  let mut tableCases := 0
  for c in cases do
    if (← str c "function") != "permits" then continue
    let a ← str c "actor"
    let k ← str c "class"
    let ctx ← contextWordsOf c
    match c.getObjValAs? (Array String) "permitted" with
    | .ok listed =>
      for op in (WireWord.members : List Principia.Permissions.Op) do
        let o := WireWord.toWire op
        t ← t.check (cellOf a k o ctx == some (word (listed.contains o)))
          s!"permissions table: {a} on {k} {o} in {ctx}: got {repr (cellOf a k o ctx)}"
    | .error _ =>
      let o ← str c "op"
      let want ← IO.ofExcept (c.getObjValAs? Bool "expected")
      t ← t.check (cellOf a k o ctx == some (word want))
        s!"permissions table: {a} on {k} {o} in {ctx}: got {repr (cellOf a k o ctx)}"
    tableCases := tableCases + 1
  let askers := listOf "askers"
  let classes := listOf "classes"
  let ops := listOf "ops"
  let size := askers.length * classes.length * ops.length * contexts.length
  t ← t.check (size == 207360) s!"permissions table: {size} cells, not 207,360"
  for n in List.range 2000 do
    let i := (n * 9221) % size
    let ix := i % contexts.length
    let io := (i / contexts.length) % ops.length
    let ic := (i / (contexts.length * ops.length)) % classes.length
    let ia := i / (contexts.length * ops.length * classes.length)
    match askers[ia]?, classes[ic]?, ops[io]?, contexts[ix]? with
    | some a, some k, some o, some ws =>
      let want := (call (permitsRequest a k o ws)).toOption
      t ← t.check (want.isSome && (cellAt a k o ix).map Value.str == want)
        s!"permissions table: cell {i} ({a} on {k} {o} in {ws}): got {repr (cellAt a k o ix)}"
    | _, _, _, _ => t ← t.check false s!"permissions table: cell {i} out of the domain"
  IO.println s!"pcalc permissions: {given} of {cases.length} cases of permissions.json through the family (AccountClass's members and the groups aside), and the domain's 96 contexts; the table: {tableCases} cases of permissions.json and 2000 of its {size} cells against permits"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Permissions

open Tests.Calculator

/-- The family `permissions`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc permissions (permissions)", runPermissionsCalls),
]

end Tests.Calculator.Permissions
