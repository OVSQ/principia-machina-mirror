import Tests.Calculator.Common

/-!
The Calculator's runners of the family `provision`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- A corpus request's members with `text_parts`, v1's runner's packing of a long text, joined
into `text` as v1's `run_case` joins it: each part's string repeated its count of times. -/
def joinTextParts (ms : List (String × Value)) : IO (List (String × Value)) := do
  match ms.lookup "text_parts" with
  | none => pure ms
  | some (.arr parts) =>
    let pieces ← parts.mapM fun
      | .arr [.str s, .int n] => pure (String.join (List.replicate n.toNat s))
      | _ => throw (IO.userError "text_parts: not [string, count] pairs")
    pure ((ms.filter (·.1 != "text_parts")) ++ [("text", .str (String.join pieces))])
  | some _ => throw (IO.userError "text_parts: not a list")

/-- `module_corpus.owed.json`'s cases: each name with the detail its reason is refused with. -/
def provisionOwed : IO (List (String × String)) := do
  match readString (← IO.FS.readFile "vectors/module_corpus.owed.json") with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => do
      let why ← memberStr o "reason"
      let w : Principia.Provision.Owed :=
        if why == "digests" then .digest else .exact (String.ofList (why.toList.drop 7))
      pure (← memberStr o "name", Calculator.Provision.owedDetail w)
    | _ => throw (IO.userError "module_corpus.owed.json: no owed list")
  | _ => throw (IO.userError "module_corpus.owed.json: not an object")

/-- `module_corpus.json`: every case's `args` through `provision <fn>`; the answer is v1's
value, `["OK", ...]` or `["REFUSED", reason]`, compared with the case's `expected` text read
as JSON, through canonical JSON, which writes two values alike only when they are equal. A
case in `module_corpus.owed.json` must be refused `OWED`, its detail the plain words for its
reason, and no other case may be (none is listed). -/
def runProvisionCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let owed ← provisionOwed
  for c in ← v1Cases "vectors/module_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some (.obj args) := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "provision" fn (.obj (← joinTextParts args))
    match owed.lookup name with
    | some detail =>
      let ok := match got with
        | .error r => r.code == .owed && r.detail == detail
        | .ok _ => false
      t ← t.check ok s!"provision {fn} {name}: listed as owed, got {repr (got.toOption.map (·.canonicalJson))}"
    | none =>
      let want ← match readString expected with
        | .ok v => pure v.canonicalJson
        | .error _ => throw (IO.userError s!"{name}: the expected text does not read")
      let ok := match got with
        | .ok v => want.isSome && v.canonicalJson == want
        | .error _ => false
      t ← t.check ok
        s!"provision {fn} {name}: expected {expected}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The provision family's bounds, each at its value and one past it. -/
def provisionBounds : List (String × String × String × Value × Bool) := [
  ("lines at 256", "provision", "catalogue_state", .obj [("lines", valueCopies 256 .null)], false),
  ("lines past 256", "provision", "catalogue_state", .obj [("lines", valueCopies 257 .null)], true),
  ("claims at 8", "provision", "module_expand", .obj [("claims", valueCopies 8 .null)], false),
  ("claims past 8", "provision", "module_expand", .obj [("claims", valueCopies 9 .null)], true),
  ("rounds at 64", "provision", "interview_check", .obj [("answer", valueCopies 64 .null)], false),
  ("rounds past 64", "provision", "interview_check", .obj [("answer", valueCopies 65 .null)], true),
  ("carried at 64", "provision", "not_included_lines", .obj [("carried", valueCopies 64 .null)], false),
  ("carried past 64", "provision", "not_included_lines", .obj [("carried", valueCopies 65 .null)], true),
  ("modified at 64", "provision", "interview_check", .obj [("modified", valueCopies 64 .null)], false),
  ("modified past 64", "provision", "interview_check", .obj [("modified", valueCopies 65 .null)], true),
  ("certificates at 1024", "provision", "module_use_view", .obj [("certificates", valueCopies 1024 .null)], false),
  ("certificates past 1024", "provision", "module_use_view", .obj [("certificates", valueCopies 1025 .null)], true),
  ("Provisions used at 4096", "provision", "module_use_view",
    .obj [("certificates", .arr [.obj [("MODULES_USED", valueCopies 4096 .null)]])], false),
  ("Provisions used past 4096", "provision", "module_use_view",
    .obj [("certificates", .arr [.obj [("MODULES_USED", valueCopies 2048 .null)],
      .obj [("MODULES_USED", valueCopies 2049 .null)]])], true),
  ("texts at 8", "provision", "module_verify", .obj [("modules", valueCopies 8 (.str "x"))], false),
  ("texts past 8", "provision", "module_verify", .obj [("modules", valueCopies 9 (.str "x"))], true),
  ("texts at 65536 bytes", "provision", "draft_module_status",
    .obj [("modules", .arr [.str (chars 65536 'a')])], false),
  ("texts past 65536 bytes", "provision", "draft_module_status",
    .obj [("modules", .arr [.str (chars 65537 'a')])], true),
  ("texts with the checked text at 65536 bytes", "provision", "module_check",
    .obj [("text", .str (chars 32768 'a')), ("modules", .arr [.str (chars 32768 'a')])], false),
  ("texts with the checked text past 65536 bytes", "provision", "module_check",
    .obj [("text", .str (chars 32769 'a')), ("modules", .arr [.str (chars 32768 'a')])], true),
  ("a text alone past 65536 bytes, outside the texts' bound", "provision", "module_parse",
    .obj [("text", .str (chars 65537 'a'))], false),
  ("DOF at 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["DOF"] 64)], false),
  ("DOF past 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["DOF"] 65)], true),
  ("BOUNDARY past 64", "provision", "module_bind", .obj [("tpk", entriesTpk ["BOUNDARY"] 65)], true),
  ("a draft's LAW past 64", "provision", "module_expand",
    .obj [("draft", .obj [("TPK", entriesTpk ["LAW"] 65)])], true),
  ("a base's CONSTRAINT past 64", "provision", "draft_module_status",
    .obj [("base", .obj [("TPK", entriesTpk ["CONSTRAINT"] 65)])], true),
  ("a test binding's ASSUMPTION past 64", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("TEST_BINDINGS", .arr [.obj [("TPK", entriesTpk ["ASSUMPTION"] 65)]])]))], true),
  ("entries in all at 1024", "provision", "module_verify", entriesInAll 256, false),
  ("entries in all past 1024", "provision", "module_verify", entriesInAll 257, true),
  ("a REFS at 128", "provision", "module_bind",
    .obj [("tpk", .obj [("LAW", .arr [.obj [("REFS", valueCopies 128 (.str "x"))]])])], false),
  ("a REFS past 128", "provision", "module_bind",
    .obj [("tpk", .obj [("LAW", .arr [.obj [("REFS", valueCopies 129 (.str "x"))]])])], true),
  ("an EQUATION at 16384", "provision", "module_bind", fieldTpk "LAW" "EQUATION" 16384, false),
  ("an EQUATION past 16384", "provision", "module_bind", fieldTpk "LAW" "EQUATION" 16385, true),
  ("a CONDITION at 16384", "provision", "module_bind", fieldTpk "BOUNDARY" "CONDITION" 16384, false),
  ("a CONDITION past 16384", "provision", "module_bind", fieldTpk "BOUNDARY" "CONDITION" 16385, true),
  ("a PROPOSITION at 256", "provision", "module_bind", fieldTpk "ASSUMPTION" "PROPOSITION" 256, false),
  ("a PROPOSITION past 256", "provision", "module_bind", fieldTpk "ASSUMPTION" "PROPOSITION" 257, true),
  ("a PREDICATE at 256", "provision", "module_bind", fieldTpk "BOUNDARY" "PREDICATE" 256, false),
  ("a PREDICATE past 256", "provision", "module_bind", fieldTpk "BOUNDARY" "PREDICATE" 257, true),
  ("a text's PROPOSITION at 256", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str (chars 256 'p'))]])]))], false),
  ("a text's PROPOSITION past 256", "provision", "module_parse",
    .obj [("text", jsonText (.obj [("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str (chars 257 'p'))]])]))], true),
  ("a text's PREDICATE past 256", "provision", "module_digest",
    .obj [("text", jsonText (.obj [("BOUNDARIES", .arr [.obj [("PREDICATE", .str (chars 257 'p'))]])]))], true),
  ("a PROPOSITION filled to 256", "provision", "module_expand", filledRequest 256, false),
  ("a PROPOSITION filled past 256", "provision", "module_expand", filledRequest 257, true),
  ("a PROPOSITION filled by a test binding to 256", "provision", "module_check", filledCheck 256, false),
  ("a PROPOSITION filled by a test binding past 256", "provision", "module_check", filledCheck 257, true),
  ("placements at 64", "provision", "module_expand", placedRequest 4 16, false),
  ("placements past 64", "provision", "module_expand", placedRequest 5 13, true),
  ("a test binding's placements at 64", "provision", "module_check", placedCheck 4 16, false),
  ("a test binding's placements past 64", "provision", "module_check", placedCheck 5 13, true),
  ("a slot given more names than any slot takes places none", "provision", "module_expand",
    placedRequest 16 17, false),
  ("the interview fills nothing", "provision", "interview_check", filledRequest 257, false)]

/-- The provision family's bounds: a request at a bound is not refused by it, one past it is,
with the bound named. -/
def runProvisionBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for (what, family, fn, request, refused) in provisionBounds do
    let got := respondTo family fn request
    t ← t.check (boundRefusal got == refused)
      s!"{family} {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}: {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Provision

open Tests.Calculator

/-- The family `provision`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc provision (module_corpus)", runProvisionCalls),
  ("pcalc provision bounds", runProvisionBounds),
]

end Tests.Calculator.Provision
