import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/module_corpus.json` (v1's `tpc_module` 0.1.1, corpus 0.2.1, 418 cases)
against `Principia.Provision`.

Each case's arguments are read into `Principia.Zone.Value` as v1's JSON reader gives them
(`Tests.Zone.toValue`; a text given as `text_parts` is joined first, as v1's `run_case` joins
it), the function is run, and its answer is compared with the case's `expected` text: that
text is JSON, read into the canonical writers' values (`Principia.Canonical.Value`), and the
two values are compared through their canonical JSON, which writes two values alike only when
they are equal (strings by `Canonical.quote`, which is injective).

Every case runs twice:
* as the Calculator answers it, its digests SHA-256 (`DigestHook.calculator`,
  `Principia.Sha256`; decision D2, option 1): an answer must be v1's; an owed answer must be
  listed with its reason in `vectors/module_corpus.owed.json`, and every case listed there must
  come out owed for that reason (none is);
* with v1's SHA-256 values for the very preimages the Calculator computes
  (`vectors/module_corpus.digests.json`, written by `scripts/provision_digests.py` with v1's own
  `tpc_module.py`): every case not owed for another reason must then be answered, and as v1
  answered. A preimage that is not in the table stops the case owed and fails it, so the table
  also checks that every preimage the Calculator computes is the one v1 digested.

The table itself is checked too: the Calculator's SHA-256 of each of its preimages must be v1's
value for it, exactly.

Fault checks run first: the comparison must refuse a changed expectation, and the owed list's
check must refuse a list missing or adding a case.
-/

open Lean
open Principia
open Principia.Provision

namespace Tests.Provision

/-! ## Reading the corpus -/

/-- An argument, as v1's JSON reader gives it; absent is `null`. -/
def arg (args : Json) (k : String) : Zone.Value :=
  match args.getObjVal? k with
  | .ok j => Tests.Zone.toValue j
  | .error _ => .null

/-- v1's `_text_arg`: `text_parts` joined, each part repeated, or `text`. -/
def textArg (args : Json) : IO Zone.Value := do
  match args.getObjVal? "text_parts" with
  | .ok (.arr parts) =>
    let mut out := ""
    for p in parts do
      let s ← IO.ofExcept ((← IO.ofExcept (p.getArrVal? 0)).getStr?)
      let n ← IO.ofExcept ((← IO.ofExcept (p.getArrVal? 1)).getNat?)
      out := out ++ String.join (List.replicate n s)
    pure (.str out)
  | _ => pure (arg args "text")

/-- An expected text, read as JSON into the canonical writers' values: strings, integers and
lists only, as every answer of this corpus is. -/
partial def expectedValue : Json → Option Canonical.Value
  | .str s => some (.str s)
  | .num n => if n.exponent == 0 then some (.int n.mantissa) else none
  | .arr xs => (xs.toList.mapM expectedValue).map .arr
  | _ => none

/-- A value's canonical JSON, for comparison. -/
def textOf (v : Canonical.Value) : String := (v.canonicalJson).getD "<no canonical JSON>"

/-- A case's answer: v1's value, or the owed reason. -/
abbrev Outcome := Except Owed Canonical.Value

/-- An answer as an outcome. -/
def outcome {α : Type} (f : α → List Canonical.Value) (a : Answer α) : Outcome :=
  match a with
  | .owed w => .error w
  | a => .ok ((a.toValue? f).getD (.str "<none>"))

/-- Run one case under a digest hook. -/
def runCase (D : DigestHook) (fn : String) (args : Json) : IO Outcome := do
  let a := arg args
  match fn with
  | "module_parse" => pure (outcome Parsed.parts (parse (← textArg args)))
  | "module_digest" => pure (outcome digestParts (digest D (← textArg args)))
  | "module_bind" => pure (outcome Bound.parts (bind (a "tpk") (a "text") (a "bind") (a "values")))
  | "module_expand" => pure (outcome Rendered.parts (expand D (a "draft") (a "claims") (a "modules")))
  | "module_verify" =>
    pure (outcome Verified.parts (verify D (a "base") (a "claims") (a "modules") (a "lines") (a "draft")))
  | "interview_check" =>
    pure (outcome InterviewAnswer.parts
      (interviewCheck D (a "answer") (a "claims") (a "lines") (a "modules") (a "carried") (a "modified")))
  | "not_included_lines" =>
    pure (outcome linesParts
      (notIncludedLines D (a "answer") (a "claims") (a "lines") (a "modules") (a "carried") (a "modified")))
  | "catalogue_state" => pure (outcome CatalogueState.parts (catalogueState D (a "lines")))
  | "module_check" =>
    pure (outcome Checked.parts (check D (a "text") (a "act") (a "date") (a "lines") (a "modules")))
  | "draft_module_status" =>
    pure (outcome DraftStatus.parts (draftStatus D (a "base") (a "claims") (a "modules") (a "lines")))
  | "module_use_view" => pure (outcome UseView.parts (useView (a "certificates") (a "lines")))
  | other => throw (IO.userError s!"unknown function {other}")

/-! ## The digest table -/

/-- v1's SHA-256 values, by preimage. -/
def loadDigests : IO (List (String × String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/module_corpus.digests.json"))
  let rows ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "digests")).getArr?)
  rows.toList.mapM fun r => do
    pure ((← IO.ofExcept (r.getObjValAs? String "preimage")), (← IO.ofExcept (r.getObjValAs? String "sha256")))

/-- The table as a digest hook. -/
def tableHook (rows : List (String × String)) : DigestHook := ⟨fun p => rows.lookup p⟩

/-! ## The run -/

/-- The owed list: each listed case's name and reason. -/
def loadOwed : IO (List (String × String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/module_corpus.owed.json"))
  let rows ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "owed")).getArr?)
  rows.toList.mapM fun r => do
    pure ((← IO.ofExcept (r.getObjValAs? String "name")), (← IO.ofExcept (r.getObjValAs? String "reason")))

/-- The owed cases are exactly the listed ones, each for its listed reason. -/
def owedMatches (found listed : List (String × String)) : Bool :=
  found.all listed.contains && listed.all found.contains

/-- A value with its last string changed: a mutated expectation. -/
def mutateLast : Canonical.Value → Option Canonical.Value
  | .str s => some (.str (s ++ "?"))
  | .arr xs =>
    let rec go : List Canonical.Value → Option (List Canonical.Value)
      | [] => none
      | x :: rest => match go rest with
        | some rest' => some (x :: rest')
        | none => (mutateLast x).map (· :: rest)
    (go xs).map .arr
  | _ => none

/-- A list with its last two items swapped, where they differ. -/
def swapLast : Canonical.Value → Option Canonical.Value
  | .arr xs =>
    match xs.reverse with
    | a :: b :: rest => if textOf a == textOf b then none else some (.arr ((b :: a :: rest).reverse))
    | _ => none
  | _ => none

/-- The fault checks: a changed or reordered expectation is refused; an owed list missing a
case or adding one is refused; a digest the table lacks leaves the case owed. -/
def faultChecks (cases : Array Json) (table : DigestHook) (listed : List (String × String)) :
    IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let mut mutated := 0
  for c in cases do
    if mutated ≥ 12 then break
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let args ← IO.ofExcept (c.getObjVal? "args")
    let expText ← IO.ofExcept (c.getObjValAs? String "expected")
    let some exp := (Json.parse expText).toOption.bind expectedValue | continue
    let .ok v ← runCase table fn args | continue
    if textOf v != textOf exp then continue
    for bad in [mutateLast exp, swapLast exp] do
      if let some b := bad then
        mutated := mutated + 1
        if textOf v != textOf b then pass := pass + 1
        else
          IO.eprintln s!"FAIL provision fault check: a changed expectation passed: {textOf b}"
          fail := fail + 1
  -- with no case owed, a synthetic one stands for the list
  let found := if listed.isEmpty then [("X98 a synthetic owed case", "digests")] else listed
  match found with
  | _ :: rest =>
    for (what, l) in [("missing a case", rest), ("adding a case", found ++ [("X99 no such case", "digests")])] do
      if owedMatches found l then
        IO.eprintln s!"FAIL provision fault check: an owed list {what} passed"
        fail := fail + 1
      else pass := pass + 1
  | [] =>
    IO.eprintln "FAIL provision fault check: no owed list to mutate"
    fail := fail + 1
  -- a digest the table lacks leaves the case owed, never answered
  match cases.toList.find? (fun c => (c.getObjValAs? String "fn").toOption == some "module_digest") with
  | some c =>
    let args ← IO.ofExcept (c.getObjVal? "args")
    match ← runCase (tableHook []) "module_digest" args with
    | .error .digest => pass := pass + 1
    | _ =>
      IO.eprintln "FAIL provision fault check: a digest the table lacks was answered"
      fail := fail + 1
  | none => fail := fail + 1
  if mutated == 0 then fail := fail + 1
  return (pass, fail)

/-- The kind derived from a Provision's text, against version 1's record of the first
catalogue: the kind read from each first-catalogue text in the corpus (`Provision.kind`: a
Convention writes no term and binds no slot) is the kind version 1 records for it
(`kindOf?`); all four are found. -/
def kindChecks (cases : Array Json) : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let mut seen : List String := []
  for c in cases do
    unless (c.getObjValAs? String "fn").toOption == some "module_parse" do continue
    let args ← IO.ofExcept (c.getObjVal? "args")
    let .ok M := parseText (← textArg args) | continue
    let some k := kindOf? M.id | continue
    if seen.contains M.id then continue
    seen := seen ++ [M.id]
    if M.kind == k then pass := pass + 1
    else
      IO.eprintln s!"FAIL provision kinds: {M.id} is recorded {k.word}, but its text reads {M.kind.word}"
      fail := fail + 1
  if (firstCatalogue.map (·.1)).all seen.contains then pass := pass + 1
  else
    IO.eprintln s!"FAIL provision kinds: the first catalogue's texts not all found ({seen})"
    fail := fail + 1
  return (pass, fail)

/-- Run the corpus: passing and failing checks. -/
def runProvision : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/module_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "cases")).getArr?)
  let rows ← loadDigests
  let table := tableHook rows
  let listed ← loadOwed
  let (fp, ff) ← faultChecks cases table listed
  let (kp, kf) ← kindChecks cases
  let mut pass := fp + kp
  let mut fail := ff + kf
  -- v1's digests reproduced: the Calculator's SHA-256 of each preimage is v1's value
  let mut reproduced := 0
  for (pre, v1) in rows do
    let mine := Digest.ofPreimage pre
    if mine == v1 then
      pass := pass + 1
      reproduced := reproduced + 1
    else
      IO.eprintln s!"FAIL provision digest table: SHA-256 {mine}, v1 {v1}, of {repr pre}"
      fail := fail + 1
  let mut owed : List (String × String) := []
  let mut answered := 0
  let mut withTable := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let args ← IO.ofExcept (c.getObjVal? "args")
    let expText ← IO.ofExcept (c.getObjValAs? String "expected")
    let some exp := (Json.parse expText).toOption.bind expectedValue
      | throw (IO.userError s!"provision {name}: the expected text does not read")
    let want := textOf exp
    -- the Calculator, its digests SHA-256
    match ← runCase DigestHook.calculator fn args with
    | .ok v =>
      if textOf v == want then
        pass := pass + 1
        answered := answered + 1
      else
        IO.eprintln s!"FAIL provision {name}:\n  expected {want}\n  got      {textOf v}"
        fail := fail + 1
    | .error w => owed := owed ++ [(name, w.word)]
    -- with v1's SHA-256 values
    match ← runCase table fn args with
    | .ok v =>
      if textOf v == want then
        pass := pass + 1
        withTable := withTable + 1
      else
        IO.eprintln s!"FAIL provision {name} (v1's digests):\n  expected {want}\n  got      {textOf v}"
        fail := fail + 1
    | .error .digest =>
      IO.eprintln s!"FAIL provision {name} (v1's digests): a preimage the Calculator computes is not one v1 digested"
      fail := fail + 1
    | .error _ => pure ()
  if owedMatches owed listed then pass := pass + 1
  else
    IO.eprintln s!"FAIL provision: the owed cases are not the listed ones\n  owed   {owed}\n  listed {listed}"
    fail := fail + 1
  IO.println s!"provision: {answered} of {cases.size} answered as v1 answered, {owed.length} owed; {withTable} as v1 answered with v1's digests; {reproduced} of {rows.length} of v1's digests reproduced by the Calculator's SHA-256"
  return (pass, fail)

end Tests.Provision
