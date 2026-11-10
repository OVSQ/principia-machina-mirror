import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The runner of `vectors/identity_corpus.json` (v1's `tpc_identity` 0.1.1, 102 cases:
tools 28, digest 19, family 21, class 18, compare 16) against `Principia.Identity`.

Each case's arguments are read into `Principia.Zone.Value` as v1's JSON reader gives
them, the function is run, and its typed outcome is compared with the case's `expected`
text read back into the same types: a refusal `ERROR:<word>` into `Refusal`; a family
answer into `FamilyResult`, its fields unescaped as v1's `_esc` escaped them (`\|`,
`\\`, `\xNN`); a change class into `ChangeResult` through the classes' and details'
wire words; a comparison into `Comparison`, line by line. The canonical tools are a
text, compared as one.

A PROMPT digest is SHA-256 (`Principia.Sha256`; decision D2, option 1), compared with v1's
as text; for each digest case v1 answered with a digest, the preimage the Calculator digested
must also equal the one v1 digested (`vectors/identity_corpus.preimages.json`). Nothing of
identity is owed: `vectors/identity_corpus.owed.json` must list no case. Fault checks run
first: the comparisons must refuse mutated expectations, and the owed list's check must
refuse a list missing or adding a case.
-/

open Lean
open Principia
open Principia.Identity
open Principia.Zone (Value)

namespace Tests.Identity

/-- Passing and failing checks. -/
structure Count where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr. -/
def Count.check (t : Count) (ok : Bool) (what : String) : IO Count := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL identity: {what}"
    return { t with fail := t.fail + 1 }

/-! ## Reading v1's texts back into the types -/

/-- v1's `_esc` undone, the fields split on the unescaped `|`; `none` when malformed. -/
def splitEsc (s : String) : Option (List String) :=
  let rec go : List Char → List Char → List String → Option (List String)
    | [], cur, acc => some ((acc ++ [String.ofList cur.reverse]))
    | '\\' :: '|' :: r, cur, acc => go r ('|' :: cur) acc
    | '\\' :: '\\' :: r, cur, acc => go r ('\\' :: cur) acc
    | '\\' :: 'x' :: a :: b :: r, cur, acc =>
      match hexVal a, hexVal b with
      | some x, some y => go r (Char.ofNat (x * 16 + y) :: cur) acc
      | _, _ => none
    | '\\' :: _, _, _ => none
    | '|' :: r, cur, acc => go r [] (acc ++ [String.ofList cur.reverse])
    | c :: r, cur, acc => go r (c :: cur) acc
  go s.toList [] []

/-- A refusal text, `ERROR:<word>`. -/
def refusalOf? (expected : String) : Option Refusal :=
  if expected.startsWith "ERROR:" then Refusal.ofMessage? (expected.drop 6).toString else none

/-- v1's `render_family` read back. -/
def familyOf? (expected : String) : Option FamilyResult :=
  if expected == "UNMAPPED" then some .unmapped
  else match splitEsc expected with
    | some ["MAPPED", fam, o, s, q, key] =>
      let openW? : Option Bool := if o == "true" then some true else if o == "false" then some false else none
      openW?.bind fun ow =>
        if ow then some (.mapped fam true (some s) (some q) key)
        else if s == "-" && q == "-" then some (.mapped fam false none none key) else none
    | _ => none

/-- v1's `render_class` read back. -/
def classOf? (expected : String) : Option ChangeResult :=
  match expected.splitOn "|" with
  | [c, d] =>
    (WireWord.ofWire? c : Option ChangeClass).bind fun cls =>
      if d == "-" then some ⟨cls, none⟩
      else (WireWord.ofWire? d : Option ChangeDetail).map fun det => ⟨cls, some det⟩
  | _ => none

/-- A value's name read back. -/
def partyOf? : String → Option Party
  | "declared" => some .declared
  | "stated" => some .stated
  | "relayed" => some .relayed
  | "inferred" => some .inferred
  | _ => none

/-- v1's `render_compare` read back. -/
def compareOf? (expected : String) : Option Comparison :=
  match expected.splitOn "\n" with
  | head :: lines =>
    match head.splitOn "|" with
    | ["overall", o, n] => do
      let overall ← (WireWord.ofWire? o : Option Agreement)
      let differ ← n.toNat?
      let ps ← lines.mapM fun l =>
        match l.splitOn "|" with
        | [a, b, r] => do pure ((← partyOf? a), (← partyOf? b), (← (WireWord.ofWire? r : Option Agreement)))
        | _ => none
      pure { overall, pairs := ps, differ }
    | _ => none
  | [] => none

/-! ## Running a case -/

/-- What a case gives, typed. -/
inductive Outcome' where
  | tools (o : Outcome String)
  | digest (o : Outcome String)
  | family (o : Outcome FamilyResult)
  | cls (o : Outcome ChangeResult)
  | compare (o : Outcome Comparison)

def arg (args : Json) (k : String) : IO Value := do
  match args.getObjVal? k with
  | .ok v => pure (Tests.Zone.toValue v)
  | .error _ => throw (IO.userError s!"identity: no argument {k}")

def runCase (fn : String) (args : Json) : IO Outcome' := do
  match fn with
  | "tools" => pure (.tools (canonicalTools (← arg args "json")))
  | "digest" => pure (.digest (promptDigest (← arg args "family") (← arg args "salt")
      (← arg args "template") (← arg args "tools")))
  | "family" => pure (.family (familyOf (← arg args "model") (← arg args "map")))
  | "class" => pure (.cls (changeClass (← arg args "certified") (← arg args "last")
      (← arg args "reported") (← arg args "lookup")))
  | "compare" => pure (.compare (identityCompare (← arg args "declared") (← arg args "stated")
      (← arg args "relayed") (← arg args "inferred")))
  | other => throw (IO.userError s!"identity: unknown fn {other}")

/-- A judged outcome against the expected text, typed: `true` when they agree. -/
def agrees (expected : String) : Outcome' → Bool
  | .tools (.ok s) => s == expected
  | .digest (.ok d) => d == expected
  | .family (.ok r) => familyOf? expected == some r
  | .cls (.ok r) => classOf? expected == some r
  | .compare (.ok r) => compareOf? expected == some r
  | .tools (.error (.refused r)) | .digest (.error (.refused r)) | .family (.error (.refused r))
  | .cls (.error (.refused r)) | .compare (.error (.refused r)) => refusalOf? expected == some r

/-- v1 answered with a digest: 64 lower-case hexadecimal characters. -/
def isDigest (s : String) : Bool :=
  s.length == 64 && s.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- The owed list's check, both ways: every owed case listed for its reason, every listed
case owed for it. Returns the complaints. -/
def owedComplaints (owed listed : List (String × String)) : List String :=
  (owed.filter (!listed.contains ·)).map (fun (n, r) => s!"{n}: owed ({r}) but not listed so") ++
  (listed.filter (!owed.contains ·)).map (fun (n, r) => s!"{n}: listed as owed ({r}) but not owed for that reason")

/-! ## Fault checks -/

/-- Each is `true` when the check refuses a fault, or accepts what it must. -/
def faultChecks : List (String × Bool) :=
  let fam := FamilyResult.mapped "Meta/Llama-4" true (some "together") (some "fp8")
    "4:OPEN12:Meta/Llama-48:together3:fp8"
  let famText := "MAPPED|Meta/Llama-4|true|together|fp8|4:OPEN12:Meta/Llama-48:together3:fp8"
  let ps : List (Party × Party × Agreement) :=
    [(Party.declared, Party.stated, Agreement.differ), (Party.declared, Party.relayed, Agreement.absent),
     (Party.declared, Party.inferred, Agreement.absent), (Party.stated, Party.relayed, Agreement.absent),
     (Party.stated, Party.inferred, Agreement.absent), (Party.relayed, Party.inferred, Agreement.absent)]
  let cmp : Comparison := Comparison.mk Agreement.differ ps 1
  let cmpText := "overall|DIFFER|1\ndeclared|stated|DIFFER\ndeclared|relayed|ABSENT\ndeclared|inferred|ABSENT\nstated|relayed|ABSENT\nstated|inferred|ABSENT\nrelayed|inferred|ABSENT"
  [("a family answer as printed is accepted", agrees famText (.family (.ok fam))),
   ("server and quantization swapped", !agrees
      "MAPPED|Meta/Llama-4|true|fp8|together|4:OPEN12:Meta/Llama-48:together3:fp8" (.family (.ok fam))),
   ("an escaped bar is a bar, not a field", splitEsc "a\\|b|c" == some ["a|b", "c"]),
   ("a bar inside a field shifts the fields", !agrees
      "MAPPED|Meta|Llama-4|true|together|fp8|4:OPEN12:Meta/Llama-48:together3:fp8" (.family (.ok fam))),
   ("a class as printed is accepted", agrees "REFUSED MODEL|OUT" (.cls (.ok ⟨.refusedModel, some (.cluster .outside)⟩))),
   ("a class's detail changed", !agrees "REFUSED MODEL|FADING" (.cls (.ok ⟨.refusedModel, some (.cluster .outside)⟩))),
   ("class and detail swapped", !agrees "OUT|REFUSED MODEL" (.cls (.ok ⟨.refusedModel, some (.cluster .outside)⟩))),
   ("a comparison as printed is accepted", agrees cmpText (.compare (.ok cmp))),
   ("a pair's answer changed", !agrees (cmpText.replace "stated|DIFFER" "stated|AGREE") (.compare (.ok cmp))),
   ("the count changed", !agrees (cmpText.replace "DIFFER|1" "DIFFER|2") (.compare (.ok cmp))),
   ("a refusal's word changed", !agrees "ERROR:model" (.family (.error (.refused .modelMap)))),
   ("a refusal where a value is expected", !agrees famText (.family (.error (.refused .modelMap)))),
   ("a digest as printed is accepted", agrees (String.ofList (List.replicate 64 'a'))
      (.digest (.ok (String.ofList (List.replicate 64 'a'))))),
   ("a digest changed in its last character", !agrees (String.ofList (List.replicate 64 'a'))
      (.digest (.ok (String.ofList (List.replicate 63 'a' ++ ['b']))))),
   ("an owed case missing from the list", !(owedComplaints [("x", "digest")] []).isEmpty),
   ("a listed case not owed", !(owedComplaints [] [("x", "digest")]).isEmpty),
   ("a case owed for another reason", !(owedComplaints [("x", "digest")] [("x", "unicode U+0301")]).isEmpty)]

/-! ## The run -/

/-- Run the corpus: passes and failures; owed cases are counted and printed. -/
def run : IO (Nat × Nat) := do
  let mut t : Count := {}
  for (what, ok) in faultChecks do
    t ← t.check ok s!"fault check: {what}"
  let corpus ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/identity_corpus.json"))
  let cases ← IO.ofExcept ((← IO.ofExcept (corpus.getObjVal? "cases")).getArr?)
  let owedJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/identity_corpus.owed.json"))
  let listed ← (← IO.ofExcept ((← IO.ofExcept (owedJson.getObjVal? "owed")).getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")), (← IO.ofExcept (o.getObjValAs? String "reason")))
  let preJson ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/identity_corpus.preimages.json"))
  let preimages ← (← IO.ofExcept ((← IO.ofExcept (preJson.getObjVal? "preimages")).getArr?)).toList.mapM fun o => do
    pure ((← IO.ofExcept (o.getObjValAs? String "name")), (← IO.ofExcept (o.getObjValAs? String "preimage")))
  -- Only the pass count of judged cases and owed checks; the fault checks are above.
  let faults := t
  t := {}
  -- Nothing of identity is owed: no case comes out owed.
  let owed : List (String × String) := []
  let mut preimageChecked := 0
  let mut digests := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let args ← IO.ofExcept (c.getObjVal? "args")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let out ← runCase fn args
    t ← t.check (agrees expected out) s!"{name}: expected {repr expected}"
    if fn == "digest" && isDigest expected then
      digests := digests + 1
      -- The preimage the Calculator digested is the one v1 digested.
      let pre := promptPreimage (← arg args "family") (← arg args "salt") (← arg args "template")
        (← arg args "tools")
      match pre, preimages.lookup name with
      | .ok p, some v1 =>
        if p == v1 then preimageChecked := preimageChecked + 1
        else t ← t.check false s!"{name}: preimage {repr p}, v1 digested {repr v1}"
      | _, none => t ← t.check false s!"{name}: no preimage recorded"
      | .error s, _ => t ← t.check false s!"{name}: the preimage stops with {repr s}"
  for complaint in owedComplaints owed listed do
    t ← t.check false complaint
  IO.println s!"identity: {owed.length} owed; {digests} digests SHA-256 as v1's, {preimageChecked} of them over the preimage v1 digested; {faults.pass} of {faultChecks.length} fault checks refused or accepted as they must"
  return (t.pass, t.fail + faults.fail)

end Tests.Identity
