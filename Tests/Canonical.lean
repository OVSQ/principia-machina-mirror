import Principia
import Lean.Data.Json

/-!
The vectors of the canonical serialization (`Principia.Canonical`) and of the digests and
their preimages (`Principia.Digest`, `Principia.Digest.Specification`): v1's
`canon_corpus.json`, `digest_corpus.json` and `dis_corpus.json`, and PMA's hand-written
`canonical_json.json` and `digest_preimage.json`. `Lean.Json` reads the inputs only, and
`dis_corpus.json` is read by the Calculator's own reader, which keeps a value's kind.

A hand-written corpus writes a value in a tagged form, so that member order and a
repeated key survive the reading (`Lean.Json` sorts keys and keeps one of two):
`["null"]`, `["bool", b]`, `["int", n]`, `["num", mantissa, exponent]`, `["str", s]`,
`["arr", [v, ...]]`, `["obj", [[key, v], ...]]`; a tree `["text", s]`, `["int", n]`,
`["list", [t, ...]]`. An expected `null` is a refusal.
-/

open Lean
open Principia.Canonical
open Principia.Digest

namespace Tests.Canonical

/-- A corpus's passing and failing checks. -/
structure Counts where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr with what was checked. -/
def Counts.check (t : Counts) (ok : Bool) (what : String) : IO Counts := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL {what}"
    return { t with fail := t.fail + 1 }

def Counts.pair (t : Counts) : Nat × Nat := (t.pass, t.fail)

def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

def field (j : Json) (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
def str (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)
def arr (j : Json) : IO (List Json) := return (← IO.ofExcept j.getArr?).toList

/-- An integer, refusing a number with a fraction. -/
def int (j : Json) : IO Int := do
  match j with
  | .num ⟨m, 0⟩ => return m
  | _ => throw (IO.userError s!"not an integer: {j.compress}")

/-- A JSON number's exact value as a decimal: `Lean.Json` keeps the mantissa and the
power of ten exactly. -/
def decimal (j : Json) : IO Decimal := do
  match j with
  | .num ⟨m, e⟩ => return ⟨m, -(e : Int)⟩
  | _ => throw (IO.userError s!"not a number: {j.compress}")

/-- An expectation: a string, or `null` for a refusal. -/
def expected (j : Json) : IO (Option String) := do
  match j with
  | .null => return none
  | .str s => return some s
  | _ => throw (IO.userError s!"not an expectation: {j.compress}")

/-- A value in the corpus's tagged form. -/
partial def value (j : Json) : IO Value := do
  match ← arr j with
  | [.str "null"] => return .null
  | [.str "bool", .bool b] => return .bool b
  | [.str "int", n] => return .int (← int n)
  | [.str "num", m, e] => return .num ⟨← int m, ← int e⟩
  | [.str "str", .str s] => return .str s
  | [.str "arr", xs] => return .arr (← (← arr xs).mapM value)
  | [.str "obj", ms] =>
    return .obj (← (← arr ms).mapM fun m => do
      match ← arr m with
      | [.str k, v] => return (k, ← value v)
      | _ => throw (IO.userError s!"not a member: {m.compress}"))
  | _ => throw (IO.userError s!"not a tagged value: {j.compress}")

/-- A tree in the corpus's tagged form. -/
partial def tree (j : Json) : IO Tree := do
  match ← arr j with
  | [.str "text", .str s] => return .text s
  | [.str "int", n] => return .int (← int n)
  | [.str "list", xs] => return .list (← (← arr xs).mapM tree)
  | _ => throw (IO.userError s!"not a tagged tree: {j.compress}")

/-- Two read numbers are one when they are the same constructor with the same fields. -/
def sameNumber : Option Value → Option Value → Bool
  | some (.int a), some (.int b) => a == b
  | some (.num a), some (.num b) => a == b
  | none, none => true
  | _, _ => false

/-! ## canon_corpus.json (v1), with its recorded divergences -/

/-- One recorded divergence: v1's text, the Calculator's text. -/
structure Divergence where
  id : String
  v1 : String
  v2 : String

def loadDivergences (path : System.FilePath) : IO (List Divergence) := do
  let j ← readJson path
  (← arr (← field j "divergences")).mapM fun d => do
    return { id := ← str d "id", v1 := ← str d "v1", v2 := ← str d "v2" }

/-- Every case's input is a number (v1's float) and its text the twelve-digit form; a
case with a recorded divergence must give the recorded v2 text, and its v1 text must be
the corpus's. -/
def runCanonCorpus : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let divs ← loadDivergences "vectors/canon_corpus.divergences.json"
  let cases ← arr (← field (← readJson "vectors/canon_corpus.json") "cases")
  let mut seen : List String := []
  for c in cases do
    let id ← str c "id"
    let fn ← str c "fn"
    if fn != "canon" then throw (IO.userError s!"{id}: unknown function {fn}")
    let x ← decimal (← field (← field c "input") "x")
    let exp ← str c "expect"
    let got := (Value.num x).canon
    match divs.find? (·.id == id) with
    | some d =>
      seen := id :: seen
      t ← t.check (d.v1 == exp && got == some d.v2)
        s!"canon {id}: recorded divergence v1 {repr d.v1}, v2 {repr d.v2}; corpus {repr exp}, got {repr got}"
    | none =>
      t ← t.check (got == some exp) s!"canon {id}: expected {repr exp}, got {repr got}"
  for d in divs do
    if !seen.contains d.id then
      t ← t.check false s!"canon: the divergence {d.id} names no case"
  IO.println s!"canon_corpus: {seen.length} of {cases.length} cases are recorded v2 divergences"
  return t.pair

/-! ## canonical_json.json (hand-written) -/

def runCanonicalJson : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/canonical_json.json") do
    let what := c.compress
    match ← str c "function" with
    | "canonicalJson" =>
      let got := (← value (← field c "value")).canonicalJson
      let exp ← expected (← field c "expected")
      t ← t.check (got == exp) s!"{what}: got {repr got}"
    | "canon" =>
      let got := (← value (← field c "value")).canon
      let exp ← expected (← field c "expected")
      t ← t.check (got == exp) s!"{what}: got {repr got}"
    | "readNumber" =>
      let got := readNumber? (← str c "literal")
      let e ← field c "expected"
      let exp ← if e.isNull then pure none else some <$> value e
      t ← t.check (sameNumber got exp) s!"{what}: got {repr got}"
    | other => throw (IO.userError s!"unknown function {other}")
  -- The digit bound, at the limit and just past it; these literals are too long to sit
  -- on a corpus line, so they are built here.
  let digits (n : Nat) : String := String.ofList (List.replicate n '7')
  let fraction (n : Nat) : String := "0." ++ String.ofList (List.replicate (n - 2) '0') ++ "1"
  let accepted (lit : String) : Bool := (readNumber? lit).isSome
  t ← t.check (sameNumber (readNumber? (digits maxNumberDigits))
      (some (.int (digitsValue (List.replicate maxNumberDigits '7')))))
    s!"readNumber: {maxNumberDigits} integer digits read"
  t ← t.check (!accepted (digits (maxNumberDigits + 1)))
    s!"readNumber: {maxNumberDigits + 1} integer digits refused"
  t ← t.check (sameNumber (readNumber? (fraction maxNumberDigits))
      (some (.num ⟨1, -((maxNumberDigits : Int) - 1)⟩)))
    s!"readNumber: {maxNumberDigits} digits with a fraction read"
  t ← t.check (!accepted (fraction (maxNumberDigits + 1)))
    s!"readNumber: {maxNumberDigits + 1} digits with a fraction refused"
  -- The worst literal accepted: every digit, the most negative exponent; its text.
  let worst := fraction maxNumberDigits ++ "e-9999"
  t ← t.check ((readNumber? worst).bind Value.canon == some "1e-14094")
    s!"readNumber: the worst accepted literal writes 1e-14094"
  return t.pair

/-! ## digest_corpus.json (v1): the preimages and the digests -/

/-- A digest field as v1 takes it: a string, or an integer. -/
def digestField (j : Json) : IO Field := do
  match j with
  | .str s => return .text s
  | _ => return .int (← int j)

/-- Each case's preimage is checked, then its `expect`, the SHA-256 of the preimage, against
the Calculator's digest. -/
def runDigestCorpus : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← field (← readJson "vectors/digest_corpus.json") "cases") do
    let id ← str c "id"
    let input ← field c "input"
    let pre ← str c "preimage"
    let expect ← str c "expect"
    let (got, digest) ← match ← str c "fn" with
      | "digest_fields" => do
        let fs ← (← arr (← field input "fields")).mapM digestField
        pure (some (preimageFields fs), some (digestFields fs))
      | "combine_digests" => do
        let ds ← (← arr (← field input "hex_digests")).mapM fun h => IO.ofExcept h.getStr?
        pure (preimageDigests ds, combineDigests ds)
      | "d_tfk" => do
        let (a, b, k) := (← str input "d_tpk", ← str input "d_trm", ← str input "d_tms")
        pure (preimageResearchAssembly a b k, digestResearchAssembly a b k)
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    t ← t.check (got == some pre) s!"digest {id}: expected preimage {repr pre}, got {repr got}"
    t ← t.check (digest == some expect) s!"digest {id}: expected {expect}, got {repr digest}"
  return t.pair

/-! ## digest_preimage.json (hand-written) -/

def runDigestPreimage : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/digest_preimage.json") do
    let what := c.compress
    let exp ← expected (← field c "expected")
    let got ← match ← str c "function" with
      | "treePreimage" => pure (some (← tree (← field c "tree")).preimage)
      | "preimageFields" => some <$> preimageFields <$> (← arr (← field c "fields")).mapM digestField
      | "preimageDigests" =>
        pure (preimageDigests (← (← arr (← field c "digests")).mapM fun h => IO.ofExcept h.getStr?))
      | other => throw (IO.userError s!"unknown function {other}")
    t ← t.check (got == exp) s!"{what}: got {repr got}"
  return t.pair

/-! ## dis_corpus.json (v1): the specification's and the instruction set's digests

v1's `tpc_digest` 0.3.0 functions `pre_texts`, `d_tps`, `d_is` and `tps_pages`, ported as
`preTextsOf`, `digestSpecificationOf`, `digestInstructionSetOf` and `specificationPagesOf`.
Each case's input is read by the Calculator's reader (`readString`), which keeps a value's
kind (an object, `null` and a number stay what they are, and v1 refused them for their type).
The answer, v1's `["OK", x]` or `["REFUSED", reason]`, is written as v1's `canon` text and
compared with `expect`; since `canon` writes a string unquoted, a string of the answer that
holds `,`, `[` or `]` fails its case rather than compares. The one case whose text cannot tell
a block that is empty from no block, `pre/empty-block` (`[OK,[]]`), is answered `[""]`, as v1
answered it; the digest cases `tps/section-with-an-empty-block` and
`pages/empty-block-on-the-root` pin the difference. A digest case that carries `preimage` has
its preimage compared too, byte for byte; its `expect` is the SHA-256 of that preimage. -/

/-- No string of a value holds `,`, `[` or `]`, so v1's `canon` text of it reads back as it. -/
partial def bracketFree : Value → Bool
  | .str s => !s.any fun c => c == ',' || c == '[' || c == ']'
  | .arr xs => xs.all bracketFree
  | _ => true

/-- A member of an object. -/
def memberOf (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

/-- A member that must be there. -/
def needMember (v : Value) (k : String) : IO Value :=
  match memberOf v k with
  | some x => pure x
  | none => throw (IO.userError s!"no member {k}")

/-- A string member that must be there. -/
def needText (v : Value) (k : String) : IO String := do
  match ← needMember v k with
  | .str s => pure s
  | _ => throw (IO.userError s!"member {k} is not a string")

/-- A v1 corpus's cases, read by the Calculator's reader. -/
def readCases (path : System.FilePath) : IO (List Value) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError s!"{path}: no cases")
  | .ok _ => throw (IO.userError s!"{path}: not an object")
  | .error f => throw (IO.userError s!"{path}: refused {repr f}")

/-- A preimage answered, or the reason it was refused. -/
def preimageText : Except Principia.Digest.Specification.Reason String → String
  | .ok p => p
  | .error r => s!"refused {r.word}"

open Principia.Digest.Specification in
def runDisCorpus : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let mut counted : List String := []
  for c in ← readCases "vectors/dis_corpus.json" do
    let id ← needText c "id"
    let fn ← needText c "fn"
    let expect ← needText c "expect"
    let input ← needMember c "input"
    let arg (k : String) : IO Value := needMember input k
    counted := fn :: counted
    let (got, preimage) ← match fn with
      | "pre_texts" =>
        pure (answer (fun bs => .arr (bs.map .str)) (preTextsOf (← arg "wikitext")), none)
      | "tps_pages" => pure (answer pairsValue (specificationPagesOf (← arg "pages")), none)
      | "d_tps" => do
        let (v, p) := (← arg "version", ← arg "pages")
        pure (answer .str (digestSpecificationOf v p), some (preimageSpecificationOf v p))
      | "d_is" => do
        let (v, d, m) := (← arg "version", ← arg "d_tps", ← arg "members")
        pure (answer .str (digestInstructionSetOf v d m), some (preimageInstructionSetOf v d m))
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    t ← t.check (got.canon == some expect && bracketFree got)
      s!"dis {fn} {id}: expected {repr expect}, got {repr got.canon}"
    match memberOf c "preimage", preimage with
    | some (.str pre), some p =>
      t ← t.check (preimageText p == pre)
        s!"dis {fn} {id}: expected preimage {repr pre}, got {repr (preimageText p)}"
    | none, _ => pure ()
    | _, _ => throw (IO.userError s!"{id}: a preimage where none is computed")
  -- The corpus is v1's whole: 189 cases, by function.
  let count (f : String) := (counted.filter (· == f)).length
  let counts := ["pre_texts", "d_tps", "d_is", "tps_pages"].map count
  t ← t.check (counts == [28, 58, 15, 88])
    s!"dis_corpus: expected 28, 58, 15 and 88 cases, got {counts}"
  return t.pair

end Tests.Canonical
