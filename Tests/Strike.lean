import Principia
import Lean.Data.Json
import Tests.Zone

/-!
The strike family's runner: v1's `strike_corpus.json` (20 cases), `sr8_order_corpus.json`
(5) and `sr9_corpus.json` (31), run against `Principia.Strike` and `Principia.Strike.SR9`.

Each corpus is `{"meta", "cases"}`, a case `{"id", "fn", "input", "expect"}`, its `expect`
v1's `canon` text of the result. An exact result (a boolean, an integer, a word, a list of
them) is compared with that text, written here in v1's form; PMA's canonical
serialization is its own item, and this text form is the runner's, not the Calculator's.
v1's text writes a word unquoted and so is not one to one; `plainWords` fails a case
whose words could collide, so a pass is equality of the typed result.
A scale factor, a real number, is compared by value: the corpus's twelve significant
digits against `ScaleFactor.digits 12`, the exact root correctly rounded. Numbers are
read from the corpus's decimal text, exactly.

A case that differs is reported on stderr and counted as failing; v2 divergences would be
listed in `vectors/README.md`, and these three corpora have none.
-/

namespace Tests.Strike

open Lean
open Principia
open Principia.Strike
open Principia.Strike.SR9

/-! ## Reading the corpus -/

/-- The cases of one of v1's corpora. -/
def loadV1Cases (path : System.FilePath) : IO (Array Json) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (json.getObjValAs? (Array Json) "cases")

def field (j : Json) (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)

def str (j : Json) : IO String := IO.ofExcept j.getStr?

def strs (j : Json) : IO (List String) := do
  (← IO.ofExcept j.getArr?).toList.mapM str

/-- A JSON number as the exact rational its decimal text writes. -/
def rat (j : Json) : IO Rat := do
  let n ← IO.ofExcept j.getNum?
  return (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

/-- A JSON number written as an integer (no fraction part). -/
def int (j : Json) : IO Int := do
  let n ← IO.ofExcept j.getNum?
  if n.exponent = 0 then return n.mantissa
  throw (IO.userError s!"not an integer: {j.compress}")

def nat (j : Json) : IO Nat := do
  let i ← int j
  if 0 ≤ i then return i.toNat
  throw (IO.userError s!"not a count: {j.compress}")

/-- A JSON object's members, in key order. -/
def members (j : Json) : IO (List (String × Json)) := do
  let kvs ← IO.ofExcept j.getObj?
  return kvs.foldl (fun acc k v => acc ++ [(k, v)]) []

/-- An optional list field, `[]` when absent (v1's `rec.get(..., [])`). -/
def strsOr (j : Json) (k : String) : IO (List String) :=
  match j.getObjVal? k with
  | .ok v => strs v
  | .error _ => pure []

def strikeRecords (j : Json) : IO Records := do
  (← members j).mapM fun (id, r) => do
    return (id, { assumptions := ← strsOr r "assumptions", cites := ← strsOr r "cites",
                  steps := ← nat (← field r "steps") })

def distance (j : Json) : IO Distance := do
  match (← IO.ofExcept j.getArr?).toList with
  | [a, s] => return ⟨← nat a, ← nat s⟩
  | _ => throw (IO.userError s!"not a distance: {j.compress}")

/-- `S`, at least 1, as its square; absent, 1. -/
def scale (input : Json) : IO ScaleFactor := do
  match input.getObjVal? "S" with
  | .error _ => return .one
  | .ok j =>
    let s ← rat j
    if h : 1 ≤ s * s then return ⟨s * s, h⟩
    throw (IO.userError s!"S below 1: {j.compress}")

def regime (j : Json) : IO Regime := do
  let w ← str j
  match (WireWord.ofWire? w : Option Regime) with
  | some r => return r
  | none => throw (IO.userError s!"not a regime: {repr w}")

def suite (j : Json) : IO Suite := do
  let recs ← (← members (← field j "records")).mapM fun (id, r) => do
    return (id, { regime := ← regime (← field r "regime"),
                  assumptions := ← strsOr r "assumptions", cites := ← strsOr r "cites",
                  steps := ← nat (← field r "steps"), domain := ← str (← field r "domain"),
                  sr1Fail := ← IO.ofExcept (r.getObjValAs? Bool "sr1_fail") })
  let pairs ← match j.getObjVal? "contradictions" with
    | .error _ => pure []
    | .ok cs => (← IO.ofExcept cs.getArr?).toList.mapM fun p => do
      match ← strs p with
      | [a, b] => pure (a, b)
      | _ => throw (IO.userError s!"not a pair: {p.compress}")
  return { records := recs, assembly := ← strsOr j "tfk_assumptions", contradictions := pairs }

/-- The Criteria Set's parameters as the gate reads them: a parameter absent, or not of its
type (a boolean is no number), is `none`. -/
def tmsParams (j : Json) : TmsParams :=
  let get k := (j.getObjVal? k).toOption
  { k := match get "k" with
      | some (.num n) => some ((n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat))
      | _ => none
    stepConvention := match get "step_convention" with
      | some (.str s) => some s
      | _ => none
    nX := match get "n_x" with
      | some (.num n) => if n.exponent = 0 then some n.mantissa else none
      | _ => none }

/-! ## v1's text of a result -/

def canonBool (b : Bool) : String := if b then "true" else "false"

def canonList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

/-- Whether v1's text of a list of words reads back as that list. v1's `canon` writes a
string unquoted, so `["a,b"]` and `["a","b"]` share the text `[a,b]`, and `[""]` and `[]`
share `[]`; a word holding a comma or a bracket, or an empty word, makes the text
ambiguous. Every other result here is a boolean, a count, an SR5 word or one of the
gate's fixed names, whose text is already one to one. -/
def plainWords (ws : List String) : Bool :=
  ws.all fun w => !w.isEmpty && !w.any fun c => c == ',' || c == '[' || c == ']'

/-- `r`, unless the result's words `ws` are ambiguous in v1's text: then the case fails,
so a passing case's text equality is equality of the typed result. -/
def unlessAmbiguous (ws : List String) (r : Bool × String) : Bool × String :=
  if plainWords ws then r else (false, s!"{r.2}, ambiguous in v1's text: {repr ws}")

def orRefused {α : Type} (f : α → String) : Option α → String
  | some a => f a
  | none => "REFUSED"

/-! ## Running -/

/-- One case: `(ok, what was got)`. -/
def runCase (fn : String) (input : Json) (expect : String) : IO (Bool × String) := do
  let text (got : String) := (got == expect, got)
  match fn with
  | "a_of_r" =>
    let got := aOfR (← str (← field input "rid")) (← strikeRecords (← field input "records"))
      (← strsOr input "tfk_assumptions")
    return text (orRefused toString got)
  | "d_of_r" =>
    let got := dOfR (← str (← field input "rid")) (← strikeRecords (← field input "records"))
      (← strsOr input "tfk_assumptions")
    return text (orRefused (fun d => canonList [toString d.assumptions, toString d.steps]) got)
  | "sr8_scale_factor" =>
    let ms ← (← IO.ofExcept (← field input "measurements").getArr?).toList.mapM fun m => do
      return ({ value := ← rat (← field m "x"), uncertainty := ← rat (← field m "u") } :
        Measurement)
    let want ← rat (← IO.ofExcept (Json.parse expect))
    match sr8ScaleFactor ms with
    | none => return (false, "REFUSED")
    | some S =>
      let (m, e) := S.digits 12
      let got : Rat := (m : Rat) * (10 : Rat) ^ e
      return (got == want, s!"{m}e{e}")
  | "mm_contradicts" =>
    let got := mmContradicts (← rat (← field input "x1")) (← rat (← field input "u1"))
      (← rat (← field input "x2")) (← rat (← field input "u2")) (← rat (← field input "k"))
      (← scale input)
    return text (canonBool got)
  | "lm_contradicts" =>
    let got := lmContradicts (← rat (← field input "x_l")) (← rat (← field input "x_m"))
      (← rat (← field input "u_m")) (← rat (← field input "k")) (← scale input)
    return text (canonBool got)
  | "sr5_order" =>
    let got := sr5Order (← distance (← field input "d1")) (← distance (← field input "d2"))
    return text got.toV1
  | "sr6_independence_count" =>
    let sets ← (← IO.ofExcept (← field input "sets").getArr?).toList.mapM strs
    let flags ← match input.getObjVal? "same_model" with
      | .error _ => pure none
      | .ok f => some <$> (← IO.ofExcept f.getArr?).toList.mapM (IO.ofExcept ·.getBool?)
    return text (orRefused toString (sr6IndependenceCount sets flags))
  | "sr6_audit_opens" =>
    let got := sr6AuditOpens (← nat (← field input "n_ind")) (← nat (← field input "n_x"))
    return text (orRefused canonBool got)
  | "tms_params_ok" =>
    let (ok, missing) := tmsParamsOk (tmsParams (← field input "params"))
    return text (canonList [canonBool ok, canonList missing])
  | _ =>
    let name ← str (← field input "entry")
    let some e := fixture name | throw (IO.userError s!"unknown entry {name}")
    let s ← suite (← field input "suite")
    match fn with
    | "sr9_c1" =>
      let r := sr9C1 e s
      return unlessAmbiguous ((r.map (·.2)).getD [])
        (text (orRefused (fun (p, w) => canonList [canonBool p, canonList w]) r))
    | "sr9_c2" =>
      let r := sr9C2 e s
      return unlessAmbiguous ((r.map fun (_, v, x) => v ++ x).getD [])
        (text (orRefused (fun (p, v, x) => canonList [canonBool p, canonList v, canonList x]) r))
    | "sr9_c4" =>
      let r := sr9C4 e s
      return unlessAmbiguous ((r.map (·.2)).getD [])
        (text (orRefused (fun (p, w) => canonList [canonBool p, canonList w]) r))
    | "sr9_harness" => return text (orRefused (fun (a, b, c, n) =>
        canonList [canonBool a, canonBool b, canonBool c, toString n]) (sr9Harness e s))
    | other => throw (IO.userError s!"unknown function {other}")

/-- Run one corpus: `(pass, fail)`. -/
def runCorpus (path : System.FilePath) : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in ← loadV1Cases path do
    let id ← str (← field c "id")
    let (ok, got) ← runCase (← str (← field c "fn")) (← field c "input") (← str (← field c "expect"))
    if ok then pass := pass + 1
    else
      IO.eprintln s!"FAIL {path} {id}: expected {← str (← field c "expect")}, got {got}"
      fail := fail + 1
  return (pass, fail)

def runStrike : IO (Nat × Nat) := runCorpus "vectors/strike_corpus.json"
def runSr8Order : IO (Nat × Nat) := runCorpus "vectors/sr8_order_corpus.json"
def runSr9 : IO (Nat × Nat) := runCorpus "vectors/sr9_corpus.json"

/-! ## sr3_scope_corpus.json: `sr3Scope`

Each case's `expect` is v1's text of the answer: a word, or `[REFUSED,<reason>]`. It is
read back into its kind (the reason is the text between `[REFUSED,` and the last `]`, so
a reason holding a comma or a bracket stays whole) and compared typed. -/

/-- v1's text of `sr3_scope`'s answer, read back: the word, or the refusal's reason. -/
def sr3Expect (e : String) : Except String String :=
  if e.startsWith "[REFUSED," && e.endsWith "]" then
    .error (String.ofList ((e.toList.drop "[REFUSED,".length).dropLast))
  else .ok e

def runSr3Scope : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in ← loadV1Cases "vectors/sr3_scope_corpus.json" do
    let id ← str (← field c "id")
    let input ← field c "input"
    let get (k : String) : Zone.Value :=
      ((input.getObjVal? k).toOption.map Tests.Zone.toValue).getD .null
    let got := sr3Scope (get "tfk") (get "quantity")
    let exp := sr3Expect (← str (← field c "expect"))
    let ok := match got, exp with
      | .ok s, .ok w => s.toV1 == w
      | .error r, .error w => r == w
      | _, _ => false
    if ok then pass := pass + 1
    else
      let shown := match got with
        | .ok s => s.toV1
        | .error r => s!"REFUSED {r}"
      IO.eprintln s!"FAIL sr3_scope {id}: expected {repr exp}, got {shown}"
      fail := fail + 1
  return (pass, fail)

/-! ## conditions_corpus.json: `conditionsOf`, `comparisonSet`, `sr8Groups`

Each case's `expected` is TPM's canonical JSON of v1's answer, `["OK", ...]` or
`["REFUSED", [[code, field, message]]]`. The Calculator's typed answer is written in that
form by the canonical serialization (`Canonical.Value.canonicalJson`), which quotes every
string, so equal text is an equal answer. An owed answer fails here: the corpus has
none. -/

/-- A JSON value as the canonical writers take it: a number with a fraction or an
exponent is v1's float (`num`), any other an integer. -/
partial def toCanonical : Json → Canonical.Value
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent == 0 then .int n.mantissa else .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr a => .arr (a.toList.map toCanonical)
  | .obj kvs => .obj (kvs.foldl (fun acc k v => acc ++ [(k, toCanonical v)]) [])

def runConditions : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in ← loadV1Cases "vectors/conditions_corpus.json" do
    let name ← str (← field c "name")
    let args ← field c "args"
    let arg (k : String) : Canonical.Value :=
      ((args.getObjVal? k).toOption.map toCanonical).getD .null
    let got : Option Canonical.Value ← match ← str (← field c "fn") with
      | "conditions_of" => pure ((conditionsOf (arg "records") (arg "id")).toValue
          Conditions.toValue)
      | "comparison_set" => pure ((comparisonSet (arg "records") (arg "words") (arg "tfk")
          (arg "quantity")).toValue pairsValue)
      | "sr8_groups" => pure ((sr8Groups (arg "records") (arg "words") (arg "tfk")
          (arg "quantity")).toValue groupsValue)
      | other => throw (IO.userError s!"unknown function {other}")
    let exp ← str (← field c "expected")
    let text := got.bind (·.canonicalJson)
    if text == some exp then pass := pass + 1
    else
      IO.eprintln s!"FAIL conditions {name}: expected {exp}, got {text.getD "owed"}"
      fail := fail + 1
  return (pass, fail)

end Tests.Strike
