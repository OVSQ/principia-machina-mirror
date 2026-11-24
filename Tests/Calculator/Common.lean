import Principia
import Tests.Canonical
import Tests.Form
import Tests.Governor
import Tests.Sha256
import Tests.Strike
import Tests.Unicode

/-!
The helpers shared by the Calculator's runners (`Tests/Calculator/*.lean`): a case's input,
a v1 corpus's cases and owed lists, and the requests the bounds runners build.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- Bytes from lowercase hexadecimal. -/
def hexBytes (s : String) : IO ByteArray := do
  let digit (c : Char) : IO UInt8 :=
    match hexValue c with
    | some n => pure n.toUInt8
    | none => throw (IO.userError s!"not hexadecimal: {s}")
  let rec go : List Char → ByteArray → IO ByteArray
    | a :: b :: rest, acc => do go rest (acc.push ((← digit a) * 16 + (← digit b)))
    | [], acc => pure acc
    | _, _ => throw (IO.userError s!"odd hexadecimal: {s}")
  go s.toList ByteArray.empty

/-- A case's input: `text` as UTF-8, or `bytes` / `stdin_hex` in hexadecimal. -/
def input (c : Json) (textKey hexKey : String) : IO ByteArray := do
  match c.getObjValAs? String textKey with
  | .ok t => pure t.toUTF8
  | .error _ => hexBytes (← str c hexKey)

/-- A reading refused with exactly `f`. -/
def refusedWith (r : Except ReadFailure Value) (f : ReadFailure) : Bool :=
  match r with
  | .error g => g == f
  | .ok _ => false

/-- A value read back from its own canonical JSON writes the same text. -/
def rereads (v : Value) : Bool :=
  match v.canonicalJson with
  | none => false
  | some t =>
    match readString t with
    | .ok w => w.canonicalJson == some t
    | .error _ => false

/-! ## v1's corpora through the dispatch

Each case of a v1 corpus is read with the Calculator's own reader, which keeps a number's
kind and the members' order (`Lean.Json` would turn `2.0` into `2`), and its input given
to the family's function as a request, through `Calculator.respondTo`; the text path is
`pcalc.json`'s. -/

/-- A v1 corpus's cases, read by the Calculator's reader. -/
def v1Cases (path : System.FilePath) : IO (List Value) := do
  let text ← IO.FS.readFile path
  match readString text with
  | .error f => throw (IO.userError s!"{path}: refused {repr f}")
  | .ok (.obj ms) =>
    match ms.lookup "cases" with
    | some (.arr cs) => pure cs
    | _ => throw (IO.userError s!"{path}: no cases")
  | .ok _ => throw (IO.userError s!"{path}: not an object")

def member (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

def memberStr (v : Value) (k : String) : IO String :=
  match member v k with
  | some (.str s) => pure s
  | _ => throw (IO.userError s!"no string {k}")

/-- Whether v1's `canon` text of an answer reads back as that answer: every string in it
non-empty and free of `,`, `[` and `]` (v1 wrote strings unquoted). -/
partial def plainStrings : Value → Bool
  | .str s => !s.isEmpty && !s.any fun c => c == ',' || c == '[' || c == ']'
  | .arr xs => xs.all plainStrings
  | _ => true

/-- A v1 corpus of the strike family (`strike`) or SR9 (`sr9`): every case's `input`
through `<family> <fn>`; v1's `canon` text of the answer compared with `expect`. -/
def runCanonCalls (family : String) (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases path do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo family fn input
    let ok := match got with
      | .ok v => v.canon == some expect && plainStrings v
      | .error _ => false
    t ← t.check ok s!"{family} {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))}"
  return t.pair

/-- A v1 corpus's owed list: `(id, reason)` for each case the Calculator does not answer yet. -/
def owedList (path : System.FilePath) : IO (List (String × String)) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => do pure (← memberStr o "id", ← memberStr o "reason")
    | _ => throw (IO.userError s!"{path}: no owed list")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- The names of a v1 corpus's owed cases (`{"owed": [{"name": ...}, ...]}`). -/
def owedNames (path : System.FilePath) : IO (List String) := do
  match readString (← IO.FS.readFile path) with
  | .ok (.obj ms) =>
    match ms.lookup "owed" with
    | some (.arr os) => os.mapM fun o => memberStr o "name"
    | _ => throw (IO.userError s!"{path}: no owed list")
  | _ => throw (IO.userError s!"{path}: not an object")

/-- A v1 corpus of `{name, fn, args, expected}` cases: every case's `args` through `call`
with the Calculator's name of v1's `run_case` function; v1's text, or v1's word as a
refusal's detail (`ERROR:<word>`); a case the owed list names answered `OWED`, and no
other. -/
def runTextCalls (family : String) (path : System.FilePath) (owed : List String)
    (functions : List (String × String)) (call : String → Value → Except Refusal Value) :
    IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases path do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let some fn := functions.lookup (← memberStr c "fn")
      | throw (IO.userError s!"{name}: unknown function")
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := call fn args
    let ok := match got, owed.contains name with
      | .error r, true => r.code == .owed
      | .ok (.str text), false => text == expected
      | .error r, false => r.code == .badArgument && "ERROR:" ++ r.detail == expected
      | _, _ => false
    t ← t.check ok s!"{family} {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-! ## The families' bounds, at each and one past it

Built here, too long for a line of `pcalc.json`. A request at a bound must not be refused
by it; one past it must be, with the bound named. -/

/-- Whether an answer is a refusal by one of the Calculator's family bounds. -/
def boundRefusal : Except Refusal Value → Bool
  | .error r => r.code == .badArgument && (r.detail.splitOn "the Calculator's bound").length > 1
  | .ok _ => false

def strs (xs : List String) : Value := .arr (xs.map .str)

/-- `n` cluster rows of distinct models. -/
def clusterRows (n : Nat) : Value :=
  .arr ((List.range n).map fun (i : Nat) => .arr [.str s!"m{i}", .str "c", .int (i : Int), .int 1])

/-- `n` strike records, each with one assumption and `cites` citations of the next. -/
def strikeRecords (n cites : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"R{i}", .obj [("assumptions", strs [s!"a{i}"]),
    ("cites", strs ((List.range cites).map fun _ => s!"R{(i + 1) % n}")), ("steps", .int 1)]))

/-- A suite of `n` records, each with `cites` citations, and `k` contradictions. -/
def suite (n cites k : Nat) : Value :=
  .obj [("records", .obj ((List.range n).map fun i => (s!"R{i}", .obj [
      ("regime", .str (if i % 2 == 0 then "M" else "L")), ("assumptions", strs [s!"A{i}"]),
      ("cites", strs ((List.range cites).map fun _ => s!"R{(i + 1) % n}")),
      ("steps", .int 1), ("domain", .str "MAIN"), ("sr1_fail", .bool false)]))),
    ("contradictions", .arr ((List.range k).map fun i => strs [s!"R{i % n}", s!"R{(i + 1) % n}"]))]

/-- `n` standing probe records, each citing the next. -/
def probeRecords (n : Nat) : Value :=
  .obj ((List.range n).map fun i => (s!"P{i}", .obj [
    ("cites", strs (if i + 1 < n then [s!"P{i + 1}"] else [])), ("assumptions", strs []),
    ("standing", .bool true)]))

/-- An M `compare` request with `n` standing records whose values and uncertainties carry
`d` digits. -/
def standingCompare (n d : Nat) : Value :=
  let digits (lead : Nat) : Value := .num ⟨((lead * 10 ^ (d - 1) + 7 : Nat) : Int), -((d : Int) - 1)⟩
  let mrec (x : Nat) : Value := .obj [("x", .int x), ("u", .int 1),
    ("unit", .str "m")]
  .obj [("kind", .str "M"), ("original", mrec 10), ("reproduction", mrec 11),
    ("standing", .arr ((List.range n).map fun (i : Nat) =>
      .obj [("x", digits (1 + i % 9)), ("u", digits 1)])), ("k", .int 2)]

/-- `n` revisions, each allocating `per` identifiers. -/
def revisions (n per : Nat) : Value :=
  .arr ((List.range n).map fun (i : Nat) => .obj [("rev", .int (i : Int)),
    ("allocated", strs ((List.range per).map fun j => s!"a{i}_{j}"))])

/-- `n` measurements whose values carry `d` digits. -/
def measurements (n d : Nat) : Value :=
  .arr ((List.range n).map fun i =>
    .obj [("x", .num ⟨((10 ^ (d - 1) + i : Nat) : Int), -((d : Int) - 1)⟩), ("u", .num ⟨((10 ^ (d - 1) : Nat) : Int), -((d : Int) - 1)⟩)])

/-- The specification's root and `n - 1` section pages, each with one block. -/
def specPages (n : Nat) : Value :=
  .arr (.arr [.str "The Principia Machina/TPS", .str "<pre>\nroot\n</pre>"] ::
    (List.range (n - 1)).map fun i =>
      .arr [.str s!"The Principia Machina/TPS/{i / 100 + 1}.{i % 100} Section {i}",
        .str s!"<pre>\nsection {i}\n</pre>"])

/-- A digest of 64 lowercase hexadecimal characters. -/
def hex64a : String := String.ofList (List.replicate 64 'a')

/-- `n` members of the instruction set, of distinct titles. -/
def members (n : Nat) : Value :=
  .arr ((List.range n).map fun i => .arr [.str s!"Member {i}", .str hex64a])

/-- `n` copies of a value, as a list. -/
def valueCopies (n : Nat) (v : Value) : Value := .arr (List.replicate n v)

/-- `n` code points `c`. -/
def chars (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-- A value's canonical JSON as a string: a Provision's text built as a value. -/
def jsonText (v : Value) : Value := .str (v.canonicalJson.getD "")

/-- A Starting Set of `n` empty entries in each of `kinds`. -/
def entriesTpk (kinds : List String) (n : Nat) : Value :=
  .obj (kinds.map fun k => (k, valueCopies n (.obj [])))

/-- The Starting Set's six kinds. -/
def tpkKinds : List String := ["DOF", "CONSTANT", "LAW", "ASSUMPTION", "CONSTRAINT", "BOUNDARY"]

/-- A text that writes one ASSUMPTION `{S}`, and a claim binding `S` to one name of `n` code
points: the PROPOSITION filled holds `n`. -/
def filledRequest (n : Nat) : Value :=
  .obj [("modules", .arr [jsonText (.obj [("ID", .str "FILL"),
      ("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str "{S}")]])])]),
    ("claims", .arr [.obj [("ID", .str "FILL"), ("BIND", .obj [("S", strs [chars n 'n'])])]])]

/-- A `module_check` text that writes one ASSUMPTION `{S}` with one test binding binding `S`
to one name of `n` code points. -/
def filledCheck (n : Nat) : Value :=
  .obj [("text", jsonText (.obj [("ID", .str "FILL"),
      ("ASSUMPTIONS", .arr [.obj [("PROPOSITION", .str "{S}")]]),
      ("TEST_BINDINGS", .arr [.obj [("BIND", .obj [("S", strs [chars n 'n'])])]])])),
    ("modules", .arr [])]

/-- A text of `terms` TERMs aimed at `V`, claimed with `V` bound to `names` names. -/
def placedRequest (terms names : Nat) : Value :=
  .obj [("modules", .arr [jsonText (.obj [("ID", .str "TERMS"),
      ("TERMS", valueCopies terms (.obj [("TARGET", .str "V")]))])]),
    ("claims", .arr [.obj [("ID", .str "TERMS"),
      ("BIND", .obj [("V", strs ((List.range names).map fun i => s!"v{i}"))])]])]

/-- The same, `module_check`'s text placing its terms by its own test binding. -/
def placedCheck (terms names : Nat) : Value :=
  .obj [("text", jsonText (.obj [("ID", .str "TERMS"),
      ("TERMS", valueCopies terms (.obj [("TARGET", .str "V")])),
      ("TEST_BINDINGS", .arr [.obj [("BIND", .obj [("V", strs ((List.range names).map fun i => s!"v{i}"))])]])])),
    ("modules", .arr [])]

/-- A `module_verify` request whose base and draft hold 384 entries each, and one text whose
test binding's Starting Set holds `n`. -/
def entriesInAll (n : Nat) : Value :=
  .obj [("base", .obj [("TPK", entriesTpk tpkKinds 64)]), ("draft", .obj [("TPK", entriesTpk tpkKinds 64)]),
    ("modules", .arr [jsonText (.obj [("TEST_BINDINGS", .arr [.obj [("TPK",
      .obj [("DOF", valueCopies (min n 64) (.obj [])), ("CONSTANT", valueCopies (min (n - 64) 64) (.obj [])),
        ("LAW", valueCopies (min (n - 128) 64) (.obj [])), ("ASSUMPTION", valueCopies (n - 192) (.obj []))])]])])])]

/-- A Starting Set with one entry of `kind` whose `field` holds `n` code points. -/
def fieldTpk (kind field : String) (n : Nat) : Value :=
  .obj [("tpk", .obj [(kind, .arr [.obj [(field, .str (chars n 'p'))]])])]

/-- A register of `n` standing M RESULT records of `E_x`, the first holding `entries - 1`
assumptions and citing itself, so that the register holds `entries` ASSUMPTIONS and CITES
entries in all. -/
def register (n entries : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj ([("ID", .str s!"R{i}"), ("CLASS", .str "RESULT"),
    ("QUANTITY", .str "E_x"), ("REGIME", .str "M")] ++
    if i == 0 then [("ASSUMPTIONS", strs ((List.range (entries - 1)).map fun j => s!"A{j}")),
      ("CITES", strs ["R0"])] else []))

/-- A decimal `m × 10^e`. -/
def dec (m e : Int) : Value := .num ⟨m, e⟩

/-- An account of RANK. -/
def account : Value :=
  .obj [("account", .str "a"), ("S", dec 5 (-1)), ("S_lo", dec 4 (-1)), ("S_hi", dec 6 (-1)),
    ("n", .int 0), ("active", .bool true)]

/-- A string of `n` code points. -/
def codePoints (n : Nat) : String := String.ofList (List.replicate n 'a')

/-- Strings of `total` code points in all, at most `maxText` each. -/
def textsOf (total : Nat) : List Value :=
  let full := total / Record.maxText
  let rest := total % Record.maxText
  ((List.range full).map fun _ => .str (codePoints Record.maxText)) ++
    (if rest = 0 then [] else [.str (codePoints rest)])

/-! ## The governor, the permissions, SHA-256 and Unicode through `pcalc`

The families `governor`, `permissions`, `sha256` and `unicode`, each corpus's cases given to
the family's functions through `Calculator.respondTo`, and their bounds at and past each
bound through `Calculator.answer`, the slowest accepted request of each family timed. -/

/-- A wire word as a value. -/
def wordValue {α : Type} [WireWord α] (a : α) : Value := .str (WireWord.toWire a)

/-- The member `k` of an object, which the case needs. -/
def need (v : Value) (k : String) : IO Value :=
  match member v k with
  | some x => pure x
  | none => throw (IO.userError s!"no member {k} in {repr (v.canonicalJson)}")

/-- An object with the member `k` set to `x`, in place or added. -/
def withMember (v : Value) (k : String) (x : Value) : Value :=
  match v with
  | .obj ms => if ms.any (·.1 == k) then .obj (ms.map fun m => if m.1 == k then (k, x) else m)
    else .obj (ms ++ [(k, x)])
  | _ => v

/-- An answer's canonical JSON; `none` for a refusal. -/
def canonOf (r : Except Refusal Value) : Option String :=
  match r with
  | .ok v => v.canonicalJson
  | .error _ => none

/-- A refusal's code, `none` for an answer. -/
def refusalOf (r : Except Refusal Value) : Option RefusalCode :=
  match r with
  | .ok _ => none
  | .error f => some f.code

/-! ## The zones through `pcalc` -/

/-- A Starting Set of `n` DOF, each `{"NAME": "x<i>", "DIMENSION": "L1"}`. -/
def dofTpk (n : Nat) : Value :=
  .obj [("DOF", .arr ((List.range n).map fun i =>
    .obj [("NAME", .str s!"x{i}"), ("DIMENSION", .str "L1")]))]

end Tests.Calculator
