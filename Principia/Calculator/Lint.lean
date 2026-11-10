import Principia.Calculator.Identity
import Principia.Lint

/-!
# Family `lint`: the prompt lint's coded findings

Version 1's prompt lint (`Principia.Lint`), one function each, named as version 1 names it
and taking its arguments as version 1 names them; every argument may be absent, as
version 1 read each with `get`:

* `lint {"zone", "tools", "cap"}`: the findings on a SPONSOR ZONE and the JSON text of a
  tool list, in version 1's canonical text, `[{"code":...,"item":...,"locator":...},...]`.
  A zone or a tool list given as bytes is given as `zone_hex` or `tools_hex`, the bytes in
  hexadecimal, and one given in pieces as `zone_parts` or `tools_parts`, a list of
  `[text, count]` pairs, each text repeated `count` times, as version 1's test cases give
  them.
* `counts`, with the arguments of `lint`: the lint's findings counted per code,
  `{"PL0":n,...,"PL9":n}`, the only output of the lint the Research Client may place in
  a record's CAPABILITY.
* `lint_counts {"findings"}`: findings given counted per code, in the same form.
* `lint_norm {"text"}`: the text as the lint matches it.
* `name_tokens {"name"}`: the tokens of a tool name, a JSON list of texts.
* `tables {}`: the version of the lint's tables and their recorded SHA-256.

`counts` and `tables` are named as version 1's test cases name them: version 1 has no one
function for either (`counts` is `lint_counts` of `lint`). The answer is version 1's text;
a request version 1 refused is refused with version 1's word as the detail. The lint
itself never refuses: an input it cannot read is its finding PL0. Every text is put in NFC
as version 1 puts it, so nothing is owed.

Bounds, measured. Version 1 lints a zone and a tool text of at most 1 MiB of UTF-8 each and
finds PL0 past that; a text given in pieces past it is not built. At that size the slowest
inputs found, a zone of hidden characters (one finding each) and a tool list of strings
each holding five, take about 2 s to lint. The findings can be many times longer than the
input that gives them, so `lint` writes at most `maxAnswerChars` characters of them; past
that it is refused, and `counts` answers.
-/

namespace Principia.Calculator.Lint

open Principia.Canonical
open Principia.Lint (Input Outcome Stop Finding findingsJson countsJson)

/-! ## The family's bounds, measured -/

/-- The most characters of findings `lint` writes, the size of the largest request: a
zone of 1 MiB of hidden characters gives 18,763,246 characters of findings, which take
about 12 s to write; 1,288,898 characters take about 0.2 s. -/
def maxAnswerChars : Nat := 1048576

/-! ## Reading a request -/

/-- A hexadecimal digit's value, either case. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Bytes from hexadecimal, two digits each. -/
def hexBytes? (s : String) : Option ByteArray :=
  let rec go : List Char → Array UInt8 → Option (Array UInt8)
    | [], acc => some acc
    | a :: b :: rest, acc => do go rest (acc.push (((← hexDigit? a) * 16 + (← hexDigit? b)).toUInt8))
    | [_], _ => none
  (go s.toList #[]).map ByteArray.mk

/-- A text past version 1's size, in place of one given in pieces: any such text is PL0 for
its size alone. -/
def pastSize : String := String.ofList (List.replicate (Principia.Lint.maxBytes + 1) ' ')

/-- The pieces of `<name>_parts`, each a text and how many times it is repeated (a count
below 0 as 0, as version 1 repeated it). -/
def readParts (name : String) (v : Value) : Except Refusal (List (String × Nat)) := do
  let ps ← asList s!"{name}_parts" v
  ps.mapM fun p => match p with
    | .arr [.str s, .int n] => pure (s, n.toNat)
    | _ => badArgument s!"an entry of {name}_parts is not [text, count]"

/-- A zone or a tool text as version 1 read it: `<name>_hex` as bytes, else `<name>_parts`
joined, else `<name>` itself, a text or anything else. -/
def readInput (ms : List (String × Value)) (name : String) : Except Refusal Input := do
  match ms.lookup (name ++ "_hex") with
  | some h =>
    match hexBytes? (← asString s!"{name}_hex" h) with
    | some b => pure (.bytes b)
    | none => badArgument s!"{name}_hex is not bytes in hexadecimal"
  | none =>
  match ms.lookup (name ++ "_parts") with
  | some p =>
    let parts ← readParts name p
    if Principia.Lint.maxBytes < (parts.map fun (s, n) => s.utf8ByteSize * n).sum then
      pure (.text pastSize)
    else pure (.text (String.join (parts.map fun (s, n) => String.join (List.replicate n s))))
  | none =>
  match ms.lookup name with
  | some (.str s) => pure (.text s)
  | _ => pure .other

/-- A member as version 1 read it with `get`: `null` when absent. -/
def member (ms : List (String × Value)) (k : String) : Zone.Value :=
  ((ms.lookup k).map Identity.zoneValue).getD .null

/-- The lint's findings on a request of `lint`'s arguments. -/
def findingsOf (v : Value) : Except Refusal (Outcome (List Finding)) := do
  let ms ← membersOf ["cap", "tools", "tools_hex", "tools_parts", "zone", "zone_hex", "zone_parts"] v
  let zone ← readInput ms "zone"
  let tools ← readInput ms "tools"
  pure (Principia.Lint.lint zone tools (member ms "cap"))

/-! ## Version 1's texts -/

/-- Version 1's `json.dumps` of the tokens: each is ASCII letters and digits, nothing to
escape. -/
def tokensJson (ts : List String) : String :=
  "[" ++ ",".intercalate (ts.map fun t => "\"" ++ t ++ "\"") ++ "]"

/-- An answer as `pcalc` gives it: version 1's text, or version 1's word as a refusal. -/
def answer {α : Type} (render : α → String) : Outcome α → Except Refusal Value
  | .ok a => .ok (.str (render a))
  | .error (.refused r) => badArgument r.message

/-- The findings' text, within `maxAnswerChars`. -/
def findingsWithin (fs : List Finding) : Except Refusal Value :=
  let text := findingsJson fs
  if maxAnswerChars < text.length then
    badArgument s!"the findings' text is longer than {maxAnswerChars} characters (the Calculator's bound); counts gives their number per code"
  else .ok (.str text)

/-- The family's functions. -/
def calls : Family := [
  ("counts", fun v => do
    answer (fun fs => countsJson (Principia.Lint.counts fs)) (← findingsOf v)),
  ("lint", fun v => do
    match ← findingsOf v with
    | .ok fs => findingsWithin fs
    | .error (.refused r) => badArgument r.message),
  ("lint_counts", fun v => do
    let ms ← membersOf ["findings"] v
    answer countsJson (Principia.Lint.countsOf (member ms "findings"))),
  ("lint_norm", fun v => do
    let ms ← membersOf ["text"] v
    answer id (Principia.Lint.lintNorm (member ms "text"))),
  ("name_tokens", fun v => do
    let ms ← membersOf ["name"] v
    answer tokensJson (Principia.Lint.nameTokens (member ms "name"))),
  ("tables", fun v => do
    let _ ← membersOf [] v
    pure (.str Principia.Lint.tablesAnswer)),
]

end Principia.Calculator.Lint
