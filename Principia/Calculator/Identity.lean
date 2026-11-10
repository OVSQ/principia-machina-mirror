import Principia.Calculator.Interface
import Principia.Identity

/-!
# Family `identity`: the PROMPT digest, the MODEL MAP, the change class and the comparison

Version 1's unit of identity (`Principia.Identity`), one function each, named as version 1
names it, its arguments named as version 1's test cases name them:

* `canonical_tools {"json"}`: the tool definitions in TPM's canonical JSON, a text.
* `prompt_digest {"family", "salt", "template", "tools"}`: the PROMPT digest, SHA-256 in
  lowercase hexadecimal.
* `family_of {"model", "map"}`: `UNMAPPED`, or `MAPPED|family|open|server|quantization|key`.
* `change_class {"certified", "last", "reported", "lookup"}`: `class|detail`.
* `identity_compare {"declared", "stated", "relayed", "inferred"}`: the overall line and
  the six pairs' lines.

Each argument is read as version 1 read it: a number written with a fraction or an
exponent is one version 1 read as a float, which every function refuses where it wants a
text or a flag. The answer is version 1's text of the result, each field of `family_of`
escaped as version 1 escaped it (`|` and `\` behind a backslash, a control as `\xNN`); a
request version 1 refused is refused with version 1's word as the detail, the checks made
in version 1's order. Every text is put in NFC as version 1 puts it, and every answer is
computed, so none is refused as owed.

Bounds, measured. Every text and list is bounded by the size of the request, 1 MiB, read
whole, and each function's time grows about in proportion to it, a sort aside. The slowest
requests found near that size: a PROMPT whose template is 680,000 characters of letters and
combining marks, put in NFC and digested with SHA-256, about 0.55 s; a tools text of 80,000
members in one object, sorted by their keys, about 0.4 s; a MODEL MAP of 13,000 rows, each
name put in NFC once and the names sorted to find one held twice, about 0.2 s.
-/

namespace Principia.Calculator.Identity

open Principia.Canonical
open Principia.Identity (Outcome Stop FamilyResult ChangeResult Comparison)

/-! ## Reading a request -/

/-- A request's value as version 1's identity functions received it: an integer as
Python's `int`, a number written with a fraction or an exponent as Python's `float`. -/
partial def zoneValue : Value → Zone.Value
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .num _ => .real
  | .str s => .str s
  | .arr xs => .arr (xs.map zoneValue)
  | .obj ms => .obj (ms.map fun (k, v) => (k, zoneValue v))

/-- The request's members, each one the function needs, as version 1 received them. -/
def read (names : List String) (v : Value) : Except Refusal (String → Zone.Value) := do
  let ms ← membersOf names v
  for n in names do
    let _ ← needed ms n
  pure fun k => ((ms.lookup k).map zoneValue).getD .null

/-! ## Version 1's texts -/

/-- Version 1's `_esc`: `|` and `\` behind a backslash, a control character and DEL as
`\x` and two lowercase hexadecimal digits, every other character as it is. -/
def esc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '|' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      "\\x" ++ String.ofList [Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)]
    else c.toString)

/-- Version 1's `render_family`. -/
def renderFamily : FamilyResult → String
  | .unmapped => "UNMAPPED"
  | .mapped fam o server quant key =>
    "|".intercalate ["MAPPED", esc fam, if o then "true" else "false",
      (server.map esc).getD "-", (quant.map esc).getD "-", esc key]

/-- Version 1's `render_class`: the class and its detail, `-` for none. -/
def renderClass (r : ChangeResult) : String :=
  WireWord.toWire r.cls ++ "|" ++ ((r.detail.map WireWord.toWire).getD "-")

/-- Version 1's `render_compare`: the overall line, then one line per pair. -/
def renderCompare (r : Comparison) : String :=
  "\n".intercalate (s!"overall|{WireWord.toWire r.overall}|{r.differ}" ::
    r.pairs.map fun (a, b, x) => s!"{a.name}|{b.name}|{WireWord.toWire x}")

/-- An answer as `pcalc` gives it: version 1's text, or version 1's word as a refusal. -/
def answer {α : Type} (render : α → String) : Outcome α → Except Refusal Value
  | .ok a => .ok (.str (render a))
  | .error (.refused r) => badArgument r.message

/-- The family's functions. -/
def calls : Family := [
  ("canonical_tools", fun v => do
    let g ← read ["json"] v
    answer id (Principia.Identity.canonicalTools (g "json"))),
  ("change_class", fun v => do
    let g ← read ["certified", "last", "reported", "lookup"] v
    answer renderClass
      (Principia.Identity.changeClass (g "certified") (g "last") (g "reported") (g "lookup"))),
  ("family_of", fun v => do
    let g ← read ["model", "map"] v
    answer renderFamily (Principia.Identity.familyOf (g "model") (g "map"))),
  ("identity_compare", fun v => do
    let g ← read ["declared", "stated", "relayed", "inferred"] v
    answer renderCompare
      (Principia.Identity.identityCompare (g "declared") (g "stated") (g "relayed") (g "inferred"))),
  ("prompt_digest", fun v => do
    let g ← read ["family", "salt", "template", "tools"] v
    answer id (Principia.Identity.promptDigest (g "family") (g "salt") (g "template") (g "tools"))),
]

end Principia.Calculator.Identity
