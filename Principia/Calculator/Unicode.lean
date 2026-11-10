import Principia.Calculator.Interface
import Principia.Unicode

/-!
# Family `unicode`: normalization and the general category on the command line

`Principia.Unicode` at Unicode 15.1.0 on the command line, as version 1 read text
(the same version): the Research Client and the certification probes check an agent's own
normalization against it.
* `nfc {"text"}`: the text in Normalization Form C.
* `nfd {"text"}`: the text in Normalization Form D.
* `general_category {"text"}`: the general category of each of the text's code points, in
  order, as its two-letter code (`Lu`, `Mn`, ...: the Unicode Character Database's spelling).

Bounds: a text of at most `maxText` code points. Normalization sorts each run of
combining marks by class, so its cost grows faster than the text where one run is long.
The slowest accepted request measured, `nfc` of a letter and 131,071 combining marks drawn
at random from ten, four of which decompose into two (one run of 183,409 marks once
decomposed), took 1.45 s on the command line and `nfd` of it 1.19 s; 131,071 marks of falling
class, 0.83 s; `general_category` at most 0.19 s. NFC of 500,000 combining marks took about
4.7 s, which the bound refuses. Python's `unicodedata` at Unicode 15.1.0 gives the same NFC
and NFD of these texts.
-/

namespace Principia.Calculator.Unicode

open Principia.Canonical

/-- The most code points a text holds: 2^17. -/
def maxText : Nat := 131072

/-- A text argument within `maxText` code points. -/
def textOf (v : Value) : Except Refusal String := do
  let s ← asString "text" (← argument1 "text" v)
  if maxText < s.length then
    badArgument s!"text holds more than {maxText} code points (the Calculator's bound)"
  else pure s

/-- The family's functions. -/
def calls : Family := [
  ("general_category", fun v => do
    let s ← textOf v
    pure (.arr (s.toList.map fun c => .str (Principia.Unicode.generalCategory c).code))),
  ("nfc", fun v => do pure (.str (Principia.Unicode.nfc (← textOf v)))),
  ("nfd", fun v => do pure (.str (Principia.Unicode.nfd (← textOf v)))),
]

end Principia.Calculator.Unicode
