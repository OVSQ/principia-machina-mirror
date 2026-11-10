import Principia.Calculator.Interface
import Principia.Calculator.Strike
import Principia.Strike.Landing

/-!
# Family `landing`: the checks Custos runs at landing

* `strike_screen {"records", "tfk", "incoming"}`: `["OK", [[id1, id2, word, via], ...]]`,
  the pairs the strike rule would have to strike that the batch reaches
  (`Principia.Strike.Landing.screen`), `word` `CONTRADICTS` or `UNDECIDED`, `via` the batch
  record that reaches the pair; `[]` when there is none. `records` is the register as it
  would stand, the batch appended; `incoming` the batch's identifiers; `tfk` the Research
  Assembly. Refused as `comparison_set` refuses, `["REFUSED", [[code, field, message]]]`,
  a value; owed, and refused `OWED`, past `maxQuantities` quantities.

Bounds, measured: `records` at most `Strike.maxRecords` members; where the batch reaches a
QUANTITY, the register within `maxScreenRecords` records holding `maxScreenEntries`
ASSUMPTIONS and CITES entries and `Strike.maxPoints` AT points (`Strike.registerWithin`), and
at most `maxQuantities` comparison sets.
-/

namespace Principia.Calculator.Landing

open Principia.Canonical

/-- The most members the register holds for `strike_screen` where the batch reaches a
QUANTITY, above `comparison_set`'s `Strike.maxScopeRecords`: the screen tests every pair of
the comparison set, and that test, not the set, is its cost. At the bounds (225 standing
RESULT records, 218 of one quantity and seven of seven others, eight quantities reached, each
record citing the next six in a cycle, the first also holding 150 distinct ASSUMPTIONS, 900 AT
points of 2047 bits, every one of the 23,653 pairs of the largest set held), one call takes
1.8 s, as with one quantity; with 2000 entries 1.9 s, with 1125 AT points 1.9 s, with 250
records 2.1 s. -/
def maxScreenRecords : Nat := 225

/-- The most ASSUMPTIONS and CITES entries the register's records hold in all for
`strike_screen` (see `maxScreenRecords`): about six for each record at the bound. The AT
points stay within `Strike.maxPoints`. -/
def maxScreenEntries : Nat := 1500

/-- The family's functions. -/
def calls : Family := [
  ("strike_screen", fun v => do
    let (records, tfk, incoming) ← match ← arguments ["records", "tfk", "incoming"] v with
      | [r, t, i] => pure (r, t, i)
      | _ => badArgument "the arguments do not read"
    let ids ← asStrings "incoming" incoming
    if let .arr rs := records then atMost "records" Strike.maxRecords rs
    match Principia.Strike.Landing.plan records ids with
    | some (_, _, []) => pure (.arr [.str "OK", .arr []])
    | _ =>
      Strike.registerWithin maxScreenRecords maxScreenEntries records
      Strike.registerAnswer (fun hs => .arr (hs.map Principia.Strike.Landing.Held.toValue))
        (Principia.Strike.Landing.screen records tfk ids))]

end Principia.Calculator.Landing
