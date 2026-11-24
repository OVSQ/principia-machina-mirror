import Tests.Calculator.Common

/-!
The Calculator's runners of the family `unicode`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- Unicode's NormalizationTest.txt through `unicode`: one check a line, of the file's ten
conformance equalities through `nfc` and `nfd` and of the general category of each code point
of its first column through `general_category`, against UnicodeData.txt as `Tests.Unicode`
reads it. -/
def runUnicodeCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let u ← IO.ofExcept ((Tests.Unicode.readUnicodeData (← IO.FS.readFile "vectors/unicode/UnicodeData.txt")).mapError IO.userError)
  let call (f s : String) : Option String := canonOf (respondTo "unicode" f (.obj [("text", .str s)]))
  let canonStr (s : String) : Option String := (Value.str s).canonicalJson
  let mut lines := 0
  for raw in (← IO.FS.readFile "vectors/unicode/NormalizationTest.txt").splitOn "\n" do
    let line := ((raw.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty || line.startsWith "@Part" then continue
    let cols := line.splitOn ";"
    unless cols.length == 6 do throw (IO.userError s!"unicode: not five columns: {line}")
    let some cs := (cols.take 5).mapM Tests.Unicode.codes?
      | throw (IO.userError s!"unicode: a column that does not read: {line}")
    let col := (cs.map String.ofList).toArray
    let f (k : Nat) : String := col[k]!
    let nfcOk := [0, 1, 2].all (fun k => call "nfc" (f k) == canonStr (f 1)) &&
      [3, 4].all (fun k => call "nfc" (f k) == canonStr (f 3))
    let nfdOk := [0, 1, 2].all (fun k => call "nfd" (f k) == canonStr (f 2)) &&
      [3, 4].all (fun k => call "nfd" (f k) == canonStr (f 4))
    let cats := (Value.arr ((cs.headD []).map fun c => .str (u.category[c.toNat]!).code)).canonicalJson
    let gcOk := call "general_category" (f 0) == cats
    t ← t.check (nfcOk && nfdOk && gcOk) s!"unicode {line}: nfc {nfcOk}, nfd {nfdOk}, general_category {gcOk}"
    lines := lines + 1
  IO.println s!"pcalc unicode: {lines} lines of NormalizationTest.txt through nfc, nfd and general_category"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Unicode

open Tests.Calculator

/-- The family `unicode`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc unicode (NormalizationTest, UnicodeData)", runUnicodeCalls),
]

end Tests.Calculator.Unicode
