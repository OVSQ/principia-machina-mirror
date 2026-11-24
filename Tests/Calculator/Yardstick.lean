import Tests.Calculator.Common

/-!
The Calculator's runners of the family `yardstick`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The yardsticks through `pcalc` -/

/-- A value of `yardstick_corpus.json`'s expectation, or of the answer: a decimal, or
`numerator/denominator`, read exactly. -/
def exactOf (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [a, b] => do
    let n ← a.toInt?
    let d ← b.toNat?
    if d = 0 then none else some ((n : Rat) / (d : Rat))
  | _ => Decimal.value s

/-- `yardstick_corpus.json`: all 46 cases through `yardstick <fn>`. -/
def runYardstickCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/yardstick_corpus.json" do
    let id ← memberStr c "id"
    let fn ← memberStr c "fn"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let keys := if fn == "yardstick_key" then ["tms", "name", "rid", "records", "fields"]
      else ["tms", "name", "suite"]
    let request : Value := .obj (keys.filterMap fun k => (member input k).map (k, ·))
    let got := respondTo "yardstick" fn request
    let ok := match got with
      | .ok (.arr [.str "REFUSED", .str r]) => expect == "[REFUSED," ++ r ++ "]"
      | .ok (.arr [.str "OK", .arr vs]) =>
        if fn == "yardstick_key" then
          let want := (String.ofList ((expect.toList.drop 5).dropLast.dropLast)).splitOn "," |>.map exactOf
          let have_ := vs.map fun | .str s => exactOf s | _ => none
          want == have_ && want.all Option.isSome
        else false
      | .ok v => fn != "yardstick_key" && v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"yardstick {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Yardstick

open Tests.Calculator

/-- The family `yardstick`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc yardstick (yardstick_corpus)", runYardstickCalls),
]

end Tests.Calculator.Yardstick
