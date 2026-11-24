import Tests.Calculator.Common

/-!
The Calculator's runners of the family `hold`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## Hold scope through `pcalc` -/

/-- `hold_corpus.json`: all 140 cases through `hold <fn>`, version 1's `tpx_allocate` spelled
`allocate_identifiers`; version 1's `canon` text of the answer compared with `expect`. -/
def runHoldCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/hold_corpus.json" do
    let id ← memberStr c "id"
    let v1 ← memberStr c "fn"
    let fn := if v1 == "tpx_allocate" then "allocate_identifiers" else v1
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "hold" fn input
    let ok := match got with
      | .ok v => v.canon == some expect
      | .error _ => false
    t ← t.check ok s!"hold {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canon))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The hold family's bounds (`Calculator.Hold`), each at its value and one past it. -/
def runHoldBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let blocks (n : Nat) : Value := .obj [("account", .str "acct"), ("admission_block", .str "B0"),
    ("blocks", .arr ((List.range n).map fun i => .obj [("block_id", .str s!"B{i}"), ("canary", .null)]))]
  let cases : List (String × String × Value × Bool) := [
    ("history at 4000 blocks", "hold_scope",
      .obj [("history", blocks 4000), ("lookback_passes", .int 2)], false),
    ("history past 4000 blocks", "hold_scope",
      .obj [("history", blocks 4001), ("lookback_passes", .int 2)], true),
    ("records at 1000", "held_closure",
      .obj [("records", .arr ((List.range 1000).map fun i => .obj [("id", .str s!"RR-{i}")])),
        ("seeds", .obj [])], false),
    ("records past 1000", "held_closure",
      .obj [("records", .arr ((List.range 1001).map fun i => .obj [("id", .str s!"RR-{i}")])),
        ("seeds", .obj [])], true),
    ("a name at 16384 code points", "allocate_identifiers",
      .obj [("range", .obj [("prefix", .str (codePoints 16384))])], false),
    ("a name past 16384 code points", "allocate_identifiers",
      .obj [("range", .obj [("prefix", .str (codePoints 16385))])], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "hold" fn request
    t ← t.check (boundRefusal got == refused)
      s!"hold {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Hold

open Tests.Calculator

/-- The family `hold`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc hold (hold_corpus)", runHoldCalls),
  ("pcalc hold bounds", runHoldBounds),
]

end Tests.Calculator.Hold
