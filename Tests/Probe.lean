import Principia
import Lean.Data.Json

/-!
The probe family's runner: v1's `probe_corpus.json` (252 cases), against
`Principia.Probe`.

A case is `{"name", "fn", "args", "hand_checked", "expected"}`, `expected` v1's text of
the answer: its render (`render_compare`, `render_load`, ...), or `ERROR:` and v1's
message. The Calculator's text is written in the same form and compared byte for byte;
numbers that v1 printed with `%.12g` are the exact values correctly rounded to twelve
significant digits. A render whose separators an identifier could hold (a comma in
LOAD's and the view's lists, which v1 does not escape) fails its case rather than compare
texts that could collide.

Nothing is owed: the draws are SHA-256 (decision D2) compared exactly (decision D6), so
`vectors/probe_corpus.owed.json` must list none. For each `uniform` case the 52 bits of the
draw are also read a second way, from the first 13 characters of the digest's hexadecimal
text as v1 read them, and must agree with the bytes' reading (`top52`). The mutation checks
run first: the comparison must refuse a text with two fields swapped or a word changed.
-/

namespace Tests.Probe

open Lean Principia Principia.Probe

/-- A JSON value as v1's functions received it. -/
partial def datum : Json → Datum
  | .null => .null
  | .bool b => .bool b
  | .num n => if n.exponent = 0 then .int n.mantissa
    else .real ((n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat))
  | .str s => .str s
  | .arr xs => .arr (xs.toList.map datum)
  | .obj kvs => .obj (kvs.toList.map fun (k, v) => (k, datum v))

/-- The identifiers a render lists, which must hold no comma for its text to be read one
way. -/
def plainIds (ids : List String) : Bool := ids.all fun s => !s.toList.contains ','

/-- A case's answer, as v1's text. -/
def answer (fn : String) (a : Datum) : Except String String :=
  let g (k : String) := a.getD k
  let p := g "params"
  let out {α : Type} (r : Answer α) (render : α → String) : String := r.text render
  match fn with
  | "uniform" => .ok (out (uniform (g "tag") (g "r") (g "counter")) Exact.printRat12)
  | "compare" =>
    .ok (out (compare (g "kind") (g "original") (g "reproduction") (g "standing") (g "k")
      (g "material_ratio")) renderCompare)
  | "load" =>
    let r := load (g "records") (g "r")
    match r with
    | .ok (_, ids) => if plainIds ids then .ok (out r renderLoad)
      else .error "an identifier holding a comma"
    | _ => .ok (out r renderLoad)
  | "el" => .ok (out (expectedLoss (g "e_lo") (g "load")) Exact.printRat12)
  | "ratio" => .ok (out (ratioStep (g "state") (g "r") p) renderRatio)
  | "schedule" => .ok (out (scheduleStep (g "state") (g "r") p) renderSchedule)
  | "probe" =>
    .ok (out (probeDraw (g "schedule") (g "ratio") (g "reset") (g "has_own_record") (g "r") p)
      renderProbe)
  | "step" => .ok (out (probeStep (g "state") (g "r") p (g "has_own_record")) renderStep)
  | "reset" =>
    .ok (out (resetUpdate (g "reset") (g "event") (g "account_state") p) renderReset)
  | "view" =>
    let r := historicalView (g "revisions") (g "target")
    match r with
    | .ok (_, ids) => if plainIds ids then .ok (out r renderView)
      else .error "an identifier holding a comma"
    | _ => .ok (out r renderView)
  | other => .error s!"unknown fn {other}"

/-! ## The mutation checks: the comparison refuses what it must -/

/-- Swap two `|` fields of a text. -/
def swapFields (t : String) (i j : Nat) : String :=
  let fs := t.splitOn "|"
  "|".intercalate ((fs.set i (fs.getD j "")).set j (fs.getD i ""))

/-- Each check is `true` when it holds: a render compared with a mutated copy differs, and
the escaped renders of different findings differ. -/
def mutationChecks : List (String × Bool) :=
  let m : MCompare := ⟨"MATCH", 1, 1/10, 23/20, 1/10, 1, 2, 9/8, "m", some 1⟩
  let t := renderCompare (.m m)
  let lA := renderCompare (.l "MATCH" "a|b" "c")
  let lB := renderCompare (.l "MATCH" "a" "b|c")
  let r := renderReset ⟨true, 2, "-"⟩
  [("the M render as computed", t == "M|MATCH|1|0.1|1.15|0.1|1|2|1.06066017178|m|1"),
   ("x1 and x2 swapped", swapFields t 2 4 != t),
   ("S and k swapped", swapFields t 6 7 != t),
   ("the outcome word changed", t.replace "|MATCH|" "|MATCH WITH DIFFERENCE NOTED|" != t),
   ("findings holding a bar print apart", lA != lB),
   ("the reset's fields swapped", swapFields r 0 1 != r),
   ("a comma in a listed id is refused", !plainIds ["a,b"])]

/-! ## The run -/

/-- The owed list: case, reason. -/
def owedList : IO (List (String × String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/probe_corpus.owed.json"))
  let xs ← IO.ofExcept (j.getObjValAs? (Array Json) "owed")
  xs.toList.mapM fun o => do
    return (← IO.ofExcept (o.getObjValAs? String "case"),
      ← IO.ofExcept (o.getObjValAs? String "reason"))

/-- A hexadecimal digit's value. -/
def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- v1's reading of a draw: `int(h[:13], 16)` over the digest's hexadecimal text. -/
def bitsFromHex (tag r : String) (counter : Nat) : Nat :=
  let h := Digest.ofPreimage (Digest.preimage [tag, "1", r, toString counter])
  (h.toList.take 13).foldl (fun acc c => acc * 16 + hexValue c) 0

def runProbe : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for (what, ok) in mutationChecks do
    unless ok do
      IO.eprintln s!"FAIL probe runner mutation check: {what}"
      fail := fail + 1
  let listed ← owedList
  for (code, why) in listed do
    IO.eprintln s!"FAIL probe {code}: listed as owed ({why}), but nothing is owed"
    fail := fail + 1
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile "vectors/probe_corpus.json"))
  let cases ← IO.ofExcept (json.getObjValAs? (Array Json) "cases")
  let mut bitsChecked := 0
  for c in cases do
    let name ← IO.ofExcept (c.getObjValAs? String "name")
    let fn ← IO.ofExcept (c.getObjValAs? String "fn")
    let expected ← IO.ofExcept (c.getObjValAs? String "expected")
    let args := datum (← IO.ofExcept (c.getObjVal? "args"))
    if fn == "uniform" then
      match args.getD "tag", args.getD "r", (args.getD "counter").intIn? 0 countMax with
      | .str tag, .str r, some n =>
        if tag != "" && isHex32 (.str r) then
          bitsChecked := bitsChecked + 1
          unless drawBits tag r n.toNat == bitsFromHex tag r n.toNat do
            IO.eprintln s!"FAIL probe {name}: the draw's bits read from the bytes and from the hexadecimal text differ"
            fail := fail + 1
      | _, _, _ => pure ()
    match answer fn args with
    | .error e =>
      IO.eprintln s!"FAIL probe {name}: {e}"
      fail := fail + 1
    | .ok got =>
      if got == expected then pass := pass + 1
      else
        IO.eprintln s!"FAIL probe {name}: expected {repr expected}, got {repr got}"
        fail := fail + 1
  IO.println s!"probe_corpus: {pass} computed and agree, none owed, {fail} fail; the draw's bits read two ways on {bitsChecked} uniform cases"
  return (pass, fail)

end Tests.Probe
