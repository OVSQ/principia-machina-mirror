import Tests.Calculator.Common

/-!
The Calculator's runners of the family `sha256`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- The CAVP response files through `sha256 digest`, the message as hexadecimal; FIPS's
examples through `sha256 digest_text`. -/
def runSha256Calls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let j ← readJson "vectors/sha256.json"
  let mut messages := 0
  for e in ← arr (← field j "cavp") do
    let file ← str e "file"
    let bytes ← IO.FS.readBinFile ("vectors" / file)
    let some text := String.fromUTF8? bytes | throw (IO.userError s!"{file}: not UTF-8")
    let ms ← IO.ofExcept ((Tests.Sha256.readResponse text).mapError fun e => IO.userError s!"{file}: {e}")
    for m in ms do
      let got := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str (Principia.Sha256.hex m.msg))]))
      t ← t.check (got == (Value.str m.md).canonicalJson) s!"sha256 digest {file} Len = {m.bits}: got {repr got}"
      messages := messages + 1
  let examples ← arr (← field j "examples")
  for c in examples do
    let n ← IO.ofExcept (c.getObjValAs? Nat "repeat")
    let text := String.join (List.replicate n (← str c "text"))
    let got := canonOf (respondTo "sha256" "digest_text" (.obj [("text", .str text)]))
    t ← t.check (got == (Value.str (← str c "expect")).canonicalJson) s!"sha256 digest_text {← str c "id"}: got {repr got}"
  IO.println s!"pcalc sha256: {messages} CAVP messages through digest, {examples.length} FIPS examples through digest_text"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Sha256

open Tests.Calculator

/-- The family `sha256`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc sha256 (sha256, SHA256ShortMsg, SHA256LongMsg)", runSha256Calls),
]

end Tests.Calculator.Sha256
