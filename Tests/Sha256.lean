import Principia
import Tests.Canonical

/-!
The vectors of SHA-256 (`Principia.Sha256`): NIST's CAVP byte-oriented response files
`vectors/SHA256ShortMsg.rsp` (65 messages of 0 to 64 bytes) and `vectors/SHA256LongMsg.rsp`
(64 messages of 163 to 6400 bytes), read as NIST published them, and the hand-written
`vectors/sha256.json`: the files' provenance digests and case counts, FIPS 180-4's three
examples ("abc", the 448-bit two-block message, one million "a"), and the padding's size at
each boundary of a block.

A response file is read line by line, a line ending CRLF or LF: `#` comments, the
`[L = 32]` header, blank lines, and per message `Len = <bits>`, `Msg = <hex>` and
`MD = <hex>` in that order. Any other line, a length that is not whole bytes, a message
whose hexadecimal does not hold exactly its length (a zero length is written `00`), or a
count of messages other than the one recorded fails the run. The file's own SHA-256 must
be the one recorded, so a checkout that changed its bytes fails too.
-/

open Lean
open Principia.Sha256
open Tests.Canonical (Counts readJson field str arr)

namespace Tests.Sha256

/-- A hexadecimal digit's value. -/
def hexValue? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

/-- Bytes from lowercase hexadecimal. -/
def hexBytes (s : String) : Except String ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → Except String ByteArray
    | a :: b :: rest, acc =>
      match hexValue? a, hexValue? b with
      | some x, some y => go rest (acc.push (x * 16 + y))
      | _, _ => .error s!"not lowercase hexadecimal: {s}"
    | [], acc => .ok acc
    | _, _ => .error s!"odd hexadecimal: {s}"

/-- One message of a response file. -/
structure Message where
  bits : Nat
  msg : ByteArray
  md : String

/-- A response file's messages, or why the file does not read. -/
def readResponse (text : String) : Except String (List Message) := do
  let lines := (text.splitOn "\n").map fun l => if l.endsWith "\r" then l.dropEnd 1 |>.toString else l
  let mut out : Array Message := #[]
  let mut bits : Option Nat := none
  let mut msg : Option ByteArray := none
  let mut n := 0
  for line in lines do
    n := n + 1
    if line.isEmpty || line.startsWith "#" || line == "[L = 32]" then
      continue
    if line.startsWith "Len = " then
      if bits.isSome then throw s!"line {n}: a length before the message's digest"
      let some b := (line.drop 6).toString.toNat? | throw s!"line {n}: not a length"
      if b % 8 != 0 then throw s!"line {n}: a length that is not whole bytes"
      bits := some b
    else if line.startsWith "Msg = " then
      let some b := bits | throw s!"line {n}: a message without a length"
      if msg.isSome then throw s!"line {n}: a second message"
      let hex := (line.drop 6).toString
      let m ← hexBytes hex
      if b == 0 then
        if hex != "00" then throw s!"line {n}: the empty message is not written 00"
        msg := some ByteArray.empty
      else
        if m.size * 8 != b then throw s!"line {n}: the message does not hold {b} bits"
        msg := some m
    else if line.startsWith "MD = " then
      let (some b, some m) := (bits, msg) | throw s!"line {n}: a digest without a message"
      let md := (line.drop 5).toString
      if md.length != 64 || (hexBytes md).toOption.isNone then
        throw s!"line {n}: not a digest"
      out := out.push { bits := b, msg := m, md }
      bits := none
      msg := none
    else
      throw s!"line {n}: not a line of a response file"
  if bits.isSome then throw "the file ends inside a message"
  return out.toList

/-- One response file, recorded in `sha256.json`: its digest, its count, every message's
digest. -/
def runResponse (t : Counts) (entry : Json) : IO Counts := do
  let mut t := t
  let file ← str entry "file"
  let bytes ← IO.FS.readBinFile ("vectors" / file)
  let fileDigest ← str entry "sha256"
  t ← t.check (hex (digest bytes) == fileDigest)
    s!"{file}: its SHA-256 is not the recorded {fileDigest}"
  let text ← match String.fromUTF8? bytes with
    | some s => pure s
    | none => throw (IO.userError s!"{file}: not UTF-8")
  let messages ← IO.ofExcept ((readResponse text).mapError fun e => IO.userError s!"{file}: {e}")
  let count ← IO.ofExcept (entry.getObjValAs? Nat "cases")
  t ← t.check (messages.length == count) s!"{file}: {messages.length} messages, recorded {count}"
  for m in messages do
    let got := hex (digest m.msg)
    t ← t.check (got == m.md) s!"{file} Len = {m.bits}: expected {m.md}, got {got}"
  return t

/-- The bytes of a text repeated `n` times. -/
def repeated (s : String) (n : Nat) : ByteArray := Id.run do
  let b := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (b.size * n)
  for _ in [0:n] do
    out := out ++ b
  return out

/-- A padding case: a message of `size` bytes, each `i % 251`; its padding's size, and its
shape: the message, `0x80`, zeros, the length in bits as 8 big-endian bytes. -/
def checkPadding (t : Counts) (c : Json) : IO Counts := do
  let mut t := t
  let size ← IO.ofExcept (c.getObjValAs? Nat "size")
  let padded ← IO.ofExcept (c.getObjValAs? Nat "padded")
  let m : ByteArray := ⟨(Array.range size).map fun i => (i % 251).toUInt8⟩
  let p := pad m
  t ← t.check (p.size == padded) s!"pad of {size} bytes: expected {padded} bytes, got {p.size}"
  let shape := p.data.extract 0 size == m.data && p.data[size]! == 0x80 &&
    (p.data.extract (size + 1) (p.size - 8)).all (· == 0) &&
    bigEndian (p.data.extract (p.size - 8) p.size) == 8 * size
  t ← t.check shape s!"pad of {size} bytes: not the message, 0x80, zeros and its length"
  return t

def run : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let j ← readJson "vectors/sha256.json"
  let start ← IO.monoMsNow
  let mut messages := 0
  for e in ← arr (← field j "cavp") do
    t ← runResponse t e
    messages := messages + (← IO.ofExcept (e.getObjValAs? Nat "cases"))
  let examples ← arr (← field j "examples")
  for c in examples do
    let id ← str c "id"
    let n ← IO.ofExcept (c.getObjValAs? Nat "repeat")
    let expect ← str c "expect"
    let got := hex (digest (repeated (← str c "text") n))
    t ← t.check (got == expect) s!"sha256 {id}: expected {expect}, got {got}"
  let elapsed := (← IO.monoMsNow) - start
  for c in ← arr (← field j "padding") do
    t ← checkPadding t c
  IO.println s!"sha256: {messages} CAVP messages and {examples.length} FIPS examples in {elapsed} ms"
  return t.pair

end Tests.Sha256
