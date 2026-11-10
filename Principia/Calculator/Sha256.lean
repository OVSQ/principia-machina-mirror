import Principia.Calculator.Interface
import Principia.Sha256

/-!
# Family `sha256`: SHA-256 on the command line

`Principia.Sha256`'s digest (FIPS 180-4) on the command line, so that an agent's tools and
the certification probes can check their own SHA-256 against the Calculator's:
* `digest {"hex"}`: the digest of the bytes the hexadecimal text spells, two digits a byte,
  upper or lower case; an empty text is the empty message.
* `digest_text {"text"}`: the digest of the text's UTF-8 bytes (`Sha256.digestText`).

Each answers the digest as 64 lowercase hexadecimal digits.

Bounds: the reader's, a request of at most 1 MiB (`Canonical.maxTextBytes`), so at most a
message of 1 MiB less the request's own members (`digest_text`) or half of it (`digest`).
SHA-256's cost grows with the message's length and no faster. The slowest accepted request
measured, a `digest` of a request of 1 MiB of hexadecimal, took 0.16 s on the command line;
a `digest_text` of 1 MiB, 0.13 s.
-/

namespace Principia.Calculator.Sha256

open Principia.Canonical

/-- A hexadecimal digit's value, upper or lower case. -/
def hexDigit? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- The bytes a hexadecimal text spells, two digits a byte, the high half first; `none` for
a character that is not a hexadecimal digit or an odd count of digits. -/
def bytesOfHex? (s : String) : Option ByteArray :=
  go s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2))
where
  go : List Char → ByteArray → Option ByteArray
    | a :: b :: rest, acc =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => go rest (acc.push (x * 16 + y))
      | _, _ => none
    | [], acc => some acc
    | [_], _ => none

/-- The family's functions. -/
def calls : Family := [
  ("digest", fun v => do
    let s ← asString "hex" (← argument1 "hex" v)
    match bytesOfHex? s with
    | some m => pure (.str (Principia.Sha256.hex (Principia.Sha256.digest m)))
    | none => badArgument "hex is not an even count of hexadecimal digits"),
  ("digest_text", fun v => do
    let s ← asString "text" (← argument1 "text" v)
    pure (.str (Principia.Sha256.digestText s))),
]

end Principia.Calculator.Sha256
