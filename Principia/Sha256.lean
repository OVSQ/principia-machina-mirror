/-!
# SHA-256 (FIPS 180-4)

The digest function under every PMA digest (the Declarer's choice of SHA-256 under
every digest): SHA-256 as FIPS 180-4 defines it, written here in core Lean
over a `ByteArray`, with `UInt32` arithmetic. No library, no foreign function: the
Calculator computes it as it computes everything else.

* the functions of section 4.1.2 (`ch`, `maj`, the four sigma functions, over `rotr`);
* the sixty-four constants of section 4.2.2 (`K`) and the initial value of section 5.3.3
  (`initial`), written as FIPS writes them in hexadecimal; the theorems `K_cube_roots` and
  `initial_square_roots` check them against their definition in FIPS: the first 32 bits of
  the fractional parts of the cube roots of the first sixty-four primes, and of the square
  roots of the first eight;
* the padding of section 5.1.1 (`pad`), byte oriented: the message, the byte `0x80`, the
  fewest zero bytes that leave the length 56 modulo 64, then the message's length in bits
  as a 64-bit big-endian integer; `pad_size_mod` and `pad_ends_with_length` prove the two
  properties the parsing of section 5.2.1 rests on;
* the computation of section 6.2.2 (`schedule`, `round`, `compress`), block by block from
  the initial value (`digest`), the 32 bytes of the final value being the digest
  (`digest_size`).

Correctness rests on vectors (the SHA-256 corpus and NIST's short-message and long-message
response files, run by the SHA-256 vector tests): NIST's CAVP byte-oriented test
vectors and FIPS's examples, each checked beforehand with an independent implementation.
The Lean kernel itself evaluates FIPS's one-block example (`digest_abc`).
-/

namespace Principia.Sha256

/-! ## Functions (FIPS 180-4, 4.1.2) -/

/-- Rotation of a word `n` bits to the right, `0 < n < 32` (FIPS 180-4, 3.2). -/
@[inline] def rotr (n : UInt32) (x : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- `Ch(x, y, z)`: each bit of `y` where `x` has a one, of `z` where it has a zero. -/
@[inline] def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z)`: each bit's majority. -/
@[inline] def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x)`. -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 :=
  rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x

/-- `Σ1(x)`. -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 :=
  rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x

/-- `σ0(x)`. -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 :=
  rotr 7 x ^^^ rotr 18 x ^^^ (x >>> 3)

/-- `σ1(x)`. -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 :=
  rotr 17 x ^^^ rotr 19 x ^^^ (x >>> 10)

/-! ## Constants (FIPS 180-4, 4.2.2 and 5.3.3) -/

/-- The sixty-four constant words `K0` to `K63`, as FIPS 180-4 writes them, from left to
right. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

theorem K_size : K.size = 64 := rfl

/-- Eight words: FIPS's working variables `a` to `h`, and the intermediate value
`H0` to `H7` between blocks. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
  deriving DecidableEq, Repr

/-- The initial value `H(0)`, as FIPS 180-4 writes it (5.3.3). -/
def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The eight words in order. -/
def State.words (s : State) : List UInt32 := [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/-! ### Where the constants come from

FIPS derives each constant word from a prime: the first 32 bits of the fractional part of
its cube root (`K`) or of its square root (`initial`). With `r` the integer `k`-th root of
`p · 2^(32k)`, rounded down, those bits are `r mod 2^32`. The theorems below compute `r`
for each prime, check that it is the root rounded down (`r^k ≤ p · 2^(32k) < (r+1)^k`),
and compare its low 32 bits with the word as written. -/

/-- `n` is prime: at least 2, and no number from 2 to `n - 1` divides it. -/
def isPrime (n : Nat) : Bool :=
  2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The primes below 312: the first sixty-four (`firstPrimes_length`). -/
def firstPrimes : List Nat :=
  (List.range 312).filter isPrime

theorem firstPrimes_length : firstPrimes.length = 64 := by decide +kernel

/-- The greatest `r < 2^64` with `r^k ≤ n`, found bit by bit from the highest. -/
def rootFloor (k n : Nat) : Nat :=
  go 64 0
where
  go : Nat → Nat → Nat
    | 0, r => r
    | i + 1, r => if (r + 2 ^ i) ^ k ≤ n then go i (r + 2 ^ i) else go i r

/-- The integer `k`-th root of `p · 2^(32k)`, rounded down, brackets it. -/
def bracketsRoot (k p : Nat) : Bool :=
  let r := rootFloor k (p * 2 ^ (32 * k))
  r ^ k ≤ p * 2 ^ (32 * k) && p * 2 ^ (32 * k) < (r + 1) ^ k

/-- The first 32 bits of the fractional part of the `k`-th root of `p`. -/
def fractionBits (k p : Nat) : Nat :=
  rootFloor k (p * 2 ^ (32 * k)) % 2 ^ 32

/-- The constants are the first 32 bits of the fractional parts of the cube roots of the
first sixty-four primes, each root rounded down exactly. -/
theorem K_cube_roots :
    firstPrimes.all (bracketsRoot 3) = true ∧
      firstPrimes.map (fractionBits 3) = K.toList.map UInt32.toNat := by
  decide +kernel

/-- The initial value is the first 32 bits of the fractional parts of the square roots of
the first eight primes, each root rounded down exactly. -/
theorem initial_square_roots :
    (firstPrimes.take 8).all (bracketsRoot 2) = true ∧
      (firstPrimes.take 8).map (fractionBits 2) = initial.words.map UInt32.toNat := by
  decide +kernel

/-! ## Padding (FIPS 180-4, 5.1.1) -/

/-- The zero bytes that follow `0x80` after a message of `n` bytes: the fewest that leave
the length 56 modulo 64, room for the 8 bytes of the length. -/
def zeroCount (n : Nat) : Nat :=
  (119 - n % 64) % 64

/-- A number of bits as the 64-bit big-endian integer that ends the padding: its
eight bytes, the most significant first. -/
def lengthBytes (bits : Nat) : Array UInt8 :=
  #[UInt8.ofNat (bits / 2 ^ 56), UInt8.ofNat (bits / 2 ^ 48), UInt8.ofNat (bits / 2 ^ 40),
    UInt8.ofNat (bits / 2 ^ 32), UInt8.ofNat (bits / 2 ^ 24), UInt8.ofNat (bits / 2 ^ 16),
    UInt8.ofNat (bits / 2 ^ 8), UInt8.ofNat bits]

/-- The padded message: the message, the byte `0x80` (a one bit, then seven zero bits),
`zeroCount` zero bytes, and the message's length in bits. -/
def pad (m : ByteArray) : ByteArray :=
  ⟨m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0 ++ lengthBytes (8 * m.size)⟩

/-- Bytes read as a big-endian integer. -/
def bigEndian (bytes : Array UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem lengthBytes_size (bits : Nat) : (lengthBytes bits).size = 8 := rfl

/-- The length bytes read back give the length, modulo 2^64. -/
theorem bigEndian_lengthBytes (bits : Nat) : bigEndian (lengthBytes bits) = bits % 2 ^ 64 := by
  simp only [bigEndian, lengthBytes, List.foldl_toArray', List.foldl_cons, List.foldl_nil,
    UInt8.toNat_ofNat']
  omega

theorem zeroCount_lt (n : Nat) : zeroCount n < 64 := by
  unfold zeroCount; omega

theorem pad_size (m : ByteArray) :
    (pad m).size = m.size + 1 + zeroCount m.size + 8 := by
  show (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0 ++
    lengthBytes (8 * m.size)).size = m.data.size + 1 + zeroCount m.size + 8
  rw [Array.size_append, Array.size_append, Array.size_append, Array.size_replicate,
    lengthBytes_size]
  rfl

/-- The padded message is a whole number of 512-bit blocks. -/
theorem pad_size_mod (m : ByteArray) : (pad m).size % 64 = 0 := by
  rw [pad_size]; unfold zeroCount; omega

/-- The padding adds at most one block more than the message needs: the zero bytes are
the fewest that fit (FIPS's `k`, the smallest non-negative solution). -/
theorem pad_size_lt (m : ByteArray) : (pad m).size < m.size + 73 := by
  rw [pad_size]; have := zeroCount_lt m.size; omega

/-- The padded message begins with the message. -/
theorem pad_starts_with_message (m : ByteArray) : (pad m).data.extract 0 m.size = m.data := by
  show (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0 ++
    lengthBytes (8 * m.size)).extract 0 m.data.size = m.data
  rw [Array.append_assoc, Array.append_assoc, Array.extract_append_left, Array.extract_size]

/-- The padded message ends with the message's length in bits, as 8 big-endian bytes. -/
theorem pad_ends_with_lengthBytes (m : ByteArray) :
    (pad m).data.extract ((pad m).size - 8) (pad m).size = lengthBytes (8 * m.size) := by
  have hf : (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0).size =
      m.size + 1 + zeroCount m.size := by
    rw [Array.size_append, Array.size_append, Array.size_replicate]
    rfl
  have h1 : (pad m).size - 8 = (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0).size := by
    rw [pad_size, hf]; omega
  have h2 : (pad m).size = (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0).size + 8 := by
    rw [pad_size, hf]
  rw [h1, h2]
  show (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0 ++ lengthBytes (8 * m.size)).extract
    (m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0).size
    ((m.data ++ #[0x80] ++ Array.replicate (zeroCount m.size) 0).size + 8) = _
  rw [Array.extract_append_right]
  exact Array.extract_eq_self_iff.mpr (Or.inr ⟨rfl, Nat.le_refl _⟩)

/-- Read back, those last 8 bytes are the message's length in bits, for every message
shorter than 2^61 bytes (FIPS's bound, 2^64 bits). -/
theorem pad_ends_with_length (m : ByteArray) (h : m.size < 2 ^ 61) :
    bigEndian ((pad m).data.extract ((pad m).size - 8) (pad m).size) = 8 * m.size := by
  rw [pad_ends_with_lengthBytes, bigEndian_lengthBytes]
  omega

/-! ## The computation (FIPS 180-4, 6.2.2) -/

/-- The big-endian word at byte `i`. -/
@[inline] def word (p : ByteArray) (i : Nat) : UInt32 :=
  ((p.get! i).toUInt32 <<< 24) ||| ((p.get! (i + 1)).toUInt32 <<< 16) |||
    ((p.get! (i + 2)).toUInt32 <<< 8) ||| (p.get! (i + 3)).toUInt32

/-- The message schedule `W0` to `W63` of the block at byte `off` (step 1). -/
def schedule (p : ByteArray) (off : Nat) : Array UInt32 :=
  extend 48 (first 16 0 (Array.emptyWithCapacity 64))
where
  /-- `W0` to `W15`: the block's sixteen words. -/
  first : Nat → Nat → Array UInt32 → Array UInt32
    | 0, _, w => w
    | n + 1, i, w => first n (i + 1) (w.push (word p (off + 4 * i)))
  /-- `W16` to `W63`, each from four words before it. -/
  extend : Nat → Array UInt32 → Array UInt32
    | 0, w => w
    | n + 1, w =>
      let t := w.size
      extend n (w.push (smallSigma1 w[t - 2]! + w[t - 7]! + smallSigma0 w[t - 15]! + w[t - 16]!))

/-- One round on the working variables, with the round's constant and word (step 3). -/
@[inline] def round (s : State) (k w : UInt32) : State :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + k + w
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Rounds `t` to `t + n - 1`. -/
def rounds (w : Array UInt32) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, t, s => rounds w n (t + 1) (round s K[t]! w[t]!)

/-- Word by word sum, modulo 2^32. -/
def State.add (s r : State) : State :=
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

/-- The block at byte `off` processed from the intermediate value `s` (steps 1 to 4). -/
def compress (s : State) (p : ByteArray) (off : Nat) : State :=
  s.add (rounds (schedule p off) 64 0 s)

/-- `n` blocks processed in order from byte `off`. -/
def blocks (p : ByteArray) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, off, s => blocks p n (off + 64) (compress s p off)

/-- A word's four bytes, the most significant first. -/
def wordBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The final value's 32 bytes, `H0` first. -/
def State.bytes (s : State) : ByteArray :=
  ⟨(wordBytes s.a ++ wordBytes s.b ++ wordBytes s.c ++ wordBytes s.d ++ wordBytes s.e ++
    wordBytes s.f ++ wordBytes s.g ++ wordBytes s.h).toArray⟩

/-- SHA-256 of a message: its padding parsed into blocks of 64 bytes, processed from the
initial value; the final value's 32 bytes. -/
def digest (m : ByteArray) : ByteArray :=
  let p := pad m
  (blocks p (p.size / 64) 0 initial).bytes

/-- A digest is 32 bytes, whatever the message. -/
theorem digest_size (m : ByteArray) : (digest m).size = 32 := rfl

/-! ## The digest as text -/

/-- A half byte's lowercase hexadecimal digit. -/
def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Bytes in lowercase hexadecimal, two digits each, the high half first. -/
def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit (b &&& 15)])

theorem hex_length (bytes : ByteArray) : (hex bytes).length = 2 * bytes.size := by
  simp only [hex, String.length_ofList, List.length_flatMap, List.length_cons, List.length_nil]
  rw [show (fun (_ : UInt8) => 0 + 1 + 1) = fun _ => 2 from rfl, List.map_const',
    List.sum_replicate_nat, Array.length_toList, ByteArray.size, Nat.mul_comm]

/-- SHA-256 of a text's UTF-8 bytes, in lowercase hexadecimal: 64 characters. -/
def digestText (s : String) : String :=
  hex (digest s.toUTF8)

theorem digestText_length (s : String) : (digestText s).length = 64 := by
  simp [digestText, hex_length, digest_size]

/-- FIPS 180-4's one-block example, "abc", evaluated by the Lean kernel. -/
theorem digest_abc :
    digestText "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

end Principia.Sha256
