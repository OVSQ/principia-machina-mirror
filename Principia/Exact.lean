import Principia.Decimal

/-!
# Exact numbers

The unit functions' numbers: a rational times a whole power of π, `coef × π^pi`. Every
unit scale is one (a degree is π/180 rad), and so is every value normalized to coherent
SI. Nothing is rounded and nothing overflows.

v1 computed these numbers in IEEE doubles and printed them to twelve significant digits.
The Declarer's choice of exact values keeps exact values in the Calculator (this
file) rather than reproducing binary64 bit for bit; under the second this file is what would change.
Where v1's printed number differs from the exact value, the case is recorded beside v1's
corpus (the divergence list of the units corpus).

v1 also refused a scale, and a normalized value, that is zero or infinite as a double. The
rule is kept, decided on the exact value (`Product.range`): the double range enters the
Calculator here only, as the two bounds `underflowInv` and `overflowBound`. A unit's scale
is held as an unevaluated product of powers until it is known to lie within them, so a short
UNIT whose scale no double holds is refused without its exact value being computed.

π is transcendental, so `q × π^k` and `q' × π^k'` with `q, q'` nonzero are equal exactly
when `q = q'` and `k = k'`; zero is kept as `0 × π^0`, so the derived equality is the
equality of the numbers.
-/

namespace Principia

/-- `coef × π^pi`, exactly; zero is `0 × π^0`. -/
structure Exact where
  coef : Rat
  pi : Int
  deriving DecidableEq, Repr

namespace Exact

/-- `q × π^k`, with zero kept as `0 × π^0`. -/
def of (q : Rat) (k : Int) : Exact := if q = 0 then ⟨0, 0⟩ else ⟨q, k⟩

/-- A rational, with no power of π. -/
def ofRat (q : Rat) : Exact := of q 0

/-- One. -/
def one : Exact := ⟨1, 0⟩

/-- The product. -/
def mul (a b : Exact) : Exact := of (a.coef * b.coef) (a.pi + b.pi)

/-- A whole power. -/
def zpow (a : Exact) (n : Int) : Exact := of (a.coef ^ n) (a.pi * n)

/-- A rational multiple. -/
def scale (q : Rat) (a : Exact) : Exact := of (q * a.coef) a.pi

/-- The decimal digits of `n` in exactly `w` places, leading zeros kept; `w` is at least
the number of digits. Halving `w` at each step makes the work that of a few divisions of
numbers `n`'s size, not one division per digit as `Nat.repr` does. -/
def fixedDigits (n w : Nat) : List Char :=
  if h : w ≤ 18 then
    let ds := (toString n).toList
    List.replicate (w - ds.length) '0' ++ ds
  else
    let half := w / 2
    let p := 10 ^ half
    have : w - half < w := by omega
    have : half < w := by omega
    fixedDigits (n / p) (w - half) ++ fixedDigits (n % p) half
termination_by w

/-- The decimal digits of a number, with no leading zero. -/
def decimalDigits (n : Nat) : List Char :=
  -- 30103 / 100000 is just above log10 2, so `w` is at least the number of digits.
  let w := (Nat.log2 n + 1) * 30103 / 100000 + 1
  match (fixedDigits n w).dropWhile (· = '0') with
  | [] => ['0']
  | ds => ds

/-- The exponent of 2 in a positive number: its lowest set bit, found in one step. -/
def twoAdic (n : Nat) : Nat := Nat.log2 (n &&& (n ^^^ (n - 1)))

/-- The exponent `b` with `5^b = m`, if there is one: `b` is within one of
`log2 m / log2 5`, and each candidate is checked by one power. -/
def fiveLog? (m : Nat) : Option Nat :=
  -- 2321928 / 1000000 is just below log2 5.
  let b := Nat.log2 m * 1000000 / 2321928
  [b, b + 1, b - 1, b + 2].find? fun c => 5 ^ c == m

/-- A rational's spelling: the canonical decimal (`Decimal.canonChars`) when its
denominator has no prime factor but 2 and 5, so it has one (`5e-2`, `1e29997`); otherwise
`<numerator>/<denominator>` in lowest terms (`1/60`). -/
def renderRat (q : Rat) : String :=
  let a := twoAdic q.den
  match fiveLog? (q.den >>> a) with
  | some b =>
    let k := max a b
    let n := q.num.natAbs * 10 ^ k / q.den
    String.ofList (Decimal.canonChars
      { neg := decide (q.num < 0), ip := decimalDigits n, fp := [], ex := -(k : Int) })
  | none =>
    String.ofList ((if q.num < 0 then ['-'] else []) ++ decimalDigits q.num.natAbs ++ '/' ::
      decimalDigits q.den)

/-- An exact number's spelling: the rational, then `pi` with its exponent when there is a
power of π (`1/32400 pi2`, `1/648000 pi`); exponent 1 is not written. -/
def render (a : Exact) : String :=
  renderRat a.coef ++
    if a.pi = 0 then "" else if a.pi = 1 then " pi" else " pi" ++ toString a.pi

example : render (ofRat (1 / 20)) = "5e-2" := by decide +kernel
example : render (ofRat (1 / 60)) = "1/60" := by decide +kernel
example : render (of (1 / 32400) 2) = "1/32400 pi2" := by decide +kernel

/-! ## The double range

Under round to nearest, ties to even, a positive value at or below 2^-1075, half the least
subnormal, becomes zero (the tie goes to zero, which is even), and a value at or above
2^1024 - 2^970, halfway between the greatest double and 2^1024, becomes infinite (the tie
goes to 2^1024, which is even, and overflows). -/

/-- 2^1075: a positive value at or below `1 / underflowInv` is zero as a double. -/
def underflowInv : Nat := 2 ^ 1075

/-- 2^1024 - 2^970: a value at or above it is infinite as a double. -/
def overflowBound : Nat := 2 ^ 1024 - 2 ^ 970

/-- A positive rational whose nearest double is neither zero nor infinite. -/
def ratInRange (q : Rat) : Bool :=
  decide (1 / (underflowInv : Rat) < q) && decide (q < (overflowBound : Rat))

/-- Compare `x × 2^a` with `y × 2^b`: by bit length first, exactly only when the bit
lengths tie, so no operand grows beyond the larger of the two. -/
def cmpScaled (x : Nat) (a : Int) (y : Nat) (b : Int) : Ordering :=
  if x = 0 then (if y = 0 then .eq else .lt)
  else if y = 0 then .gt
  else
    let lx : Int := Nat.log2 x + a
    let ly : Int := Nat.log2 y + b
    if lx < ly then .lt
    else if ly < lx then .gt
    else if b ≤ a then compare (x <<< (a - b).toNat) y
    else compare x (y <<< (b - a).toNat)

/-- A nonnegative real known to lie between `lo × 2^exp` and `hi × 2^exp`. -/
structure Interval where
  lo : Nat
  hi : Nat
  exp : Int

namespace Interval

/-- A whole number, exactly. -/
def exact (n : Nat) : Interval := ⟨n, n, 0⟩

/-- At most `p` bits kept, `lo` rounded down and `hi` up; `p = 0` keeps every bit. -/
def trim (p : Nat) (a : Interval) : Interval :=
  let s := Nat.log2 a.hi + 1 - p
  if p = 0 || s = 0 then a else ⟨a.lo >>> s, (a.hi >>> s) + 1, a.exp + s⟩

/-- The product, trimmed to `p` bits. -/
def mul (p : Nat) (a b : Interval) : Interval :=
  trim p ⟨a.lo * b.lo, a.hi * b.hi, a.exp + b.exp⟩

/-- A whole power by repeated squaring, trimmed to `p` bits at each step. -/
def pow (p : Nat) (a : Interval) (n : Nat) : Interval :=
  if h : n = 0 then exact 1
  else
    let half := pow p a (n / 2)
    let sq := mul p half half
    if n % 2 = 0 then sq else mul p sq a
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

end Interval

/-- `2^w atan(1/x)` within `w / (2 log2 x) + 2`: the series 1/x - 1/(3x^3) + ... summed
term by term, each term rounded down, until a term would fall below 1. -/
def atanFixed (x w : Nat) : Int :=
  let t := w / (2 * Nat.log2 x) + 1
  (List.range t).foldl (fun acc k =>
    let term : Int := ((2 ^ w / ((2 * k + 1) * x ^ (2 * k + 1)) : Nat) : Int)
    if k % 2 = 0 then acc + term else acc - term) 0

/-- π to `p` bits, from Machin's formula π = 16 atan(1/5) - 4 atan(1/239), with 24 guard
bits absorbing the rounding of every term. -/
def piInterval (p : Nat) : Interval :=
  let g := 24
  let w := p + g
  let c := 16 * atanFixed 5 w - 4 * atanFixed 239 w
  let err : Int := 16 * (w / (2 * Nat.log2 5) + 3) + 4 * (w / (2 * Nat.log2 239) + 3)
  ⟨(c - err).toNat >>> g, ((c + err).toNat >>> g) + 1, -(p : Int)⟩

/-- A positive number as an unevaluated product: the powers `b^e` of `num` over those of
`den`, times `π^pi`. -/
structure Product where
  num : List (Nat × Nat) := []
  den : List (Nat × Nat) := []
  pi : Int := 0

/-- Where a positive number lies against the double range. -/
inductive Range where
  | zero
  | inside
  | infinite
  deriving DecidableEq, Repr

namespace Product

/-- A power of ten. -/
def ten (e : Int) : Product :=
  if 0 ≤ e then { num := [(10, e.toNat)] } else { den := [(10, (-e).toNat)] }

/-- A whole number. -/
def nat (n : Nat) : Product := { num := [(n, 1)] }

/-- The product of two. -/
def mul (a b : Product) : Product := ⟨a.num ++ b.num, a.den ++ b.den, a.pi + b.pi⟩

/-- A whole power. -/
def zpow (a : Product) (e : Int) : Product :=
  let k := e.natAbs
  let up (fs : List (Nat × Nat)) := fs.map fun f => (f.1, f.2 * k)
  if 0 ≤ e then ⟨up a.num, up a.den, a.pi * e⟩ else ⟨up a.den, up a.num, a.pi * e⟩

/-- The exact value; computed only once the value is known to lie in the double range. -/
def value (a : Product) : Exact :=
  let side (fs : List (Nat × Nat)) : Nat := fs.foldl (fun acc f => acc * f.1 ^ f.2) 1
  Exact.of ((side a.num : Rat) / (side a.den : Rat)) a.pi

/-- The numerator and the denominator as intervals at `p` bits, π folded into one side;
`p = 0` is exact, for a product with no power of π. -/
def intervals (a : Product) (p : Nat) : Interval × Interval :=
  let side (fs : List (Nat × Nat)) : Interval :=
    fs.foldl (fun acc f => Interval.mul p acc (Interval.pow p (Interval.exact f.1) f.2))
      (Interval.exact 1)
  let n := side a.num
  let d := side a.den
  if a.pi = 0 then (n, d)
  else
    let pk := Interval.pow p (piInterval p) a.pi.natAbs
    if 0 < a.pi then (Interval.mul p n pk, d) else (n, Interval.mul p d pk)

/-- The range at `p` bits, or `none` when the intervals straddle a bound. -/
def rangeAt (a : Product) (p : Nat) : Option Range :=
  let (x, y) := a.intervals p
  -- x / y ≥ overflowBound, certainly and possibly
  let infSure := cmpScaled x.lo x.exp (overflowBound * y.hi) y.exp != .lt
  let infNever := cmpScaled x.hi x.exp (overflowBound * y.lo) y.exp == .lt
  -- x / y ≤ 2^-1075, certainly and possibly
  let zeroSure := cmpScaled x.hi (x.exp + 1075) y.lo y.exp != .gt
  let zeroNever := cmpScaled x.lo (x.exp + 1075) y.hi y.exp == .gt
  if infSure then some .infinite
  else if zeroSure then some .zero
  else if infNever && zeroNever then some .inside
  else none

/-- Where the product lies against the double range. Intervals at 64, 256, 1024 and 4096
bits are tried in turn, each a few multiplications of numbers that size; a product with no
power of π that is still undecided is then decided exactly. One with a power of π cannot
be; if it lies within about 2^-4000 of a bound, which no unit of the catalogue comes near,
it is counted outside. -/
def range (a : Product) : Range :=
  match [64, 256, 1024, 4096].findSome? a.rangeAt with
  | some r => r
  | none =>
    if a.pi = 0 then (a.rangeAt 0).getD .infinite
    else
      let (x, y) := a.intervals 4096
      if cmpScaled x.hi (x.exp + 1075) y.lo y.exp != .gt then .zero else .infinite

end Product

/-! ## Comparing across powers of π

Two measurements in units of one KIND can carry different powers of π: a degree is π/180
rad, a radian is 1 rad. Their comparison is the sign of a polynomial with rational
coefficients at `t = π^m`. For `m ≠ 0`, `π^m` is transcendental, so such a polynomial is
zero there only when it is the zero polynomial; any other is decided, with certainty,
once an interval for `t` is narrow enough. -/

/-- `2^e` as a rational. -/
def pow2 (e : Int) : Rat := (2 : Rat) ^ e

/-- Rationals below and above `π^m`, at `p` bits. -/
def piPowBounds (m : Int) (p : Nat) : Rat × Rat :=
  let i := Interval.pow p (piInterval p) m.natAbs
  let lo : Rat := (i.lo : Rat) * pow2 i.exp
  let hi : Rat := (i.hi : Rat) * pow2 i.exp
  if 0 ≤ m then (lo, hi) else (1 / hi, 1 / lo)

/-- The sign of `c₀ + c₁ t + c₂ t² + ...` at `t = π^m`: `.eq` only for the zero
polynomial (or, for `m = 0`, a sum of coefficients that is zero, decided exactly);
otherwise from intervals of 64, 256, 1024 and 4096 bits, each term bounded at the two
ends of `t`'s interval. `none` if 4096 bits do not decide, which needs the value within
about 2^-4000 of zero. -/
def polySignAtPiPow (cs : List Rat) (m : Int) : Option Ordering :=
  if cs.all (· == 0) then some .eq
  else if m = 0 then
    let v := cs.foldl (· + ·) 0
    some (if v < 0 then .lt else if 0 < v then .gt else .eq)
  else
    [64, 256, 1024, 4096].findSome? fun p =>
      let (tlo, thi) := piPowBounds m p
      let (lo, hi) := cs.zipIdx.foldl (fun (acc : Rat × Rat) (ci : Rat × Nat) =>
        let a := ci.1 * tlo ^ ci.2
        let b := ci.1 * thi ^ ci.2
        (acc.1 + min a b, acc.2 + max a b)) (0, 0)
      if 0 < lo then some .gt else if hi < 0 then some .lt else none

/-! ## Printing to a number of significant digits

Where a v1 text printed a double with C's `%.12g` (v1's `canon_float`), the Calculator
prints the exact value correctly rounded to twelve significant digits, ties to even, in
the same notation. The two agree unless the double's own rounding moved the twelfth
digit, which a recorded divergence would then name. -/

/-- The digits of a positive rational, `q` rounded to `p ≥ 1` significant digits, ties to
even: `(m, e)` with `q ≈ m × 10^e` and `m` of exactly `p` digits. -/
def roundSig (q : Rat) (p : Nat) : Nat × Int :=
  let est : Int := (decimalDigits q.num.natAbs).length - (decimalDigits q.den).length
  -- 10^E ≤ q < 10^(E+1), E being est or est - 1
  let e := if Decimal.pow10 est ≤ q then est else est - 1
  let sh : Int := (p : Int) - 1 - e
  let t := q * Decimal.pow10 sh
  let f := t.floor
  let r := t - f
  let n : Int := if r > 1 / 2 then f + 1 else if r < 1 / 2 then f
    else if f % 2 == 0 then f else f + 1
  if n.toNat = 10 ^ p then (10 ^ (p - 1), -sh + 1) else (n.toNat, -sh)

/-- The digits of `√q` for a positive rational `q`, rounded to `p ≥ 1` significant digits,
ties to even, as `roundSig` gives them. -/
def sqrtSig (q : Rat) (p : Nat) : Nat × Int :=
  let l : Int := (decimalDigits q.num.natAbs).length - (decimalDigits q.den).length
  -- 10^(2E) ≤ q < 10^(2E+2); q lies in (10^(l-1), 10^(l+1)), so E is one of three
  let cands : List Int := [l / 2 + 1, l / 2, l / 2 - 1, l / 2 - 2]
  let e := (cands.find? fun c => Decimal.pow10 (2 * c) ≤ q).getD (l / 2 - 2)
  let sh : Int := (p : Int) - 1 - e
  let t := q * Decimal.pow10 (2 * sh)
  let m := Nat.sqrt t.floor.toNat
  -- round up when t > (m + 1/2)², that is 4t > (2m + 1)²; a tie goes to an even m
  let c : Rat := 4 * t
  let h : Rat := (((2 * m + 1) * (2 * m + 1) : Nat) : Rat)
  let n := if h < c ∨ (c = h ∧ m % 2 = 1) then m + 1 else m
  if n = 10 ^ p then (10 ^ (p - 1), -sh + 1) else (n, -sh)

/-- `m × 10^e`, `m` of exactly `p` digits, in C's `%.{p}g` notation: fixed when the
leading digit's exponent `X` has `-4 ≤ X < p`, else `d.ddde±XX`; trailing zeros of the
fraction dropped, and the point with them. -/
def printG (neg : Bool) (m : Nat) (e : Int) (p : Nat) : String :=
  let ds := decimalDigits m
  let x : Int := e + (p : Int) - 1
  let stripZeros (l : List Char) : List Char := (l.reverse.dropWhile (· = '0')).reverse
  let body : List Char :=
    if -4 ≤ x ∧ x < (p : Int) then
      let (ip, fp) : List Char × List Char :=
        if 0 ≤ x then (ds.take (x.toNat + 1), ds.drop (x.toNat + 1))
        else (['0'], List.replicate ((-x).toNat - 1) '0' ++ ds)
      let fp := stripZeros fp
      ip ++ (if fp.isEmpty then [] else '.' :: fp)
    else
      let rest := stripZeros (ds.drop 1)
      let xs := decimalDigits x.natAbs
      ds.take 1 ++ (if rest.isEmpty then [] else '.' :: rest) ++ 'e' ::
        (if x < 0 then '-' else '+') :: (if xs.length < 2 then '0' :: xs else xs)
  String.ofList ((if neg then ['-'] else []) ++ body)

/-- A rational as C's `%.12g` prints it, from its exact value; zero is `0`. -/
def printRat12 (q : Rat) : String :=
  if q = 0 then "0"
  else
    let (m, e) := roundSig (if q < 0 then -q else q) 12
    printG (q < 0) m e 12

/-- `√q`, for `q ≥ 0`, as C's `%.12g` prints it; zero is `0`. -/
def printSqrt12 (q : Rat) : String :=
  if q ≤ 0 then "0"
  else
    let (m, e) := sqrtSig q 12
    printG false m e 12

example : printRat12 (1 / 60) = "0.0166666666667" := by decide +kernel
example : printRat12 (149597870700 : Rat) = "149597870700" := by decide +kernel

end Exact

end Principia

namespace Principia.Decimal

/-- A positive decimal whose nearest IEEE double is positive and finite (v1's
`_is_pos_finite`): v1 used K as a double in SR3, so `1e-400` (zero) and `1e400` (infinite)
are refused there rather than silently changing what SR3 computes. Decided on the exact
value against the bounds of `Principia.Exact`: no floating point. -/
def isPosFinite (s : String) : Bool :=
  sign s > 0 &&
    match value s with
    | some v => Exact.ratInRange v
    | none => false

end Principia.Decimal
