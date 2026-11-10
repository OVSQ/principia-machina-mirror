/-!
# Exact numbers with one square root

The cluster rule (TPS 5.19.8) compares score gaps with noise terms
`Z √(se_a² + se_b²)`, and its page shows the spacing, each row's spacings and the
resolving step to six decimals. v1 computed these in binary floating point; the
Calculator computes them exactly. Every number the rule shows has the form
`a + c √b` with `a`, `c`, `b` rational and `b ≥ 0` (a `Surd`); every verdict
compares a rational gap with a sum of at most two square roots (`sqrtSumLt`).
Both are decided by squaring, with no rounding anywhere: a square root enters
only through `Nat.sqrt` of a whole number, inside `Surd.floor`, and the result is
checked against the exact value before it is used.

Text is v1's `"%.6f"`: the exact value rounded to six decimals, a tie to the even
neighbour, a minus sign on every negative value (also one that rounds to zero).
-/

namespace Principia.Cluster

/-- The sign of a rational: `1`, `0` or `-1`. -/
def ratSign (q : Rat) : Int :=
  if 0 < q then 1 else if q < 0 then -1 else 0

/-- `√A + √B < a`, for `A, B ≥ 0`, decided by squaring twice: `a` must be
positive, and then `a² - A - B > 2 √(A B)`. -/
def sqrtSumLt (A B a : Rat) : Bool :=
  0 < a && (let t := a * a - A - B; 0 < t && 4 * A * B < t * t)

/-- The number `a + c √b`; the functions below read `b` as non-negative. -/
structure Surd where
  /-- The rational part. -/
  a : Rat
  /-- The coefficient of the root. -/
  c : Rat := 0
  /-- The radicand, `b ≥ 0`. -/
  b : Rat := 0
  deriving DecidableEq, Repr

namespace Surd

/-- A rational, as a `Surd`. -/
def ofRat (q : Rat) : Surd := ⟨q, 0, 0⟩

instance : OfNat Surd n := ⟨ofRat n⟩

/-- `√b`. -/
def sqrt (b : Rat) : Surd := ⟨0, 1, b⟩

/-- `x - q`. -/
def subRat (x : Surd) (q : Rat) : Surd := ⟨x.a - q, x.c, x.b⟩

/-- `k x`. -/
def scale (x : Surd) (k : Rat) : Surd := ⟨k * x.a, k * x.c, x.b⟩

/-- `x / d`. -/
def divRat (x : Surd) (d : Rat) : Surd := ⟨x.a / d, x.c / d, x.b⟩

/-- The sign of `a + c √b`: the sign of the larger part, the parts' squares
compared when their signs differ. -/
def sign (x : Surd) : Int :=
  if x.c = 0 ∨ x.b = 0 then ratSign x.a
  else if x.a = 0 then ratSign x.c
  else if ratSign x.a = ratSign x.c then ratSign x.a
  else
    let l := x.a * x.a
    let r := x.c * x.c * x.b
    if r < l then ratSign x.a else if l < r then ratSign x.c else 0

/-- The floor. `Nat.sqrt` of `⌊c² b⌋` is `⌊|c| √b⌋`, so the floor is one of two
neighbours, and the sign of the difference picks it. -/
def floor (x : Surd) : Int :=
  let r : Int := Nat.sqrt (x.c * x.c * x.b).floor.toNat
  if 0 ≤ x.c then
    let base := (x.a + r).floor
    if 0 ≤ (x.subRat (base + 1)).sign then base + 1 else base
  else
    let base := (x.a - r).floor
    if 0 ≤ (x.subRat base).sign then base else base - 1

/-- The nearest integer, a tie to the even one. -/
def roundHalfEven (x : Surd) : Int :=
  let n := x.floor
  let d := (x.subRat ((n : Rat) + 1 / 2)).sign
  if 0 < d then n + 1 else if d < 0 then n else if n % 2 = 0 then n else n + 1

/-- Six decimals, as v1's `"%.6f"` of the exact value. -/
def fixed6 (x : Surd) : String :=
  let m := (x.scale 1000000).roundHalfEven.natAbs
  let frac := toString (m % 1000000)
  (if x.sign < 0 then "-" else "") ++ toString (m / 1000000) ++ "." ++
    "".pushn '0' (6 - frac.length) ++ frac

end Surd

/-- A value the page shows, or `-` where v1 shows none. -/
def fmt : Option Surd → String
  | none => "-"
  | some x => x.fixed6

end Principia.Cluster
