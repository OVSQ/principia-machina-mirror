import Principia.Canonical
import Principia.Form.Arithmetic

/-!
# The Beta layer's numbers: exact values, and bounds where no exact form exists

The Declarer's choice of exact values: every Calculator number is an exact
value. The Beta layer's results are of two kinds:

* a rational, exactly (`Quantity.exact`): the mean `a / (a + b)`, `ln Γ(1) = ln Γ(2) = 0`,
  `I_0 = 0`, `I_1 = 1`;
* a real number with no exact form here, given by bounds at any requested precision
  (`Quantity.bounds`): `ln Γ(x)` elsewhere, the regularized incomplete beta function
  `I_x(a, b)` and its quantile. Its twelve-digit form is the exact number's: bounds are
  narrowed until both round alike (`Principia.Form.twelveOf`, monotone rounding), at 64 bits
  first and up to 4096 (`Principia.Form.ladder`). A number those bounds do not settle (one
  lying on a rounding boundary to 4000 bits) has no answer: owed.

No floating point: the bounds are rationals rounded outward (`Principia.Form.Iv`).

## The methods, each with its stated error

* **ln Γ** by Stirling's series at `z = x + n`, `n` the whole number that brings `z` to
  `q/4 + 8` (`q = p + 40`), with `K = q/8 + 4` terms, less `ln(x (x + 1) ... (x + n - 1))`:
  `ln Γ(z) = (z - 1/2) ln z - z + ln(2π)/2 + Σ_{k=1}^{K} B_{2k} / (2k (2k - 1) z^{2k-1}) + R`,
  `|R|` at most the first omitted term for real `z > 0` (DLMF 5.11.ii), added on both sides.
  The Bernoulli numbers are exact rationals (`bernoulli`). At a whole number or a half up to
  `factorialMax`, the logarithm of an exact factorial instead (`Γ(n) = (n - 1)!`,
  `Γ(n + 1/2) = (2n)! / (4^n n!) · √π`), and `ln B(a, b)` of whole numbers as the logarithm
  of the exact `(a - 1)! (b - 1)! / (a + b - 1)!`.
* **I_x(a, b)** by its hypergeometric series,
  `I_x(a, b) = x^a (1 - x)^b / (a B(a, b)) Σ t_n`, `t_0 = 1`,
  `t_{n+1} = t_n x (a + b + n) / (a + 1 + n)`, with `ln B(a, b) = ln Γ(a) + ln Γ(b) -
  ln Γ(a + b)`; the tail after `t_n` is at most `t_n ρ / (1 - ρ)`, `ρ` the ratio at `n`
  when `b ≥ 1` (the ratios do not rise) and `x` when `b < 1` (they stay below it). Past
  `1/2` the symmetry `I_x(a, b) = 1 - I_{1-x}(b, a)` is used (v1 switched at
  `(a + 1) / (a + b + 2)`, where its continued fraction converges fast; the series here
  converges at the rate `x`).
* **Shapes held between bounds** (the evidence layer's `a0 + F`, `b0 + A`, where `F` is a
  sum of powers of 2): `I_x(a, b)` falls as `a` rises and rises as `b` rises (the Beta
  family is ordered by its likelihood ratio, `x^δ`), so over a box of shapes it lies between
  its values at the corners `(a_hi, b_lo)` and `(a_lo, b_hi)`.
* **The quantile** `x` with `I_x(a, b) = p` by narrowing a bracket on rationals, from
  `[0, 1]`: each point tried is placed below or above the quantile only when the bounds of
  `I` there lie wholly below or above `p`, so the quantile always lies within the bracket.
  The points are chosen by Newton's step from estimates of `I - p` and of the density, with
  a halving whenever a step leaves the bracket or is not half the one before the last; the
  choice affects only how fast the bracket narrows. A point that bounds at `w + 32` bits do
  not place lies on the quantile to within about those bits, and a bracket of relative
  width `2^-w` around it is then placed at its two ends, at up to `4w + 128` bits.

With core Lean alone (no real numbers) "the bounds contain the true value" rests on
the stated error terms and on vectors (the Beta corpus, every value of which was
also computed independently, with mpmath at 80 digits), not on a proof.
-/

namespace Principia.Beta

open Principia.Form

/-! ## A computed number -/

/-- A number the Beta layer computes: a rational exactly, or a real number by bounds at any
requested precision in bits. -/
inductive Quantity where
  /-- Exactly this rational. -/
  | exact (q : Rat)
  /-- Between the bounds given at each precision. -/
  | bounds (enc : Nat → Option Iv)

namespace Quantity

/-- canon's twelve-digit form of a rational, rounded once, ties to even (`%.12g`). -/
def ratText (q : Rat) : String := Canonical.ratioText (decide (q < 0)) q.num.natAbs q.den

/-- The twelve-digit form of the number, when settled: exactly for a rational; from bounds
narrowed until both round alike, up to 4096 bits, otherwise. -/
def twelve? : Quantity → Option String
  | .exact q => some (ratText q)
  | .bounds e => ladder.findSome? fun p => (e p).bind fun i => twelveOf i.lo i.hi

/-- Bounds at `p` bits: a rational is its own bounds. -/
def enc : Quantity → Nat → Option Iv
  | .exact q, _ => some ⟨q, q⟩
  | .bounds e, p => e p

end Quantity

/-! ## The Bernoulli numbers -/

/-- `B_0, ..., B_n`, exactly, by `Σ_{j=0}^{m} C(m+1, j) B_j = 0` (`m ≥ 1`); the odd ones past
`B_1` are 0. -/
def bernoulli (n : Nat) : Array Rat := Id.run do
  let mut b : Array Rat := #[1]
  for m in [1:n+1] do
    if m % 2 = 1 && 1 < m then
      b := b.push 0
    else
      let mut s : Rat := 0
      let mut c : Nat := 1
      for j in [0:m] do
        let bj := b[j]!
        if bj ≠ 0 then s := s + (c : Rat) * bj
        c := c * (m + 1 - j) / (j + 1)
      b := b.push (-s / ((m + 1 : Nat) : Rat))
  return b

example : bernoulli 8 = #[1, -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30] := by decide +kernel

/-! ## ln Γ -/

/-- A rational as a one-point interval. -/
def pt (q : Rat) : Iv := ⟨q, q⟩

/-- `x` rounded to `n` significant bits (any rounding: the result is only an estimate, or
a point to try). -/
def roughly (n : Nat) (x : Rat) : Rat := if x = 0 then 0 else Iv.down n x

/-- `ln 2π` between bounds at `q` bits. -/
def ln2Pi (q : Nat) : Option Iv := do
  Iv.ln q (← Iv.mul (q + 8) (Iv.pi (q + 8)) (pt 2))

/-- Stirling's series for `ln Γ(z)`, `z ≥ 1`, with `K` terms and the remainder's bound on
both sides, at `q` bits. -/
def stirling (q K : Nat) (z : Rat) : Option Iv := do
  let bs := bernoulli (2 * K + 2)
  let lnz ← Iv.lnPoint q z
  let t1 ← Iv.mul q (pt (z - 1 / 2)) lnz
  let half ← Iv.divNat q (← ln2Pi q) 2
  let w ← Iv.ofRat q (1 / z)
  let w2 ← Iv.mul q w w
  let mut cur := w
  let mut s : Iv := pt 0
  for k in [1:K+1] do
    let c : Rat := bs[2 * k]! / ((2 * k * (2 * k - 1) : Nat) : Rat)
    s ← Iv.add q s (← Iv.mul q (pt c) cur)
    cur ← Iv.mul q cur w2
  -- `cur` is now `z^-(2K+1)`: the first omitted term's magnitude bounds the remainder.
  let bK := bs[2 * K + 2]!
  let r : Rat := (if bK < 0 then -bK else bK) / (((2 * K + 2) * (2 * K + 1) : Nat) : Rat) * cur.hi
  let series ← Iv.add q s ⟨-r, r⟩
  Iv.add q (← Iv.add q (← Iv.sub q t1 (pt z)) half) series

/-- `ln (x (x + 1) ... (x + n - 1))`, `x > 0`, at `q` bits: the product taken in pieces kept
below `2^4096`, the logarithms of the pieces summed. -/
def lnRising (q : Nat) (x : Rat) (n : Nat) : Option Iv := do
  let mut total : Iv := pt 0
  let mut piece : Iv := pt 1
  for i in [0:n] do
    piece ← Iv.mul (q + 16) piece (pt (x + i))
    if 4096 < Iv.expOf piece.hi then
      total ← Iv.add q total (← Iv.ln q piece)
      piece := pt 1
  Iv.add q total (← Iv.ln q piece)

/-- The whole numbers and halves up to which `Γ` is taken from factorials. -/
def factorialMax : Nat := 1000

/-- `n!`. -/
def factorial (n : Nat) : Nat := (List.range n).foldl (fun acc i => acc * (i + 1)) 1

/-- `Γ(x)` exactly when `x` is a whole number up to `factorialMax` (`Γ(n) = (n - 1)!`); and
`Γ(x) / √π` when `x` is a half up to it (`Γ(n + 1/2) = (2n)! / (4^n n!) · √π`). -/
def gammaFactorial? (x : Rat) : Option (Rat × Bool) :=
  if x.den = 1 ∧ 1 ≤ x ∧ x ≤ factorialMax then some (factorial (x.num.toNat - 1), false)
  else if x.den = 2 ∧ 0 < x ∧ x ≤ factorialMax then
    let n := (x - 1 / 2).floor.toNat
    some ((factorial (2 * n) : Rat) / ((4 ^ n * factorial n : Nat) : Rat), true)
  else none

/-- Bounds of `ln Γ(x)`, `x > 0` rational, at `p` bits: from the factorial at a whole
number or a half up to `factorialMax` (with `ln √π` for a half), else Stirling's series. -/
def lgammaIv (p : Nat) (x : Rat) : Option Iv := do
  if x ≤ 0 then none
  if let some (g, half) := gammaFactorial? x then
    let l ← Iv.lnPoint (p + 8) g
    if !half then return l
    let lpi ← Iv.ln (p + 8) (Iv.pi (p + 16))
    return ← Iv.add p l (← Iv.divNat (p + 8) lpi 2)
  let q := p + 40
  let K := q / 8 + 4
  let zmin : Nat := q / 4 + 8
  let n : Nat := if (zmin : Rat) ≤ x then 0 else ((zmin : Rat) - x).ceil.toNat
  let s ← stirling q K (x + n)
  let r ← if n = 0 then pure s else Iv.sub q s (← lnRising q x n)
  Iv.make p r.lo r.hi

/-- `ln Γ(x)` for a rational `x > 0`: exactly 0 at 1 and 2, where `Γ` is 1 (`Γ` is
log-convex on `x > 0` and equal to 1 at those two points only); bounds elsewhere. -/
def lgamma (x : Rat) : Quantity :=
  if x = 1 ∨ x = 2 then .exact 0 else .bounds fun p => lgammaIv p x

/-! ## The regularized incomplete beta function -/

/-- `ln B(a, b) = ln Γ(a) + ln Γ(b) - ln Γ(a + b)` at `q` bits; for whole numbers up to
`factorialMax`, the logarithm of the exact `(a - 1)! (b - 1)! / (a + b - 1)!`. -/
def lnBeta (q : Nat) (a b : Rat) : Option Iv := do
  if a.den = 1 ∧ b.den = 1 ∧ 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ factorialMax then
    let fa := factorial (a.num.toNat - 1)
    let fb := factorial (b.num.toNat - 1)
    let fab := factorial ((a + b).num.toNat - 1)
    return ← Iv.lnPoint q (((fa * fb : Nat) : Rat) / (fab : Rat))
  Iv.sub q (← Iv.add q (← lgammaIv q a) (← lgammaIv q b)) (← lgammaIv q (a + b))

/-- The most terms of the series summed before the bounds are given up (none: owed). -/
def maxTerms : Nat := 400000

/-- `Σ t_n`, `t_0 = 1`, `t_{n+1} = t_n x (a + b + n) / (a + 1 + n)`, `0 < x < 1`, at `q`
bits, summed until the tail's bound is below `2^-q` of the sum, and that bound added. -/
def incSeries (q : Nat) (a b x : Rat) : Option Iv := Id.run do
  let mut t : Iv := pt 1
  let mut s : Iv := pt 0
  let small : Rat := (2 : Rat) ^ (-(q : Int))
  for n in [0:maxTerms] do
    match Iv.add q s t with
    | none => return none
    | some s' => s := s'
    let ρ : Rat := x * (a + b + n) / (a + 1 + n)
    let ρs : Rat := if 1 ≤ b then ρ else x
    if ρs < 1 then
      let tail := t.hi * ρs / (1 - ρs)
      if tail ≤ small * s.lo then
        return Iv.add q s ⟨0, tail⟩
    -- `t ≥ 0` and `ρ > 0`: the bounds scale by `ρ`, each rounded outward.
    t := ⟨Iv.down q (t.lo * ρ), Iv.up q (t.hi * ρ)⟩
  return none

/-- `I_x(a, b)` by the series, `0 < x < 1`, `lb` bounding `ln B(a, b)`, at `q` bits; with
an estimate of the density `x^(a-1) (1-x)^(b-1) / B(a, b)`, which is
`x^a (1-x)^b / (a B) · a / (x (1 - x))` (the estimate only guides the quantile's search). -/
def incDirect (q : Nat) (lb : Iv) (a b x : Rat) : Option (Iv × Rat) := do
  let g := q + 32
  let e1 ← Iv.mul g (pt a) (← Iv.lnPoint g x)
  let e2 ← Iv.mul g (pt b) (← Iv.lnPoint g (1 - x))
  let e ← Iv.sub g (← Iv.add g e1 e2) lb
  let pre ← Iv.mul g (← Iv.exp g e) (pt (1 / a))
  let r ← Iv.mul g pre (← incSeries g a b x)
  let density := roughly q ((pre.lo + pre.hi) / 2) * a / (x * (1 - x))
  return (← Iv.make q (max 0 r.lo) (min 1 r.hi), density)

/-- `I_x(a, b)` and the density's estimate, `0 < x < 1`, `lb` bounding `ln B(a, b)` (which
is `ln B(b, a)`): past `1/2` as `1 - I_{1-x}(b, a)`, so that the series' ratios tend to at
most `1/2`; the density of `Beta(b, a)` at `1 - x` is that of `Beta(a, b)` at `x`. -/
def incDensity (q : Nat) (lb : Iv) (a b x : Rat) : Option (Iv × Rat) := do
  if 1 / 2 < x then
    let (r, d) ← incDirect q lb b a (1 - x)
    return (← Iv.make q (1 - r.hi) (1 - r.lo), d)
  else incDirect q lb a b x

/-- `I_x(a, b)`, `0 < x < 1`, `lb` bounding `ln B(a, b)`. -/
def incWith (q : Nat) (lb : Iv) (a b x : Rat) : Option Iv :=
  (incDensity q lb a b x).map (·.1)

/-- `I_x(a, b)` for rational `a, b > 0` and `0 ≤ x ≤ 1`: exactly 0 at 0 and 1 at 1, bounds
between. -/
def betainc (a b x : Rat) : Quantity :=
  if x = 0 then .exact 0
  else if x = 1 then .exact 1
  else .bounds fun p => do incWith p (← lnBeta (p + 32) a b) a b x

/-! ## Shapes between bounds, and the quantile -/

/-- What `I_x` needs at one precision: the shapes' bounds and `ln B` at the two corners. -/
structure Corners where
  q : Nat
  aLo : Rat
  aHi : Rat
  bLo : Rat
  bHi : Rat
  /-- `ln B(aHi, bLo)`: the corner where `I_x` is least. -/
  lbLeast : Iv
  /-- `ln B(aLo, bHi)`: the corner where `I_x` is greatest. -/
  lbMost : Iv

/-- The corners at `q` bits of shapes given by bounds; the shapes must be positive. -/
def corners (a b : Quantity) (q : Nat) : Option Corners := do
  let ai ← a.enc (q + 16)
  let bi ← b.enc (q + 16)
  if ai.lo ≤ 0 || bi.lo ≤ 0 then none
  let l1 ← lnBeta (q + 32) ai.hi bi.lo
  let l2 ← if ai.lo = ai.hi ∧ bi.lo = bi.hi then pure l1 else lnBeta (q + 32) ai.lo bi.hi
  return ⟨q, ai.lo, ai.hi, bi.lo, bi.hi, l1, l2⟩

/-- Bounds of `I_x(a, b)` over the box of shapes, `0 < x < 1`, and the density's estimate
at the corner where `I_x` is least. -/
def incBox (c : Corners) (x : Rat) : Option (Iv × Rat) := do
  let (least, d) ← incDensity c.q c.lbLeast c.aHi c.bLo x
  if c.aLo = c.aHi ∧ c.bLo = c.bHi then return (least, d)
  let most ← incWith c.q c.lbMost c.aLo c.bHi x
  return (⟨least.lo, most.hi⟩, d)

/-- A point placed: below (`.lt`) or above (`.gt`) the quantile, with estimates of `I - p`
and of the density there, and the index of the precision that placed it. -/
structure Placement where
  side : Ordering
  value : Rat
  density : Rat
  level : Nat

/-- Where `I_x` lies against `p`, when the bounds at one of the precisions settle it: the
precisions tried from the index `start`, each one's corners computed once, when first
needed. -/
def placeAt (cs : List (Thunk (Option Corners))) (start : Nat) (p x : Rat) : Option Placement :=
  (cs.zipIdx.drop start).findSome? fun (c, i) => c.get.bind fun c => (incBox c x).bind fun (iv, d) =>
    let v := (iv.lo + iv.hi) / 2 - p
    if iv.hi < p then some ⟨.lt, v, d, i⟩ else if p < iv.lo then some ⟨.gt, v, d, i⟩ else none

/-- A bracket of the quantile: `lo` placed below it (or 0), `hi` above (or 1), the last
point placed, and the lengths of the last two steps (for the bisection safeguard). -/
structure Bracket where
  lo : Rat
  hi : Rat
  last : Option (Rat × Placement)
  step1 : Option Rat
  step2 : Option Rat

/-- `|x|`. -/
def absRat (x : Rat) : Rat := if x < 0 then -x else x

/-- The next point to try: Newton's step from the last point placed, rounded to `w + 24`
bits; a step shorter than the tolerance `2^-(w+2)` (relative) is lengthened to it, so that a
point on the quantile is bracketed at once (Dekker's rule). The midpoint instead when the
step falls outside the bracket, or is longer than half the step before the last (Newton is
not converging there), or when there is no estimate. -/
def nextPoint (w : Nat) (k : Bracket) (start : Rat) : Rat :=
  let mid := (k.lo + k.hi) / 2
  let c : Option Rat := match k.last with
    | none => some start
    | some (x, pl) =>
      if pl.density ≤ 0 then none
      else
        let c := roughly (w + 24) (x - pl.value / pl.density)
        let tol := (if 0 < k.lo then k.lo else k.hi) / (2 : Rat) ^ ((w + 2 : Nat) : Int)
        let d := c - x
        let c := if -tol < d && d < tol then (if 0 < pl.value then x - tol else x + tol) else c
        match k.step2 with
        | some s2 => if s2 < 2 * absRat (c - x) then none else some c
        | none => some c
  match c with
  | some c => if k.lo < c && c < k.hi then c else mid
  | none => mid

/-- The index of the first precision worth trying for a bracket: one at least
`log2(lo / width) + 16` bits, so that the estimates are finer than the bracket. -/
def startIndex (precs : List Nat) (k : Bracket) : Nat :=
  if k.lo ≤ 0 then 0
  else
    let need : Int := Iv.expOf k.lo - Iv.expOf (k.hi - k.lo) + 16
    (precs.findIdx? fun (q : Nat) => decide (need ≤ (q : Int))).getD 0

/-- Narrow the bracket until its relative width is at most `2^-w`. Each point is placed
only when bounds of `I` there lie wholly below or above `p`, so the quantile always lies
within the bracket; the estimates only choose the points. A point is placed at the
precisions up to `w + 32` bits (`low`), from the first worth trying (`startIndex`); one they
do not place lies on the quantile to within about `2^-(w+32)`, and a bracket of relative
width `2^-w` around it is then placed at both ends, at any precision (`cs`). -/
def narrow (precs : List Nat) (low cs : List (Thunk (Option Corners))) (p start : Rat) (w : Nat) :
    Nat → Bracket → Option (Rat × Rat)
  | 0, _ => none
  | fuel + 1, k =>
    if 0 < k.lo ∧ (k.hi - k.lo) * (2 : Rat) ^ (w : Int) ≤ k.lo then some (k.lo, k.hi)
    else
      let c := nextPoint w k start
      let step := match k.last with
        | some (x, _) => some (absRat (c - x))
        | none => none
      match placeAt low (min (startIndex precs k) (low.length - 1)) p c with
      | some pl =>
        if pl.side == .lt then narrow precs low cs p start w fuel ⟨c, k.hi, some (c, pl), step, k.step1⟩
        else narrow precs low cs p start w fuel ⟨k.lo, c, some (c, pl), step, k.step1⟩
      | none =>
        let d := c / (2 : Rat) ^ ((w + 2 : Nat) : Int)
        match placeAt cs 0 p (c - d), placeAt cs 0 p (c + d) with
        | some a, some b => if a.side == .lt && b.side == .gt then some (c - d, c + d) else none
        | _, _ => none

/-- The precisions at which a point is placed: from 24 bits, doubling, to `4w + 128`. -/
def placePrecisions (w : Nat) : List Nat :=
  ((List.range 12).map (24 * 2 ^ ·)).filter (· < 4 * w + 128) ++ [4 * w + 128]

/-- The quantile of `Beta(a, b)` at `p`, `0 < p < 1`, for shapes given exactly or by
bounds: a bracket of relative width `2^-w`, from `[0, 1]` (`I_0 = 0`, `I_1 = 1`), the first
point tried the mean. -/
def quantileAt (a b : Quantity) (p : Rat) (w : Nat) : Option Iv := do
  let precs := placePrecisions w
  let cs := precs.map fun q => (q, Thunk.mk fun _ => corners a b q)
  let low := (cs.filter (·.1 ≤ w + 32)).map (·.2)
  let ai ← a.enc 24
  let bi ← b.enc 24
  let start := roughly 24 (ai.hi / (ai.hi + bi.hi))
  let (lo, hi) ← narrow precs low (cs.map (·.2)) p start w (4 * w + 4200) ⟨0, 1, none, none, none⟩
  return ⟨lo, hi⟩

/-- The quantile of `Beta(a, b)` at `p`: 0 at 0 and 1 at 1, bounds between. -/
def quantile (a b : Quantity) (p : Rat) : Quantity :=
  if p = 0 then .exact 0
  else if p = 1 then .exact 1
  else .bounds (quantileAt a b p)

end Principia.Beta
