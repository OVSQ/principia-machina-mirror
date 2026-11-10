import Principia.Beta.Enclosure

/-!
# The evidence layer's numbers: sums of rational multiples of powers of 2

The reliability score weights each resolved event by `2^(-age / HALF-LIFE)` (CR11)
and each window weight in the diversity quota likewise (PD-SC-13). With a rational
HALF-LIFE these weights are `2^e` for rational `e`, which is rational exactly when `e` is a
whole number. Every number of the evidence layer (F, A, a pad's weight, the quota's window
sums, an admitted weight) is a finite sum `Σ c_i 2^(f_i)` with rational `c_i` and rational
`f_i`, and the Calculator keeps it so, exactly (the Declarer's choice of exact values): a `PowSum`, its terms
normalized to `0 ≤ f_i < 1`, the whole part of each exponent moved into the coefficient
(`2^(n + f) = 2^n · 2^f`), one term per `f`, no zero coefficient, `f` rising.

**Equality is exact.** For distinct rationals `f_1, ..., f_k` in `[0, 1)` the numbers
`2^(f_i)` are linearly independent over the rationals: with `d` a common denominator they
are among `2^(j/d)`, `0 ≤ j < d`, a basis of `Q(2^(1/d))` over `Q`, since `x^d - 2` is
irreducible (Eisenstein at 2). So a normalized sum is zero exactly when it has no term, and
rational exactly when its only term has `f = 0`. Its sign, when it is not rational, is
read from bounds (`2^f = e^(f ln 2)`, `Principia.Form.Iv`), which settle it at some
precision because the number is not zero; its twelve digits likewise, and an irrational
number never lies on a rounding boundary. A sign or twelve digits that bounds up to 4096
bits do not settle (a number within `2^-4000` of zero or of a boundary) is owed.
-/

namespace Principia.Score

open Principia.Form
open Principia.Beta

/-- `Σ c · 2^f` over the terms `(f, c)`: `0 ≤ f < 1`, `c ≠ 0`, `f` strictly rising. -/
structure PowSum where
  terms : List (Rat × Rat)
  deriving DecidableEq, Repr

namespace PowSum

/-- Zero: no term. -/
def zero : PowSum := ⟨[]⟩

/-- A rational. -/
def ofRat (q : Rat) : PowSum := if q = 0 then zero else ⟨[(0, q)]⟩

/-- Add the term `c · 2^f`, `0 ≤ f < 1`, keeping the list normalized. -/
def insertTerm (f c : Rat) : List (Rat × Rat) → List (Rat × Rat)
  | [] => if c = 0 then [] else [(f, c)]
  | (g, d) :: rest =>
    if f < g then (if c = 0 then (g, d) :: rest else (f, c) :: (g, d) :: rest)
    else if f = g then (if c + d = 0 then rest else (g, c + d) :: rest)
    else (g, d) :: insertTerm f c rest

/-- The sum. -/
def add (x y : PowSum) : PowSum := ⟨y.terms.foldl (fun acc t => insertTerm t.1 t.2 acc) x.terms⟩

/-- A rational multiple. -/
def scale (q : Rat) (x : PowSum) : PowSum :=
  if q = 0 then zero else ⟨x.terms.map fun t => (t.1, q * t.2)⟩

/-- The difference. -/
def sub (x y : PowSum) : PowSum := add x (scale (-1) y)

/-- `2^e` as `2^⌊e⌋` and the fractional part `e - ⌊e⌋`. -/
def split (e : Rat) : Rat × Rat :=
  let n := e.floor
  (e - n, (2 : Rat) ^ n)

/-- `2^e`, exactly. -/
def pow2 (e : Rat) : PowSum := let (f, c) := split e; ⟨[(f, c)]⟩

/-- The product with `2^e`. -/
def mulPow2 (e : Rat) (x : PowSum) : PowSum :=
  x.terms.foldl (fun acc t => let (g, k) := split (t.1 + e); add acc ⟨[(g, t.2 * k)]⟩) zero

/-- The rational, when the sum is one. -/
def isRat? (x : PowSum) : Option Rat :=
  match x.terms with
  | [] => some 0
  | [(f, c)] => if f = 0 then some c else none
  | _ => none

/-- Bounds of `2^f`, `0 ≤ f < 1`, at `q` bits. -/
def twoPow (q : Nat) (f : Rat) : Option Iv :=
  if f = 0 then some (pt 1)
  else do Iv.exp q (← Iv.mul (q + 8) (Iv.ln2 (q + 8)) (pt f))

/-- Bounds of the sum at `p` bits. -/
def enc (x : PowSum) (p : Nat) : Option Iv := do
  let g := p + 16
  let s ← x.terms.foldlM (fun acc t => do
    Iv.add g acc (← Iv.mul g (pt t.2) (← twoPow (g + 8) t.1))) (pt 0)
  Iv.make p s.lo s.hi

/-- The sum as a computed number: exactly when it is rational. -/
def toQuantity (x : PowSum) : Quantity :=
  match x.isRat? with
  | some q => .exact q
  | none => .bounds x.enc

/-- The sign, -1, 0 or 1: exactly when rational, otherwise from bounds, when settled. -/
def sign? (x : PowSum) : Option Int :=
  match x.isRat? with
  | some q => some (if q < 0 then -1 else if q = 0 then 0 else 1)
  | none => ladder.findSome? fun p => (x.enc p).bind Iv.sign?

/-- `max 0 (min x 1)` (v1 `_clip(x, 0, 1)`), when the two comparisons are settled. -/
def clip01 (x : PowSum) : Option PowSum := do
  if (← x.sign?) < 0 then return zero
  if 0 < (← (sub x (ofRat 1)).sign?) then return ofRat 1
  return x

/-- The quotient `u / v`, `v > 0`, as a computed number: exactly when it is rational,
which it is when `u` is a rational multiple of `v` (the terms are a basis). -/
def ratio (u v : PowSum) : Quantity :=
  match u.isRat?, v.isRat? with
  | some a, some b => .exact (a / b)
  | _, _ =>
    match u.terms, v.terms with
    | (f, c) :: _, (g, d) :: _ =>
      let k := c / d
      if f = g ∧ u = scale k v then .exact k
      else .bounds fun p => do Iv.div p (← u.enc (p + 8)) (← v.enc (p + 8))
    | _, _ => .bounds fun p => do Iv.div p (← u.enc (p + 8)) (← v.enc (p + 8))

/-- Every coefficient's bits, numerator and denominator: the size of the exact value. -/
def bits (x : PowSum) : Nat × Nat :=
  x.terms.foldl (fun acc t =>
    (max acc.1 (Nat.log2 t.2.num.natAbs + 1), max acc.2 (Nat.log2 t.2.den + 1))) (0, 0)

example : add (pow2 (1 / 2)) (pow2 (-1 / 2)) = ⟨[(1 / 2, 3 / 2)]⟩ := by decide +kernel
example : sub (pow2 (3 / 2)) (scale 2 (pow2 (1 / 2))) = zero := by decide +kernel
example : (mulPow2 (1 / 2) (pow2 (1 / 2))).isRat? = some 2 := by decide +kernel

end PowSum

end Principia.Score
