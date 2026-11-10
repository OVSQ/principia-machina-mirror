import Principia.Strike.Bounded
import Principia.Form.Arithmetic

/-!
# The strike rule across powers of π

SR8's scale factor over measurements whose values carry different powers of π (a degree
against a radian, after `Principia.Units` normalizes both to coherent SI). Each value is
`a × π^f` and each uncertainty `b × π^e` with `a`, `b` rational (`Principia.Exact`), so
every sum SR8 forms is a Laurent polynomial in π with rational coefficients (`PiPoly`), and
`S²` is a ratio of two (`PiRatio`).

* A sign is decided by `Exact.polySignAtPiPow`: the zero polynomial has sign 0 exactly
  (`polySign_zero_iff`); π is transcendental, so every other sign is certain once an
  enclosure of π is narrow enough. A sign 4096 bits do not settle is refused `undecided`.
* `sr8ScaleSquarePi` follows `Strike.sr8ScaleFactor` step for step: the outlier test
  `u_i² < 9 N ū²` as a sign, the weights `w_i = 1 / u_i²`, `x̄ = Σ x_i w_i / Σ w_i`, the
  chi-square and the reduced value, and the maximum with 1. With `A = Σ w_i`,
  `B = Σ x_i w_i` and `C = Σ x_i² w_i`, the chi-square `Σ (x_i - x̄)² w_i` is
  `(A C - B²) / A` exactly, so the reduced value is `(A C - B²) / ((n - 1) A)`. Where every
  power is one, it is `Strike.sr8ScaleFactor` on the coefficients (`sr8Pi_same_power`).
* `exceedsPi` is SR3's `|d| > c · S · √v` with `S²` such a ratio, multiplied through by the
  denominator with its sign.
* `PiRatio.digits` gives `S` to a number of significant digits from enclosures of π
  (`Form.Iv`), narrowed over `Form.ladder` until both ends round alike.

Bounds, so that no accepted request runs long: the powers of π of one group differ by at
most `maxSpread` (64), so every polynomial spans at most 4 × 64 + 1 powers; every
coefficient is formed under the bound on an exact value (`ValueBound.add`, `mul`, `div`).
-/

namespace Principia.Strike.PiScale

open Principia.Parameters (sr8MinGroup sr8OutlierFactor)
open Principia.ValueBound (Bounded tooLarge)
open Principia.Form (Iv)

/-- The reason for a sign that 4096 bits of π do not decide. -/
def undecided : String :=
  "the comparison lies within 2^-4000 of its bound and is not decided"

/-- The most the powers of π of one group may differ. -/
def maxSpread : Nat := 64

/-- The refusal of a group whose powers of π differ by more than `maxSpread`. -/
def spreadRefusal : String := "powers of pi differ by more than 64"

/-! ## Laurent polynomials in π -/

/-- `c₀ π^shift + c₁ π^(shift+1) + ...`: coefficients from the lowest power up. -/
structure PiPoly where
  shift : Int
  cs : List Rat
  deriving Repr, Inhabited

namespace PiPoly

/-- The zero polynomial. -/
def zero : PiPoly := ⟨0, []⟩

/-- The coefficient of `π^e`. -/
def coefAt (p : PiPoly) (e : Int) : Rat :=
  if e < p.shift then 0 else p.cs.getD (e - p.shift).toNat 0

/-- Leading and trailing zero coefficients dropped; the zero polynomial is `zero`. -/
def norm (p : PiPoly) : PiPoly :=
  let lead := (p.cs.takeWhile (· == 0)).length
  let body := ((p.cs.drop lead).reverse.dropWhile (· == 0)).reverse
  if body.isEmpty then zero else ⟨p.shift + lead, body⟩

/-- `q × π^e`, its coefficient read under the bound. -/
def mono (q : Rat) (e : Int) : Bounded PiPoly := do
  let q ← ValueBound.ofRat q
  pure (if q = 0 then zero else ⟨e, [q]⟩)

/-- The sum, every coefficient formed under the bound. -/
def add (p q : PiPoly) : Bounded PiPoly :=
  if p.cs.isEmpty then pure q
  else if q.cs.isEmpty then pure p
  else do
    let lo := min p.shift q.shift
    let hi := max (p.shift + p.cs.length) (q.shift + q.cs.length)
    let cs ← (List.range (hi - lo).toNat).mapM fun (i : Nat) =>
      ValueBound.add (p.coefAt (lo + (i : Int))) (q.coefAt (lo + (i : Int)))
    pure (norm ⟨lo, cs⟩)

/-- The negation. -/
def neg (p : PiPoly) : PiPoly := ⟨p.shift, p.cs.map (- ·)⟩

/-- The difference. -/
def sub (p q : PiPoly) : Bounded PiPoly := add p q.neg

/-- A rational multiple. -/
def scale (q : Rat) (p : PiPoly) : Bounded PiPoly := do
  pure (norm ⟨p.shift, ← p.cs.mapM (ValueBound.mul q)⟩)

/-- The product: each coefficient the sum of the products of the coefficients whose powers
add to its own, every product and sum formed under the bound. -/
def mul (p q : PiPoly) : Bounded PiPoly :=
  if p.cs.isEmpty || q.cs.isEmpty then pure zero
  else do
    let qa := q.cs.toArray
    let cs ← (List.range (p.cs.length + q.cs.length - 1)).mapM fun k =>
      p.cs.zipIdx.foldlM (fun s (ci : Rat × Nat) =>
        if ci.2 ≤ k ∧ k - ci.2 < qa.size then do
          ValueBound.add s (← ValueBound.mul ci.1 qa[k - ci.2]!)
        else pure s) 0
    pure (norm ⟨p.shift + q.shift, cs⟩)

/-- The sum of a list of polynomials. -/
def sum (ps : List PiPoly) : Bounded PiPoly := ps.foldlM add zero

/-- The sign at π: `π^shift` is positive, so it is the sign of `Σ cᵢ πⁱ`, which
`Exact.polySignAtPiPow` decides; `none` when 4096 bits do not. -/
def sign (p : PiPoly) : Option Ordering := Exact.polySignAtPiPow p.cs 1

/-- `Σ cᵢ πⁱ` by Horner's rule over an enclosure of π. -/
def horner (prec : Nat) (piv : Iv) : List Rat → Option Iv
  | [] => Iv.ofRat prec 0
  | c :: rest => do
    let r ← horner prec piv rest
    let m ← Iv.mul prec r piv
    Iv.add prec (← Iv.ofRat prec c) m

/-- An enclosure of the polynomial's value at π, at `prec` bits. -/
def enclose (p : PiPoly) (prec : Nat) : Option Iv := do
  let piv := Iv.pi prec
  let body ← horner prec piv p.cs
  let s ← Iv.powNat prec piv p.shift.natAbs
  if 0 ≤ p.shift then Iv.mul prec body s else Iv.div prec body s

end PiPoly

/-! ## Ratios -/

/-- `num / den`, two polynomials in π. -/
structure PiRatio where
  num : PiPoly
  den : PiPoly
  deriving Repr, Inhabited

namespace PiRatio

/-- A rational as a ratio. -/
def ofRat (q : Rat) : PiRatio := ⟨⟨0, [q]⟩, ⟨0, [1]⟩⟩

/-- Whether the ratio is above 1, for a positive denominator: the sign of `num - den`. -/
def above (r : PiRatio) : Bounded (Option Ordering) := do
  let d ← r.num.sub r.den
  pure (match r.den.sign with
    | some .gt => d.sign
    | _ => none)

/-- `√(num / den)` to `p` significant digits, `(m, e)` with value `m × 10^e`: enclosures
of π at the precisions of `Form.ladder`, until both ends of the root's enclosure round
alike (rounding is monotone). `none` if 4096 bits do not settle it. -/
def rootDigits (r : PiRatio) (p : Nat) : Option (Nat × Int) :=
  Form.ladder.findSome? fun prec => do
    let n ← r.num.enclose prec
    let d ← r.den.enclose prec
    let q ← Iv.div prec n d
    let s ← Iv.root prec 2 q
    if 0 < s.lo ∧ Exact.roundSig s.lo p = Exact.roundSig s.hi p then
      some (Exact.roundSig s.lo p)
    else none

end PiRatio

/-! ## SR8 -/

/-- SR8's `S²` across powers of π: a `ScaleFactor` where it is rational, or a ratio of
polynomials in π decided above 1. -/
inductive PiSquare where
  | rat (S : ScaleFactor)
  | pi (r : PiRatio) (h : r.above = .ok (some .gt))

/-- `S² ≥ 1`, as a fact of the rational, or as the decided sign of `num - den`. -/
def PiSquare.OneLe : PiSquare → Prop
  | .rat S => 1 ≤ S.square
  | .pi r _ => r.above = .ok (some .gt)

/-- A measurement's power of π: its uncertainty's (it is positive), and its value's when
the value is not zero. -/
def powers (m : Exact × Exact) : List Int :=
  if m.1.coef = 0 then [m.2.pi] else [m.1.pi, m.2.pi]

/-- Every value and uncertainty carries one power of π. -/
def onePower (ms : List (Exact × Exact)) : Bool :=
  match ms.flatMap powers with
  | [] => true
  | k :: rest => rest.all (· == k)

/-- The least power of π in the group. -/
def leastPower (ms : List (Exact × Exact)) : Int :=
  match ms.flatMap powers with
  | [] => 0
  | k :: rest => rest.foldl min k

/-- The spread of the group's powers of π. -/
def spread (ms : List (Exact × Exact)) : Nat :=
  match ms.flatMap powers with
  | [] => 0
  | k :: rest => (rest.foldl max k - rest.foldl min k).toNat

/-- The decision of a sign, refused `undecided` when 4096 bits do not settle it. -/
def decided : Option Ordering → Bounded Ordering
  | some o => pure o
  | none => .error undecided

/-- SR8 over the kept records, their powers of π made relative to the group's least:
`A = Σ w_i`, `B = Σ x_i w_i`, `C = Σ x_i² w_i`, and `S²` the reduced chi-square
`(A C - B²) / ((n - 1) A)` when it is above 1, else 1. -/
def ofKept (kept : List (Exact × Exact)) (p0 : Int) : Bounded (Option PiSquare) :=
  if kept.length < sr8MinGroup then pure (some (.rat .one))
  else do
    let terms ← kept.mapM fun (x, u) => do
      let uu ← ValueBound.mul u.coef u.coef
      let w ← ValueBound.div 1 uu
      let xw ← ValueBound.mul x.coef w
      let xxw ← ValueBound.mul x.coef xw
      let e := u.pi - p0
      let f := if x.coef = 0 then e else x.pi - p0
      pure (← PiPoly.mono w (-2 * e), ← PiPoly.mono xw (f - 2 * e),
        ← PiPoly.mono xxw (2 * f - 2 * e))
    let A ← PiPoly.sum (terms.map (·.1))
    let B ← PiPoly.sum (terms.map (·.2.1))
    let C ← PiPoly.sum (terms.map (·.2.2))
    let num ← (← A.mul C).sub (← B.mul B)
    let den ← A.scale ((kept.length : Rat) - 1)
    let r : PiRatio := ⟨num, den⟩
    match h : r.above with
    | .ok (some .gt) => pure (some (.pi r h))
    | .ok (some _) => pure (some (.rat .one))
    | .ok none => .error undecided
    | .error e => .error e

/-- v1's `sr8_scale_factor` over `(value, uncertainty)` pairs carrying powers of π, step
for step as `Strike.sr8ScaleFactor`: fewer than two records, 1; an uncertainty not
positive, `none`; the records with `u_i² < 9 N ū²` kept, each decided as a sign; fewer than
two kept, 1; otherwise `ofKept`. Where every power is one, the strike rule itself on the
coefficients, under the bound (`sr8Pi_same_power`). Refused past `maxSpread`, and
`undecided` where a sign is not settled. -/
def sr8ScaleSquarePi (ms : List (Exact × Exact)) : Bounded (Option PiSquare) :=
  if onePower ms then
    (Strike.Bounded.sr8ScaleFactor (ms.map fun m => ⟨m.1.coef, m.2.coef⟩)).map
      (Option.map .rat)
  else if ms.length < sr8MinGroup then pure (some (.rat .one))
  else if ms.any (·.2.coef ≤ 0) then pure none
  else if maxSpread < spread ms then .error spreadRefusal
  else do
    let p0 := leastPower ms
    let n : Rat := ms.length
    let us ← ms.mapM fun m => PiPoly.mono m.2.coef (m.2.pi - p0)
    let uMean ← (← PiPoly.sum us).scale (1 / n)
    let uMean2 ← uMean.mul uMean
    let f : Rat := sr8OutlierFactor
    let ff ← ValueBound.mul f f
    let ffn ← ValueBound.mul ff n
    let bound ← uMean2.scale ffn
    let kept ← ms.filterM fun m => do
      let uu ← ValueBound.mul m.2.coef m.2.coef
      let d ← bound.sub (← PiPoly.mono uu (2 * (m.2.pi - p0)))
      pure ((← decided d.sign) == .gt)
    ofKept kept p0

/-! ## SR3 with `S²` across powers of π -/

/-- `|d| > c · S · √v`, as `Strike.Numeric.exceedsBound` decides it, with `d²` and `c² v`
polynomials in π, the signs of `c` and `v` given, and `S² = P / Q`: for `c > 0`, the sign of
`d² Q - c² v P` times the sign of `Q`; otherwise `S` does not enter. `none` when a sign is
not settled. -/
def exceedsPi (dd ccv : PiPoly) (cSign : Ordering) (vPos : Bool) (s2 : PiRatio) :
    Bounded (Option Bool) :=
  match cSign with
  | .gt => do
    let lhs ← dd.mul s2.den
    let rhs ← ccv.mul s2.num
    let diff ← lhs.sub rhs
    pure (match s2.den.sign, diff.sign with
      | some .gt, some o => some (o == .gt)
      | some .lt, some o => some (o == .lt)
      | _, _ => none)
  | .lt => pure (if vPos then some true else dd.sign.map (· == .gt))
  | .eq => pure (dd.sign.map (· == .gt))

/-! ## PROVED -/

/-- `S² ≥ 1`, as a sign fact: every `PiSquare` is 1 or more. -/
theorem sr8Pi_one_le (s : PiSquare) : s.OneLe := by
  cases s with
  | rat S => exact S.one_le_square
  | pi r h => exact h

/-- Where every value and uncertainty carries one power of π, SR8 across powers of π is the
strike rule on the coefficients. -/
theorem sr8Pi_same_power {ms : List (Exact × Exact)} {r : Option PiSquare}
    (hp : onePower ms = true) (h : sr8ScaleSquarePi ms = .ok r) :
    r = (Strike.sr8ScaleFactor (ms.map fun m => ⟨m.1.coef, m.2.coef⟩)).map .rat := by
  unfold sr8ScaleSquarePi at h
  rw [ite_eq_left hp] at h
  cases hs : Strike.Bounded.sr8ScaleFactor (ms.map fun m => ⟨m.1.coef, m.2.coef⟩) with
  | error e => rw [hs] at h; cases h
  | ok s =>
    rw [hs] at h
    cases h
    rw [Strike.Bounded.sr8ScaleFactor_ok hs]

/-- Where `c` is not positive, `S²` does not enter the test: a larger `S²` never creates an
excess, nor removes one. -/
theorem exceeds_pi_of_le_nonpos {dd ccv : PiPoly} {cSign : Ordering} {vPos : Bool}
    (hc : cSign ≠ .gt) (s2 s2' : PiRatio) :
    exceedsPi dd ccv cSign vPos s2' = exceedsPi dd ccv cSign vPos s2 := by
  cases cSign with
  | gt => exact absurd rfl hc
  | lt => rfl
  | eq => rfl

/-- `polySignAtPiPow`'s search over its precisions answers only `.gt` or `.lt`. -/
theorem polySign_search_ne_eq (cs : List Rat) (m : Int) (ps : List Nat) :
    ps.findSome? (fun p =>
      let (tlo, thi) := Exact.piPowBounds m p
      let (lo, hi) := cs.zipIdx.foldl (fun (acc : Rat × Rat) (ci : Rat × Nat) =>
        let a := ci.1 * tlo ^ ci.2
        let b := ci.1 * thi ^ ci.2
        (acc.1 + min a b, acc.2 + max a b)) (0, 0)
      if 0 < lo then some Ordering.gt else if hi < 0 then some Ordering.lt else none) ≠
      some .eq := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.findSome?_cons]
    split
    · rename_i o ho
      intro he
      cases he
      simp only at ho
      split at ho
      · cases ho
      · split at ho <;> cases ho
    · exact ih

/-- For a power `m ≠ 0`, the sign at `π^m` is 0 exactly for the zero polynomial: π^m is
transcendental, and `polySignAtPiPow` answers `.eq` for no other. -/
theorem polySign_zero_iff {cs : List Rat} {m : Int} (hm : m ≠ 0) :
    Exact.polySignAtPiPow cs m = some .eq ↔ cs.all (· == 0) = true := by
  unfold Exact.polySignAtPiPow
  constructor
  · intro h
    by_cases hz : cs.all (· == 0) = true
    · exact hz
    · rw [ite_eq_right hz, ite_eq_right hm] at h
      exact absurd h (polySign_search_ne_eq cs m _)
  · intro hz
    rw [ite_eq_left hz]

end Principia.Strike.PiScale
