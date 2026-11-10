import Principia.Canonical
import Principia.Exact
import Principia.Form.Interval

/-!
# Declared forms: the evaluator's numbers

The numeric primitives of `eval_form` and T3 over the laws, in one place with
`Principia.Form.Interval`, so that a change of the number model (exact values or
binary64) stays local to them.

v1 evaluated a form in IEEE doubles. The Calculator keeps each number exact where it has
an exact form here, a rational times a whole power of π (`Exact`): every binding normalized
to coherent SI is one (a degree is π/180 rad), and so is every result of `+ - * /`, of a
whole power, and of a root or a function where its result has such a form: a root of a
perfect power, `exp 0`, `ln 1`, and sin, cos and tan at a rational multiple of π where they
are rational (Niven: sin and cos take 0, ±1/2, ±1 there, tan 0 and ±1).

Every other result is held as an enclosure (`Num.approx`): bounds at any requested
precision, outward-rounded (`Principia.Form.Interval`): exp, ln, sin, cos and tan beyond
those values, a root that is not exact, a sum of different powers of π, and a number whose
numerator or denominator would pass `maxBits` bits (the bound that keeps the work on any
form within reach: `x^9999` of a 1000-bit number has ten million bits). A decision on such
a number (its sign, the double range, its twelve digits) is taken when bounds at some
precision up to 4096 bits settle it; when none does (a number that is exactly zero but not
known so, or lies exactly on a rounding boundary), the decision is owed.
`Num.unknown` is a number with no enclosure here: tan at an odd multiple of π/2, which has
no value where v1's double gave a large one, and exp of an argument past 2^14, certainly
beyond the double range when the argument is positive (`e^710 > 2^1024`).

v1's double range is kept as v1 kept it: a result infinite as a double is refused ("not a
finite double"), decided on the number, not on a partial result (as `Principia.Exact`
decides the units'); a result too small for a double is kept, where v1 made it zero. A
value is written in canon's twelve-digit form, rounded once from the number (`twelve`).
-/

namespace Principia.Form

/-- The most bits a numerator and a denominator may hold together. -/
def maxBits : Nat := 65536

/-- The steps one operation of the evaluator costs, its bounds formed at `p` bits. -/
def stepCost (p : Nat) : Nat := p / 64 + p * p / 131072

/-- The bits of a positive whole number. -/
def bitsOf (n : Nat) : Nat := Nat.log2 n + 1

/-- The bits an exact number's rational holds. -/
def sizeOf (x : Exact) : Nat := bitsOf x.coef.num.natAbs + bitsOf x.coef.den

/-- Bounds of an exact number `q × π^k` at `p` bits. -/
def exactIv (p : Nat) (x : Exact) : Option Iv := do
  if x.coef = 0 then return ⟨0, 0⟩
  let c ← Iv.ofRat (p + 8) x.coef
  if x.pi = 0 then return c
  let g := p + Nat.log2 x.pi.natAbs + 16
  let pk ← Iv.powNat g (Iv.pi g) x.pi.natAbs
  let pk ← if x.pi < 0 then Iv.inv g pk else pure pk
  Iv.mul p c pk

/-- A number of the evaluator. -/
inductive Num where
  /-- Exact. -/
  | exact (x : Exact)
  /-- Enclosed: what made it inexact, the precision steps its bounds cost at a requested
  precision (`Num.cost`), and its bounds at a requested precision. -/
  | approx (what : String) (cost : Nat → Nat) (enc : Nat → Option Iv)
  /-- Neither: what, and whether it certainly lies beyond the double range. -/
  | unknown (what : String) (beyond : Bool)

namespace Num

/-- Zero. -/
def zero : Num := .exact ⟨0, 0⟩

/-- A rational. -/
def ofRat (q : Rat) : Num := .exact (Exact.ofRat q)

/-- What made a number inexact, for an owed reason. -/
def what : Num → String
  | .exact _ => "an exact number"
  | .approx w _ _ => w
  | .unknown w _ => w

/-- The precision steps a number's bounds cost at `p` bits: a rational none, a power of π
one operation, an enclosure the sum over the operations it is formed of (`stepCost`, each at
the precision it is formed at). -/
def cost : Num → Nat → Nat
  | .exact x, p => if x.pi = 0 then 0 else stepCost p
  | .approx _ c _, p => c p
  | .unknown _ _, _ => 0

/-- Bounds at `p` bits. -/
def enc : Num → Nat → Option Iv
  | .exact x, p => exactIv p x
  | .approx _ _ e, p => e p
  | .unknown _ _, _ => none

/-- The first inexact operand's reason, or `w`. -/
def reason (a b : Num) (w : String) : String :=
  match a, b with
  | .exact _, .exact _ => w
  | .exact _, b => b.what
  | a, _ => a.what

/-- A binary operation on bounds, as an enclosed number. -/
def lift2 (w : String) (f : Nat → Iv → Iv → Option Iv) (a b : Num) : Num :=
  match a, b with
  | .unknown v _, _ => .unknown v false
  | _, .unknown v _ => .unknown v false
  | _, _ => .approx (reason a b w) (fun p => stepCost p + a.cost (p + 8) + b.cost (p + 8))
    fun p => do
    f p (← a.enc (p + 8)) (← b.enc (p + 8))

/-- A unary operation on bounds, as an enclosed number. -/
def lift1 (w : String) (f : Nat → Iv → Option Iv) (a : Num) : Num :=
  match a with
  | .unknown v _ => .unknown v false
  | .exact _ => .approx w (fun p => stepCost p + a.cost (p + 8)) fun p => do f p (← a.enc (p + 8))
  | .approx v c e => .approx v (fun p => stepCost p + c (p + 8)) fun p => do f p (← e (p + 8))

/-- The reason a number passes the bound on its digits. -/
def wideReason : String := "a number beyond the bound on its digits"

/-- The sum. -/
def add (a b : Num) : Num :=
  match a, b with
  | .exact x, .exact y =>
    if x.coef = 0 then b
    else if y.coef = 0 then a
    else if x.pi = y.pi ∧ sizeOf x + sizeOf y ≤ maxBits then
      let s := Exact.of (x.coef + y.coef) x.pi
      if sizeOf s ≤ maxBits then .exact s else lift2 wideReason Iv.add a b
    else lift2 (if x.pi = y.pi then wideReason else "a sum of different powers of pi") Iv.add a b
  | _, _ => lift2 "" Iv.add a b

/-- The negation. -/
def neg : Num → Num
  | .exact x => .exact (Exact.of (-x.coef) x.pi)
  | .approx w c e => .approx w c fun p => (e p).map Iv.neg
  | .unknown w beyond => .unknown w beyond

/-- The difference. -/
def sub (a b : Num) : Num := add a (neg b)

/-- The absolute value (a power of π is positive). -/
def abs : Num → Num
  | .exact x => .exact (Exact.of (if x.coef < 0 then -x.coef else x.coef) x.pi)
  | .approx w c e => .approx w c fun p => (e p).map Iv.abs
  | .unknown w beyond => .unknown w beyond

/-- The product: zero times any number is zero. -/
def mul (a b : Num) : Num :=
  match a, b with
  | .exact x, .exact y =>
    if x.coef = 0 ∨ y.coef = 0 then zero
    else if sizeOf x + sizeOf y ≤ maxBits then .exact (Exact.mul x y)
    else lift2 wideReason Iv.mul a b
  | .exact x, _ => if x.coef = 0 then zero else lift2 "" Iv.mul a b
  | _, .exact y => if y.coef = 0 then zero else lift2 "" Iv.mul a b
  | _, _ => lift2 "" Iv.mul a b

/-- The quotient, the divisor known not to be zero. -/
def div (a b : Num) : Num :=
  match a, b with
  | .exact x, .exact y =>
    if x.coef = 0 then zero
    else if sizeOf x + sizeOf y ≤ maxBits then .exact (Exact.of (x.coef / y.coef) (x.pi - y.pi))
    else lift2 wideReason Iv.div a b
  | .exact x, _ => if x.coef = 0 then zero else lift2 "" Iv.div a b
  | _, _ => lift2 "" Iv.div a b

/-- `⌊log2 |q|⌋` from below: `|q| ≥ 2 ^ lowerLog2 q` for `q ≠ 0`. -/
def lowerLog2 (q : Rat) : Int := (Nat.log2 q.num.natAbs : Int) - Nat.log2 q.den - 1

/-- A whole power `a ^ n`, `n ≥ 0`; a result too large to form exactly is enclosed, or,
when `|a| ≥ 2^m` with `n·m ≥ 1025` and no negative power of π, known beyond the double
range without bounds. -/
def powNat (a : Num) (n : Nat) : Num :=
  match a with
  | .exact x =>
    if n = 0 then .exact Exact.one
    else if x.coef = 0 then zero
    else if n * sizeOf x ≤ maxBits then .exact (Exact.zpow x n)
    else if decide (0 ≤ x.pi) && decide (1 ≤ lowerLog2 x.coef) &&
        decide (1025 ≤ (n : Int) * lowerLog2 x.coef) then .unknown wideReason true
    else lift1 wideReason (fun p i => Iv.powNat p i n) a
  | _ => lift1 "" (fun p i => Iv.powNat p i n) a

/-- The reciprocal, `a` known not to be zero. -/
def inv (a : Num) : Num := div (.exact Exact.one) a

end Num

/-! ## Roots -/

/-- The whole `k`-th root of `n`, when `n` is a perfect `k`-th power, `k ≥ 1`. -/
def exactRoot? (n k : Nat) : Option Nat :=
  if k = 0 then none
  else
    let r := Iv.floorRoot n k
    if r ^ k = n then some r else none

/-- The positive `x ^ (p/q)` in lowest terms `q ≥ 2`, when exact: the rational's numerator
and denominator perfect `q`-th powers and π's exponent times `p` divisible by `q`. -/
def rootPow? (x : Exact) (p : Int) (q : Nat) : Option Exact := do
  if (x.pi * p) % (q : Int) ≠ 0 then none
  let a ← exactRoot? x.coef.num.natAbs q
  let b ← exactRoot? x.coef.den q
  let r : Rat := (a : Rat) / (b : Rat)
  if p.natAbs * (bitsOf a + bitsOf b) > maxBits then none
  return Exact.of (r ^ p) (x.pi * p / (q : Int))

namespace Num

/-- `x^(p/q)` on bounds, `x ≥ 0` known: a root, then a whole power, then the reciprocal
for a negative exponent. A lower bound below 0 is raised to 0, which `x ≥ 0` permits. -/
def rootPowIv (p' : Int) (q' : Nat) (prec : Nat) (i : Iv) : Option Iv := do
  let r ← Iv.root prec q' ⟨if i.lo < 0 then 0 else i.lo, i.hi⟩
  let r ← Iv.powNat prec r p'.natAbs
  if p' < 0 then Iv.inv prec r else pure r

/-- `a ^ (p/q)` as written, `q ≥ 2`, for `a ≥ 0` known and not zero under a negative
exponent (v1's checks come first): exact when the root is, else enclosed. -/
def powRat (a : Num) (p : Int) (q : Nat) : Num :=
  let g := Nat.gcd p.natAbs q
  let p' := p / (g : Int)
  let q' := q / g
  match a with
  | .exact x =>
    if x.coef = 0 then (if p = 0 then .exact Exact.one else zero)
    else if q' = 1 then
      if 0 ≤ p' then powNat a p'.toNat else inv (powNat a p'.natAbs)
    else match rootPow? x p' q' with
      | some r =>
        -- `rootPow?`'s guard keeps `r` within the bound; checked again so the bound's
        -- theorem (`Principia.Form.Within`) holds by the check.
        if sizeOf r ≤ maxBits then .exact r
        else lift1 "a root with no exact form" (rootPowIv p' q') a
      | none => lift1 "a root with no exact form" (rootPowIv p' q') a
  | _ =>
    if q' = 1 then
      if 0 ≤ p' then powNat a p'.toNat else inv (powNat a p'.natAbs)
    else lift1 "" (rootPowIv p' q') a

/-- The square root of `a ≥ 0` known. -/
def sqrt (a : Num) : Num := powRat a 1 2

/-- exp: 1 at 0; past 2^14 no bounds are formed, the result beyond the double range when
the argument is positive; otherwise enclosed (transcendental, Lindemann). -/
def exp : Num → Num
  | .exact x =>
    if x.coef = 0 then .exact Exact.one
    else if x.pi = 0 ∧ (2 : Rat) ^ (14 : Int) < x.coef then .unknown "exp past 2^14" true
    else if x.pi = 0 ∧ x.coef < -(2 : Rat) ^ (14 : Int) then .unknown "exp below -2^14" false
    else lift1 "exp of a nonzero number" Iv.exp (.exact x)
  | a => lift1 "" Iv.exp a

/-- ln of `a > 0` known: 0 at 1, otherwise enclosed. -/
def ln : Num → Num
  | .exact x =>
    if x.coef = 1 ∧ x.pi = 0 then zero else lift1 "ln of a number other than 1" Iv.ln (.exact x)
  | a => lift1 "" Iv.ln a

/-- `r` reduced into `[0, m)`. -/
def turns (r : Rat) (m : Nat) : Rat := r - (m : Rat) * ((r / m).floor : Rat)

/-- sin(rπ) when rational: at the multiples of π/6 where it is 0, ±1/2 or ±1. -/
def sinPi? (r : Rat) : Option Rat :=
  let t := turns r 2 * 6
  if t.den ≠ 1 then none
  else match t.num.toNat with
    | 0 => some 0 | 1 => some (1 / 2) | 3 => some 1 | 5 => some (1 / 2) | 6 => some 0
    | 7 => some (-1 / 2) | 9 => some (-1) | 11 => some (-1 / 2)
    | _ => none

/-- A function of a rational multiple of π, or of zero: `x = rπ` gives `r`. -/
def piMultiple? (x : Exact) : Option Rat :=
  if x.coef = 0 then some 0 else if x.pi = 1 then some x.coef else none

/-- sin: exact at the multiples of π/6 where it is rational, else enclosed. -/
def sin : Num → Num
  | .exact x =>
    match (piMultiple? x).bind sinPi? with
    | some v => ofRat v
    | none => lift1 "sin with no exact value" (fun p i => Iv.sinCos p true i) (.exact x)
  | a => lift1 "" (fun p i => Iv.sinCos p true i) a

/-- cos: exact where cos(rπ) = sin((r + 1/2)π) is rational, else enclosed. -/
def cos : Num → Num
  | .exact x =>
    match (piMultiple? x).bind fun r => sinPi? (r + 1 / 2) with
    | some v => ofRat v
    | none => lift1 "cos with no exact value" (fun p i => Iv.sinCos p false i) (.exact x)
  | a => lift1 "" (fun p i => Iv.sinCos p false i) a

/-- tan on bounds: sin over cos, cos's bounds excluding 0. -/
def tanIv (p : Nat) (i : Iv) : Option Iv := do
  Iv.div p (← Iv.sinCos (p + 8) true i) (← Iv.sinCos (p + 8) false i)

/-- tan: 0 and ±1 at the multiples of π/4 where it is rational; at an odd multiple of π/2
it has no value, where v1's double gave a large one (owed); else enclosed. -/
def tan : Num → Num
  | .exact x =>
    match piMultiple? x with
    | some r =>
      let t := turns r 1 * 4
      if t.den ≠ 1 then lift1 "tan with no exact value" tanIv (.exact x)
      else match t.num.toNat with
        | 0 => zero | 1 => ofRat 1 | 3 => ofRat (-1)
        | _ => .unknown "tan at an odd multiple of pi/2" false
    | none => lift1 "tan with no exact value" tanIv (.exact x)
  | a => lift1 "" tanIv a

end Num

/-! ## Decisions: the sign, the double range, the twelve digits -/

/-- The precisions tried, in bits, before a decision is owed. -/
def ladder : List Nat := [64, 128, 256, 512, 1024, 2048, 4096]

/-- `|x|` as an unevaluated product, for `Principia.Exact`'s range and bounds. -/
def magnitude (x : Exact) : Exact.Product :=
  { num := [(x.coef.num.natAbs, 1)], den := [(x.coef.den, 1)], pi := x.pi }

/-- `x` is infinite as a double: `|x| ≥ 2^1024 - 2^970`, decided on the exact value. -/
def beyondDouble (x : Exact) : Bool :=
  x.coef ≠ 0 && (magnitude x).range == Exact.Range.infinite

namespace Num

/-- The sign at one precision, when its bounds settle it. -/
def signAt (e : Nat → Option Iv) (p : Nat) : Option Int := (e p).bind Iv.sign?

/-- Whether bounds at one precision settle a number infinite as a double. -/
def beyondAt (e : Nat → Option Iv) (p : Nat) : Option Bool :=
  let ob : Rat := (Exact.overflowBound : Rat)
  (e p).bind fun i =>
    if ob ≤ i.lo || i.hi ≤ -ob then some true
    else if -ob < i.lo && i.hi < ob then some false
    else none

/-- The sign, when settled: -1, 0 or 1. An enclosed number is settled nonzero only. -/
def sign? : Num → Option Int
  | .exact x => some (if x.coef < 0 then -1 else if x.coef = 0 then 0 else 1)
  | .approx _ _ e => ladder.findSome? (signAt e)
  | .unknown _ _ => none

/-- Whether a number is zero, when settled. -/
def isZero? (a : Num) : Option Bool := a.sign?.map (· == 0)

/-- Whether a number is negative, when settled. -/
def isNeg? (a : Num) : Option Bool := a.sign?.map (· < 0)

/-- Whether a number is infinite as a double, when settled. -/
def beyond? : Num → Option Bool
  | .exact x => some (beyondDouble x)
  | .unknown _ b => if b then some true else none
  | .approx _ _ e => ladder.findSome? (beyondAt e)

end Num

/-- `m × 2^e` as a rational. -/
def scaled (m : Nat) (e : Int) : Rat := (m : Rat) * (2 : Rat) ^ e

/-- The twelve-digit form of a number between two bounds of one sign, when both bounds
round alike: rounding is monotone, so the number rounds so too. -/
def twelveOf (lo hi : Rat) : Option String :=
  let r (q : Rat) := Canonical.roundSignificant Canonical.significantDigits q.num.natAbs q.den
  if 0 < lo then (if r lo = r hi then some (Canonical.signedLayout false (r lo)) else none)
  else if hi < 0 then (if r lo = r hi then some (Canonical.signedLayout true (r hi)) else none)
  else none

/-- The twelve digits of an exact number with a power of π at one precision, when its bounds
round alike. -/
def twelveExactAt (x : Exact) (p : Nat) : Option String :=
  let (n, d) := (magnitude x).intervals p
  if n.lo = 0 ∨ d.lo = 0 then none
  else
    let lo := scaled n.lo n.exp / scaled d.hi d.exp
    let hi := scaled n.hi n.exp / scaled d.lo d.exp
    (twelveOf lo hi).map fun s => if x.coef < 0 then "-" ++ s else s

/-- canon's twelve-digit form of an exact number, rounded once, ties to even (as
`Principia.Canonical` writes a number). A power of π is placed between bounds from
Machin's formula, narrowed until both bounds round alike. `none` if 4096 bits do not
settle it. -/
def twelve (x : Exact) : Option String :=
  if x.coef = 0 then some "0"
  else if x.pi = 0 then some (Canonical.ratioText (x.coef < 0) x.coef.num.natAbs x.coef.den)
  else ladder.findSome? (twelveExactAt x)

/-- The twelve digits at one precision, when the bounds round alike. -/
def twelveAt (e : Nat → Option Iv) (p : Nat) : Option String :=
  (e p).bind fun i => twelveOf i.lo i.hi

/-- A number's twelve-digit form, when settled. -/
def Num.twelve? : Num → Option String
  | .exact x => twelve x
  | .approx _ _ e => ladder.findSome? (twelveAt e)
  | .unknown _ _ => none

/-! ## The precision-step budget

Every decision above narrows a number's bounds up the ladder, and each precision tried forms
again the bounds of every operation the number is made of. A request's work is counted in
precision steps: trying a precision `p` on a number costs `Num.cost` steps, each operation
it is formed of `stepCost` at the precision its bounds are formed at, and the steps of every
decision a request takes are summed across the whole request.
Before a precision is tried its steps are added; past the budget the precision is not tried
and the request is refused "budget exceeded" (`budgetExceeded`). A decision taken within the
budget answers as its ladder answers (`climb_findSome`, `Num.signIn_sign`,
`Num.beyondIn_beyond`, `Num.twelveIn_twelve`), so a request the budget does not refuse is
answered as without it.

`stepCost p` is `p/64 + p²/2^17`: 1, 2, 4, 10, 24, 64 and 192 steps at the seven precisions,
297 for the whole ladder. The time ln takes on the Calculator's bounds, measured at those
precisions, grows about so: 2, 4, 7, 15, 35, 95 and 346 ms for four values, interpreted. -/

/-- The refusal of a request whose decisions pass the budget. -/
def budgetExceeded : String :=
  "budget exceeded: the request's narrowing passes the Calculator's bound on precision steps"

/-- A decision up the precisions `ps` under a budget (`none`, no budget) with `s` steps spent
before it: its answer and the steps spent after it, or `none` when the next precision would
pass the budget. -/
def climb {α : Type} (budget : Option Nat) (c : Nat → Nat) (f : Nat → Option α) :
    List Nat → Nat → Option (Option α × Nat)
  | [], s => some (none, s)
  | p :: ps, s =>
    if budget.any (· < s + c p) then none
    else match f p with
      | some a => some (some a, s + c p)
      | none => climb budget c f ps (s + c p)

/-- A decision taken within the budget answers as the ladder does. -/
theorem climb_findSome {α : Type} {budget : Option Nat} {c : Nat → Nat} {f : Nat → Option α} :
    ∀ {ps : List Nat} {s s' : Nat} {r : Option α},
      climb budget c f ps s = some (r, s') → r = ps.findSome? f := by
  intro ps
  induction ps with
  | nil => intro s s' r h; simp [climb] at h; simp [h.1]
  | cons p ps ih =>
    intro s s' r h
    simp only [climb] at h
    split at h
    · cases h
    · rw [List.findSome?_cons]
      split at h
      · rename_i a ha; cases h; simp [ha]
      · rename_i ha; rw [ha]; exact ih h

/-- With no budget a decision is always taken. -/
theorem climb_none {α : Type} {c : Nat → Nat} {f : Nat → Option α} :
    ∀ {ps : List Nat} {s : Nat}, (climb none c f ps s).isSome := by
  intro ps
  induction ps with
  | nil => intro s; simp [climb]
  | cons p ps ih =>
    intro s
    simp only [climb, Option.any_none]
    split
    · contradiction
    · split
      · rfl
      · exact ih

namespace Num

/-- `sign?` under a budget, `s` steps spent. -/
def signIn (budget : Option Nat) (a : Num) (s : Nat) : Option (Option Int × Nat) :=
  match a with
  | .approx _ c e => climb budget c (signAt e) ladder s
  | a => some (a.sign?, s)

/-- `beyond?` under a budget, `s` steps spent. -/
def beyondIn (budget : Option Nat) (a : Num) (s : Nat) : Option (Option Bool × Nat) :=
  match a with
  | .approx _ c e => climb budget c (beyondAt e) ladder s
  | a => some (a.beyond?, s)

/-- `twelve?` under a budget, `s` steps spent: a power of π is narrowed as one operation. -/
def twelveIn (budget : Option Nat) (a : Num) (s : Nat) : Option (Option String × Nat) :=
  match a with
  | .approx _ c e => climb budget c (twelveAt e) ladder s
  | .exact x =>
    if x.coef = 0 ∨ x.pi = 0 then some (twelve x, s)
    else climb budget stepCost (twelveExactAt x) ladder s
  | a => some (a.twelve?, s)

/-- `signIn` answers as `sign?`. -/
theorem signIn_sign {budget : Option Nat} {a : Num} {s s' : Nat} {r : Option Int}
    (h : a.signIn budget s = some (r, s')) : r = a.sign? := by
  cases a with
  | approx w c e => exact climb_findSome h
  | exact x => simp only [signIn, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | unknown w b => simp only [signIn, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm

/-- `beyondIn` answers as `beyond?`. -/
theorem beyondIn_beyond {budget : Option Nat} {a : Num} {s s' : Nat} {r : Option Bool}
    (h : a.beyondIn budget s = some (r, s')) : r = a.beyond? := by
  cases a with
  | approx w c e => exact climb_findSome h
  | exact x => simp only [beyondIn, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | unknown w b => simp only [beyondIn, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm

/-- `twelveIn` answers as `twelve?`. -/
theorem twelveIn_twelve {budget : Option Nat} {a : Num} {s s' : Nat} {r : Option String}
    (h : a.twelveIn budget s = some (r, s')) : r = a.twelve? := by
  cases a with
  | approx w c e => exact climb_findSome h
  | unknown w b => simp only [twelveIn, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  | exact x =>
    simp only [twelveIn] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
    · rename_i hx
      rw [climb_findSome h]
      simp only [not_or] at hx
      simp [Num.twelve?, twelve, hx.1, hx.2]

end Num

/-! ## Facts -/

/-- `e^710 > 2^1024`, from `e > 2.718`: `2.718^710 > 2^1024`. -/
theorem exp_bound : 2 ^ 1024 * 1000 ^ 710 < 2718 ^ 710 := by decide +kernel

example : exactRoot? 16 2 = some 4 := by decide +kernel
example : exactRoot? 17 2 = none := by decide +kernel
example : Num.sinPi? (1 / 2) = some 1 := by decide +kernel
example : Num.sinPi? 1 = some 0 := by decide +kernel

end Principia.Form
