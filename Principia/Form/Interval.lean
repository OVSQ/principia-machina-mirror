import Principia.Exact

/-!
# Declared forms: enclosures

The evaluator's numbers where no exact form exists (`Principia.Form.Arithmetic`): a real
number placed between two rationals, `lo ≤ x ≤ hi`, at a requested precision of `p`
bits, every bound rounded outward to `p` significant bits so that no number grows with
the work. Each operation encloses its result whenever its operands enclose theirs:

* `+ - *` and `1/x` by the extreme combinations of the bounds (`1/x` only for an
  interval that excludes 0); a whole power by repeated products;
* a `k`-th root of a nonnegative interval by whole roots of its bounds scaled by `2^(sk)`;
* exp, increasing, at its two bounds: `e^y` for `0 ≤ y ≤ 1/4` lies between the partial
  sum of its series and that sum plus twice the next term (`e^y ≤ 2`), and
  `e^r = (e^(r/2^s))^(2^s)`, `e^(-r) = 1/e^r`;
* ln, increasing, at its two bounds: `ln r = m ln 2 + 2 atanh((f-1)/(f+1))` with
  `r = 2^m f`, `1 ≤ f < 2`; the atanh series has positive terms, its tail below twice the
  next term (`z ≤ 1/3`); `ln 2 = 2 atanh(1/3)`;
* sin and cos at the midpoint of the interval, the argument first reduced by a whole
  number of turns with π from `Principia.Exact.piInterval`; Taylor's remainder is below the
  next term's magnitude; the interval's half-width is added, as both have slope at most 1.

π, e and the logarithm are never computed beyond these bounds, so a decision taken on an
enclosure (a sign, the double range, the twelve digits canon writes) is the exact
number's. A bound too large or too small to hold (beyond 2^±70000) gives no enclosure.
-/

namespace Principia.Form

/-- A closed interval of rationals. -/
structure Iv where
  lo : Rat
  hi : Rat
  deriving Repr

namespace Iv

/-- The binary exponent of a nonzero rational, within one: `2^(e-1) < |q| < 2^(e+1)`. -/
def expOf (q : Rat) : Int := (Nat.log2 q.num.natAbs : Int) - Nat.log2 q.den

/-- The largest magnitude exponent a bound may have. -/
def maxExp : Nat := 70000

/-- A bound is within the magnitudes kept. -/
def holdable (q : Rat) : Bool := q == 0 || (expOf q).natAbs ≤ maxExp

/-- `q` rounded down to about `p` significant bits. -/
def down (p : Nat) (q : Rat) : Rat :=
  if q = 0 then 0
  else
    let s : Int := (p : Int) - expOf q
    ((q * (2 : Rat) ^ s).floor : Rat) / (2 : Rat) ^ s

/-- `q` rounded up to about `p` significant bits. -/
def up (p : Nat) (q : Rat) : Rat :=
  if q = 0 then 0
  else
    let s : Int := (p : Int) - expOf q
    ((q * (2 : Rat) ^ s).ceil : Rat) / (2 : Rat) ^ s

/-- The interval between two bounds, rounded outward; none beyond the magnitudes kept. -/
def make (p : Nat) (lo hi : Rat) : Option Iv :=
  if holdable lo && holdable hi then some ⟨down p lo, up p hi⟩ else none

/-- A rational, enclosed. -/
def ofRat (p : Nat) (q : Rat) : Option Iv := make p q q

/-- The sum. -/
def add (p : Nat) (a b : Iv) : Option Iv := make p (a.lo + b.lo) (a.hi + b.hi)

/-- The negation. -/
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

/-- The difference. -/
def sub (p : Nat) (a b : Iv) : Option Iv := add p a b.neg

/-- The least of a nonempty list. -/
def least (x : Rat) (xs : List Rat) : Rat := xs.foldl (fun m y => if y < m then y else m) x

/-- The greatest of a nonempty list. -/
def greatest (x : Rat) (xs : List Rat) : Rat := xs.foldl (fun m y => if m < y then y else m) x

/-- The product: the least and greatest of the four products of bounds. -/
def mul (p : Nat) (a b : Iv) : Option Iv :=
  let c := [a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  make p (least (a.lo * b.lo) c) (greatest (a.lo * b.lo) c)

/-- The reciprocal of an interval that excludes 0. -/
def inv (p : Nat) (a : Iv) : Option Iv :=
  if 0 < a.lo || a.hi < 0 then make p (1 / a.hi) (1 / a.lo) else none

/-- The quotient by an interval that excludes 0. -/
def div (p : Nat) (a b : Iv) : Option Iv := (inv p b).bind (mul p a)

/-- The quotient by a positive whole number. -/
def divNat (p : Nat) (a : Iv) (n : Nat) : Option Iv := make p (a.lo / n) (a.hi / n)

/-- The absolute value. -/
def abs (a : Iv) : Iv :=
  if 0 ≤ a.lo then a
  else if a.hi ≤ 0 then a.neg
  else ⟨0, if -a.lo < a.hi then a.hi else -a.lo⟩

/-- A whole power, by repeated squaring. -/
def powNat (p : Nat) (a : Iv) (n : Nat) : Option Iv :=
  if h : n = 0 then some ⟨1, 1⟩
  else do
    let half ← powNat p a (n / 2)
    let sq ← mul p half half
    if n % 2 = 0 then
      -- an even power is nonnegative
      some ⟨if sq.lo < 0 then 0 else sq.lo, sq.hi⟩
    else mul p sq a
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The interval excludes 0 and lies on one side of it: its sign. -/
def sign? (a : Iv) : Option Int :=
  if 0 < a.lo then some 1 else if a.hi < 0 then some (-1) else none

/-- The interval clamped to `[-1, 1]`, where sin and cos lie. -/
def unit (a : Iv) : Iv :=
  ⟨if a.lo < -1 then -1 else a.lo, if 1 < a.hi then 1 else a.hi⟩

/-! ## Roots -/

/-- `⌊n^(1/k)⌋` by bisection between `lo` and `hi`. -/
def rootBisect (n k : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid ^ k ≤ n then rootBisect n k fuel mid hi else rootBisect n k fuel lo mid

/-- `⌊n^(1/k)⌋`, `k ≥ 1`. -/
def floorRoot (n k : Nat) : Nat :=
  let hi := 2 ^ (Nat.log2 n / k + 1)
  rootBisect n k (Nat.log2 hi + 2) 0 hi

/-- A lower bound of `q^(1/k)`, `q ≥ 0`: `r / 2^s` with `r = ⌊⌊q 2^(sk)⌋^(1/k)⌋`. -/
def rootDown (p k : Nat) (q : Rat) : Rat :=
  if q ≤ 0 then 0
  else
    let s : Nat := (p + 2 + ((-(expOf q)) / (k : Int)).toNat)
    let n := (q * (2 : Rat) ^ (s * k)).floor.toNat
    (floorRoot n k : Rat) / (2 : Rat) ^ s

/-- An upper bound of `q^(1/k)`, `q ≥ 0`. -/
def rootUp (p k : Nat) (q : Rat) : Rat :=
  if q ≤ 0 then 0
  else
    let s : Nat := (p + 2 + ((-(expOf q)) / (k : Int)).toNat)
    let n := (q * (2 : Rat) ^ (s * k)).ceil.toNat
    let r := floorRoot n k
    let r' := if n ≤ r ^ k then r else r + 1
    -- `r'^k ≥ n` is checked, not assumed; `2^(log2 n / k + 1)` is always above the root
    let top := if n ≤ r' ^ k then r' else 2 ^ (Nat.log2 n / k + 1)
    (top : Rat) / (2 : Rat) ^ s

/-- The `k`-th root of a nonnegative interval. -/
def root (p k : Nat) (a : Iv) : Option Iv :=
  if a.lo < 0 || (expOf a.hi).natAbs > maxExp then none
  else make p (rootDown p k a.lo) (rootUp p k a.hi)

/-! ## π -/

/-- π between bounds at `p` bits (`Principia.Exact.piInterval`, Machin's formula). -/
def pi (p : Nat) : Iv :=
  let i := Exact.piInterval p
  ⟨(i.lo : Rat) * (2 : Rat) ^ i.exp, (i.hi : Rat) * (2 : Rat) ^ i.exp⟩

/-! ## exp -/

/-- The series of `e^y`, `0 ≤ y`, rounded down (`up = false`) or up, at `q` bits:
`Σ_{k<N} y^k/k!`, and on the upper side twice the next term added. -/
def expSeries (q : Nat) (y : Rat) (up : Bool) : Rat := Id.run do
  let rnd := if up then Iv.up q else Iv.down q
  let mut t : Rat := 1
  let mut s : Rat := 0
  let small : Rat := (2 : Rat) ^ (-(q : Int) - 8)
  for k in List.range (q + 8) do
    if t < small then break
    s := rnd (s + t)
    t := rnd (t * y / ((k + 1 : Nat) : Rat))
  return if up then rnd (s + 2 * t) else s

/-- Bounds of `e^r`, `r ≥ 0`, `r ≤ 2^14`: halved `s` times to at most 1/4, the series,
squared back `s` times. -/
def expNonneg (p : Nat) (r : Rat) : Option Iv :=
  if (2 : Rat) ^ (14 : Int) < r then none
  else
    let s : Nat := (expOf r + 3).toNat
    let q := p + s + 16
    let y := r / (2 : Rat) ^ (s : Int)
    let lo0 := expSeries q (down q y) false
    let hi0 := expSeries q (up q y) true
    let sq (up : Bool) (x : Rat) : Rat := if up then Iv.up q (x * x) else Iv.down q (x * x)
    let lo := (List.range s).foldl (fun x _ => sq false x) lo0
    let hi := (List.range s).foldl (fun x _ => sq true x) hi0
    make p lo hi

/-- Bounds of `e^r`. -/
def expPoint (p : Nat) (r : Rat) : Option Iv :=
  if 0 ≤ r then expNonneg p r else (expNonneg (p + 4) (-r)).bind (inv p)

/-- exp of an interval, exp increasing. -/
def exp (p : Nat) (a : Iv) : Option Iv := do
  let lo ← expPoint (p + 4) a.lo
  let hi ← expPoint (p + 4) a.hi
  make p lo.lo hi.hi

/-! ## ln -/

/-- `2 atanh z = 2 Σ z^(2k+1)/(2k+1)`, `0 ≤ z ≤ 1/3 + ε`, rounded down or up at `q` bits;
on the upper side twice the next term bounds the tail (`1/(1-z²) ≤ 9/8 + ε`). -/
def atanhTwice (q : Nat) (z : Rat) (up : Bool) : Rat := Id.run do
  let rnd := if up then Iv.up q else Iv.down q
  let z2 := rnd (z * z)
  let mut u : Rat := z
  let mut s : Rat := 0
  let small : Rat := (2 : Rat) ^ (-(q : Int) - 8)
  let mut last : Rat := 0
  for k in List.range (q + 8) do
    let t := rnd (u / ((2 * k + 1 : Nat) : Rat))
    last := t
    if t < small then break
    s := rnd (s + t)
    u := rnd (u * z2)
  return rnd (2 * (if up then s + 2 * last else s))

/-- ln 2 between bounds: `2 atanh(1/3)`. -/
def ln2 (q : Nat) : Iv := ⟨atanhTwice q (1 / 3) false, atanhTwice q (1 / 3) true⟩

/-- `m` with `1 ≤ r / 2^m < 2`, `r > 0`. -/
def log2Floor (r : Rat) : Int :=
  let e := expOf r
  if r < (2 : Rat) ^ e then e - 1 else if (2 : Rat) ^ (e + 1) ≤ r then e + 1 else e

/-- Bounds of `ln r`, `r > 0`. -/
def lnPoint (p : Nat) (r : Rat) : Option Iv :=
  if r ≤ 0 || !holdable r then none
  else
    let m := log2Floor r
    let q := p + (m.natAbs.log2) + 16
    let f := r / (2 : Rat) ^ m
    let fl := down q f
    let fh := up q f
    let zl := down q ((fl - 1) / (fl + 1))
    let zh := up q ((fh - 1) / (fh + 1))
    let lnf : Iv := ⟨atanhTwice q (if zl < 0 then 0 else zl) false, atanhTwice q zh true⟩
    let l2 := ln2 q
    let ml : Iv := if 0 ≤ m then ⟨m * l2.lo, m * l2.hi⟩ else ⟨m * l2.hi, m * l2.lo⟩
    add p ml lnf

/-- ln of a positive interval, ln increasing. -/
def ln (p : Nat) (a : Iv) : Option Iv := do
  if a.lo ≤ 0 then none
  let lo ← lnPoint (p + 4) a.lo
  let hi ← lnPoint (p + 4) a.hi
  make p lo.lo hi.hi

/-! ## sin and cos -/

/-- The Taylor sum of sin (`odd = true`) or cos at `m`, `|m| ≤ 4`, as an interval at `q`
bits: the terms' magnitudes `T_j` as intervals, summed with alternating signs, and the
remainder, below the next term's magnitude (Lagrange), added on both sides. -/
def taylor (q : Nat) (m : Rat) (odd : Bool) : Option Iv := do
  let a := if m < 0 then -m else m
  let a2 ← ofRat q (a * a)
  let mut t : Iv := if odd then ⟨a, a⟩ else ⟨1, 1⟩
  let mut s : Iv := ⟨0, 0⟩
  let small : Rat := (2 : Rat) ^ (-(q : Int) - 8)
  for j in List.range (2 * q + 16) do
    if t.hi < small then break
    s ← if j % 2 = 0 then add q s t else sub q s t
    let n := if odd then (2 * j + 2) * (2 * j + 3) else (2 * j + 1) * (2 * j + 2)
    t ← (mul q t a2).bind (divNat q · n)
  let r ← add q s ⟨-t.hi, t.hi⟩
  -- sin is odd, cos even
  return if odd && m < 0 then r.neg else r

/-- sin (`odd = true`) or cos of an interval: its midpoint reduced by whole turns, the
Taylor sum there, widened by the half-width; clamped to `[-1, 1]`. -/
def sinCos (p : Nat) (odd : Bool) (a : Iv) : Option Iv := do
  let mid := (a.lo + a.hi) / 2
  let half := (a.hi - a.lo) / 2
  if mid ≠ 0 && expOf mid > 4000 then none
  let q := p + (if mid = 0 then 0 else (expOf mid).toNat) + 24
  let piq := pi q
  -- a whole number of turns to take off: any count is exact; this one leaves |t| ≤ 4
  let k : Int := ((mid / (2 * piq.lo)) + 1 / 2).floor
  let pk ← mul q piq ⟨2 * k, 2 * k⟩
  let t ← sub q ⟨mid, mid⟩ pk
  -- `t` encloses `mid - 2kπ`; Taylor at its midpoint, widened by its half-width
  let tm := (t.lo + t.hi) / 2
  let th := (t.hi - t.lo) / 2
  if 4 < (if tm < 0 then -tm else tm) then none
  let v ← taylor q tm odd
  let w ← make p (v.lo - th - half) (v.hi + th + half)
  return w.unit

/-! ## Guarantees

Each bound is rounded outward, and each operation on bounds encloses the operation on any
two rational numbers its operands enclose: rounding, `+`, `-`, `*`, `1/x` and `/`, and the
sign a decision reads off an interval. The reals are not in Lean's core library, so these
are stated for rational numbers; a real number between two bounds is a limit of rationals
between them, and every operation here is continuous where it is defined. The function
bounds (exp, ln, sin, cos, roots) rest on the series' remainders stated above, and are
checked against an independent computation, the form numbers' corpus. -/


/-- Rounding down never rises above the number. -/
theorem down_le (p : Nat) (q : Rat) : down p q ≤ q := by
  unfold down
  split
  · next h => subst h; exact Rat.le_refl
  · next h =>
    have hpos : (0 : Rat) < (2 : Rat) ^ ((p : Int) - expOf q) := Rat.zpow_pos (by decide)
    apply Rat.le_of_mul_le_mul_right _ hpos
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hpos)]
    exact Rat.floor_le _

/-- Rounding up never falls below the number. -/
theorem le_up (p : Nat) (q : Rat) : q ≤ up p q := by
  unfold up
  split
  · next h => subst h; exact Rat.le_refl
  · next h =>
    have hpos : (0 : Rat) < (2 : Rat) ^ ((p : Int) - expOf q) := Rat.zpow_pos (by decide)
    apply Rat.le_of_mul_le_mul_right _ hpos
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hpos)]
    exact Rat.le_ceil

/-- `x` lies in the interval. -/
def Mem (x : Rat) (a : Iv) : Prop := a.lo ≤ x ∧ x ≤ a.hi

/-- An interval made from two bounds holds every number between them. -/
theorem mem_make {p : Nat} {lo hi x : Rat} {a : Iv} (h : make p lo hi = some a)
    (h1 : lo ≤ x) (h2 : x ≤ hi) : Mem x a := by
  unfold make at h
  split at h
  · cases h
    exact ⟨Rat.le_trans (down_le p lo) h1, Rat.le_trans h2 (le_up p hi)⟩
  · cases h

theorem add_le_add' {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

/-- The sum of two intervals holds the sum of any two numbers they hold. -/
theorem mem_add {p : Nat} {a b c : Iv} {x y : Rat} (hx : Mem x a) (hy : Mem y b)
    (h : add p a b = some c) : Mem (x + y) c :=
  mem_make h (add_le_add' hx.1 hy.1) (add_le_add' hx.2 hy.2)

/-- The negation of an interval holds the negation of any number it holds. -/
theorem mem_neg {a : Iv} {x : Rat} (hx : Mem x a) : Mem (-x) a.neg :=
  ⟨Rat.neg_le_neg hx.2, Rat.neg_le_neg hx.1⟩

/-- The difference of two intervals holds the difference of any two numbers they hold. -/
theorem mem_sub {p : Nat} {a b c : Iv} {x y : Rat} (hx : Mem x a) (hy : Mem y b)
    (h : sub p a b = some c) : Mem (x - y) c := by
  rw [Rat.sub_eq_add_neg]
  exact mem_add hx (mem_neg hy) h

/-- An interval settled positive holds only positive numbers. -/
theorem sign_pos {a : Iv} {x : Rat} (hx : Mem x a) (h : a.sign? = some 1) : 0 < x := by
  unfold sign? at h
  split at h
  · next h0 => exact Std.lt_of_lt_of_le h0 hx.1
  · split at h <;> simp at h

/-- An interval settled negative holds only negative numbers. -/
theorem sign_neg {a : Iv} {x : Rat} (hx : Mem x a) (h : a.sign? = some (-1)) : x < 0 := by
  unfold sign? at h
  split at h
  · simp at h
  · split at h
    · next h0 => exact Std.lt_of_le_of_lt hx.2 h0
    · simp at h

theorem mul_le_mul_nonpos {a b c : Rat} (h : a ≤ b) (hc : c ≤ 0) : b * c ≤ a * c := by
  have hn : 0 ≤ -c := by
    have := Rat.neg_le_neg hc
    simpa using this
  have h1 := Rat.mul_le_mul_of_nonneg_right h hn
  rw [Rat.mul_neg, Rat.mul_neg] at h1
  have := Rat.neg_le_neg h1
  simpa using this

/-- `x c` lies between `lo c` and `hi c`, in one order or the other. -/
theorem mul_between {lo hi x c : Rat} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    ∃ u ∈ [lo * c, hi * c], ∃ v ∈ [lo * c, hi * c], u ≤ x * c ∧ x * c ≤ v := by
  cases Rat.le_total (a := 0) (b := c) with
  | inl hc =>
    exact ⟨lo * c, by simp, hi * c, by simp,
      Rat.mul_le_mul_of_nonneg_right h1 hc, Rat.mul_le_mul_of_nonneg_right h2 hc⟩
  | inr hc =>
    exact ⟨hi * c, by simp, lo * c, by simp, mul_le_mul_nonpos h2 hc, mul_le_mul_nonpos h1 hc⟩

theorem least_le_aux (xs : List Rat) : ∀ (m : Rat), ∀ y ∈ m :: xs, xs.foldl (fun m y => if y < m then y else m) m ≤ y := by
  induction xs with
  | nil => intro m y hy; simp at hy; subst hy; exact Rat.le_refl
  | cons z zs ih =>
    intro m y hy
    simp only [List.foldl]
    by_cases hz : z < m
    · simp only [hz, ite_true]
      rcases List.mem_cons.mp hy with h | h
      · subst h; exact Rat.le_trans (ih z z (by simp)) (Rat.le_of_lt hz)
      · exact ih z y h
    · simp only [hz]
      rcases List.mem_cons.mp hy with h | h
      · subst h; exact ih y y (by simp)
      · rcases List.mem_cons.mp h with h' | h'
        · subst h'
          exact Rat.le_trans (ih m m (by simp)) (Rat.not_lt.mp hz)
        · exact ih m y (List.mem_cons_of_mem _ h')

theorem least_le {x : Rat} {xs : List Rat} {y : Rat} (h : y ∈ x :: xs) : least x xs ≤ y :=
  least_le_aux xs x y h

theorem le_greatest_aux (xs : List Rat) : ∀ (m : Rat), ∀ y ∈ m :: xs, y ≤ xs.foldl (fun m y => if m < y then y else m) m := by
  induction xs with
  | nil => intro m y hy; simp at hy; subst hy; exact Rat.le_refl
  | cons z zs ih =>
    intro m y hy
    simp only [List.foldl]
    by_cases hz : m < z
    · simp only [hz, ite_true]
      rcases List.mem_cons.mp hy with h | h
      · subst h; exact Rat.le_trans (Rat.le_of_lt hz) (ih z z (by simp))
      · exact ih z y h
    · simp only [hz]
      rcases List.mem_cons.mp hy with h | h
      · subst h; exact ih y y (by simp)
      · rcases List.mem_cons.mp h with h' | h'
        · subst h'
          exact Rat.le_trans (Rat.not_lt.mp hz) (ih m m (by simp))
        · exact ih m y (List.mem_cons_of_mem _ h')

theorem le_greatest {x : Rat} {xs : List Rat} {y : Rat} (h : y ∈ x :: xs) : y ≤ greatest x xs :=
  le_greatest_aux xs x y h

/-- The product of two intervals holds the product of any two numbers they hold. -/
theorem mem_mul {p : Nat} {a b c : Iv} {x y : Rat} (hx : Mem x a) (hy : Mem y b)
    (h : mul p a b = some c) : Mem (x * y) c := by
  unfold mul at h
  apply mem_make h
  · obtain ⟨u, hu, -, -, hux, -⟩ := mul_between (c := x) hy.1 hy.2
    have hxy : u ≤ x * y := by rw [Rat.mul_comm x y]; exact hux
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with hu | hu <;> subst hu
    · obtain ⟨w, hw, -, -, hwx, -⟩ := mul_between (c := b.lo) hx.1 hx.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      refine Rat.le_trans ?_ (Rat.le_trans hwx (by rw [Rat.mul_comm]; exact hxy))
      rcases hw with hw | hw <;> subst hw <;> apply least_le <;> simp [Rat.mul_comm]
    · obtain ⟨w, hw, -, -, hwx, -⟩ := mul_between (c := b.hi) hx.1 hx.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      refine Rat.le_trans ?_ (Rat.le_trans hwx (by rw [Rat.mul_comm]; exact hxy))
      rcases hw with hw | hw <;> subst hw <;> apply least_le <;> simp [Rat.mul_comm]
  · obtain ⟨-, -, v, hv, -, hxv⟩ := mul_between (c := x) hy.1 hy.2
    have hxy : x * y ≤ v := by rw [Rat.mul_comm x y]; exact hxv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with hv | hv <;> subst hv
    · obtain ⟨-, -, w, hw, -, hxw⟩ := mul_between (c := b.lo) hx.1 hx.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      refine Rat.le_trans (Rat.le_trans hxy (by rw [Rat.mul_comm]; exact hxw)) ?_
      rcases hw with hw | hw <;> subst hw <;> apply le_greatest <;> simp [Rat.mul_comm]
    · obtain ⟨-, -, w, hw, -, hxw⟩ := mul_between (c := b.hi) hx.1 hx.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      refine Rat.le_trans (Rat.le_trans hxy (by rw [Rat.mul_comm]; exact hxw)) ?_
      rcases hw with hw | hw <;> subst hw <;> apply le_greatest <;> simp [Rat.mul_comm]

/-- Inversion reverses the order of two numbers of one sign. -/
theorem inv_le_inv_of_mul_pos {a b : Rat} (hab : a ≤ b) (hp : 0 < a * b) : b⁻¹ ≤ a⁻¹ := by
  have ha : a ≠ 0 := by intro h; subst h; simp at hp
  have hb : b ≠ 0 := by intro h; subst h; simp at hp
  apply Rat.le_of_mul_le_mul_right _ hp
  have e1 : b⁻¹ * (a * b) = a := by
    rw [Rat.mul_comm a b, ← Rat.mul_assoc, Rat.inv_mul_cancel b hb, Rat.one_mul]
  have e2 : a⁻¹ * (a * b) = b := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel a ha, Rat.one_mul]
  rw [e1, e2]
  exact hab

/-- The reciprocal of an interval that excludes 0 holds the reciprocal of any number it
holds. -/
theorem mem_inv {p : Nat} {a c : Iv} {x : Rat} (hx : Mem x a) (h : inv p a = some c) :
    Mem (1 / x) c := by
  unfold inv at h
  split at h
  · next hs =>
    have key : ∀ u v : Rat, u ≤ v → (0 < u ∨ v < 0) → 0 < u * v := by
      intro u v huv hs
      rcases hs with hu | hv
      · exact Rat.mul_pos hu (Std.lt_of_lt_of_le hu huv)
      · have hu : u < 0 := Std.lt_of_le_of_lt huv hv
        have : 0 < (-u) * (-v) := Rat.mul_pos (by simpa using Rat.neg_lt_neg hu)
          (by simpa using Rat.neg_lt_neg hv)
        simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using this
    have side : 0 < a.lo ∨ a.hi < 0 := by simpa using hs
    apply mem_make h
    · rw [Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul]
      apply inv_le_inv_of_mul_pos hx.2
      apply key x a.hi hx.2
      rcases side with h1 | h1
      · exact Or.inl (Std.lt_of_lt_of_le h1 hx.1)
      · exact Or.inr h1
    · rw [Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul]
      apply inv_le_inv_of_mul_pos hx.1
      apply key a.lo x hx.1
      rcases side with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Std.lt_of_le_of_lt hx.2 h1)
  · cases h

/-- The quotient of two intervals holds the quotient of any two numbers they hold. -/
theorem mem_div {p : Nat} {a b c : Iv} {x y : Rat} (hx : Mem x a) (hy : Mem y b)
    (h : div p a b = some c) : Mem (x / y) c := by
  unfold div at h
  cases hi : inv p b with
  | none => simp [hi] at h
  | some d =>
    simp only [hi, Option.bind_some] at h
    have := mem_mul hx (mem_inv hy hi) h
    rwa [Rat.div_def 1, Rat.one_mul, ← Rat.div_def] at this

end Iv

end Principia.Form
