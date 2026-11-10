/-!
# The bound on an exact value's size

The Calculator's numbers are exact. An exact value's numerator and denominator each hold
at most `maxBits` bits, 65,536, as the Declarer chose: a value that would cross the bound is
refused, "exact value too large", where version 1, computing in doubles, never grew. The
check is made from the operands before the value is formed, so the work a request can
cause stays within reach. It first divides out the factors the operands share, as `Rat`
itself does when it forms the value, with a greatest common divisor of numbers already
within the bound; then a product's numerator has at most the bits of what is left of its
operands' numerators together, its denominator likewise, and a sum's denominator at most
the bits of the operands' least common multiple, its numerator one bit more than the
larger of its two cross products over that multiple.

A site that forms a value from a request's inputs computes through `add`, `sub`, `mul` and
`div`, each refused by `tooLarge` when its result could cross the bound and otherwise the
plain operation (`mul_ok`, ...), so a guarded computation that answers answers what the
plain one does. A check that passes may still give a value well under the bound, since a
sum or product is reduced; a refusal can be conservative, by at most one operation's
growth.
-/

namespace Principia.ValueBound

/-- The most bits an exact value's numerator, and its denominator, may hold. -/
def maxBits : Nat := 65536

/-- The refusal of a value that would cross the bound. -/
def tooLarge : String := "exact value too large"

/-- A computation that may be refused for the bound. -/
abbrev Bounded := Except String

/-- The bits of a whole number: `0` for `0`. -/
def bits (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- The bits of a value's numerator, by magnitude. -/
def numBits (q : Rat) : Nat := bits q.num.natAbs

/-- The bits of a value's denominator. -/
def denBits (q : Rat) : Nat := bits q.den

/-- A value within the bound. -/
def within (q : Rat) : Bool := numBits q ≤ maxBits && denBits q ≤ maxBits

/-- `n / d · m / e` cannot cross the bound, the factors `n` shares with `e` and `m` with `d`
divided out first. -/
def prodFits (n d m e : Nat) : Bool :=
  let g1 := Nat.gcd n e
  let g2 := Nat.gcd m d
  bits (n / g1) + bits (m / g2) ≤ maxBits && bits (d / g2) + bits (e / g1) ≤ maxBits

/-- `a * b` cannot cross the bound. -/
def mulFits (a b : Rat) : Bool := prodFits a.num.natAbs a.den b.num.natAbs b.den

/-- `a / b` cannot cross the bound. -/
def divFits (a b : Rat) : Bool := prodFits a.num.natAbs a.den b.den b.num.natAbs

/-- `a + b`, and `a - b`, cannot cross the bound: over the least common multiple of the
denominators, `a.den / g · b.den`. -/
def addFits (a b : Rat) : Bool :=
  let g := Nat.gcd a.den b.den
  max (numBits a + bits (b.den / g)) (numBits b + bits (a.den / g)) + 1 ≤ maxBits &&
    bits (a.den / g * b.den) ≤ maxBits

/-- A value read whole, refused when it already crosses the bound. -/
def ofRat (q : Rat) : Bounded Rat := if within q then .ok q else .error tooLarge

/-- `a + b`, or refused. -/
def add (a b : Rat) : Bounded Rat := if addFits a b then .ok (a + b) else .error tooLarge

/-- `a - b`, or refused. -/
def sub (a b : Rat) : Bounded Rat := if addFits a b then .ok (a - b) else .error tooLarge

/-- `a * b`, or refused. -/
def mul (a b : Rat) : Bounded Rat := if mulFits a b then .ok (a * b) else .error tooLarge

/-- `a / b`, or refused. -/
def div (a b : Rat) : Bounded Rat := if divFits a b then .ok (a / b) else .error tooLarge

/-- The sum of `f` over `l`, left to right, each addition checked. -/
def sumBy {α : Type} (f : α → Bounded Rat) (l : List α) : Bounded Rat :=
  l.foldlM (fun s a => do add s (← f a)) 0

/-! ## PROVED -/

theorem ofRat_ok {q r : Rat} (h : ofRat q = .ok r) : r = q := by
  unfold ofRat at h; split at h <;> cases h; rfl

theorem add_ok {a b c : Rat} (h : add a b = .ok c) : c = a + b := by
  unfold add at h; split at h <;> cases h; rfl

theorem sub_ok {a b c : Rat} (h : sub a b = .ok c) : c = a - b := by
  unfold sub at h; split at h <;> cases h; rfl

theorem mul_ok {a b c : Rat} (h : mul a b = .ok c) : c = a * b := by
  unfold mul at h; split at h <;> cases h; rfl

theorem div_ok {a b c : Rat} (h : div a b = .ok c) : c = a / b := by
  unfold div at h; split at h <;> cases h; rfl

/-- A refusal is the bound's. -/
theorem mul_error {a b : Rat} {e : String} (h : mul a b = .error e) : e = tooLarge := by
  unfold mul at h; split at h <;> cases h; rfl

/-- Every `bits n` bits hold `n`. -/
theorem lt_two_pow_bits (n : Nat) : n < 2 ^ bits n := by
  unfold bits
  split
  · rename_i h; subst h; exact Nat.two_pow_pos 0
  · rename_i h; exact Nat.lt_log2_self

/-- The checked sum, when it answers, is the plain left-to-right sum of what each term
answers. -/
theorem sumBy_ok {α : Type} (f : α → Bounded Rat) (g : α → Rat)
    (hf : ∀ a c, f a = .ok c → c = g a) :
    ∀ (l : List α) (s0 r : Rat),
      l.foldlM (fun s a => do add s (← f a)) s0 = .ok r →
        r = l.foldl (fun s a => s + g a) s0
  | [], s0, r, h => by
    simp only [List.foldlM_nil] at h
    cases h; rfl
  | a :: l, s0, r, h => by
    simp only [List.foldlM_cons] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok c =>
      rw [hfa] at h
      change (add s0 c >>= fun init => l.foldlM (fun s a => do add s (← f a)) init) = .ok r at h
      cases hadd : add s0 c with
      | error e => rw [hadd] at h; cases h
      | ok s1 =>
        rw [hadd] at h
        have hc := hf a c hfa
        have hs1 := add_ok hadd
        rw [sumBy_ok f g hf l s1 r h, List.foldl_cons, hs1, hc]

end Principia.ValueBound
