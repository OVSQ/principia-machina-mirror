import Principia.Calculator.Interface
import Principia.Calculator.Strike
import Principia.Units.Bounded

/-!
# Family `units`: units and dimensions

v1's seven unit functions, each taking v1's arguments by v1's names. A UNIT, a DIMENSION,
a VALUE and an UNCERTAINTY may be any JSON value, as v1 took them: a string is read, and
any other value is refused by the function, quoted `?`, as v1 refused it.

* `unit_parse {"u"}`: `["OK", spelling, DIMENSION, KIND]`.
* `unit_scale {"u"}`: `["OK", scale]`, the factor to coherent SI.
* `unit_matches {"u", "dimension"}`: `["OK", true or false]`, whether the UNIT is
  commensurable with the DIMENSION.
* `normalize_measurement {"value", "uncertainty", "u"}`: `["OK", value, uncertainty,
  DIMENSION, KIND]`, scaled to coherent SI.
* `mm_contradicts_units {"x1", "u1", "unit1", "x2", "u2", "unit2", "k", "s"?}` and
  `lm_contradicts_units {"x_l", "unit_l", "x_m", "u_m", "unit_m", "k", "s"?}`: SR3's two
  tests after normalization, `["OK", true or false]`; `k` a number, `s` at least 1, 1 when
  absent or null.
* `sr8_scale_factor_units {"measurements": [{"x", "u", "unit"}, ...]}`: SR8's scale factor
  after normalization, `["OK", S]`, `S` correctly rounded to twelve significant digits, as
  the strike rule's `sr8_scale_factor` gives it; across powers of π, from enclosures of π
  (`Principia.Strike.PiScale`).

Each answers as v1 answered, a list: `["OK", ...]`, `["REFUSED", reason]` for a request v1
refused, with v1's reason, or `["CONVENTION", reason]` for measurements of different KIND,
which are never compared. Numbers are exact, never rounded: a rational times a power of π,
written as a canonical decimal (`5e-2`, `1e308`) or as a fraction in lowest terms (`1/60`),
then `pi` and its power when there is one (`1/32400 pi2`). Where v1 printed a double, its
twelve digits are that exact number's, rounded.

Two answers are owed, refused `OWED` with these words, since the Calculator does not
compute them yet: SR8 over measurements whose units carry different powers of π (a degree
against a radian), until the strike rule takes them; and an SR3 test across two powers of π
that bounds on π of 4096 bits do not decide, which needs the two sides within about
2^-4000 of each other.

Bounds, measured: a UNIT or a DIMENSION of at most `maxUnitChars` characters and
`maxUnitTokens` tokens; a VALUE, an UNCERTAINTY, `x1`, `x_l` and the others of at most
`maxDecimalChars` characters; at most `maxMeasurements` measurements for SR8, each value and
uncertainty of at most `maxMeasurementDigits` digits, the strike rule's bounds. Every number
formed from a request lies within the bound on an exact value; one that would cross it is
refused, "exact value too large". A unit's scale is held in lowest terms, so its bound is
exact: a scale whose denominator has 65,536 bits is given in 0.03 s, one of 65,537 refused,
and a unit of 21 prefixed arcseconds in 253 characters, whose scale near 10^12 has a
numerator and a denominator of more than a million bits, is refused at once.
-/

namespace Principia.Calculator.Units

open Principia.Canonical
open Principia.Units (Arg Outcome)

/-! ## The family's bounds, measured -/

/-- The most characters a UNIT or a DIMENSION holds. Reading a unit is linear in its
length, and its scale is formed in lowest terms within the bound on an exact value: a unit
of 1024 characters and 128 tokens is read and scaled in 0.02 s, no longer than the shortest
request, and one of a mebibyte is refused in 0.1 s, most of it reading the request. The
bound keeps a reason, which quotes the unit, short. -/
def maxUnitChars : Nat := 1024

/-- The most tokens a UNIT or a DIMENSION holds: each token is merged with those before
it. -/
def maxUnitTokens : Nat := 128

/-- The most characters a decimal holds: as many as the digits of a number the request's
reader takes. A VALUE and an UNCERTAINTY of 4096 characters in a unit of 1024 are
normalized in 0.03 s, and SR3's two tests over them take 0.04 s. -/
def maxDecimalChars : Nat := 4096

/-- The most measurements SR8 scales: the strike rule's bound. -/
def maxMeasurements : Nat := Principia.Calculator.Strike.maxMeasurements

/-- The most digits of an SR8 measurement's value or uncertainty, those before its
exponent: the strike rule's bound, since SR8's exact sums run over fractions whose
denominators grow with them. 100 measurements of 30 digits take 0.29 s in metres, 0.39 s
with exponents spread from -300 to 250, and 0.54 s each in a unit of 1024 characters;
without this bound, 100 of 4096 characters took 1.8 s. -/
def maxMeasurementDigits : Nat := Principia.Calculator.Strike.maxMeasurementDigits

/-! ## Reading a request -/

/-- A UNIT or a DIMENSION within the bounds. -/
def spaced (what : String) (v : Value) : Except Refusal Arg := do
  match v with
  | .str s =>
    if maxUnitChars < s.length then
      badArgument s!"{what} has more than {maxUnitChars} characters (the Calculator's bound)"
    if maxUnitTokens < (s.toList.filter (· == ' ')).length + 1 then
      badArgument s!"{what} has more than {maxUnitTokens} tokens (the Calculator's bound)"
    pure (some s)
  | _ => pure none

/-- A decimal within the bound. -/
def decimal (what : String) (v : Value) : Except Refusal Arg := do
  match v with
  | .str s =>
    if maxDecimalChars < s.length then
      badArgument s!"{what} has more than {maxDecimalChars} characters (the Calculator's bound)"
    pure (some s)
  | _ => pure none

/-- The digits of a decimal before its exponent. -/
def digitsOf (s : String) : Nat :=
  ((s.toList.takeWhile fun c => c != 'e' && c != 'E').filter Char.isDigit).length

/-- An SR8 measurement's value or uncertainty: a decimal within the bound, of at most
`maxMeasurementDigits` digits. -/
def sr8Decimal (what : String) (v : Value) : Except Refusal Arg := do
  let a ← decimal what v
  if (a.map digitsOf).any (maxMeasurementDigits < ·) then
    badArgument s!"{what} has more than {maxMeasurementDigits} digits (the Calculator's bound)"
  pure a

/-- `s`: at least 1, held as its square, formed within the bound; 1 when absent. -/
def readScale (ms : List (String × Value)) : Except Refusal Principia.Strike.ScaleFactor := do
  match optional ms "s" with
  | none => pure .one
  | some x =>
    let s ← asNumber "s" x
    let ss ← bounded (Principia.ValueBound.mul s s)
    if h : 1 ≤ s ∧ 1 ≤ ss then pure ⟨ss, h.2⟩
    else badArgument "s is at least 1 (SR8's scale factor)"

/-! ## Answers -/

/-- The reasons of answers the Calculator owes. -/
def owedReasons : List String := [Principia.Units.undecided]

/-- v1's list of a refusal. -/
def refusedValue (r : String) : Value := .arr [.str "REFUSED", .str r]

/-- A result as v1 listed it, `["OK", ...]` or `["REFUSED", reason]`. -/
def listed {α : Type} (items : α → List Value) : Except String α → Value
  | .ok a => .arr (.str "OK" :: items a)
  | .error r => refusedValue r

/-- An outcome as v1 listed it, or refused `OWED` when the Calculator owes it. -/
def outcome {α : Type} (items : α → List Value) : Outcome α → Except Refusal Value
  | .ok a => .ok (.arr (.str "OK" :: items a))
  | .convention r => .ok (.arr [.str "CONVENTION", .str r])
  | .refused r => if owedReasons.contains r then .error ⟨.owed, r⟩ else .ok (refusedValue r)

/-- An exact number. -/
def exact (x : Exact) : Value := .str x.render

/-- A normalized measurement's items. -/
def measurementItems (m : Principia.Units.Measurement) : List Value :=
  [exact m.x, exact m.u, .str m.dimension, .str m.kind]

/-- SR8's `S`, correctly rounded to twelve significant digits. -/
def scaleFactorItem (S : Principia.Units.ScaleAnswer) : Value :=
  let (m, e) := S.digits12
  .num ⟨m, e⟩

/-- The family's functions. -/
def calls : Family := [
  ("lm_contradicts_units", fun v => do
    let ms ← membersOf ["x_l", "unit_l", "x_m", "u_m", "unit_m", "k", "s"] v
    let xL ← decimal "x_l" (← needed ms "x_l")
    let unitL ← spaced "unit_l" (← needed ms "unit_l")
    let xM ← decimal "x_m" (← needed ms "x_m")
    let uM ← decimal "u_m" (← needed ms "u_m")
    let unitM ← spaced "unit_m" (← needed ms "unit_m")
    let k ← asNumber "k" (← needed ms "k")
    let S ← readScale ms
    outcome (fun b => [.bool b])
      (← bounded (Principia.Units.Bounded.lmContradictsUnitsArg xL unitL xM uM unitM k S))),
  ("mm_contradicts_units", fun v => do
    let ms ← membersOf ["x1", "u1", "unit1", "x2", "u2", "unit2", "k", "s"] v
    let x1 ← decimal "x1" (← needed ms "x1")
    let u1 ← decimal "u1" (← needed ms "u1")
    let unit1 ← spaced "unit1" (← needed ms "unit1")
    let x2 ← decimal "x2" (← needed ms "x2")
    let u2 ← decimal "u2" (← needed ms "u2")
    let unit2 ← spaced "unit2" (← needed ms "unit2")
    let k ← asNumber "k" (← needed ms "k")
    let S ← readScale ms
    outcome (fun b => [.bool b])
      (← bounded (Principia.Units.Bounded.mmContradictsUnitsArg x1 u1 unit1 x2 u2 unit2 k S))),
  ("normalize_measurement", fun v => do
    let (a, b, c) ← argument3 "value" "uncertainty" "u" v
    let value ← decimal "value" a
    let uncertainty ← decimal "uncertainty" b
    let u ← spaced "u" c
    pure (listed measurementItems
      (← bounded (Principia.Units.Bounded.normalizeMeasurementArg value uncertainty u)))),
  ("sr8_scale_factor_units", fun v => do
    let mlist ← asList "measurements" (← argument1 "measurements" v)
    atMost "measurements" maxMeasurements mlist
    let ms ← mlist.mapM fun m => do
      let o ← asObject "a measurement" m
      let x ← sr8Decimal "x" (← needed o "x")
      let u ← sr8Decimal "u" (← needed o "u")
      let unit ← spaced "unit" (← needed o "unit")
      pure (x, u, unit)
    outcome (fun S => [scaleFactorItem S])
      (← bounded (Principia.Units.Bounded.sr8ScaleFactorUnitsArg ms))),
  ("unit_matches", fun v => do
    let (a, b) ← argument2 "u" "dimension" v
    let u ← spaced "u" a
    let d ← spaced "dimension" b
    pure (listed (fun b => [.bool b]) (Principia.Units.unitMatchesArg u d))),
  ("unit_parse", fun v => do
    let u ← spaced "u" (← argument1 "u" v)
    pure (listed (fun p => [.str p.spelling, .str p.dimension, .str p.kind])
      (Principia.Units.unitParseArg u))),
  ("unit_scale", fun v => do
    let u ← spaced "u" (← argument1 "u" v)
    pure (listed (fun x => [exact x]) (← bounded (Principia.Units.Bounded.unitScaleArg u))))]

end Principia.Calculator.Units
