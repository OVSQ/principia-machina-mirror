import Principia.Units
import Principia.Strike
import Principia.Strike.PiScale

/-!
# Units: the strike rule after normalization

v1's tpc_units 0.1.1 wrappers around the strike rule (tpm_units 0.2.0, 7 and 9; TPS 4.4.4
as amended): `mm_contradicts_units`, `lm_contradicts_units` and
`sr8_scale_factor_units`. Each normalizes its measurements to coherent SI
(`normalizeMeasurement`), refuses measurements of different DIMENSION, answers CONVENTION
for different KIND (an audit block, never compared and never an error), and only then
calls the strike rule (`Principia.Strike`).

Powers of π. A normalized value is `q × π^k` (`Principia.Exact`); the strike rule takes
rationals. Measurements whose values share one power of π have it divided out, which
changes no verdict (both sides of SR3's test, and SR8's chi-square, scale alike), and go to
the strike rule as rationals. Measurements of one KIND can still carry different powers (a
degree against a radian):
- SR3's two tests compare squares, a polynomial in `t = π^m` with rational coefficients;
  its sign is decided with certainty by `Exact.polySignAtPiPow`, since `π^m` is
  transcendental. Only a comparison within about 2^-4000 of its bound would be left
  undecided, and is refused with that reason.
- SR8 over such a group gives an `S²` that is a ratio of two polynomials in π
  (`Strike.PiScale.sr8ScaleSquarePi`), every sign it needs decided as SR3's are; `S` is
  answered to twelve significant digits from enclosures of π. A group whose powers differ
  by more than 64 is refused, and a sign 4096 bits do not settle is left undecided.

Results are `Outcome`: OK, CONVENTION or REFUSED, as v1's lists were.
-/

namespace Principia.Units

/-- v1's three answers: `["OK", ...]`, `["CONVENTION", reason]` (an audit block) or
`["REFUSED", reason]`. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | convention (reason : String)
  | refused (reason : String)
  deriving Repr

/-- An outcome in v1's bracket form. -/
def Outcome.bracket {α : Type} (items : α → List String) : Outcome α → String
  | .ok a => "[" ++ ",".intercalate ("OK" :: items a) ++ "]"
  | .convention r => "[CONVENTION," ++ r ++ "]"
  | .refused r => "[REFUSED," ++ r ++ "]"

/-- A normalized measurement's power of π: its value's, or its uncertainty's when the
value is zero (zero is `0 × π^0`, and equally `0 × π^k`). -/
def Measurement.piPower (m : Measurement) : Int :=
  if m.x.coef = 0 then m.u.pi else m.x.pi

/-- The value and the uncertainty with `π^k` divided out, for `k` the measurement's power:
rationals. -/
def Measurement.coefs (m : Measurement) : Rat × Rat := (m.x.coef, m.u.coef)

/-- v1's convention answer for two KINDs. -/
def kindConvention (k1 k2 : String) : String := s!"units of different kind: {k1} and {k2}"

/-- v1's refusal for two DIMENSIONs. -/
def dimensionRefusal (d1 d2 : String) : String :=
  escape s!"units of different dimension: {d1} and {d2}"

/-- v1's `_pair`: both measurements normalized (the first refusal is the answer), then
refused unless they share a DIMENSION, and CONVENTION unless they share a KIND. -/
def pairMeasurements (xa ua unitA xb ub unitB : Arg) : Outcome (Measurement × Measurement) :=
  match normalizeMeasurementArg xa ua unitA with
  | .error r => .refused r
  | .ok ma =>
    match normalizeMeasurementArg xb ub unitB with
    | .error r => .refused r
    | .ok mb =>
      if ma.dimension != mb.dimension then .refused (dimensionRefusal ma.dimension mb.dimension)
      else if ma.kind != mb.kind then .convention (kindConvention ma.kind mb.kind)
      else .ok (ma, mb)

/-- The reason for a comparison that 4096 bits of π do not decide. -/
def undecided : String := Strike.PiScale.undecided

/-- `|d| > c · √v` as `Strike.Numeric.exceedsBound` decides it, with `dd`, `c²v` and the
signs of `c` and `v` given as polynomials in `t = π^m` (coefficients from `t⁰` up). -/
def exceedsAtPiPow (dd ccv : List Rat) (cSign : Ordering) (vPos : Bool) (m : Int) :
    Option Bool :=
  match cSign with
  | .gt =>
    let diff := (List.range (max dd.length ccv.length)).map fun i =>
      dd.getD i 0 - ccv.getD i 0
    (Exact.polySignAtPiPow diff m).map (· == .gt)
  | .lt => if vPos then some true else (Exact.polySignAtPiPow dd m).map (· == .gt)
  | .eq => (Exact.polySignAtPiPow dd m).map (· == .gt)

/-- The sign of a rational. -/
def ratSign (q : Rat) : Ordering := if q < 0 then .lt else if 0 < q then .gt else .eq

/-- SR3's M-M test on two normalized measurements of one DIMENSION and KIND:
`|x1 - x2| > k · S · √(u1² + u2²)`. With one power of π, divided out, it is
`Strike.mmContradicts`; otherwise, with `π^p1` divided out and `t = π^(p2 - p1)`, `x2` and
`u2` are `a2 t` and `b2 t`, and the test is a polynomial's sign at `t`. -/
def mmCompare (m1 m2 : Measurement) (k : Rat) (S : Strike.ScaleFactor) : Option Bool :=
  let (a1, b1) := m1.coefs
  let (a2, b2) := m2.coefs
  let m := m2.piPower - m1.piPower
  if m = 0 then some (Strike.mmContradicts a1 b1 a2 b2 k S)
  else
    let ss := S.square
    -- (a1 - a2 t)²  and  k² S² (b1² + b2² t²)
    exceedsAtPiPow [a1 * a1, -2 * a1 * a2, a2 * a2]
      [k * k * ss * (b1 * b1), 0, k * k * ss * (b2 * b2)] (ratSign k)
      (b1 != 0 || b2 != 0) m

/-- SR3's L-M test: the L record's derived value `xL`, no uncertainty, against the M
measurement: `|xM - xL| > k · uM · S`. With `π^pL` divided out and `t = π^(pM - pL)`,
`xM` and `uM` are `aM t` and `bM t`. -/
def lmCompare (mL mM : Measurement) (k : Rat) (S : Strike.ScaleFactor) : Option Bool :=
  let aL := mL.x.coef
  let (aM, bM) := mM.coefs
  let m := mM.piPower - mL.piPower
  if m = 0 then some (Strike.lmContradicts aL aM bM k S)
  else
    -- (aM t - aL)²  and  (k bM t)² S²
    exceedsAtPiPow [aL * aL, -2 * aM * aL, aM * aM] [0, 0, k * k * bM * bM * S.square]
      (ratSign (k * bM)) true m

/-- `mm_contradicts_units`: SR3's M-M test after normalization. -/
def mmContradictsUnitsArg (x1 u1 unit1 x2 u2 unit2 : Arg) (k : Rat)
    (S : Strike.ScaleFactor := .one) : Outcome Bool :=
  match pairMeasurements x1 u1 unit1 x2 u2 unit2 with
  | .ok (ma, mb) =>
    match mmCompare ma mb k S with
    | some b => .ok b
    | none => .refused undecided
  | .convention r => .convention r
  | .refused r => .refused r

/-- `lm_contradicts_units`: SR3's L-M test after normalization; the L value carries no
uncertainty. -/
def lmContradictsUnitsArg (xL unitL xM uM unitM : Arg) (k : Rat)
    (S : Strike.ScaleFactor := .one) : Outcome Bool :=
  match pairMeasurements xL (some "0") unitL xM uM unitM with
  | .ok (mL, mM) =>
    match lmCompare mL mM k S with
    | some b => .ok b
    | none => .refused undecided
  | .convention r => .convention r
  | .refused r => .refused r

/-- SR8's `S` after normalization: exact (`S²` rational, where the measurements share one
power of π), or twelve significant digits `m × 10^e` (across powers of π). -/
inductive ScaleAnswer where
  | exact (S : Strike.ScaleFactor)
  | digits (m : Nat) (e : Int)

/-- `S` to twelve significant digits. -/
def ScaleAnswer.digits12 : ScaleAnswer → Nat × Int
  | .exact S => S.digits 12
  | .digits m e => (m, e)

/-- SR8 over measurements carrying different powers of π: `Strike.PiScale.sr8ScaleSquarePi`,
and `S` to twelve digits from enclosures of π. A refusal is its reason. -/
def mixedAnswer (norm : List Measurement) : Except String ScaleAnswer :=
  match Strike.PiScale.sr8ScaleSquarePi (norm.map fun m => (m.x, m.u)) with
  | .error r => .error r
  | .ok none => .error (escape "every M record needs an uncertainty above zero")
  | .ok (some (.rat S)) => .ok (.exact S)
  | .ok (some (.pi r _)) =>
    match r.rootDigits 12 with
    | some (m, e) => .ok (.digits m e)
    | none => .error undecided

/-- `sr8_scale_factor_units`: SR8 over `{x, u, unit}` measurements of one DIMENSION and
KIND, after normalization. Every measurement is normalized first; a refusal outranks a
convention difference, which outranks a missing uncertainty (v1's order). -/
def sr8ScaleFactorUnitsArg (ms : List (Arg × Arg × Arg)) : Outcome ScaleAnswer :=
  let rec go : List (Arg × Arg × Arg) → Option (String × String) → Option String →
      List Measurement → Outcome (List Measurement)
    | [], _, conv, acc =>
      match conv with
      | some r => .convention r
      | none => .ok acc.reverse
    | (x, u, unit) :: rest, dk, conv, acc =>
      match normalizeMeasurementArg x u unit with
      | .error r => .refused r
      | .ok m =>
        match dk with
        | none => go rest (some (m.dimension, m.kind)) conv (m :: acc)
        | some (d, k) =>
          if m.dimension != d then .refused (dimensionRefusal d m.dimension)
          else
            let conv := if m.kind != k && conv.isNone then some (kindConvention k m.kind)
              else conv
            go rest dk conv (m :: acc)
  match go ms none none [] with
  | .refused r => .refused r
  | .convention r => .convention r
  | .ok norm =>
    if norm.any (fun m => m.u.coef ≤ 0) then
      .refused (escape "every M record needs an uncertainty above zero")
    else
      match norm with
      | [] => .ok (.exact .one)
      | m0 :: _ =>
        if norm.any (·.piPower != m0.piPower) then
          match mixedAnswer norm with
          | .ok a => .ok a
          | .error r => .refused r
        else
          match Strike.sr8ScaleFactor (norm.map fun m => ⟨m.x.coef, m.u.coef⟩) with
          | some S => .ok (.exact S)
          | none => .refused (escape "every M record needs an uncertainty above zero")

/-- `S` written exactly: `1`, or `sqrt(<S²>)`. -/
def renderScaleFactor (S : Strike.ScaleFactor) : String :=
  if S.square = 1 then "1" else "sqrt(" ++ Exact.renderRat S.square ++ ")"

/-- An answer written: exact as `renderScaleFactor`, digits as C's `%.12g`. -/
def renderScaleAnswer : ScaleAnswer → String
  | .exact S => renderScaleFactor S
  | .digits m e => Exact.printG false m e 12

end Principia.Units
