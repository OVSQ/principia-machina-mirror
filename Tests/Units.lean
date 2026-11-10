import Principia
import Lean.Data.Json

/-!
The units and dimensions family's vectors (`Principia/Dimension.lean`,
`Principia/Decimal.lean`, `Principia/Exact.lean`, `Principia/Units.lean`,
`Principia/UnitsStrike.lean`):

- `units_corpus.json`, v1's: all 91 cases, of `unit_parse`, `unit_scale`, `unit_matches`,
  `normalize_measurement` and the three wrappers of the strike rule. A case recorded in
  `units_corpus.divergences.json` is checked against the Calculator's recorded answer
  instead of v1's, and its cause is checked too.
- `zone_corpus.json`, v1's: the cases of `canon_dimension`, `normalize_dimension`,
  `is_canonical_dimension` and `canon_decimal`. The other functions' cases belong to the
  zones' runner, and are counted here as left to it.
- `units_helpers.json`, PMA's: `dimension_out_of_range`, `_dec_sign`, `_is_pos_finite`.
- `units_range.json`, PMA's: the double range at its bounds.
- `units_pi.json`, PMA's: the enclosure of π against 1400 reference digits, the sign of a
  polynomial at a power of π, and the wrappers across powers of π.
- `pi_scale.json`, PMA's: SR3's test with `S²` a ratio of polynomials in π
  (`Strike.PiScale.exceedsPi`), its own runner line.

v1's expectations are its results in canonical form: a string as itself, `true`, `false`
or `null`, a list as its items joined by commas in brackets, a double to twelve
significant digits. A number is compared exactly: v1's digits read as a decimal must equal
the Calculator's exact value.
-/

namespace Tests.Units

open Lean Principia Principia.Units

/-- A corpus's counts: passed, failed, passed against a recorded divergence (counted in
passed too), and left to another runner, by function. -/
structure Count where
  pass : Nat := 0
  fail : Nat := 0
  diverged : Nat := 0
  owed : List (String × Nat) := []

def Count.check (t : Count) (ok : Bool) (what : String) : IO Count := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL {what}"
    return { t with fail := t.fail + 1 }

def Count.owe (t : Count) (fn : String) : Count :=
  match t.owed.find? (·.1 == fn) with
  | some _ => { t with owed := t.owed.map fun p => if p.1 == fn then (p.1, p.2 + 1) else p }
  | none => { t with owed := t.owed ++ [(fn, 1)] }

def Count.line (t : Count) (name owner : String) : String :=
  let owed := (t.owed.map (·.2)).sum
  let base := s!"{name}: {t.pass} pass ({t.diverged} as recorded v2 divergences), {t.fail} fail"
  if owed == 0 then base
  else
    let fns := ", ".intercalate (t.owed.map fun p => s!"{p.1} {p.2}")
    base ++ s!"; {owed} left to {owner} ({fns})"

def loadJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

def casesOf (j : Json) : IO (Array Json) := IO.ofExcept (j.getObjValAs? (Array Json) "cases")

def jStr (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)

def input (c : Json) : IO Json := IO.ofExcept (c.getObjVal? "input")

/-- An input argument: a string, or `none` for any other JSON value. -/
def arg (c : Json) (k : String) : IO Arg := do
  match (← input c).getObjVal? k with
  | .ok (.str s) => return some s
  | .ok _ => return none
  | .error e => throw (IO.userError s!"{e} in {c.compress}")

/-! ## v1's printed numbers

v1 printed a double with C's `%.12g`. Where the exact value is not a short decimal, its
printed number is checked to be the exact value rounded to twelve significant digits.
π enters as bounds from Machin's formula, π = 16 atan(1/5) - 4 atan(1/239): the partial
sums of an alternating series with decreasing terms lie alternately above and below its
sum. -/

/-- The first `terms` terms of atan(1/x) = 1/x - 1/(3x^3) + 1/(5x^5) - ...: above the sum
for an odd count, below for an even one. -/
def atanPartial (x terms : Nat) : Rat :=
  (List.range terms).foldl (fun acc k =>
    let t : Rat := 1 / (((2 * k + 1) * x ^ (2 * k + 1) : Nat) : Rat)
    if k % 2 == 0 then acc + t else acc - t) 0

def piLo : Rat := 16 * atanPartial 5 20 - 4 * atanPartial 239 7
def piHi : Rat := 16 * atanPartial 5 21 - 4 * atanPartial 239 6

/-- Bounds on the value of `q × π^k`, `q > 0`. -/
def bounds (x : Exact) : Rat × Rat :=
  let n := x.pi.natAbs
  if 0 ≤ x.pi then (x.coef * piLo ^ n, x.coef * piHi ^ n)
  else (x.coef / piHi ^ n, x.coef / piLo ^ n)

/-- A positive rational rounded to twelve significant digits, ties to even. -/
def round12 (q : Rat) : Rat :=
  let e0 : Int := (toString q.num.natAbs).length - (toString q.den).length
  let e := if Decimal.pow10 e0 ≤ q then e0 else e0 - 1
  let s := q * Decimal.pow10 (11 - e)
  let f := s.floor
  let r := s - f
  let n : Int :=
    if r > 1 / 2 then f + 1 else if r < 1 / 2 then f else if f % 2 == 0 then f else f + 1
  (n : Rat) * Decimal.pow10 (e - 11)

/-- v1's printed number is the exact positive value rounded to twelve significant
digits. -/
def roundsTo (x : Exact) (printed : String) : Bool :=
  let (lo, hi) := bounds x
  match Decimal.value printed with
  | some p => decide (0 < x.coef) && round12 lo == round12 hi && round12 lo == p
  | none => false

/-- 2^1024 - 2^970 and 2^-1075, the double range's bounds, written here again so that the
check below does not lean on the library's. -/
def overflowAt : Rat := ((2 ^ 1024 - 2 ^ 970 : Nat) : Rat)
def underflowAt : Rat := 1 / ((2 ^ 1075 : Nat) : Rat)

/-- A number the functions return lies inside the double range as v1 bounded it: a scale
above 2^-1075 and below 2^1024 - 2^970; a normalized value or uncertainty below
2^1024 - 2^970 in absolute value. v1 refused neither a zero value nor one too small for a
double, which it made zero; the Calculator keeps that one exact. -/
def withinRange (x : Exact) (isValue : Bool) : Bool :=
  if x.coef == 0 then isValue
  else
    let (lo, hi) := bounds ⟨if x.coef < 0 then -x.coef else x.coef, x.pi⟩
    decide (hi < overflowAt) && (isValue || decide (underflowAt < lo))

/-! ## Comparing with v1 -/

/-- One item of a result: text, or an exact number. -/
inductive Item where
  | text (s : String)
  | num (x : Exact)

def Item.render : Item → String
  | .text s => s
  | .num x => x.render

/-- A result in v1's bracket form, numbers exact. -/
def render (r : Except String (List Item)) : String := bracket (·.map Item.render) r

/-- The items of v1's `["OK", ...]` expectation, or `none` for a refusal. -/
def okItems (expect : String) : Option (List String) :=
  if expect.startsWith "[OK," && expect.endsWith "]" then
    some (String.ofList ((expect.toList.drop 4).dropLast) |>.splitOn ",")
  else none

/-- A text item that could not be told apart from its neighbours in v1's text: it holds
a comma or a bracket. No item of these functions does; one that did fails its case rather
than risk matching v1's items split differently. -/
def separable (s : String) : Bool := !s.any fun c => c == ',' || c == '[' || c == ']'

/-- The result agrees with v1's expectation: a refusal word for word; an answer item by
item, text byte for byte, a number as the exact value of v1's digits. The kinds are the
function's (strings, a boolean, numbers), so v1's untyped text is read against them. -/
def agrees (expect : String) (r : Except String (List Item)) : Bool :=
  match r with
  | .error reason => expect == "[REFUSED," ++ reason ++ "]"
  | .ok items =>
    match okItems expect with
    | none => false
    | some parts =>
      parts.length == items.length && (parts.zip items).all fun (p, i) =>
        match i with
        | .text s => separable s && p == s
        | .num x => (Decimal.value p).any fun q => x == Exact.ofRat q

/-- v1's printed numbers are the exact numbers rounded to twelve significant digits. -/
def roundsAll (expect : String) (r : Except String (List Item)) : Bool :=
  match r, okItems expect with
  | .ok items, some parts =>
    parts.length == items.length && (parts.zip items).all fun (p, i) =>
      match i with
      | .text s => separable s && p == s
      | .num x => (Decimal.value p).any (fun q => x == Exact.ofRat q) || roundsTo x p
  | _, _ => false

/-- The numbers a result returns, each with whether it is a normalized value or
uncertainty rather than a scale. -/
def returned (fn : String) (r : Except String (List Item)) : List (Exact × Bool) :=
  match r with
  | .error _ => []
  | .ok items =>
    items.filterMap fun i => match i with
      | .num x => some (x, fn == "normalize_measurement")
      | .text _ => none

/-! ## units_corpus.json -/

/-- The Calculator's answer to a case, or `none` for a function not yet ported. -/
def answer (fn : String) (c : Json) : IO (Option (Except String (List Item))) := do
  match fn with
  | "unit_parse" =>
    return some ((unitParseArg (← arg c "u")).map fun p => p.items.map .text)
  | "unit_scale" =>
    return some ((unitScaleArg (← arg c "u")).map fun x => [.num x])
  | "unit_matches" =>
    return some ((unitMatchesArg (← arg c "u") (← arg c "dimension")).map fun b =>
      [.text (toString b)])
  | "normalize_measurement" =>
    return some ((normalizeMeasurementArg (← arg c "value") (← arg c "uncertainty")
      (← arg c "u")).map fun m => [.num m.x, .num m.u, .text m.dimension, .text m.kind])
  | _ => return none

/-- A JSON number as the exact rational its decimal text writes (v1's `k` is a number). -/
def ratNum (j : Json) : IO Rat := do
  let n ← IO.ofExcept j.getNum?
  return (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

/-- The three functions that go on to the strike rule (`Principia/UnitsStrike.lean`): the
Calculator's answer in v1's bracket form, and whether it agrees with v1's expectation. A
boolean, a CONVENTION or a refusal is compared as text (the kinds are fixed: OK with a
boolean, or a reason); SR8's `S` by value, v1's twelve significant digits against the exact
root correctly rounded (`ScaleFactor.digits 12`), as the strike rule's runner compares it. -/
def strikeOutcome (fn : String) (c : Json) :
    IO (Option (String × Option (Nat × Int))) := do
  let i ← input c
  let num (k : String) : IO Rat := do ratNum (← IO.ofExcept (i.getObjVal? k))
  match fn with
  | "mm_contradicts_units" =>
    let r := mmContradictsUnitsArg (← arg c "x1") (← arg c "u1") (← arg c "unit1")
      (← arg c "x2") (← arg c "u2") (← arg c "unit2") (← num "k")
    return some (r.bracket fun b => [toString b], none)
  | "lm_contradicts_units" =>
    let r := lmContradictsUnitsArg (← arg c "x_l") (← arg c "unit_l") (← arg c "x_m")
      (← arg c "u_m") (← arg c "unit_m") (← num "k")
    return some (r.bracket fun b => [toString b], none)
  | "sr8_scale_factor_units" =>
    let ms ← (← IO.ofExcept ((← IO.ofExcept (i.getObjVal? "measurements")).getArr?)).toList.mapM
      fun m => do
        let field (k : String) : IO Arg := do
          match m.getObjVal? k with
          | .ok (.str s) => return some s
          | .ok _ => return none
          | .error e => throw (IO.userError e)
        return (← field "x", ← field "u", ← field "unit")
    let r := sr8ScaleFactorUnitsArg ms
    let S := match r with
      | .ok S => some S.digits12
      | _ => none
    return some (r.bracket fun S => [renderScaleAnswer S], S)
  | _ => return none

def strikeAnswer (fn : String) (c : Json) (expect : String) : IO (Option (Bool × String)) := do
  match ← strikeOutcome fn c with
  | none => return none
  | some (got, none) => return some (got == expect, got)
  | some (got, some (m, e)) =>
    match okItems expect with
    | some [p] =>
      return some ((Decimal.value p).any (· == (m : Rat) * Decimal.pow10 e), got)
    | _ => return some (false, got)

def runUnitsCorpus : IO (Count × List (String × Exact × Bool)) := do
  let divs ← IO.ofExcept ((← loadJson "vectors/units_corpus.divergences.json").getObjValAs?
    (Array Json) "divergences")
  let mut seen : List String := []
  let mut values : List (String × Exact × Bool) := []
  let mut t : Count := {}
  for c in ← casesOf (← loadJson "vectors/units_corpus.json") do
    let id ← jStr c "id"
    let fn ← jStr c "fn"
    let expect ← jStr c "expect"
    match ← answer fn c with
    | none =>
      match ← strikeAnswer fn c expect with
      | some (ok, got) => t ← t.check ok s!"{id}: expected {expect}, got {got}"
      | none => t ← t.check false s!"{id}: unknown function {fn}"
    | some r =>
      values := values ++ (returned fn r).map fun v => (id, v)
      match divs.find? fun d => (d.getObjValAs? String "id").toOption == some id with
      | none => t ← t.check (agrees expect r) s!"{id}: expected {expect}, got {render r}"
      | some d =>
        seen := id :: seen
        let v1 ← jStr d "v1"
        let v2 ← jStr d "v2"
        let cause ← jStr d "cause"
        let causeOk := match cause with
          | "rounding" => roundsAll expect r
          | "partial product" => expect.startsWith "[REFUSED,"
          | _ => false
        let ok := v1 == expect && v2 == render r && causeOk
        t ← t.check ok s!"{id} (recorded divergence, {cause}): v1 {expect}, recorded {v1}; recorded v2 {v2}, got {render r}"
        if ok then t := { t with diverged := t.diverged + 1 }
  -- A divergence recorded for a case the corpus does not have is a stale record.
  for d in divs do
    let id ← jStr d "id"
    unless seen.contains id do
      t ← t.check false s!"{id}: a recorded divergence with no case"
  return (t, values)

/-! ## units_range.json: the double range at its bounds -/

/-- An unevaluated product from its JSON form: bases as decimal strings. -/
def readFactors (j : Json) : IO (List (Nat × Nat)) := do
  let arr ← IO.ofExcept (j.getArr?)
  arr.toList.mapM fun f => do
    let pair ← IO.ofExcept f.getArr?
    match pair.toList with
    | [b, e] =>
      let some base := (← IO.ofExcept b.getStr?).toNat? | throw (IO.userError s!"base {b}")
      return (base, ← IO.ofExcept e.getNat?)
    | _ => throw (IO.userError s!"not a factor: {f.compress}")

def rangeWord : Exact.Range → String
  | .zero => "zero"
  | .inside => "inside"
  | .infinite => "infinite"

def runRangeCorpus : IO (Count × List (String × Exact × Bool)) := do
  let mut values : List (String × Exact × Bool) := []
  let mut t : Count := {}
  for c in ← casesOf (← loadJson "vectors/units_range.json") do
    let id ← jStr c "id"
    let fn ← jStr c "fn"
    let expect ← jStr c "expect"
    if fn == "range" then
      let i ← input c
      let prod : Exact.Product :=
        { num := ← readFactors (← IO.ofExcept (i.getObjVal? "num")),
          den := ← readFactors (← IO.ofExcept (i.getObjVal? "den")),
          pi := ← IO.ofExcept (i.getObjValAs? Int "pi") }
      let got := rangeWord prod.range
      t ← t.check (got == expect) s!"{id}: expected {expect}, got {got}"
    else
      match ← answer fn c with
      | none => t ← t.check false s!"{id}: unknown function {fn}"
      | some r =>
        values := values ++ (returned fn r).map fun v => (id, v)
        t ← t.check (render r == expect) s!"{id}: expected {expect}, got {render r}"
  return (t, values)

/-! ## zone_corpus.json: the dimension and decimal cases -/

/-- v1's rendering of an optional string: `null` for none. -/
def orNull : Option String → String
  | some s => s
  | none => "null"

def runZoneCorpus : IO Count := do
  let mut t : Count := {}
  for c in ← casesOf (← loadJson "vectors/zone_corpus.json") do
    let id ← jStr c "id"
    let fn ← jStr c "fn"
    let expect ← jStr c "expect"
    let got? : Option String ← match fn with
      | "normalize_dimension" => pure (some (orNull (Dimension.normalize (← jStr (← input c) "s"))))
      | "is_canonical_dimension" =>
        pure (some (toString (Dimension.isCanonical (← jStr (← input c) "s"))))
      | "canon_decimal" => pure (some (orNull (Decimal.canon (← jStr (← input c) "s"))))
      | "canon_dimension" =>
        let exps ← IO.ofExcept ((← input c).getObjVal? "exps")
        let e : Dimension.Exponents := fun b =>
          match exps.getObjValAs? Int (String.ofList b.spell) with
          | .ok n => n
          | .error _ => 0
        pure (some (Dimension.canon e))
      | _ => pure none
    match got? with
    | some got => t ← t.check (got == expect) s!"{id}: expected {expect}, got {got}"
    | none => t := t.owe fn
  return t

/-! ## units_helpers.json -/

def runHelpers : IO Count := do
  let mut t : Count := {}
  for c in ← casesOf (← loadJson "vectors/units_helpers.json") do
    let id ← jStr c "id"
    let s ← jStr (← input c) "s"
    let expect ← IO.ofExcept (c.getObjVal? "expect")
    let got : Json ← match ← jStr c "fn" with
      | "dimension_out_of_range" => pure (toJson (Dimension.outOfRange s))
      | "dec_sign" => pure (toJson (Decimal.sign s))
      | "is_pos_finite" => pure (toJson (Decimal.isPosFinite s))
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    t ← t.check (got == expect) s!"{id}: expected {expect.compress}, got {got.compress}"
  return t

/-! ## units_pi.json: π's enclosure against reference digits -/

/-- A coefficient: a decimal, or a fraction `a/b`. -/
def readRat (t : String) : IO Rat := do
  match t.splitOn "/" with
  | [a, b] =>
    let some n := (Decimal.value a) | throw (IO.userError s!"not a number: {t}")
    let some d := (Decimal.value b) | throw (IO.userError s!"not a number: {t}")
    return n / d
  | _ =>
    let some q := Decimal.value t | throw (IO.userError s!"not a number: {t}")
    return q

def signWord : Option Ordering → String
  | some .gt => "gt"
  | some .lt => "lt"
  | some .eq => "eq"
  | none => "undecided"

def runPiCorpus : IO Count := do
  let doc ← loadJson "vectors/units_pi.json"
  let reference ← IO.ofExcept ((← IO.ofExcept (doc.getObjVal? "meta")).getObjVal? "reference")
  let some d := Decimal.value (← jStr reference "digits")
    | throw (IO.userError "units_pi: the reference does not read")
  let decimals ← IO.ofExcept (reference.getObjValAs? Nat "decimals")
  -- π lies in [d, d + eps)
  let eps : Rat := 1 / ((10 ^ decimals : Nat) : Rat)
  let mut t : Count := {}
  for c in ← casesOf doc do
    let id ← jStr c "id"
    let fn ← jStr c "fn"
    let expect ← jStr c "expect"
    let i ← input c
    match fn with
    | "pi_interval" =>
      let p ← IO.ofExcept (i.getObjValAs? Nat "p")
      let iv := Exact.piInterval p
      let lo := (iv.lo : Rat) * Exact.pow2 iv.exp
      let hi := (iv.hi : Rat) * Exact.pow2 iv.exp
      let ok := decide (lo ≤ d) && decide (d + eps ≤ hi) && decide (iv.hi ≤ iv.lo + 4)
      t ← t.check (ok == (expect == "brackets")) s!"{id}: piInterval {p} does not hold pi tightly"
    | "pi_pow" =>
      let m ← IO.ofExcept (i.getObjValAs? Int "m")
      let p ← IO.ofExcept (i.getObjValAs? Nat "p")
      let (lo, hi) := Exact.piPowBounds m p
      let k := m.natAbs
      let (rlo, rhi) := if 0 ≤ m then (d ^ k, (d + eps) ^ k)
        else (1 / (d + eps) ^ k, 1 / d ^ k)
      let ok := decide (lo ≤ rlo) && decide (rhi ≤ hi)
      t ← t.check (ok == (expect == "brackets")) s!"{id}: piPowBounds {m} {p} does not hold pi^{m}"
    | "runner_pi" =>
      let ok := decide (piLo ≤ d) && decide (d + eps ≤ piHi)
      t ← t.check (ok == (expect == "brackets")) s!"{id}: the runner's pi bounds do not hold pi"
    | "poly_sign" =>
      let cs ← (← IO.ofExcept (i.getObjValAs? (Array String) "coefs")).toList.mapM readRat
      let m ← IO.ofExcept (i.getObjValAs? Int "m")
      let got := signWord (Exact.polySignAtPiPow cs m)
      t ← t.check (got == expect) s!"{id}: expected {expect}, got {got}"
    | _ =>
      match ← strikeOutcome fn c with
      | some (got, _) => t ← t.check (got == expect) s!"{id}: expected {expect}, got {got}"
      | none => t ← t.check false s!"{id}: unknown function {fn}"
  return t

/-! ## pi_scale.json: SR3's test with `S²` a ratio of polynomials in π -/

/-- A polynomial in π from `{"shift", "coefs"}`. -/
def readPoly (j : Json) : IO Strike.PiScale.PiPoly := do
  let shift ← IO.ofExcept (j.getObjValAs? Int "shift")
  let cs ← (← IO.ofExcept (j.getObjValAs? (Array String) "coefs")).toList.mapM readRat
  return ⟨shift, cs⟩

/-- An ordering from its word. -/
def readOrdering : String → IO Ordering
  | "gt" => pure .gt
  | "lt" => pure .lt
  | "eq" => pure .eq
  | w => throw (IO.userError s!"not an ordering: {w}")

/-- `Strike.PiScale.exceedsPi` over `vectors/pi_scale.json`: `true`, `false`,
`undecided` or `too large`. -/
def runPiScale : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in ← casesOf (← loadJson "vectors/pi_scale.json") do
    let id ← jStr c "id"
    let expect ← jStr c "expect"
    let i ← input c
    let dd ← readPoly (← IO.ofExcept (i.getObjVal? "dd"))
    let ccv ← readPoly (← IO.ofExcept (i.getObjVal? "ccv"))
    let cSign ← readOrdering (← jStr i "c_sign")
    let vPos ← IO.ofExcept (i.getObjValAs? Bool "v_pos")
    let s2 : Strike.PiScale.PiRatio :=
      ⟨← readPoly (← IO.ofExcept (i.getObjVal? "s2_num")),
       ← readPoly (← IO.ofExcept (i.getObjVal? "s2_den"))⟩
    let got := match Strike.PiScale.exceedsPi dd ccv cSign vPos s2 with
      | .ok (some b) => toString b
      | .ok none => "undecided"
      | .error _ => "too large"
    if got == expect then pass := pass + 1
    else
      fail := fail + 1
      IO.eprintln s!"FAIL {id}: expected {expect}, got {got}"
  return (pass, fail)

/-- The family's run: one line per corpus, then one for the returned numbers' range;
passed and failed checks in all. -/
def run : IO (Nat × Nat) := do
  let (units, unitValues) ← runUnitsCorpus
  let (range, rangeValues) ← runRangeCorpus
  let mut inRange : Count := {}
  for (id, x, isValue) in unitValues ++ rangeValues do
    inRange ← inRange.check (withinRange x isValue)
      s!"{id}: returned {x.render}, outside the double range"
  let mut pass := 0
  let mut fail := 0
  for (name, owner, t) in [
      ("units_corpus", "", units),
      ("zone_corpus (dimensions, decimals)", "the zones' runner", ← runZoneCorpus),
      ("units_helpers", "", ← runHelpers),
      ("units_range", "", range),
      ("units_pi", "", ← runPiCorpus),
      ("returned numbers within the double range", "", inRange)] do
    IO.println (t.line name owner)
    pass := pass + t.pass
    fail := fail + t.fail
    if t.pass + t.fail == 0 then
      IO.eprintln s!"FAIL {name}: the corpus checked nothing"
      fail := fail + 1
  return (pass, fail)

end Tests.Units
