import Principia.Units
import Principia.Form.Checks
import Principia.Form.Arithmetic
import Principia.Units.Bounded

/-!
# Declared forms: evaluation, the ground fragment (S7, S11)

v1's `eval_form` and `t3_laws` (`tpc_form` 0.2.1): a form whose identifiers are bound,
each to a VALUE in a UNIT normalized to coherent SI, evaluated in v1's order; the KIND of
each side carried as exponents over rad, Hz, Bq, Gy and Sv; a KIND difference between the
sides of a sum or an equation is a CONVENTION; D of a bound identifier is 0 with that
identifier's KIND, its variable need not be bound.

v1 evaluated in IEEE doubles. The Calculator evaluates on exact numbers where they have an
exact form here and on outward-rounded enclosures elsewhere (`Principia.Form.Arithmetic`,
`Principia.Form.Interval`; exact values are the default), in v1's order: every refusal v1
makes is made on the number, not on a double, and a result infinite as a double is refused
as v1 refused it. A check whose answer no bounds up to 4096 bits settle (a value exactly
zero but not known so, a twelfth digit on a rounding boundary) is owed, unless a
refusal, an unbound name or a KIND difference comes first in v1's order.

Every decision on a value spends precision steps (`Principia.Form.climb`), summed across the
request: a form's walk and its finish under `eval_form`, every LAW's under `t3_laws`. Given a
budget, a request whose decisions would pass it stops `budget` before the precision that
would pass it is tried; within it, every answer is the one the ladder gives
(`climb_findSome`).

Known differences from v1, which no case of its corpus reaches: a value too small for a
double is kept, where v1 made it zero (and then refused a division by it, or gave 0); a
partial result infinite as a double is carried on, where v1 carried an infinity (its
reciprocal 0, its difference with itself not a number); sin, cos and tan of an exact
multiple of π are exact (cos(π/2) is 0, recorded beside the corpus); tan at an odd multiple
of π/2 has no value and is owed.
-/

namespace Principia.Form

open Principia.Zone (Value Entry getStr? nameOf escape)

/-! ## KIND -/

/-- A KIND's exponents over rad, Hz, Bq, Gy, Sv. -/
abbrev Kinds := List Int

/-- No KIND. -/
def Kinds.none : Kinds := [0, 0, 0, 0, 0]

/-- An optionally signed run of ASCII digits. -/
def readSigned (cs : List Char) : Option Int :=
  match cs with
  | '-' :: ds => if ds ≠ [] ∧ ds.all isDigit then some (-(Canonical.digitsValue ds : Int)) else none
  | ds => if ds ≠ [] ∧ ds.all isDigit then some (Canonical.digitsValue ds : Int) else none

/-- A KIND's exponents, as `Principia.Units` writes a KIND (`rad2 Hz-1`, `none`); v1's
`_kexps`. -/
def kindsOf (kind : String) : Kinds :=
  if kind == "none" then Kinds.none
  else (kind.splitOn " ").foldl (fun acc tok =>
    let cs := tok.toList
    match (Units.kindBases.zip (List.range 5)).find? fun (b, _) =>
        b.toList.isPrefixOf cs && (readSigned (cs.drop b.length)).isSome with
    | some (b, i) => acc.set i ((readSigned (cs.drop b.length)).getD 0)
    | none => acc) Kinds.none

/-- A KIND's text: `rad2 Hz-1`, or `none` (v1's `_kstr`). -/
def kindText (k : Kinds) : String :=
  let toks := ((Units.kindBases.zip k).filter (·.2 ≠ 0)).map fun (b, e) => b ++ toString e
  if toks.isEmpty then "none" else " ".intercalate toks

/-! ## Bindings -/

/-- A bound identifier: its value in coherent SI and its KIND. -/
structure Bound where
  value : Exact
  kind : Kinds

/-- The bound identifiers. -/
abbrev Bindings := List (String × Bound)

/-- A binding as given: its VALUE and UNIT arguments (`none` for a value that is not a
string), or `none` for an entry that is not an object, which binds nothing. -/
abbrev BindingArg := Option (Units.Arg × Units.Arg)

/-- Names sorted in code point order. -/
def sortPairs {α : Type} (xs : List (String × α)) : List (String × α) :=
  let rec ins (x : String × α) : List (String × α) → List (String × α)
    | [] => [x]
    | y :: ys => if x.1 < y.1 then x :: y :: ys else y :: ins x ys
  xs.foldl (fun acc x => ins x acc) []

/-- The bindings normalized to coherent SI, in name order, the first refusal ending them
(v1's `_bindings`). A refusal is the unit grammar's, escaped as v1's `_show` escapes it, or
the bound on an exact value's ("exact value too large"): each binding is normalized
within it (`Units.Bounded.normalizeMeasurementArg`), and its value, numerator and denominator
together, holds at most `maxBits` bits, the measure the evaluator's arithmetic keeps. -/
def readBindings (bs : List (String × BindingArg)) : Answer Bindings :=
  (sortPairs bs).foldl (fun acc (name, arg) =>
    acc.bind fun out =>
      match arg with
      | none => .ok out
      | some (v, u) =>
        match Units.Bounded.normalizeMeasurementArg v (some "0") u with
        | .ok (.ok m) =>
          if sizeOf m.x ≤ maxBits then .ok (out ++ [(name, ⟨m.x, kindsOf m.kind⟩)])
          else .refused ValueBound.tooLarge
        | .ok (.error r) => .refused r
        | .error _ => .refused ValueBound.tooLarge) (.ok [])

/-! ## The walk -/

/-- Why an evaluation stops: v1's three exceptions, owed, and the request's precision-step
budget spent (`budgetExceeded`). -/
inductive Stop where
  | unbound (name : String)
  | convention (reason : String)
  | refused (reason : String)
  | owed (why : Owed)
  | budget

/-- A decision under the budget (`Num.signIn`, `Num.beyondIn`, `Num.twelveIn`): its answer
and the steps spent, or the budget's stop. -/
def spend {α : Type} (s : Nat) : Option (α × Nat) → Except (Stop × Nat) (α × Nat)
  | some r => .ok r
  | none => .error (.budget, s)

/-- A stop, with the steps spent before it. -/
def stopAt {α : Type} (s : Nat) (x : Stop) : Except (Stop × Nat) α := .error (x, s)

/-- A step that spends no precision steps, its stop carrying `s`. -/
def stepped {α : Type} (s : Nat) (r : Except Stop α) : Except (Stop × Nat) α :=
  r.mapError (·, s)

/-- v1's reasons for a refused evaluation. -/
def reasonDiv0 : String := "division by zero"
def reasonFin : String := "not a finite double"
def reasonLn : String := "ln of a non-positive value"
def reasonSqrt : String := "sqrt of a negative value"
def reasonRat : String := "a negative base under a rational exponent"
def reasonNeg0 : String := "0 under a negative exponent"

/-- S14 on a KIND. -/
def kindRange (k : Kinds) : Except Stop Kinds :=
  match inRange true k with
  | .ok k => .ok k
  | .error r => .error (.refused r)

/-- A check on a value the Calculator has no exact form of: owed. -/
def unknownValue (v : Num) : Stop := .owed (.exact v.what)

/-- The most a literal's exponent may hold: `10^19728` holds 65,536 bits, the bound
(`maxBits`); past it a literal is refused before its value is formed. -/
def maxLiteralExponent : Nat := 19728

/-- A canonical decimal's exact value (`5e-1`, `15e2`) before the bound: its digits, then
its exponent within `maxLiteralExponent`. -/
def literalRaw (c : String) : Option Rat :=
  match c.splitOn "e" with
  | [m] => if m.toList.all isDigit then some (Canonical.digitsValue m.toList : Rat) else none
  | [m, e] =>
    match readSigned e.toList with
    | some x =>
      if m.toList.all isDigit ∧ x.natAbs ≤ maxLiteralExponent then
        some ((Canonical.digitsValue m.toList : Rat) * (10 : Rat) ^ x)
      else none
    | none => none
  | _ => none

/-- A canonical decimal's exact value within the bound on an exact value: `none` when
its exponent passes `maxLiteralExponent` or its value's numerator and denominator together
pass `maxBits` bits (the grammar bounds its digits by the text's 4096 code points). -/
def literalValue (c : String) : Option Rat :=
  match literalRaw c with
  | some q => if sizeOf (Exact.ofRat q) ≤ maxBits then some q else none
  | none => none

/-- An expression's value and KIND, in v1's order (v1's `_ev_g`), under the request's
precision-step budget `budget` (`none`, no budget) with `s` steps spent before it: the value,
its KIND and the steps spent after it. Each decision on a value (its sign, the double range)
spends its steps (`Num.signIn`, `Num.beyondIn`); past the budget the walk stops `budget`. A stop carries the steps
spent before it, for a check that goes on past it (`t3Laws`). -/
def Expr.eval (budget : Option Nat) (b : Bindings) : Expr → Nat → Except (Stop × Nat) (Num × Kinds × Nat)
  | .num c, s =>
    match literalValue c with
    | some q => .ok (Num.ofRat q, Kinds.none, s)
    | none => stopAt s (.refused ValueBound.tooLarge)
  | .ident n, s =>
    match b.lookup n with
    | none => stopAt s (.unbound n)
    | some bd => do return (.exact bd.value, ← stepped s (kindRange bd.kind), s)
  | .paren e, s => e.eval budget b s
  | .neg e, s => do
    let (v, k, s) ← e.eval budget b s
    return (v.neg, k, s)
  | .bin op l r, s => do
    let (va, ka, s) ← l.eval budget b s
    let (vb, kb, s) ← r.eval budget b s
    match op with
    | .add | .sub =>
      if ka ≠ kb then
        stopAt s (.convention s!"units of different kind: {kindText ka} and {kindText kb}")
      return (if op == .add then va.add vb else va.sub vb, ka, s)
    | .mul => return (va.mul vb, ← stepped s (kindRange (List.zipWith (· + ·) ka kb)), s)
    | .div =>
      let (sg, s) ← spend s (vb.signIn budget s)
      match sg.map (· == 0) with
      | some true => stopAt s (.refused reasonDiv0)
      | none => stopAt s (unknownValue vb)
      | some false => return (va.div vb, ← stepped s (kindRange (List.zipWith (· - ·) ka kb)), s)
  | .pow base p q, s => do
    let (va, ka, s) ← base.eval budget b s
    if ka.any fun x => (x * p) % (q : Int) ≠ 0 then
      stopAt s (.refused s!"^ ({p}/{q}) of kind {kindText ka} is not a kind")
    let kk ← stepped s (kindRange (ka.map fun x => x * p / (q : Int)))
    if q = 1 then
      let r := va.powNat p.natAbs
      if p < 0 then
        let (sg, s) ← spend s (va.signIn budget s)
        match sg.map (· == 0) with
        | some true => stopAt s (.refused reasonNeg0)
        | none => stopAt s (unknownValue va)
        | some false => return (r.inv, kk, s)
      else return (r, kk, s)
    else
      let (sg, s) ← spend s (va.signIn budget s)
      match sg.map (fun x => decide (x < 0)), sg.map (· == 0) with
      | some true, _ => stopAt s (.refused reasonRat)
      | some false, some true =>
        if p < 0 then stopAt s (.refused reasonNeg0) else return (va.powRat p q, kk, s)
      | some false, some false => return (va.powRat p q, kk, s)
      | _, _ => stopAt s (unknownValue va)
  | .fn f a, s => do
    let (va, ka, s) ← a.eval budget b s
    match f with
    | .abs => return (va.abs, ka, s)
    | .sqrt =>
      let (sg, s) ← spend s (va.signIn budget s)
      match sg.map (fun x => decide (x < 0)) with
      | some true => stopAt s (.refused reasonSqrt)
      | none => stopAt s (unknownValue va)
      | some false =>
        if ka.any fun x => x % 2 ≠ 0 then
          stopAt s (.refused s!"sqrt of kind {kindText ka} is not a kind")
        return (va.sqrt, ka.map (· / 2), s)
    | .ln =>
      let (sg, s) ← spend s (va.signIn budget s)
      match sg.map (fun x => decide (x < 0)), sg.map (· == 0) with
      | some true, _ | _, some true => stopAt s (.refused reasonLn)
      | some false, some false => return (va.ln, Kinds.none, s)
      | _, _ => stopAt s (unknownValue va)
    | .exp => return (va.exp, Kinds.none, s)
    | .sin | .cos | .tan =>
      let (bd, s) ← spend s (va.beyondIn budget s)
      match bd with
      | some true => stopAt s (.refused reasonFin)
      | none => stopAt s (unknownValue va)
      | some false =>
        return ((match f with | .sin => va.sin | .cos => va.cos | _ => va.tan), Kinds.none, s)
  | .deriv x _ _, s =>
    match b.lookup x with
    | none => stopAt s (.unbound x)
    | some bd => do return (Num.zero, ← stepped s (kindRange bd.kind), s)

/-- A value as an answer gives it: its twelve-digit form, and the exact number when it has
one. -/
structure Reading where
  text : String
  exact : Option Exact
  deriving Repr

/-- A value's range: refused when infinite as a double, owed when not settled; the steps
spent after it. -/
def checkRange (budget : Option Nat) (v : Num) (s : Nat) : Except (Stop × Nat) Nat := do
  let (r, s) ← spend s (v.beyondIn budget s)
  match r with
  | some true => stopAt s (.refused reasonFin)
  | some false => return s
  | none => stopAt s (.owed (.exact v.what))

/-- A value read in twelve digits; owed when they are not settled. -/
def reading (budget : Option Nat) (v : Num) (s : Nat) : Except (Stop × Nat) (Reading × Nat) := do
  let (t, s) ← spend s (v.twelveIn budget s)
  match t with
  | some t => return (⟨t, match v with | .exact x => some x | _ => none⟩, s)
  | none => stopAt s (.owed (.exact ("the twelve digits of " ++ v.what)))

/-- A finished value: its range, then its digits. -/
def finished (budget : Option Nat) (v : Num) (s : Nat) : Except (Stop × Nat) (Reading × Nat) := do
  let s ← checkRange budget v s
  reading budget v s

/-- The ranges of an equation's two sides, in v1's order: refused when either is infinite as
a double, then owed when the first, then the second, is not settled. Each range is decided
once. -/
def sideRanges (budget : Option Nat) (va vb : Num) (s : Nat) : Except (Stop × Nat) Nat := do
  let (ra, s) ← spend s (va.beyondIn budget s)
  if ra == some true then stopAt s (.refused reasonFin)
  let (rb, s) ← spend s (vb.beyondIn budget s)
  if rb == some true then stopAt s (.refused reasonFin)
  if ra.isNone then stopAt s (.owed (.exact va.what))
  if rb.isNone then stopAt s (.owed (.exact vb.what))
  return s

/-- The two sides of an equation, finished, in v1's order: refused when either is
infinite as a double; then their KINDs must agree; then each is read. -/
def finishedSides (budget : Option Nat) (va vb : Num) (ka kb : Kinds) (s : Nat) :
    Except (Stop × Nat) (Reading × Reading × Nat) := do
  let s ← sideRanges budget va vb s
  if ka ≠ kb then
    stopAt s (.convention s!"units of different kind: {kindText ka} and {kindText kb}")
  let (x, s) ← reading budget va s
  let (y, s) ← reading budget vb s
  return (x, y, s)

/-! ## eval_form -/

/-- `eval_form`'s answer: one value with its KIND, an equation's two sides with theirs, an
identifier not bound, or a KIND difference (v1's `OK`, `UNBOUND` and `CONVENTION`). -/
inductive Evaluation where
  | value (x : Reading) (kind : String)
  | sides (l r : Reading) (kind : String)
  | unbound (name : String)
  | convention (reason : String)
  deriving Repr

/-- The answer's text as v1's `canon` writes it, numbers in the twelve-digit form. -/
def Evaluation.text : Evaluation → String
  | .value x k => "[OK," ++ x.text ++ "," ++ k ++ "]"
  | .sides l r k => "[OK," ++ l.text ++ "," ++ r.text ++ "," ++ k ++ "]"
  | .unbound n => "[UNBOUND," ++ n ++ "]"
  | .convention r => "[CONVENTION," ++ r ++ "]"

/-- A stop as an answer. -/
def Stop.answer : Stop → Answer Evaluation
  | .unbound n => .ok (.unbound n)
  | .convention r => .ok (.convention (escape r))
  | .refused r => refuse r
  | .owed w => .owed w
  | .budget => .refused budgetExceeded

/-- A form's evaluation under bound identifiers, within the precision-step budget. -/
def Tree.evaluate (budget : Option Nat) (b : Bindings) : Tree → Answer Evaluation
  | .eq l r =>
    match (do
        let (va, ka, s) ← l.eval budget b 0
        let (vb, kb, s) ← r.eval budget b s
        let (x, y, _) ← finishedSides budget va vb ka kb s
        return Evaluation.sides x y (kindText ka) : Except (Stop × Nat) Evaluation) with
    | .ok e => .ok e
    | .error (x, _) => x.answer
  | .expr e =>
    match (do
        let (v, k, s) ← e.eval budget b 0
        let (x, _) ← finished budget v s
        return Evaluation.value x (kindText k) : Except (Stop × Nat) Evaluation) with
    | .ok e => .ok e
    | .error (x, _) => x.answer
  | .pred _ => refuse "a predicate is not evaluated"

/-- `eval_form`, the ground fragment's evaluator: bindings `{name: {VALUE, UNIT}}`, each
normalized to coherent SI. Owed when a value's range or twelve digits cannot be settled;
refused `budgetExceeded` when its decisions pass `budget` precision steps. -/
def evalForm (budget : Option Nat) (text : String) (mode : Mode)
    (bindings : List (String × BindingArg)) : Answer Evaluation :=
  (parse text mode).bind fun tree =>
    if mode == .predicate then refuse "a predicate is not evaluated"
    else (readBindings bindings).bind fun b =>
      match tree.evaluate budget b with
      | .ok e => .ok e
      | a => a.escaped

/-! ## T3 over the laws -/

/-- The first FIX of each DOF by CONSTRAINT name, with VALUE and UNIT strings (v1's
`_fix_bindings`): the constraint's name and its VALUE and UNIT. -/
def fixBindings (tpk : Value) : List (String × String × String × String) :=
  (sortByName (entriesOf tpk "CONSTRAINT")).foldl (fun acc c =>
    match getStr? c "TARGET", getStr? c "ACTION", getStr? c "VALUE", getStr? c "UNIT" with
    | some t, some "FIX", some v, some u =>
      if acc.any (·.1 == t) then acc else acc ++ [(t, nameOf c, v, u)]
    | _, _, _, _ => acc) []

/-- `t3_laws`, fundamental test T3 over the laws, the ground fragment at depth 1: (i) a
LAW whose every identifier is bound, to a CONSTANT with VALUE and UNIT or to a DOF under a
FIX, evaluates in coherent SI, and a closed equation false through canon's twelve digits
is P and not-P; (ii) two LAWs with one canonical left side and different canonical right
sides are P and not-P. Nothing beyond depth 1 is claimed. The problems, sorted; owed when
an evaluation is; stopped `budget` when the decisions of all the LAWs together pass `budget`
precision steps, the steps of a LAW whose evaluation stops counted too. -/
def t3LawsIn (budget : Option Nat) (tpk : Value) : Except Stop (List String) := do
  let consts : List (String × String × String) := (entriesOf tpk "CONSTANT").foldl (fun acc e =>
    match getStr? e "NAME", getStr? e "VALUE", getStr? e "UNIT" with
    | some n, some v, some u => if acc.any (·.1 == n) then acc else acc ++ [(n, v, u)]
    | _, _, _ => acc) []
  let fixes := fixBindings tpk
  let mut lefts : List (String × List (String × String)) := []
  let mut probs : List String := []
  let mut steps : Nat := 0
  for e in sortByName (entriesOf tpk "LAW") do
    let some f := getStr? e "EQUATION" | continue
    let name := nameOf e
    let tag := "LAW:" ++ name
    let .ok tree ← (parseIn f .equation).mapError Stop.owed | continue
    let .eq l r := tree | continue
    let left := l.bare
    lefts := match lefts.lookup left with
      | some _ => lefts.map fun (k, v) => if k == left then (k, v ++ [(name, r.bare)]) else (k, v)
      | none => lefts ++ [(left, [(name, r.bare)])]
    let mut bs : List (String × BindingArg) := []
    let mut used : List String := []
    for n in sortedSet tree.names do
      match consts.find? (·.1 == n) with
      | some (_, v, u) => bs := bs ++ [(n, some (some v, some u))]
      | none =>
        match fixes.find? (·.1 == n) with
        | some (_, c, v, u) =>
          bs := bs ++ [(n, some (some v, some u))]
          used := used ++ [c]
        | none => pure ()
    let who := tag ++ String.join ((sortedSet used).map (" and CONSTRAINT:" ++ ·))
    let basis := if used.isEmpty then "under the declared values" else "under the fixed values"
    match readBindings bs with
    | .owed w => throw (.owed w)
    | .refused x =>
      probs := probs ++ [tag ++ ": EQUATION cannot be evaluated: " ++ x ++ " (T3)"]
    | .ok b =>
      let outcome : Except (Stop × Nat) (Option String × Nat) := do
        let (va, ka, s) ← l.eval budget b steps
        let (vb, kb, s) ← r.eval budget b s
        let s ← sideRanges budget va vb s
        if ka ≠ kb then
          return (some (tag ++ ": the two sides of EQUATION cannot be compared: units of different kind: " ++
            kindText ka ++ " and " ++ kindText kb ++ " (T3)"), s)
        let (x, s) ← reading budget va s
        let (y, s) ← reading budget vb s
        if x.text ≠ y.text then
          return (some (who ++ ": " ++ name ++ " evaluates " ++ x.text ++ " = " ++ y.text ++ " " ++ basis ++ " (T3)"), s)
        return (none, s)
      match outcome with
      | .ok (some p, s) =>
        probs := probs ++ [p]
        steps := s
      | .ok (none, s) => steps := s
      | .error (.unbound _, s) => steps := s
      | .error (.convention x, s) =>
        probs := probs ++ [tag ++ ": the two sides of EQUATION cannot be compared: " ++ x ++ " (T3)"]
        steps := s
      | .error (.refused x, s) =>
        probs := probs ++ [tag ++ ": EQUATION cannot be evaluated " ++ basis ++ ": " ++ x ++ " (T3)"]
        steps := s
      | .error (.owed w, _) => throw (.owed w)
      | .error (.budget, _) => throw .budget
  for left in sortedSet (lefts.map (·.1)) do
    let rs := (lefts.lookup left).getD []
    for i in List.range rs.length do
      for j in List.range rs.length do
        if i < j then
          let a := rs.getD i ("", "")
          let c := rs.getD j ("", "")
          if a.2 ≠ c.2 then
            probs := probs ++ ["LAW:" ++ a.1 ++ " and LAW:" ++ c.1 ++ ": the left side " ++ left ++
              " is equated to " ++ a.2 ++ " and to " ++ c.2 ++ " (T3)"]
  Except.mapError Stop.owed (finish probs)

/-- `t3LawsIn` with no budget, as the fundamental tests take it (`Principia.StartingSet`):
owed when an evaluation is. With no budget no decision passes it (`climb_none`), so the
budget's stop is not met; were it met, it would be owed. -/
def t3Laws (tpk : Value) : Except Owed (List String) :=
  (t3LawsIn none tpk).mapError fun
    | .owed w => w
    | _ => .exact budgetExceeded

end Principia.Form
