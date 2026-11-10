import Principia.Dimension
import Principia.Form.Grammar

/-!
# Declared forms: dimensions (S4) and totality (S6)

v1's `tpc_form` 0.2.1 dimension walk (`_dim_g`, `form_dimension`, fundamental test T4's law
half) and guard table (`_guards_needed_g`, `_totality_g`, `form_totality`, T6).

**Dimensions.** `+` and `-` need equal DIMENSIONs and yield it; `*` adds exponents and `/`
subtracts them; `^` multiplies by `p/q` when every resulting exponent is an integer; exp,
ln, sin, cos and tan need a dimensionless argument and yield 1; abs keeps its argument's;
sqrt halves; a literal is dimensionless, except that the literal zero has every DIMENSION
(`ANY`); `=` and every comparison need equal DIMENSIONs; `D(x, s, n)` is dim(x) less `n`
times dim(s); dividing by the literal zero's dimension is refused. Every exponent
read or computed lies within -9999..9999 (S14).

**Totality.** `+ - * abs exp sin cos` and `^` with an integer at least 0 are total; `/`
needs the guard `E != 0` (or `0 != E`) on its divisor; `ln(E)` needs `E > 0`; `sqrt(E)`
and `E^(p/q)` need `E >= 0`; `E^(negative)` needs `E != 0`; tan is refused in a predicate.
A guard is a conjunct beside the comparison, matched by canonical spelling.
-/

namespace Principia.Form

/-! ## Dimensions -/

/-- A DIMENSION as its exponents over L M T I TH N J, in that order. -/
abbrev Dims := List Int

/-- The dimensionless exponents. -/
def Dims.one : Dims := [0, 0, 0, 0, 0, 0, 0]

/-- A DIMENSION's exponents, or `none` when it does not read or leaves -9999..9999 (v1's
`_exps` over `normalize_dimension`). -/
def dimsOf? (s : String) : Option Dims :=
  match Dimension.sums s with
  | some e => if Dimension.inRange e then some (Dimension.Base.all.map e) else none
  | none => none

/-- A dimension's text: `ANY` for the literal zero's, else the canonical DIMENSION (v1's
`_dstr`). -/
def dimsText : Option Dims → String
  | none => "ANY"
  | some e => Dimension.canon fun b => e.getD b.index 0

/-- S14: every exponent within -9999..9999. -/
def inRange (kind : Bool) (e : List Int) : Except String (List Int) :=
  if e.all fun x => x.natAbs ≤ expMax then .ok e
  else .error (if kind then "a kind exponent is out of range" else "an exponent is out of range")

/-- The names a form may use, each with its DIMENSION's exponents or none; the first entry
of a name counts. -/
abbrev DimTable := List (String × Option Dims)

/-- A name's exponents, when it has a DIMENSION that reads. -/
def DimTable.find? (t : DimTable) (n : String) : Option Dims :=
  match t.lookup n with
  | some (some d) => some d
  | _ => none

/-- A name's exponents, or the refusal that it has none. -/
def DimTable.need (t : DimTable) (n : String) : Except String Dims :=
  match t.find? n with
  | some d => inRange false d
  | none => .error s!"{n} has no DIMENSION"

/-- The table of a `{name: DIMENSION}` object (v1's `_dims_of`): a value that is not a
string has none. -/
def DimTable.ofStrings (kvs : List (String × Option String)) : DimTable :=
  kvs.map fun (k, v) => (k, v.bind dimsOf?)

/-- An expression's dimension, `none` for the literal zero's ANY (v1's `_dim_g`). -/
def Expr.dims (t : DimTable) : Expr → Except String (Option Dims)
  | .num c => .ok (if c == "0" then none else some Dims.one)
  | .ident n => some <$> t.need n
  | .neg e | .paren e => e.dims t
  | .bin op l r => do
    let a ← l.dims t
    let b ← r.dims t
    match op with
    | .add | .sub =>
      match a, b with
      | none, _ => pure b
      | _, none => pure a
      | some x, some y =>
        if x == y then pure a else throw s!"{op.symbol} joins {dimsText a} and {dimsText b}"
    | .mul =>
      match a, b with
      | some x, some y => some <$> inRange false (List.zipWith (· + ·) x y)
      | _, _ => pure none
    | .div =>
      match a, b with
      | _, none => throw "divides by zero"
      | none, _ => pure none
      | some x, some y => some <$> inRange false (List.zipWith (· - ·) x y)
  | .pow b p q => do
    match ← b.dims t with
    | none => pure none
    | some x =>
      if x.any fun v => (v * p) % (q : Int) ≠ 0 then
        throw s!"^ ({p}/{q}) of {dimsText (some x)} is not a dimension"
      else some <$> inRange false (x.map fun v => v * p / (q : Int))
  | .fn f e => do
    let a ← e.dims t
    match f, a with
    | .abs, _ => pure a
    | .sqrt, none => pure none
    | .sqrt, some x =>
      if x.any fun v => v % 2 ≠ 0 then throw s!"sqrt of {dimsText a} is not a dimension"
      else pure (some (x.map (· / 2)))
    | _, some x =>
      if x.any (· ≠ 0) then throw s!"{f.name} needs a dimensionless argument, not {dimsText a}"
      else pure (some Dims.one)
    | _, none => pure (some Dims.one)
  | .deriv x s n => do
    let a ← t.need x
    let b ← t.need s
    some <$> inRange false (List.zipWith (fun u v => u - (n : Int) * v) a b)

/-- A predicate's comparisons are homogeneous (v1's `_dim_g` over a predicate). -/
def Pred.dims (t : DimTable) : Pred → Except String Unit
  | .cmp op l r => do
    let a ← l.dims t
    let b ← r.dims t
    match a, b with
    | some x, some y =>
      if x == y then pure () else throw s!"{op.symbol} compares {dimsText a} and {dimsText b}"
    | _, _ => pure ()
  | .and a b | .or a b => do a.dims t; b.dims t
  | .not a | .paren a => a.dims t

/-- A form's dimension: an equation's sides agree; a predicate's is 1. -/
def Tree.dims (t : DimTable) : Tree → Except String (Option Dims)
  | .eq l r => do
    let a ← l.dims t
    let b ← r.dims t
    match a, b with
    | none, _ => pure b
    | _, none => pure a
    | some x, some y =>
      if x == y then pure a else throw s!"sides have dimensions {dimsText a} and {dimsText b}"
  | .expr e => e.dims t
  | .pred p => do p.dims t; pure (some Dims.one)

/-- `form_dimension`: the DIMENSION of an expression, equation or form under a table of
names; `ANY` for the literal zero alone; `1` for a predicate whose comparisons are
homogeneous. -/
def formDimension (text : String) (mode : Mode) (t : DimTable) : Answer String :=
  ((parse text mode).bind fun tree => Answer.ofExcept ((tree.dims t).map dimsText)).escaped

/-! ## Totality -/

/-- A partial operation in an expression: what it is, the guard it needs (none for tan,
which no guard makes total) and the canonical comparisons that supply that guard. -/
structure Need where
  what : String
  guard : Option String
  forms : List String

/-- An expression's spelling without its enclosing parentheses (v1's `_pr(_strip(e))`). -/
def Expr.bare (e : Expr) : String := e.render.2

/-- The partial operations of an expression, its operands' first (v1's
`_guards_needed_g`). -/
def Expr.needs : Expr → List Need
  | .bin op l r =>
    l.needs ++ r.needs ++
      if op == .div then
        let e := r.bare
        [⟨"/ on " ++ e, some ("guard " ++ e ++ " != 0"), [e ++ "!=0", "0!=" ++ e]⟩]
      else []
  | .pow b p q =>
    b.needs ++
      let e := b.bare
      if q ≠ 1 then
        [⟨"^ with a rational exponent on " ++ e, some ("guard " ++ e ++ " >= 0"),
          [e ++ ">=0", "0<=" ++ e]⟩]
      else if p < 0 then
        [⟨"^ with a negative exponent on " ++ e, some ("guard " ++ e ++ " != 0"),
          [e ++ "!=0", "0!=" ++ e]⟩]
      else []
  | .fn f a =>
    a.needs ++
      let e := a.bare
      match f with
      | .ln => [⟨"ln on " ++ e, some ("guard " ++ e ++ " > 0"), [e ++ ">0", "0<" ++ e]⟩]
      | .sqrt => [⟨"sqrt on " ++ e, some ("guard " ++ e ++ " >= 0"), [e ++ ">=0", "0<=" ++ e]⟩]
      | .tan => [⟨"tan on " ++ e, none, []⟩]
      | _ => []
  | .neg e | .paren e => e.needs
  | .num _ | .ident _ | .deriv _ _ _ => []

/-- The canonical comparisons a conjunct supplies as guards: the comparison itself, or the
conjuncts of a nested `and` (v1's `_conjuncts_g`). -/
def Pred.conjuncts : Pred → List String
  | .paren a => a.conjuncts
  | .cmp op l r => [(Pred.cmp op l r).print]
  | .and a b => a.conjuncts ++ b.conjuncts
  | .or _ _ | .not _ => []

/-- The problems of a predicate under the guards in force (v1's `_totality_g`): the other
operands of every `and` on the path from the root guard each side; an `or` hides the
conjuncts below it from those above. -/
def Pred.totality (guards : List String) : Pred → List String
  | .and a b => a.totality (guards ++ b.conjuncts) ++ b.totality (guards ++ a.conjuncts)
  | .or a b => a.totality guards ++ b.totality guards
  | .not a | .paren a => a.totality guards
  | .cmp _ l r =>
    (l.needs ++ r.needs).filterMap fun n =>
      match n.guard with
      | none => some ("uses " ++ n.what ++ ", which is not total")
      | some g =>
        if n.forms.any guards.contains then none else some ("uses " ++ n.what ++ " with no " ++ g)

/-- A CONDITION's totality problems, after its homogeneity: sorted, without repeats. -/
def Pred.totalityProblems (t : DimTable) (p : Pred) : Except String (List String) := do
  p.dims t
  return sortedSet (p.totality [])

/-- `form_totality`: the problems of a CONDITION under the guard table, none when it is
total; refused when it does not parse or is not homogeneous. -/
def formTotality (text : String) (t : DimTable) : Answer (List String) :=
  ((parse text .predicate).bind fun tree =>
    match tree with
    | .pred p => Answer.ofExcept (p.totalityProblems t)
    | _ => .refused "not a predicate").escaped

end Principia.Form
