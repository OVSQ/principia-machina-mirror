import Principia.Canonical
import Principia.Decimal
import Principia.Zone.Text

/-!
# Declared forms: the grammar

v1's `tpc_form` 0.2.1 (the declared form of a LAW, a BOUNDARY and a SIGNATURE;
the bounds; S14, the computed exponents; S32, the parse tree): the closed ASCII
grammar of EQUATION, CONDITION, FORM and IMAGE_FORM, its parser, its one canonical
spelling, its tree and the names a form uses.

```
equation   := expr "=" expr                        (EQUATION)
form       := expr ( "=" expr )?                   (FORM, IMAGE_FORM)
predicate  := disj                                 (CONDITION)
disj       := conj ( "or" conj )*                  left-associative
conj       := neg ( "and" neg )*                   left-associative
neg        := "not" neg | "(" predicate ")" | expr cmp expr
cmp        := "<" | "<=" | ">" | ">=" | "=" | "!="
expr       := term ( ("+" | "-") term )*           left-associative
term       := unary ( ("*" | "/") unary )*         left-associative
unary      := "-" power | power                    -a^2 is -(a^2)
power      := atom ( "^" exponent )?               a^2^3 is refused
exponent   := integer | "(" "-"? integer ")" | "(" "-"? integer "/" integer ")"
atom       := identifier | literal | "(" expr ")" | function "(" expr ")"
            | "D" "(" identifier "," identifier ( "," integer )? ")"
function   := exp | ln | sin | cos | tan | abs | sqrt
```

The parser reads one token ahead, as v1's does; a parenthesis in a CONDITION opens a
predicate when a comparison or a keyword lies inside it, else an expression. Before any
token is read the text meets v1's bounds: at most 4096 code points, at most 64
parentheses open at once; an integer has at most four digits.

**Text.** v1 read a form after line-ending normalization and NFC (`_text`), and the bounds,
the positions and the length its refusals state count the code points of that text. So
does the Calculator, through `Principia.Zone.textChars`, at Unicode 15.1.0.

**The parser is total.** Every rule takes a step count, and each call spends one; the
count given, ten per token and twenty more, exceeds the longest chain of calls, which
consumes a token at least every nine calls. The rules recurse structurally on the count,
so the kernel can run them (the grammar witnesses in `Principia.Form` are proved so).
-/

namespace Principia.Form

open Principia.Zone (escape)

/-! ## Answers -/

/-- What the Calculator cannot settle yet, and so does not answer. -/
inductive Owed where
  /-- No exact value within the Calculator's bounds: what was met. -/
  | exact (what : String)
  deriving DecidableEq, Repr

/-- An owed answer's reason, as the owed lists spell it. -/
def Owed.word : Owed → String
  | .exact what => "exact: " ++ what

/-- A form function's answer: v1's `["OK", ...]`, its `["REFUSED", reason]`, or owed. -/
inductive Answer (α : Type) where
  | ok (a : α)
  | refused (reason : String)
  | owed (why : Owed)
  deriving Repr

namespace Answer

/-- Map an answer. -/
def map {α β : Type} (f : α → β) : Answer α → Answer β
  | .ok a => .ok (f a)
  | .refused r => .refused r
  | .owed w => .owed w

/-- Chain an answer. -/
def bind {α β : Type} (a : Answer α) (f : α → Answer β) : Answer β :=
  match a with
  | .ok x => f x
  | .refused r => .refused r
  | .owed w => .owed w

/-- An `Except` of the grammar, as an answer. -/
def ofExcept {α : Type} : Except String α → Answer α
  | .ok a => .ok a
  | .error r => .refused r

end Answer

/-! ## Modes -/

/-- What a form is read as: v1's four modes. -/
inductive Mode where
  /-- An expression, no `=`. -/
  | expression
  /-- EQUATION: `expr = expr`. -/
  | equation
  /-- CONDITION: a predicate. -/
  | predicate
  /-- FORM, IMAGE_FORM: an expression, with or without `=`. -/
  | form
  deriving DecidableEq, Repr

/-- A mode's name, as v1 spells it. -/
def Mode.ofString? : String → Option Mode
  | "expression" => some .expression
  | "equation" => some .equation
  | "predicate" => some .predicate
  | "form" => some .form
  | _ => none

/-- The mode of a form field (v1's `MODE_OF_FIELD`). -/
def Mode.ofField? : String → Option Mode
  | "EQUATION" => some .equation
  | "CONDITION" => some .predicate
  | "FORM" => some .form
  | "IMAGE_FORM" => some .form
  | _ => none

/-! ## The tree (S32) -/

/-- The seven functions. -/
inductive Fn where
  | exp | ln | sin | cos | tan | abs | sqrt
  deriving DecidableEq, Repr, Inhabited

/-- A function's name. -/
def Fn.name : Fn → String
  | .exp => "exp" | .ln => "ln" | .sin => "sin" | .cos => "cos" | .tan => "tan"
  | .abs => "abs" | .sqrt => "sqrt"

/-- A function by name. -/
def Fn.ofName? : String → Option Fn
  | "exp" => some .exp | "ln" => some .ln | "sin" => some .sin | "cos" => some .cos
  | "tan" => some .tan | "abs" => some .abs | "sqrt" => some .sqrt
  | _ => none

/-- The four arithmetic operators. -/
inductive BinOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr, Inhabited

/-- An operator's symbol. -/
def BinOp.symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

/-- The six comparisons. -/
inductive CmpOp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr, Inhabited

/-- A comparison's symbol. -/
def CmpOp.symbol : CmpOp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "=" | .ne => "!="

/-- A comparison by symbol. -/
def CmpOp.ofSymbol? : String → Option CmpOp
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "=" => some .eq | "!=" => some .ne
  | _ => none

/-- An expression, as parsed: a parenthesis the canonical spelling drops is kept. -/
inductive Expr where
  /-- A literal, in canonical decimal form. -/
  | num (canon : String)
  /-- An identifier. -/
  | ident (name : String)
  /-- Unary minus. -/
  | neg (e : Expr)
  /-- A parenthesized expression. -/
  | paren (e : Expr)
  /-- `l op r`. -/
  | bin (op : BinOp) (l r : Expr)
  /-- `base ^ (p/q)`, as written: `q ≥ 1`, not reduced. -/
  | pow (base : Expr) (p : Int) (q : Nat)
  /-- A function of an argument. -/
  | fn (f : Fn) (arg : Expr)
  /-- `D(x, s, n)`: the `n`-th derivative of `x` in the D variable `s`, `n ≥ 1`. -/
  | deriv (x s : String) (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A predicate, as parsed. -/
inductive Pred where
  /-- `l op r`. -/
  | cmp (op : CmpOp) (l r : Expr)
  /-- `a and b`. -/
  | and (a b : Pred)
  /-- `a or b`. -/
  | or (a b : Pred)
  /-- `not a`. -/
  | not (a : Pred)
  /-- A parenthesized predicate. -/
  | paren (a : Pred)
  deriving DecidableEq, Repr, Inhabited

/-- A whole form. -/
inductive Tree where
  /-- `l = r`: an equation, or a form with `=`. -/
  | eq (l r : Expr)
  /-- An expression, or a form without `=`. -/
  | expr (e : Expr)
  /-- A predicate. -/
  | pred (p : Pred)
  deriving DecidableEq, Repr, Inhabited

/-- An expression without its enclosing parentheses (v1's `_strip`). -/
def Expr.strip : Expr → Expr
  | .paren e => e.strip
  | e => e

/-- A predicate without its enclosing parentheses. -/
def Pred.strip : Pred → Pred
  | .paren a => a.strip
  | a => a

/-! ## The canonical spelling (S10)

No white space but one space around `and` and `or` and after `not`; literals in canonical
decimal form; integer exponents without leading zeros; `D(x,t,1)` written `D(x,t)`; the
author's order and parentheses kept, but redundant enclosing parentheses dropped at every
slot a delimiter bounds: the whole, each side of `=` or of a comparison, a function's
argument. -/

/-- An exponent's spelling. -/
def exponentText (p : Int) (q : Nat) : String :=
  if q = 1 ∧ 0 ≤ p then toString p
  else if q = 1 then "(" ++ toString p ++ ")"
  else "(" ++ toString p ++ "/" ++ toString q ++ ")"

/-- An expression's canonical spelling, and the spelling of the expression its enclosing
parentheses removed (v1's `_pr` of the node and of `_strip` of it), in one pass. -/
def Expr.render : Expr → String × String
  | .num s => (s, s)
  | .ident n => (n, n)
  | .neg e => let t := "-" ++ e.render.1; (t, t)
  | .paren e => ("(" ++ e.render.1 ++ ")", e.render.2)
  | .bin op l r => let t := l.render.1 ++ op.symbol ++ r.render.1; (t, t)
  | .pow b p q => let t := b.render.1 ++ "^" ++ exponentText p q; (t, t)
  | .fn f a => let t := f.name ++ "(" ++ a.render.2 ++ ")"; (t, t)
  | .deriv x s n =>
    let t := "D(" ++ x ++ "," ++ s ++ (if n = 1 then "" else "," ++ toString n) ++ ")"
    (t, t)

/-- An expression's canonical spelling (v1's `_pr`). -/
def Expr.print (e : Expr) : String := e.render.1

/-- A predicate's canonical spelling, and that of the predicate its enclosing parentheses
removed. -/
def Pred.render : Pred → String × String
  | .cmp op l r => let t := l.render.2 ++ op.symbol ++ r.render.2; (t, t)
  | .and a b => let t := a.render.1 ++ " and " ++ b.render.1; (t, t)
  | .or a b => let t := a.render.1 ++ " or " ++ b.render.1; (t, t)
  | .not a => let t := "not " ++ a.render.1; (t, t)
  | .paren a => ("(" ++ a.render.1 ++ ")", a.render.2)

/-- A predicate's canonical spelling. -/
def Pred.print (p : Pred) : String := p.render.1

/-- A form's canonical spelling. -/
def Tree.print : Tree → String
  | .eq l r => l.render.2 ++ "=" ++ r.render.2
  | .expr e => e.render.2
  | .pred p => p.render.2

/-- The second spelling is the first of the expression without its enclosing
parentheses. -/
theorem Expr.render_snd (e : Expr) : e.render.2 = e.strip.print := by
  induction e <;> simp_all [Expr.render, Expr.strip, Expr.print]

/-- The same for predicates. -/
theorem Pred.render_snd (p : Pred) : p.render.2 = p.strip.print := by
  induction p <;> simp_all [Pred.render, Pred.strip, Pred.print]

/-! ## The tree as v1's value (S32)

`form_tree`'s tree as v1's lists: `["num", c]`, `["id", n]`, `["neg", e]`, `["paren", e]`,
`["bin", op, l, r]`, `["pow", e, [p, q]]`, `["fn", f, e]`, `["D", x, s, n]`; `["cmp", op,
l, r]`, `["and", a, b]`, `["or", a, b]`, `["not", a]`, `["pparen", a]`; `["eq", l, r]`,
`["expr", e]`, `["pred", p]`. -/

open Principia.Canonical (Value) in
/-- An expression as v1's list. -/
def Expr.toValue : Expr → Value
  | .num s => .arr [.str "num", .str s]
  | .ident n => .arr [.str "id", .str n]
  | .neg e => .arr [.str "neg", e.toValue]
  | .paren e => .arr [.str "paren", e.toValue]
  | .bin op l r => .arr [.str "bin", .str op.symbol, l.toValue, r.toValue]
  | .pow b p q => .arr [.str "pow", b.toValue, .arr [.int p, .int q]]
  | .fn f a => .arr [.str "fn", .str f.name, a.toValue]
  | .deriv x s n => .arr [.str "D", .str x, .str s, .int n]

open Principia.Canonical (Value) in
/-- A predicate as v1's list. -/
def Pred.toValue : Pred → Value
  | .cmp op l r => .arr [.str "cmp", .str op.symbol, l.toValue, r.toValue]
  | .and a b => .arr [.str "and", a.toValue, b.toValue]
  | .or a b => .arr [.str "or", a.toValue, b.toValue]
  | .not a => .arr [.str "not", a.toValue]
  | .paren a => .arr [.str "pparen", a.toValue]

open Principia.Canonical (Value) in
/-- A form as v1's list. -/
def Tree.toValue : Tree → Value
  | .eq l r => .arr [.str "eq", l.toValue, r.toValue]
  | .expr e => .arr [.str "expr", e.toValue]
  | .pred p => .arr [.str "pred", p.toValue]

/-! ## Names (S5) -/

/-- The identifiers an expression names, with repeats: D's operand and variable are
identifiers; a function's name and D are not. -/
def Expr.names : Expr → List String
  | .num _ => []
  | .ident n => [n]
  | .neg e | .paren e | .pow e _ _ | .fn _ e => e.names
  | .bin _ l r => l.names ++ r.names
  | .deriv x s _ => [x, s]

/-- The identifiers a predicate names, with repeats. -/
def Pred.names : Pred → List String
  | .cmp _ l r => l.names ++ r.names
  | .and a b | .or a b => a.names ++ b.names
  | .not a | .paren a => a.names

/-- The identifiers a form names, with repeats. -/
def Tree.names : Tree → List String
  | .eq l r => l.names ++ r.names
  | .expr e => e.names
  | .pred p => p.names

/-- `x` inserted into a sorted list without repeats. -/
def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: insertSorted x ys

/-- Strings sorted in code point order, without repeats (Python's `sorted(set(...))`). -/
def sortedSet (xs : List String) : List String := xs.foldl (fun acc x => insertSorted x acc) []

/-- The D variables of an expression: the second argument of each D, with repeats. -/
def Expr.dVariables : Expr → List String
  | .num _ | .ident _ => []
  | .neg e | .paren e | .pow e _ _ | .fn _ e => e.dVariables
  | .bin _ l r => l.dVariables ++ r.dVariables
  | .deriv _ s _ => [s]

/-- The D variables of a form, with repeats (a predicate holds no D). -/
def Tree.dVariables : Tree → List String
  | .eq l r => l.dVariables ++ r.dVariables
  | .expr e => e.dVariables
  | .pred _ => []

/-! ## Bounds and computed exponents (S14) -/

/-- The most code points a form's canonical text may hold. -/
def maxCodePoints : Nat := 4096

/-- The most parentheses open at once. -/
def maxNesting : Nat := 64

/-- The most digits an integer may be written with, a leading zero counted. -/
def maxIntegerDigits : Nat := 4

/-- The bound on every computed exponent (S14), as on a DIMENSION's. -/
def expMax : Nat := 9999

/-- The first parenthesis opened beyond the nesting bound, as a 1-based position. -/
def nestingFault : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, depth, pos =>
    if c = '(' then
      if depth + 1 > maxNesting then some pos else nestingFault cs (depth + 1) (pos + 1)
    else if c = ')' ∧ depth > 0 then nestingFault cs (depth - 1) (pos + 1)
    else nestingFault cs depth (pos + 1)

/-- v1's bounds on the canonical text, before any token is read: its length, then its depth. -/
def boundsFault (cs : List Char) : Option String :=
  if cs.length > maxCodePoints then
    some s!"the form is longer than {maxCodePoints} code points"
  else (nestingFault cs 0 1).map fun pos => s!"more than {maxNesting} nested parentheses at {pos}"

/-- Whether an expression's identifiers or Ds sit under functions that end the product of
exponents (exp, ln, sin, cos, tan yield a pure number). -/
def Fn.pure : Fn → Bool
  | .exp | .ln | .sin | .cos | .tan => true
  | .abs | .sqrt => false

/-- `n/d` in lowest terms, `d ≥ 1`. -/
def lowest (n : Int) (d : Nat) : Int × Nat :=
  let g := Nat.gcd n.natAbs d
  if g = 0 then (n, d) else (n / g, d / g)

/-- S14: the exponent the form composes for each identifier and each D under an
expression, starting from `n/d` (v1's `_composed_g`): a power multiplies it by `p/q`, a
square root by 1/2, abs by 1; exp, ln, sin, cos and tan end the product. -/
def Expr.composed : Expr → Int → Nat → List (Int × Nat)
  | .num _, _, _ => []
  | .ident _, n, d | .deriv _ _ _, n, d => [(n, d)]
  | .neg e, n, d | .paren e, n, d => e.composed n d
  | .bin _ l r, n, d => l.composed n d ++ r.composed n d
  | .pow b p q, n, d => let (a, c) := lowest (n * p) (d * q); b.composed a c
  | .fn f a, n, d =>
    if f.pure then []
    else if f = .sqrt then let (x, y) := lowest n (d * 2); a.composed x y
    else a.composed n d

/-- S14, checked as each power or root completes: every composed exponent times `p/q`, in
lowest terms, within 9999 (v1's `_composed`). -/
def composedFault (base : Expr) (p : Int) (q : Nat) (pos : Nat) : Option String :=
  if (base.composed 1 1).any fun (n, d) =>
      let (a, b) := lowest (n * p) (d * q)
      a.natAbs > expMax ∨ b > expMax then
    some s!"a computed exponent beyond {expMax} at {pos}"
  else none

/-! ## Tokens -/

/-- A token's kind. -/
inductive TokKind where
  | ident | num | op
  deriving DecidableEq, Repr, Inhabited

/-- A token: its kind, its text and its 1-based position. -/
structure Token where
  kind : TokKind
  text : String
  pos : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An ASCII letter or `_`. -/
def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

/-- An ASCII digit. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The exponent of a literal after its `e`: an optional sign and one to four digits, not
followed by a fifth; else no exponent is taken. -/
def exponentChars (cs : List Char) : Option (List Char) :=
  let (sign, r) := match cs with
    | '+' :: r => (['+'], r)
    | '-' :: r => (['-'], r)
    | _ => ([], cs)
  let ds := r.takeWhile isDigit
  if 1 ≤ ds.length ∧ ds.length ≤ 4 then some (sign ++ ds) else none

/-- The characters of a literal at the front of `cs`, which starts with a digit:
`digits ("." digits)? ([eE] [-+]? digits{1,4})?`. -/
def literalChars (cs : List Char) : List Char :=
  let ip := cs.takeWhile isDigit
  let r := cs.drop ip.length
  let (fp, r) := match r with
    | '.' :: d :: r' => if isDigit d then
        let ds := (d :: r').takeWhile isDigit
        ('.' :: ds, (d :: r').drop ds.length)
      else ([], r)
    | _ => ([], r)
  let ex := match r with
    | e :: r' => if e = 'e' ∨ e = 'E' then
        match exponentChars r' with
        | some x => e :: x
        | none => []
      else []
    | [] => []
  ip ++ fp ++ ex

/-- The single-character operators. -/
def opChars : List Char := ['<', '>', '=', '+', '-', '*', '/', '^', '(', ')', ',']

/-- The tokens of a text (v1's `_tokens`), each step consuming at least one character, so
`fuel` at least the text's length suffices. -/
def tokensAux : Nat → List Char → Nat → List Token → Except String (List Token)
  | _, [], _, acc => .ok acc.reverse
  | 0, _ :: _, _, _ => .error "the tokenizer ran out of steps"
  | fuel + 1, c :: cs, pos, acc =>
    if c = ' ' ∨ c = '\t' ∨ c = '\n' then tokensAux fuel cs (pos + 1) acc
    else if isAlpha c then
      let w := cs.takeWhile fun d => isAlpha d || isDigit d
      tokensAux fuel (cs.drop w.length) (pos + 1 + w.length)
        (⟨.ident, String.ofList (c :: w), pos⟩ :: acc)
    else if isDigit c then
      let lit := literalChars (c :: cs)
      tokensAux fuel (cs.drop (lit.length - 1)) (pos + lit.length)
        (⟨.num, String.ofList lit, pos⟩ :: acc)
    else
      match cs with
      | '=' :: r =>
        if c = '<' ∨ c = '>' ∨ c = '!' then
          tokensAux fuel r (pos + 2) (⟨.op, String.ofList [c, '='], pos⟩ :: acc)
        else if opChars.contains c then
          tokensAux fuel cs (pos + 1) (⟨.op, c.toString, pos⟩ :: acc)
        else .error s!"unexpected character {escape c.toString} at {pos}"
      | _ =>
        if opChars.contains c then tokensAux fuel cs (pos + 1) (⟨.op, c.toString, pos⟩ :: acc)
        else .error s!"unexpected character {escape c.toString} at {pos}"

/-- The tokens of a text. -/
def tokens (cs : List Char) : Except String (List Token) := tokensAux (cs.length + 1) cs 1 []

/-! ## The parser -/

/-- The keywords. -/
def keywords : List String := ["and", "or", "not"]

/-- The comparison symbols. -/
def cmpSymbols : List String := ["<", "<=", ">", ">=", "=", "!="]

/-- The tokens and the mode being read. -/
structure Parser where
  toks : Array Token
  mode : Mode

namespace Parser

/-- The token at `i` is the operator `v`. -/
def isOp (P : Parser) (i : Nat) (v : String) : Bool :=
  match P.toks[i]? with
  | some t => t.kind == .op && t.text == v
  | none => false

/-- The token at `i` is the identifier `w`. -/
def isWord (P : Parser) (i : Nat) (w : String) : Bool :=
  match P.toks[i]? with
  | some t => t.kind == .ident && t.text == w
  | none => false

/-- v1's `fail_here`. -/
def failHere (P : Parser) (i : Nat) : String :=
  match P.toks[i]? with
  | none => "unexpected end"
  | some t => s!"unexpected token {t.text} at {t.pos}"

/-- Take the operator `v` at `i`. -/
def takeOp (P : Parser) (i : Nat) (v : String) : Except String Nat :=
  if P.isOp i v then .ok (i + 1) else .error (P.failHere i)

/-- v1's `integer`: an all-digit literal at `i`, its value and the next index; a fifth
digit is refused before the value is formed. -/
def integer (P : Parser) (i : Nat) : Except String (Option (Nat × Nat)) :=
  match P.toks[i]? with
  | some t =>
    if t.kind == .num && t.text.toList.all isDigit then
      if t.text.toList.length > maxIntegerDigits then
        .error s!"an integer of more than {maxIntegerDigits} digits at {t.pos}"
      else .ok (some (Canonical.digitsValue t.text.toList, i + 1))
    else .ok none
  | none => .ok none

/-- A parenthesis at the front of `ts` opens a predicate: a comparison or a keyword lies
inside it before it closes (v1's `paren_is_predicate`). -/
def predicateParen : List Token → Nat → Bool
  | [], _ => false
  | t :: ts, depth =>
    if t.kind == .op && t.text == "(" then predicateParen ts (depth + 1)
    else if t.kind == .op && t.text == ")" then
      if depth ≤ 1 then false else predicateParen ts (depth - 1)
    else if depth ≥ 1 && ((t.kind == .op && cmpSymbols.contains t.text) ||
        (t.kind == .ident && keywords.contains t.text)) then true
    else predicateParen ts depth

/-- A power's exponent after its `^` at `pos`: `(p, q, next)`. -/
def exponent (P : Parser) (i pos : Nat) : Except String (Int × Nat × Nat) := do
  let bad := s!"^ takes an integer or a parenthesized rational exponent at {pos}"
  match ← P.integer i with
  | some (p, j) => return ((p : Int), 1, j)
  | none =>
    unless P.isOp i "(" do throw bad
    let (sign, i) := if P.isOp (i + 1) "-" then ((-1 : Int), i + 2) else (1, i + 1)
    let some (p, i) ← P.integer i | throw bad
    let (q, i) ← if P.isOp i "/" then do
        let some (q, j) ← P.integer (i + 1) | throw bad
        if q = 0 then throw s!"a rational exponent needs a positive denominator at {pos}"
        pure (q, j)
      else pure (1, i)
    unless P.isOp i ")" do throw bad
    return (sign * p, q, i + 1)

/-- `D(x, s)` or `D(x, s, n)`, `D` at index `i`, position `pos`. -/
def derivative (P : Parser) (i pos : Nat) : Except String (Expr × Nat) := do
  let msg := s!"D is written D(x,t) or D(x,t,n) at {pos}"
  let ident (j : Nat) : Except String String :=
    match P.toks[j]? with
    | some t => if t.kind == .ident && !keywords.contains t.text then .ok t.text else .error msg
    | none => .error msg
  let x ← ident (i + 2)
  unless P.isOp (i + 3) "," do throw msg
  let s ← ident (i + 4)
  let (n, j) ← if P.isOp (i + 5) "," then do
      match ← P.integer (i + 6) with
      | some (n, j) => if n < 1 then throw msg else pure (n, j)
      | none => throw msg
    else pure (1, i + 5)
  unless P.isOp j ")" do throw msg
  return (.deriv x s n, j + 1)

/-- The token before `i` is an arithmetic operator: a minus there would be the second
operator in a row. -/
def afterOperator (P : Parser) (i : Nat) : Bool :=
  match i with
  | 0 => false
  | j + 1 =>
    match P.toks[j]? with
    | some t => t.kind == .op && ["+", "-", "*", "/", "^"].contains t.text
    | none => false

/-- The message when the steps run out; the count given is never short. -/
def outOfSteps : String := "the parser ran out of steps"

mutual

/-- `disj := conj ("or" conj)*`. -/
def predicate (P : Parser) : Nat → Nat → Except String (Pred × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i => do
    let (a, i) ← conj P f i
    orTail P f a i

/-- The `or` loop. -/
def orTail (P : Parser) : Nat → Pred → Nat → Except String (Pred × Nat)
  | 0, _, _ => .error outOfSteps
  | f + 1, left, i =>
    if P.isWord i "or" then do
      let (b, j) ← conj P f (i + 1)
      orTail P f (.or left b) j
    else .ok (left, i)

/-- `conj := neg ("and" neg)*`. -/
def conj (P : Parser) : Nat → Nat → Except String (Pred × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i => do
    let (a, i) ← negation P f i
    andTail P f a i

/-- The `and` loop. -/
def andTail (P : Parser) : Nat → Pred → Nat → Except String (Pred × Nat)
  | 0, _, _ => .error outOfSteps
  | f + 1, left, i =>
    if P.isWord i "and" then do
      let (b, j) ← negation P f (i + 1)
      andTail P f (.and left b) j
    else .ok (left, i)

/-- `neg := "not" neg | "(" predicate ")" | expr cmp expr`. -/
def negation (P : Parser) : Nat → Nat → Except String (Pred × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i =>
    if P.isWord i "not" then do
      let (a, j) ← negation P f (i + 1)
      return (.not a, j)
    else if P.isOp i "(" && predicateParen (P.toks.toList.drop i) 0 then do
      let (a, j) ← predicate P f (i + 1)
      let j ← P.takeOp j ")"
      return (.paren a, j)
    else do
      let (a, j) ← expr P f i
      let some op := (match P.toks[j]? with
          | some t => if t.kind == .op then CmpOp.ofSymbol? t.text else none
          | none => none)
        | throw (P.failHere j)
      let (b, k) ← expr P f (j + 1)
      return (.cmp op a b, k)

/-- `expr := term (("+" | "-") term)*`. -/
def expr (P : Parser) : Nat → Nat → Except String (Expr × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i => do
    let (a, i) ← term P f i
    exprTail P f a i

/-- The `+`, `-` loop. -/
def exprTail (P : Parser) : Nat → Expr → Nat → Except String (Expr × Nat)
  | 0, _, _ => .error outOfSteps
  | f + 1, left, i =>
    if P.isOp i "+" || P.isOp i "-" then do
      let op := if P.isOp i "+" then BinOp.add else BinOp.sub
      let (b, j) ← term P f (i + 1)
      exprTail P f (.bin op left b) j
    else .ok (left, i)

/-- `term := unary (("*" | "/") unary)*`. -/
def term (P : Parser) : Nat → Nat → Except String (Expr × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i => do
    let (a, i) ← unary P f i
    termTail P f a i

/-- The `*`, `/` loop. -/
def termTail (P : Parser) : Nat → Expr → Nat → Except String (Expr × Nat)
  | 0, _, _ => .error outOfSteps
  | f + 1, left, i =>
    if P.isOp i "*" || P.isOp i "/" then do
      let op := if P.isOp i "*" then BinOp.mul else BinOp.div
      let (b, j) ← unary P f (i + 1)
      termTail P f (.bin op left b) j
    else .ok (left, i)

/-- `unary := "-" power | power`; a minus right after another operator is refused. -/
def unary (P : Parser) : Nat → Nat → Except String (Expr × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i =>
    if P.isOp i "-" then
      if P.afterOperator i then .error (P.failHere i)
      else do
        let (e, j) ← power P f (i + 1)
        return (.neg e, j)
    else power P f i

/-- `power := atom ("^" exponent)?`; a chained `^` is refused; S14 is checked. -/
def power (P : Parser) : Nat → Nat → Except String (Expr × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i => do
    let (base, i) ← atom P f i
    if !P.isOp i "^" then return (base, i)
    let pos := (P.toks[i]?.map (·.pos)).getD 0
    let (p, q, j) ← P.exponent (i + 1) pos
    if P.isOp j "^" then throw s!"chained ^ needs parentheses at {(P.toks[j]?.map (·.pos)).getD 0}"
    if let some m := composedFault base p q pos then throw m
    return (.pow base p q, j)

/-- `atom := identifier | literal | "(" expr ")" | function "(" expr ")" | D(...)`. -/
def atom (P : Parser) : Nat → Nat → Except String (Expr × Nat)
  | 0, _ => .error outOfSteps
  | f + 1, i =>
    match P.toks[i]? with
    | none => .error "unexpected end"
    | some t =>
      if t.kind == .num then .ok (.num ((Decimal.canon t.text).getD t.text), i + 1)
      else if t.kind == .op && t.text == "(" then do
        let (e, j) ← expr P f (i + 1)
        let j ← P.takeOp j ")"
        return (.paren e, j)
      else if t.kind == .ident then
        if keywords.contains t.text then .error (P.failHere i)
        else if P.isOp (i + 1) "(" then
          if t.text == "D" then
            if P.mode == .predicate then .error s!"D is not permitted in a CONDITION at {t.pos}"
            else P.derivative i t.pos
          else match Fn.ofName? t.text with
            | none => .error s!"unknown function {t.text} at {t.pos}"
            | some fn => do
              let (a, j) ← expr P f (i + 2)
              let j ← P.takeOp j ")"
              if fn == .sqrt then
                if let some m := composedFault a 1 2 t.pos then throw m
              return (.fn fn a, j)
        else .ok (.ident t.text, i + 1)
      else .error (P.failHere i)

end

/-- A form from its tokens (v1's `top`). -/
def top (P : Parser) : Except String Tree := do
  if P.toks.isEmpty then throw "empty form"
  let fuel := 10 * P.toks.size + 20
  let (tree, i) ← if P.mode == .predicate then do
      let (p, i) ← predicate P fuel 0
      pure (Tree.pred p, i)
    else do
      let (a, i) ← expr P fuel 0
      if P.isOp i "=" then
        if P.mode == .expression then throw (P.failHere i)
        let (b, j) ← expr P fuel (i + 1)
        pure (Tree.eq a b, j)
      else if P.mode == .equation then
        if (P.toks[i]?).isSome then throw (P.failHere i)
        throw "the equation has no ="
      else pure (Tree.expr a, i)
  if (P.toks[i]?).isSome then throw (P.failHere i)
  return tree

end Parser

/-! ## Reading a form -/

/-- A form's canonical text (v1's `_text`): line endings as LF, then NFC. -/
def canonicalText (s : String) : List Char := Zone.textChars s

/-- The parse tree of a text read in a mode, or why not (v1's `_parse`, after its mode
and type checks). -/
def parse (text : String) (mode : Mode) : Answer Tree :=
  let cs := canonicalText text
  match boundsFault cs with
  | some m => .refused m
  | none => Answer.ofExcept do
    let ts ← tokens cs
    Parser.top ⟨ts.toArray, mode⟩

/-- A refusal as v1 returns it: every disallowed code point of the reason escaped. -/
def refuse {α : Type} (reason : String) : Answer α := .refused (escape reason)

/-- The answer with its refusal escaped (v1's `_refuse`). -/
def Answer.escaped {α : Type} : Answer α → Answer α
  | .refused r => .refused (escape r)
  | a => a

/-- `parse_form`: the canonical spelling, or the refusal. -/
def parseForm (text : String) (mode : Mode) : Answer String :=
  ((parse text mode).map Tree.print).escaped

/-- `form_tree` (S32): the tree every check walks, as parsed, or `parse_form`'s refusal. -/
def formTree (text : String) (mode : Mode) : Answer Tree := (parse text mode).escaped

/-- `form_names`: the identifiers a form names, sorted, without repeats. -/
def formNames (text : String) (mode : Mode) : Answer (List String) :=
  ((parse text mode).map fun t => sortedSet t.names).escaped

/-- A form field's canonical spelling, or why not: the zones' seam for EQUATION,
CONDITION, FORM and IMAGE_FORM (v1's `parse_form(v, MODE_OF_FIELD[f])`). A field that is
not a form field is refused. -/
def parseField (field text : String) : Answer String :=
  match Mode.ofField? field with
  | some m => parseForm text m
  | none => refuse s!"{field} is not a form field"

/-- The arguments as v1's public functions take them: the mode is checked first, then
that the text is a string (`none` stands for any other JSON value). -/
def withArgs {α : Type} (text : Option String) (mode : String) (k : String → Mode → Answer α) :
    Answer α :=
  match Mode.ofString? mode with
  | none => refuse ("unknown mode " ++ mode)
  | some m =>
    match text with
    | none => refuse "the form is not a string"
    | some t => k t m

/-! ## The grammar witnesses (S2)

v1 asserts these 33 when it loads, and their count: each text in its mode reads to the
spelling given, or is refused; and each canonical spelling reads back to itself. -/

/-- v1's `GRAMMAR_WITNESSES`: text, mode, canonical spelling or `REFUSED`. -/
def grammarWitnesses : List (String × Mode × String) := [
  ("a-b-c", .expression, "a-b-c"),
  ("a-(b-c)", .expression, "a-(b-c)"),
  ("a/b*c", .expression, "a/b*c"),
  ("a/(b*c)", .expression, "a/(b*c)"),
  ("-a^2", .expression, "-a^2"),
  ("(-a)^2", .expression, "(-a)^2"),
  ("a^2^3", .expression, "REFUSED"),
  ("(a^2)^3", .expression, "(a^2)^3"),
  ("a+b*c", .expression, "a+b*c"),
  ("(a+b)*c", .expression, "(a+b)*c"),
  ("((a))", .expression, "a"),
  ("a*((b))", .expression, "a*((b))"),
  ("sqrt((x))", .expression, "sqrt(x)"),
  ("x^(-1)", .expression, "x^(-1)"),
  ("x^(1/2)", .expression, "x^(1/2)"),
  ("x^02", .expression, "x^2"),
  ("0.50*x", .expression, "5e-1*x"),
  ("100*x", .expression, "1e2*x"),
  ("D(x, t, 1)", .expression, "D(x,t)"),
  ("m * D(v, t) = -k_s * x", .equation, "m*D(v,t)=-k_s*x"),
  ("(a)=(b)", .equation, "a=b"),
  ("a or b and c", .predicate, "REFUSED"),
  ("x<1 or y>2 and z=3", .predicate, "x<1 or y>2 and z=3"),
  ("(x<1 or y>2) and z=3", .predicate, "(x<1 or y>2) and z=3"),
  ("not x<1 and y>2", .predicate, "not x<1 and y>2"),
  ("not (x<1 and y>2)", .predicate, "not (x<1 and y>2)"),
  ("(x+1)<2", .predicate, "x+1<2"),
  ("(x<1)", .predicate, "x<1"),
  ("abs( x ) < x_max", .predicate, "abs(x)<x_max"),
  ("a--b", .expression, "REFUSED"),
  ("a*-b", .expression, "REFUSED"),
  ("2x", .expression, "REFUSED"),
  ("0.05 m", .expression, "REFUSED")]

/-- A witness holds: the text reads as stated, and a canonical spelling reads back to
itself. -/
def witnessHolds (w : String × Mode × String) : Bool :=
  match parseForm w.1 w.2.1 with
  | .ok s => s == w.2.2 && (match parseForm s w.2.1 with | .ok s' => s' == s | _ => false)
  | .refused _ => w.2.2 == "REFUSED"
  | .owed _ => false

end Principia.Form
