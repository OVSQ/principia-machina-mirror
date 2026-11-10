import Principia.Decimal
import Principia.Form
import Principia.Record.Derivation

/-!
# The structured derivation checker: first increment

A STRUCTURED derivation is a list of rewrite steps, each
citing a law of the Starting Set or an ASSUMPTION record, and the Calculator checks it;
a checked one earns MECHANICAL. This file is the first increment. It contains:

* **The semantics.** A declared form's expression (`Principia.Form.Expr`) is evaluated
  over `Rat` under an assignment of its identifiers. Every function symbol is read
  through an arbitrary interpretation (`Interp`): the seven functions, `D(x, s, n)` and
  a power whose exponent is written as a fraction (`q ≠ 1`). Nothing needs real
  analysis, and the question of real functions stays open. A power with an integer exponent (`q = 1`) is `Rat`'s.
  Division is `Rat`'s: dividing by zero gives zero (`eval_div_of_zero`).
* **The step language (`Start`, `Step`).** A derivation starts from a cited law or
  ASSUMPTION record, or from `e = e`. Each step rewrites one subterm of one side of the
  current equation. It does so either by a cited law `l = r`, instantiated by exact
  match only (no unification), or by one identity from a fixed list (`Identity`), each
  proved sound under the semantics. A step states the equation it leads to.
* **Parentheses.** The grammar keeps a parenthesis as a node, but it only groups, and
  the tree already records the grouping. The checker removes every parenthesis from
  each equation it reads (`unparen`, value-preserving: `eval_unparen`), so paren removal
  is applied everywhere at once and no step spends a line on it.
* **The checker (`check`).** It accepts iff every step rewrites exactly as stated (the
  same tree, parentheses aside) and the last equation is the goal (the RESULT's
  EQUATION). Otherwise it refuses with the first failing step and a word for why.
* **The soundness theorem (`check_sound`).** If the checker accepts, the goal holds
  under every assignment and every interpretation under which the cited laws hold,
  with no exception for division.

The second increment adds **matching a law to an instance of it** (`matchExpr`,
`Rule.citeInstance`). A step may cite a law by instance: one side of the law, each of its
identifiers a pattern variable, is matched against the subterm by first-order matching;
the substitution found is applied to the other side, and the step is accepted only when
that instance is exactly the equation it states. Lean proves that matching's answer is
an instance (`matchExpr_sound`), that matching finds one whenever one exists
(`matchExpr_complete`), and that the checker stays sound (`check_sound`): a law cited by
instance must hold under every assignment, for an instance of it is the law at another
assignment (`eval_subst`). A law cited exactly, as before, need hold only under the
assignment at hand. A record's step cannot cite by instance (`readSteps_instances`): the
Starting Set's laws and ASSUMPTION records state facts about one system's quantities, not
identities over every value, so the credit reads them exactly until the Declarer chooses
which may be instanced.

What is still left out: the calculus of `D(x, s, n)` (a derivative is an opaque symbol;
what it means is the Declarer's to choose), approximations beyond citing an ASSUMPTION
record, and a `pcalc` call.
-/

namespace Principia.StructuredCheck

open Principia.Form
open Principia.Record (StepCitation)

/-! ## The semantics -/

/-- An interpretation of the function symbols: the seven functions, `D(x, s, n)`, and a
power whose exponent is written as a fraction `p/q` with `q ≠ 1`. Arbitrary: nothing is
assumed of them. -/
structure Interp where
  fn : Fn → Rat → Rat
  deriv : String → String → Nat → Rat
  pow : Rat → Int → Nat → Rat

/-- An operator on two rationals; division is `Rat`'s, zero when the divisor is zero. -/
def binApply : BinOp → Rat → Rat → Rat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- A literal's value: its canonical decimal read exactly (zero for a text that does not
read, which the grammar never produces). -/
def litValue (s : String) : Rat := (Decimal.value s).getD 0

/-- An expression's value under an interpretation and an assignment of its identifiers. -/
def eval (I : Interp) (σ : String → Rat) : Expr → Rat
  | .num s => litValue s
  | .ident n => σ n
  | .neg e => - eval I σ e
  | .paren e => eval I σ e
  | .bin op l r => binApply op (eval I σ l) (eval I σ r)
  | .pow b p q => if q = 1 then eval I σ b ^ p else I.pow (eval I σ b) p q
  | .fn f a => I.fn f (eval I σ a)
  | .deriv x s n => I.deriv x s n

/-- Division by zero: a quotient whose divisor is worth zero is worth zero (`Rat`'s
convention, stated). -/
theorem eval_div_of_zero (I : Interp) (σ : String → Rat) (l r : Expr) (h : eval I σ r = 0) :
    eval I σ (.bin .div l r) = 0 := by
  simp [eval, binApply, h, Rat.div_def]

/-- `e` without its parentheses: the grouping stays in the tree. -/
def unparen : Expr → Expr
  | .paren e => unparen e
  | .neg e => .neg (unparen e)
  | .bin op l r => .bin op (unparen l) (unparen r)
  | .pow b p q => .pow (unparen b) p q
  | .fn f a => .fn f (unparen a)
  | .num s => .num s
  | .ident n => .ident n
  | .deriv x s n => .deriv x s n

/-- Removing parentheses keeps every value. -/
theorem eval_unparen (I : Interp) (σ : String → Rat) (e : Expr) :
    eval I σ (unparen e) = eval I σ e := by
  induction e <;> simp [unparen, eval, *]

/-- An equation `lhs = rhs`. -/
structure Equation where
  lhs : Expr
  rhs : Expr
  deriving DecidableEq, Repr, Inhabited

/-- An equation holds when its two sides are worth the same. -/
def Equation.holds (I : Interp) (σ : String → Rat) (e : Equation) : Prop :=
  eval I σ e.lhs = eval I σ e.rhs

/-- An expression's text read by the declared-form grammar, or why it does not read. -/
def parseExpr (text : String) : Except String Expr :=
  match formTree text .expression with
  | .ok (.expr e) => .ok e
  | .ok _ => .error "not an expression"
  | .refused r => .error r
  | .owed _ => .error "owed"

/-- The equation without its parentheses. -/
def Equation.unparen (e : Equation) : Equation := ⟨StructuredCheck.unparen e.lhs, StructuredCheck.unparen e.rhs⟩

theorem Equation.holds_unparen (I : Interp) (σ : String → Rat) (e : Equation) :
    e.unparen.holds I σ ↔ e.holds I σ := by
  simp [Equation.unparen, Equation.holds, eval_unparen]

/-- The equation a declared form's tree is, if it is one. -/
def Equation.ofTree? : Tree → Option Equation
  | .eq l r => some ⟨l, r⟩
  | _ => none

/-- An EQUATION's text read by the declared-form grammar, or why it does not read. -/
def Equation.parse (text : String) : Except String Equation :=
  match formTree text .equation with
  | .ok t => match Equation.ofTree? t with
    | some e => .ok e
    | none => .error "not an equation"
  | .refused r => .error r
  | .owed _ => .error "owed"

/-! ## Rewriting a subterm -/

/-- A step into a subterm: the operand of `-`, `( )`, a function or a power's base
(`arg`); a binary operator's left or right operand. -/
inductive Dir where
  | arg | left | right
  deriving DecidableEq, Repr, Inhabited

/-- `e` with the subterm at `path` rewritten by `f`; `none` when the path does not lead to
a subterm or `f` does not apply there. -/
def rewriteAt (f : Expr → Option Expr) : List Dir → Expr → Option Expr
  | [], e => f e
  | .arg :: p, .neg e => (rewriteAt f p e).map .neg
  | .arg :: p, .paren e => (rewriteAt f p e).map .paren
  | .arg :: p, .fn g e => (rewriteAt f p e).map (.fn g)
  | .arg :: p, .pow b x y => (rewriteAt f p b).map (fun b' => .pow b' x y)
  | .left :: p, .bin op l r => (rewriteAt f p l).map (fun l' => .bin op l' r)
  | .right :: p, .bin op l r => (rewriteAt f p r).map (fun r' => .bin op l r')
  | _ :: _, _ => none

/-- A rewrite that keeps the value of what it rewrites keeps the value of the whole: the
semantics is compositional, function symbols included. -/
theorem rewriteAt_sound (I : Interp) (σ : String → Rat) (f : Expr → Option Expr)
    (hf : ∀ e e', f e = some e' → eval I σ e' = eval I σ e) :
    ∀ (p : List Dir) (e e' : Expr), rewriteAt f p e = some e' → eval I σ e' = eval I σ e := by
  intro p
  induction p with
  | nil => intro e e' h; exact hf e e' h
  | cons d p ih =>
    intro e e' h
    cases d <;> cases e <;> simp [rewriteAt] at h
    all_goals (obtain ⟨x, hx, rfl⟩ := h; simp [eval, ih _ _ hx])

/-! ## The identities -/

/-- The fixed identities a step may apply, each in either direction. Paren removal is not
among them: the checker applies it to every equation it reads. -/
inductive Identity where
  /-- `a + b = b + a` -/
  | addComm
  /-- `a * b = b * a` -/
  | mulComm
  /-- `(a + b) + c = a + (b + c)` -/
  | addAssoc
  /-- `(a * b) * c = a * (b * c)` -/
  | mulAssoc
  /-- `a * (b + c) = a * b + a * c` -/
  | distrib
  /-- `a + 0 = a`, `0` any literal worth zero -/
  | addZero
  /-- `a * 1 = a`, `1` any literal worth one -/
  | mulOne
  /-- `-(-a) = a` -/
  | negNeg
  deriving DecidableEq, Repr, Inhabited

/-- An identity's name, as a corpus writes it. -/
def Identity.name : Identity → String
  | .addComm => "addComm" | .mulComm => "mulComm" | .addAssoc => "addAssoc"
  | .mulAssoc => "mulAssoc" | .distrib => "distrib" | .addZero => "addZero"
  | .mulOne => "mulOne" | .negNeg => "negNeg"

/-- An identity by name. -/
def Identity.ofName? (s : String) : Option Identity :=
  [Identity.addComm, .mulComm, .addAssoc, .mulAssoc, .distrib, .addZero, .mulOne, .negNeg].find? (·.name == s)

/-- Whether a literal is worth zero (one): tested when a step runs, so the identity's
soundness rests on the test, not on reading a literal in a proof. -/
def isZeroLit (s : String) : Bool := decide (Decimal.value s = some 0)
def isOneLit (s : String) : Bool := decide (Decimal.value s = some 1)

/-- The identity applied left to right (`forward`) or right to left at the root of `e`;
`none` when `e` does not have the identity's shape. -/
def Identity.apply : Identity → Bool → Expr → Option Expr
  | .addComm, _, .bin .add a b => some (.bin .add b a)
  | .mulComm, _, .bin .mul a b => some (.bin .mul b a)
  | .addAssoc, true, .bin .add (.bin .add a b) c => some (.bin .add a (.bin .add b c))
  | .addAssoc, false, .bin .add a (.bin .add b c) => some (.bin .add (.bin .add a b) c)
  | .mulAssoc, true, .bin .mul (.bin .mul a b) c => some (.bin .mul a (.bin .mul b c))
  | .mulAssoc, false, .bin .mul a (.bin .mul b c) => some (.bin .mul (.bin .mul a b) c)
  | .distrib, true, .bin .mul a (.bin .add b c) => some (.bin .add (.bin .mul a b) (.bin .mul a c))
  | .distrib, false, .bin .add (.bin .mul a b) (.bin .mul a' c) =>
      if a = a' then some (.bin .mul a (.bin .add b c)) else none
  | .addZero, true, .bin .add a (.num z) => if isZeroLit z then some a else none
  | .addZero, false, a => if isZeroLit "0" then some (.bin .add a (.num "0")) else none
  | .mulOne, true, .bin .mul a (.num u) => if isOneLit u then some a else none
  | .mulOne, false, a => if isOneLit "1" then some (.bin .mul a (.num "1")) else none
  | .negNeg, true, .neg (.neg a) => some a
  | .negNeg, false, a => some (.neg (.neg a))
  | _, _, _ => none

theorem litValue_of_isZeroLit {s : String} (h : isZeroLit s = true) : litValue s = 0 := by
  simp [isZeroLit] at h; simp [litValue, h]

theorem litValue_of_isOneLit {s : String} (h : isOneLit s = true) : litValue s = 1 := by
  simp [isOneLit] at h; simp [litValue, h]

/-- Every identity, in either direction, keeps the value of what it rewrites, under every
interpretation and assignment. -/
theorem Identity.apply_sound (I : Interp) (σ : String → Rat) (i : Identity) (fwd : Bool) :
    ∀ e e', i.apply fwd e = some e' → eval I σ e' = eval I σ e := by
  intro e e' h
  revert h
  fun_cases Identity.apply i fwd e
  all_goals
    intro h
    simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals
    subst h
    simp only [eval, binApply]
  · exact Rat.add_comm _ _
  · exact Rat.mul_comm _ _
  · exact (Rat.add_assoc _ _ _).symm
  · exact Rat.add_assoc _ _ _
  · exact (Rat.mul_assoc _ _ _).symm
  · exact Rat.mul_assoc _ _ _
  · exact (Rat.mul_add _ _ _).symm
  · exact Rat.mul_add _ _ _
  · rename_i hz; rw [litValue_of_isZeroLit hz, Rat.add_zero]
  · rename_i hz; rw [litValue_of_isZeroLit hz, Rat.add_zero]
  · rename_i hu; rw [litValue_of_isOneLit hu, Rat.mul_one]
  · rename_i hu; rw [litValue_of_isOneLit hu, Rat.mul_one]
  · exact (Rat.neg_neg _).symm
  · exact Rat.neg_neg _

/-! ## Matching a law to an instance of it

An instance of an expression is the expression with each of its identifiers replaced by
an expression (`substFn`). A literal, an operator, a function, an exponent and a
derivative `D(x, s, n)` stay as written: a derivative names identifiers but holds no
expression, and its value does not depend on the assignment. Matching (`matchExpr`)
finds the replacement that makes a pattern exactly a given expression, when there is
one. -/

/-- A substitution as matching builds it: each identifier bound with the expression it
stands for, the newest binding first. -/
abbrev Subst := List (String × Expr)

/-- What a substitution makes of an identifier: the expression bound to it, or the
identifier itself when it binds none. -/
def Subst.get (θ : Subst) (n : String) : Expr := (θ.lookup n).getD (.ident n)

/-- `θ'` keeps every binding of `θ`. -/
def Subst.Extends (θ θ' : Subst) : Prop := ∀ n e, θ.lookup n = some e → θ'.lookup n = some e

/-- `e` with each identifier `n` replaced by `f n`. -/
def substFn (f : String → Expr) : Expr → Expr
  | .num s => .num s
  | .ident n => f n
  | .neg e => .neg (substFn f e)
  | .paren e => .paren (substFn f e)
  | .bin op l r => .bin op (substFn f l) (substFn f r)
  | .pow b p q => .pow (substFn f b) p q
  | .fn g a => .fn g (substFn f a)
  | .deriv x s n => .deriv x s n

/-- `e` under a substitution: each identifier it binds replaced, the others kept. -/
def subst (θ : Subst) (e : Expr) : Expr := substFn θ.get e

/-- First-order matching: `θ` extended so that `pat` under it is exactly `e`, or `none`
when no extension does. Every identifier of `pat` is a pattern variable, and one met
twice must stand for one expression. A literal, an operator, a function, an exponent and
a derivative match only themselves. -/
def matchExpr : Expr → Expr → Subst → Option Subst
  | .ident n, e, θ =>
    match θ.lookup n with
    | some e' => if e' = e then some θ else none
    | none => some ((n, e) :: θ)
  | .num s, .num t, θ => if s = t then some θ else none
  | .neg p, .neg e, θ => matchExpr p e θ
  | .paren p, .paren e, θ => matchExpr p e θ
  | .bin op l r, .bin op' l' r', θ =>
    if op = op' then (matchExpr l l' θ).bind (matchExpr r r') else none
  | .pow b p q, .pow b' p' q', θ => if p = p' ∧ q = q' then matchExpr b b' θ else none
  | .fn f a, .fn f' a', θ => if f = f' then matchExpr a a' θ else none
  | .deriv x s n, .deriv x' s' n', θ => if x = x' ∧ s = s' ∧ n = n' then some θ else none
  | _, _, _ => none

theorem Subst.extends_refl (θ : Subst) : θ.Extends θ := fun _ _ h => h

theorem Subst.extends_trans {θ₁ θ₂ θ₃ : Subst} (h₁ : θ₁.Extends θ₂) (h₂ : θ₂.Extends θ₃) :
    θ₁.Extends θ₃ := fun n e h => h₂ n e (h₁ n e h)

theorem Subst.lookup_cons (n m : String) (e : Expr) (θ : Subst) :
    List.lookup m ((n, e) :: θ) = if m = n then some e else θ.lookup m := by
  by_cases h : m = n
  · subst h; simp [List.lookup]
  · have hb : (m == n) = false := by simpa using h
    simp [List.lookup, hb, h]

/-- What matching answers extends the substitution it started from, and under every
further extension the pattern is exactly the target. -/
theorem matchExpr_spec : ∀ (p e : Expr) (θ θ' : Subst), matchExpr p e θ = some θ' →
    θ.Extends θ' ∧ ∀ θ'', θ'.Extends θ'' → subst θ'' p = e := by
  intro p
  induction p with
  | ident n =>
    intro e θ θ' h
    simp only [matchExpr] at h
    split at h
    · rename_i e' hl
      split at h
      · rename_i he
        cases h; subst he
        refine ⟨Subst.extends_refl _, fun θ'' hx => ?_⟩
        simp [subst, substFn, Subst.get, hx n e' hl]
      · contradiction
    · rename_i hl
      cases h
      refine ⟨fun m x hm => ?_, fun θ'' hx => ?_⟩
      · rw [Subst.lookup_cons]
        by_cases hmn : m = n
        · subst hmn; rw [hl] at hm; contradiction
        · simp [hmn, hm]
      · have := hx n e (by rw [Subst.lookup_cons]; simp)
        simp [subst, substFn, Subst.get, this]
  | num s =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    split at h
    · rename_i hs; cases h; subst hs
      exact ⟨Subst.extends_refl _, fun _ _ => rfl⟩
    · contradiction
  | neg p ih =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    obtain ⟨hx, hs⟩ := ih _ θ θ' h
    exact ⟨hx, fun θ'' h'' => by simp [subst, substFn] at hs ⊢; exact hs θ'' h''⟩
  | paren p ih =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    obtain ⟨hx, hs⟩ := ih _ θ θ' h
    exact ⟨hx, fun θ'' h'' => by simp [subst, substFn] at hs ⊢; exact hs θ'' h''⟩
  | bin op l r ihl ihr =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    rename_i op' l' r'
    split at h
    · rename_i hop
      subst hop
      obtain ⟨θ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hx₁, hs₁⟩ := ihl _ θ θ₁ h₁
      obtain ⟨hx₂, hs₂⟩ := ihr _ θ₁ θ' h₂
      refine ⟨Subst.extends_trans hx₁ hx₂, fun θ'' h'' => ?_⟩
      have el := hs₁ θ'' (Subst.extends_trans hx₂ h'')
      have er := hs₂ θ'' h''
      simp only [subst, substFn] at el er ⊢
      rw [el, er]
    · contradiction
  | pow b p q ih =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    split at h
    · rename_i hpq
      obtain ⟨rfl, rfl⟩ := hpq
      obtain ⟨hx, hs⟩ := ih _ θ θ' h
      exact ⟨hx, fun θ'' h'' => by simp [subst, substFn] at hs ⊢; exact hs θ'' h''⟩
    · contradiction
  | fn f a ih =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    split at h
    · rename_i hf
      subst hf
      obtain ⟨hx, hs⟩ := ih _ θ θ' h
      exact ⟨hx, fun θ'' h'' => by simp [subst, substFn] at hs ⊢; exact hs θ'' h''⟩
    · contradiction
  | deriv x s n =>
    intro e θ θ' h
    cases e <;> simp only [matchExpr, reduceCtorEq] at h
    split at h
    · rename_i hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h
      exact ⟨Subst.extends_refl _, fun _ _ => rfl⟩
    · contradiction

/-- **The matcher is sound.** What matching answers is an instance: the pattern under
the substitution found is exactly the target. -/
theorem matchExpr_sound {p e : Expr} {θ : Subst} (h : matchExpr p e [] = some θ) :
    subst θ p = e :=
  (matchExpr_spec p e [] θ h).2 θ (Subst.extends_refl θ)

/-- Matching misses no instance: started from a substitution that agrees with `f`, it
answers one that agrees with `f`, whenever the target is the pattern's instance by `f`. -/
theorem matchExpr_complete_from (f : String → Expr) : ∀ (p : Expr) (θ : Subst),
    (∀ n e, θ.lookup n = some e → e = f n) →
    ∃ θ', matchExpr p (substFn f p) θ = some θ' ∧ ∀ n e, θ'.lookup n = some e → e = f n := by
  intro p
  induction p with
  | ident n =>
    intro θ hθ
    simp only [substFn, matchExpr]
    split
    · rename_i e' hl
      have := hθ n e' hl
      subst this
      exact ⟨θ, by simp, hθ⟩
    · refine ⟨(n, f n) :: θ, rfl, fun m e hm => ?_⟩
      rw [Subst.lookup_cons] at hm
      split at hm
      · rename_i hmn; subst hmn; cases hm; rfl
      · exact hθ m e hm
  | num s => intro θ hθ; exact ⟨θ, by simp [substFn, matchExpr], hθ⟩
  | neg p ih => intro θ hθ; simpa [substFn, matchExpr] using ih θ hθ
  | paren p ih => intro θ hθ; simpa [substFn, matchExpr] using ih θ hθ
  | bin op l r ihl ihr =>
    intro θ hθ
    obtain ⟨θ₁, h₁, hθ₁⟩ := ihl θ hθ
    obtain ⟨θ₂, h₂, hθ₂⟩ := ihr θ₁ hθ₁
    exact ⟨θ₂, by simp [substFn, matchExpr, h₁, h₂], hθ₂⟩
  | pow b p q ih => intro θ hθ; simpa [substFn, matchExpr] using ih θ hθ
  | fn g a ih => intro θ hθ; simpa [substFn, matchExpr] using ih θ hθ
  | deriv x s n => intro θ hθ; exact ⟨θ, by simp [substFn, matchExpr], hθ⟩

/-- **The matcher is complete.** Whenever the target is an instance of the pattern,
matching finds a substitution. -/
theorem matchExpr_complete {p e : Expr} (h : ∃ f, substFn f p = e) :
    (matchExpr p e []).isSome := by
  obtain ⟨f, rfl⟩ := h
  obtain ⟨θ, hθ, _⟩ := matchExpr_complete_from f p [] (by simp)
  simp [hθ]

/-- An instance is worth what the expression is worth under the assignment that gives
each identifier the value of what replaces it. -/
theorem eval_substFn (I : Interp) (σ : String → Rat) (f : String → Expr) :
    ∀ e, eval I σ (substFn f e) = eval I (fun n => eval I σ (f n)) e := by
  intro e
  induction e <;> simp [substFn, eval, *]

theorem eval_subst (I : Interp) (σ : String → Rat) (θ : Subst) (e : Expr) :
    eval I σ (subst θ e) = eval I (fun n => eval I σ (θ.get n)) e :=
  eval_substFn I σ θ.get e

/-- A cited law used by instance: the subterm matched against the law's left side
(`forward`) or right side, and the other side under the substitution found; `none` when
the subterm is no instance of that side. -/
def instanceRewrite (law : Equation) (forward : Bool) (e : Expr) : Option Expr :=
  let pat := if forward then law.lhs else law.rhs
  let other := if forward then law.rhs else law.lhs
  (matchExpr pat e []).map fun θ => subst θ other

/-- A law that holds under every assignment keeps the value of whatever an instance of it
rewrites. -/
theorem instanceRewrite_sound (I : Interp) (σ : String → Rat) (law : Equation)
    (hlaw : ∀ σ', law.holds I σ') (fwd : Bool) :
    ∀ e e', instanceRewrite law fwd e = some e' → eval I σ e' = eval I σ e := by
  intro e e' h
  unfold instanceRewrite at h
  obtain ⟨θ, hm, rfl⟩ := Option.map_eq_some_iff.mp h
  have hs := matchExpr_sound hm
  have hl := hlaw (fun n => eval I σ (θ.get n))
  unfold Equation.holds at hl
  rw [← hs, eval_subst, eval_subst]
  cases fwd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
  · exact hl
  · exact hl.symm

/-! ## The steps and the checker -/

/-- A side of an equation. -/
inductive Side where
  | lhs | rhs
  deriving DecidableEq, Repr, Inhabited

def Side.get : Side → Equation → Expr
  | .lhs, e => e.lhs
  | .rhs, e => e.rhs

def Side.set : Side → Equation → Expr → Equation
  | .lhs, e, x => { e with lhs := x }
  | .rhs, e, x => { e with rhs := x }

/-- What a step applies: a cited law, left to right (`forward`) or right to left, by exact
match (`cite`) or by an instance of it (`citeInstance`); or an identity. -/
inductive Rule where
  | cite (c : StepCitation) (forward : Bool)
  | identity (i : Identity) (forward : Bool)
  | citeInstance (c : StepCitation) (forward : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- One rewrite step: on `side`, at `path`, by `rule`, leading to `result` as stated. -/
structure Step where
  side : Side
  path : List Dir
  rule : Rule
  result : Equation
  deriving DecidableEq, Repr, Inhabited

/-- The laws a derivation may cite: each citation with the equation it names. -/
abbrev LawTable := List (StepCitation × Equation)

def lookup (laws : LawTable) (c : StepCitation) : Option Equation :=
  (laws.find? (·.1 == c)).map (·.2)

/-- A cited law used as a rewrite: exactly its left side becomes its right side (or the
reverse); no unification. -/
def lawRewrite (law : Equation) (forward : Bool) (e : Expr) : Option Expr :=
  if forward then (if e = law.lhs then some law.rhs else none)
  else (if e = law.rhs then some law.lhs else none)

/-- A step's citation, when it cites a law exactly. -/
def Step.citation? (s : Step) : Option StepCitation :=
  match s.rule with
  | .cite c _ => some c
  | .identity .. => none
  | .citeInstance .. => none

/-- A step's citation, when it cites a law by instance. -/
def Step.instanceCitation? (s : Step) : Option StepCitation :=
  match s.rule with
  | .citeInstance c _ => some c
  | _ => none

/-- The rewrite a step applies, or why it has none. -/
def ruleRewrite (laws : LawTable) : Rule → Except String (Expr → Option Expr)
  | .cite c fwd =>
    match lookup laws c with
    | some law => .ok (lawRewrite law.unparen fwd)
    | none => .error "missing-citation"
  | .identity i fwd => .ok (i.apply fwd)
  | .citeInstance c fwd =>
    match lookup laws c with
    | some law => .ok (instanceRewrite law.unparen fwd)
    | none => .error "missing-citation"

/-- One step from the current equation: the equation it leads to, or why it fails. -/
def stepOnce (laws : LawTable) (cur : Equation) (s : Step) : Except String Equation := do
  let f ← ruleRewrite laws s.rule
  match rewriteAt f s.path (s.side.get cur) with
  | none => .error "no-rewrite"
  | some x =>
    let next := s.side.set cur x
    if next = s.result.unparen then .ok next else .error "not-as-stated"

/-- The steps in order from `cur`, numbered from `i`: the last equation, or the first
failing step's number and why. -/
def runSteps (laws : LawTable) : Equation → List Step → Nat → Except (Nat × String) Equation
  | cur, [], _ => .ok cur
  | cur, s :: ss, i =>
    match stepOnce laws cur s with
    | .error w => .error (i, w)
    | .ok next => runSteps laws next ss (i + 1)

/-- The checker's verdict: accepted, or refused at a step (0 the start, `k` the `k`-th
step, one past the last step the final comparison) with a word for why. -/
inductive Verdict where
  | accepted
  | refused (step : Nat) (why : String)
  deriving DecidableEq, Repr, Inhabited

/-- Where a derivation starts: a cited law (or ASSUMPTION record), or `e = e` for an
expression `e` (reflexivity, which needs no citation). -/
inductive Start where
  | cite (c : StepCitation)
  | refl (e : Expr)
  deriving DecidableEq, Repr, Inhabited

/-- The start's citation, when it cites one. -/
def Start.citation? : Start → Option StepCitation
  | .cite c => some c
  | .refl _ => none

/-- The equation a derivation starts from, or `none` for a citation the table lacks. -/
def Start.equation? (laws : LawTable) : Start → Option Equation
  | .cite c => (lookup laws c).map Equation.unparen
  | .refl e => some ⟨unparen e, unparen e⟩

/-- Check a STRUCTURED derivation: from its start, through the steps, to the goal (the
RESULT's EQUATION). -/
def check (laws : LawTable) (start : Start) (steps : List Step) (goal : Equation) : Verdict :=
  match start.equation? laws with
  | none => .refused 0 "missing-citation"
  | some e0 =>
    match runSteps laws e0 steps 1 with
    | .error (i, w) => .refused i w
    | .ok last =>
      if last = goal.unparen then .accepted else .refused (steps.length + 1) "final-mismatch"

/-- Every exact citation a derivation makes: its start's, if any, and each step's that
cites a law exactly. -/
def citations (start : Start) (steps : List Step) : List StepCitation :=
  start.citation?.toList ++ steps.filterMap Step.citation?

/-- Every citation by instance a derivation makes, one per step that cites so. -/
def instances (steps : List Step) : List StepCitation :=
  steps.filterMap Step.instanceCitation?

/-! ## Soundness -/

theorem lawRewrite_sound (I : Interp) (σ : String → Rat) (law : Equation) (hlaw : law.holds I σ)
    (fwd : Bool) : ∀ e e', lawRewrite law fwd e = some e' → eval I σ e' = eval I σ e := by
  intro e e' h
  unfold lawRewrite at h
  cases fwd <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact hlaw
  · exact hlaw.symm

theorem Side.get_set (sd : Side) (e : Equation) (x : Expr) : sd.get (sd.set e x) = x := by
  cases sd <;> rfl

/-- A step keeps an equation holding, when the law it cites exactly (if any) holds, and
the law it cites by instance (if any) holds under every assignment. -/
theorem stepOnce_sound (I : Interp) (σ : String → Rat) (laws : LawTable) (cur next : Equation)
    (s : Step) (hcite : ∀ c, s.citation? = some c → ∀ e, lookup laws c = some e → e.holds I σ)
    (hinst : ∀ c, s.instanceCitation? = some c → ∀ e, lookup laws c = some e →
      ∀ σ', e.holds I σ')
    (hcur : cur.holds I σ) (h : stepOnce laws cur s = .ok next) : next.holds I σ := by
  unfold stepOnce at h
  have hf : ∀ f, ruleRewrite laws s.rule = .ok f → ∀ e e', f e = some e' → eval I σ e' = eval I σ e := by
    intro f hr
    cases hrule : s.rule with
    | cite c fwd =>
      rw [hrule] at hr
      simp only [ruleRewrite] at hr
      split at hr
      · rename_i law hl
        simp only [Except.ok.injEq] at hr; subst hr
        exact lawRewrite_sound I σ law.unparen
          ((Equation.holds_unparen I σ law).2 (hcite c (by simp [Step.citation?, hrule]) law hl)) fwd
      · contradiction
    | identity i fwd =>
      rw [hrule] at hr
      simp only [ruleRewrite, Except.ok.injEq] at hr; subst hr
      exact Identity.apply_sound I σ i fwd
    | citeInstance c fwd =>
      rw [hrule] at hr
      simp only [ruleRewrite] at hr
      split at hr
      · rename_i law hl
        simp only [Except.ok.injEq] at hr; subst hr
        exact instanceRewrite_sound I σ law.unparen
          (fun σ' => (Equation.holds_unparen I σ' law).2
            (hinst c (by simp [Step.instanceCitation?, hrule]) law hl σ')) fwd
      · contradiction
  cases hr : ruleRewrite laws s.rule with
  | error w => simp [hr, bind, Except.bind] at h
  | ok f =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i x hx
      split at h
      · simp only [Except.ok.injEq] at h; subst h
        have hv := rewriteAt_sound I σ f (hf f hr) s.path _ _ hx
        unfold Equation.holds at hcur ⊢
        cases hs : s.side <;> simp [hs, Side.set, Side.get] at hv ⊢ <;> simp [hv, hcur]
      · contradiction

theorem runSteps_sound (I : Interp) (σ : String → Rat) (laws : LawTable) :
    ∀ (steps : List Step) (cur last : Equation) (i : Nat),
      (∀ c ∈ steps.filterMap Step.citation?, ∀ e, lookup laws c = some e → e.holds I σ) →
      (∀ c ∈ instances steps, ∀ e, lookup laws c = some e → ∀ σ', e.holds I σ') →
      cur.holds I σ → runSteps laws cur steps i = .ok last → last.holds I σ := by
  intro steps
  induction steps with
  | nil => intro cur last i _ _ hcur h; simp [runSteps] at h; subst h; exact hcur
  | cons s ss ih =>
    intro cur last i hcite hinst hcur h
    simp only [runSteps] at h
    split at h
    · contradiction
    · rename_i next hn
      have hstep := stepOnce_sound I σ laws cur next s (by
        intro c hc e he
        exact hcite c (by simp [hc]) e he) (by
        intro c hc e he
        exact hinst c (by simp [instances, hc]) e he) hcur hn
      exact ih next last (i + 1) (by
        intro c hc e he
        exact hcite c (by
          simp only [List.filterMap_cons]
          split <;> simp_all) e he) (by
        intro c hc e he
        exact hinst c (by
          simp only [instances, List.filterMap_cons]
          split <;> simp_all [instances]) e he) hstep h

/-- **Soundness.** If the checker accepts, the goal holds under every interpretation of the
function symbols and every assignment under which all the laws the derivation cites
exactly hold, provided each law it cites by instance holds under every assignment (an
instance of a law is the law at another assignment). A derivation that cites no law by
instance needs only the first. No exception for division: it is evaluated as in the laws
themselves. -/
theorem check_sound (laws : LawTable) (start : Start) (steps : List Step) (goal : Equation)
    (h : check laws start steps goal = .accepted) (I : Interp) (σ : String → Rat)
    (hlaws : ∀ c ∈ citations start steps, ∀ e, lookup laws c = some e → e.holds I σ)
    (hinst : ∀ c ∈ instances steps, ∀ e, lookup laws c = some e → ∀ σ', e.holds I σ') :
    goal.holds I σ := by
  unfold check at h
  split at h
  · contradiction
  · rename_i e0 he0
    have h0 : e0.holds I σ := by
      cases start with
      | cite c =>
        simp only [Start.equation?, Option.map_eq_some_iff] at he0
        obtain ⟨law, hl, rfl⟩ := he0
        exact (Equation.holds_unparen I σ law).2
          (hlaws c (by simp [citations, Start.citation?]) law hl)
      | refl e =>
        simp only [Start.equation?, Option.some.injEq] at he0
        subst he0; rfl
    split at h
    · contradiction
    · rename_i last hl
      split at h
      · rename_i hg
        have hlast := runSteps_sound I σ laws steps e0 last 1
          (fun c hc => hlaws c (List.mem_append_right _ hc)) hinst h0 hl
        rw [hg] at hlast
        exact (Equation.holds_unparen I σ goal).1 hlast
      · contradiction

end Principia.StructuredCheck
