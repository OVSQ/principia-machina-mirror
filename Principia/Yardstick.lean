import Principia.Criteria
import Principia.Exact
import Principia.SR9

/-!
# The yardstick evaluator

v1's `tpc_yardstick` (TPC-PY 0.3.0, `tpc_yardstick` 0.2.0, TPS 4.5 row 17): a
yardstick declared in a Criteria Set, compiled into the SR9 entry interface
(`Principia.Strike.SR9.Entry`) and run through SR9's checks C1, C2 and C4 on the synthetic
record suite. It is the second line behind the static checks `Criteria.wellFormed` makes at
entry.

From one named yardstick of a well-formed Criteria Set it builds:
* the key of a record, a list of exact values compared lexicographically, lower closer. A
  record whose DOMAIN, after text normalization, is a LIMITING DOMAIN is keyed by that
  limiting KEY instead;
* the resolution, fixed to the framework: SR7 for an L-M pair, SR5 on the key otherwise
  (a yardstick orders, it never resolves);
* the LIMITING DOMAINs, where SR9 C2 exempts a lowered key.

The terms, on a suite record: `SR1` is 1 for a record failing SR1, else 0; `A` is `a(r)`
(SR4); `S` is `s(r)`, the record's steps; `FIELD:U_C` is the record's `U_C` from the field
table; `NEG:t` is `-t`; and `WSUM` is the sum, in canonical atom order, of each weight times
its atom, the weights read from the Criteria Set's CONSTANTS.

**Numbers.** v1 computed every value as an IEEE double. Here every value is exact (`Rat`),
the Declarer's choice of exact values. v1's two refusals that come from the double type are
kept, decided on exact values with no floating point (`overflows`, the one numeric
primitive here): a weight whose nearest double is infinite, and a value that overflows the
double range at any step v1 computes in doubles. What can still differ from v1 (none of the
corpus's cases) is recorded in the notes kept with the vectors:
* a value that v1's rounding pushes over or under the threshold, near 2^1024;
* a magnitude below the least double, which v1 rounded to zero and is kept here, so it can
  separate keys v1 found equal;
* a value v1 rounded at all, which can order two keys differently;
* `steps` of 2^1024 or more, where v1 raised and the Calculator refuses.

**Text.** As v1, a refusal's text is escaped by general category (`Zone.escape`), and a
record's DOMAIN is compared with a yardstick's LIMITING DOMAINs after v1's `_text` of each,
line endings as LF and NFC (`Zone.text`), at Unicode 15.1.0. A
result is owed, never a pass, only when the Criteria Set's verdict is owed
(`Criteria.wellFormed`).

Vectors: the yardstick corpus, run by the yardstick test runner.
-/

namespace Principia.Yardstick

open Principia.Zone

/-! ## Numbers -/

/-- `|x|`. -/
def absR (x : Rat) : Rat := if x < 0 then -x else x

/-- Whether v1's double of `x` was an infinity: `|x|` at or above `Exact.overflowBound`
(2^1024 - 2^970, the double range's bound, kept with the other in `Principia.Exact`)
rounds to one. The one numeric primitive of this file; the rest is `Rat`'s own field
operations. -/
def overflows (x : Rat) : Bool := decide ((Exact.overflowBound : Rat) ≤ absR x)

/-! ## Results -/

/-- Why a result is owed. -/
inductive Owed where
  /-- The Criteria Set's verdict is owed: the zones' reason. -/
  | zone (o : Zone.Owed)
  deriving DecidableEq, Repr

/-- The owed result's text. -/
def Owed.message : Owed → String
  | .zone o => o.message

/-- Where an evaluation stops: v1's refusal, an owed result, or v1's exception (a record
the suite lacks, or a TMS part a well-formed one always has). -/
inductive Stop where
  /-- v1's `["REFUSED", reason]`. -/
  | refused (reason : String)
  /-- Not judged: what the Calculator still lacks. -/
  | owed (why : Owed)
  /-- v1 raised. -/
  | raised
  deriving DecidableEq, Repr

/-- A refusal whose text v1 escaped with `_show`. -/
def refuseShown (msg : String) : Stop := .refused (escape msg)

/-- A yardstick function's result: v1's `["OK", ...]` or `["REFUSED", reason]`, or owed. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | refused (reason : String)
  | owed (why : Owed)
  deriving Repr

/-- The outcome of an evaluation; `none` where v1 raised. -/
def Outcome.of {α : Type} : Except Stop α → Option (Outcome α)
  | .ok a => some (.ok a)
  | .error (.refused r) => some (.refused r)
  | .error (.owed o) => some (.owed o)
  | .error .raised => none

/-! ## Compiled terms -/

/-- An atom of a term. -/
inductive Atom where
  /-- `SR1`: 1 for a record failing SR1, else 0. -/
  | sr1
  /-- `A`: `a(r)`. -/
  | a
  /-- `S`: `s(r)`. -/
  | s
  /-- `FIELD:U_C`: the record's U_C from the field table. -/
  | uC
  deriving DecidableEq, Repr

/-- The body of a term: one atom, or a weighted sum in canonical atom order. -/
inductive Body where
  | atom (x : Atom)
  | wsum (parts : List (Rat × Atom))
  deriving DecidableEq, Repr

/-- A compiled term: its body, negated or not. -/
structure Term where
  neg : Bool
  body : Body
  deriving DecidableEq, Repr

/-- The term `SR1`. -/
def sr1Term : Term := ⟨false, .atom .sr1⟩

/-- An atom's text, as a well-formed term spells it. -/
def atomOf? : String → Option Atom
  | "SR1" => some .sr1
  | "A" => some .a
  | "S" => some .s
  | "FIELD:U_C" => some .uC
  | _ => none

/-- A FIELD atom other than `FIELD:U_C` is refused: the field table holds U_C alone. -/
def fieldOk (a : String) : Except Stop Unit :=
  if a.startsWith "FIELD:" && a != "FIELD:U_C" then
    throw (refuseShown ("FIELD " ++ (a.drop 6).toString ++ " is not in the field table"))
  else pure ()

/-- One weighted atom `(atom, constant)`: the constant's VALUE, refused when its double is
infinite, and the atom. -/
def compileWeighted (weights : List (String × String)) (wt : String × String) :
    Except Stop (Rat × Atom) := do
  let some v := weights.lookup wt.2 | throw .raised
  let some w := Decimal.value v | throw .raised
  if overflows w then throw (.refused ("weight " ++ wt.2 ++ " is not a finite double"))
  let some x := atomOf? wt.1 | throw .raised
  pure (w, x)

/-- A term's base, the part after its `NEG:` prefixes, read in `Criteria.parseBase`'s order.
A WSUM's weighted atoms are put in canonical order (`Criteria.insertWt`, the order of the
canonical spelling v1 split again). Every FIELD atom other than `FIELD:U_C` is refused first,
then each weight is read from the CONSTANTS. -/
def compileBase (weights : List (String × String)) (base : String) : Except Stop Body := do
  if base == "SR1" then pure (.atom .sr1)
  else if base == "S" then pure (.atom .s)
  else if base == "A" then pure (.atom .a)
  else if base.startsWith "FIELD:" then do
    fieldOk base
    let some x := atomOf? base | throw .raised
    pure (.atom x)
  else if base.startsWith "WSUM:" then
    match Criteria.readWts ((base.drop 5).toString.splitOn ";") [] with
    | some wts =>
      let sorted := wts.foldl (fun acc w => Criteria.insertWt w acc) []
      for wt in sorted do fieldOk wt.1
      let parts ← sorted.mapM (compileWeighted weights)
      pure (.wsum parts)
    | none => throw .raised
  else throw .raised

/-- v1's `_compile_term` on `canonical_term(t)`. The term is read as `Criteria.parseTerm`
reads it: its `NEG:` prefixes counted (an odd count negates), then the base
(`compileBase`). A well-formed term is ASCII with no CR, so v1's text normalization leaves
it unchanged; a malformed one never reaches here (`Criteria.wellFormed`), and is `raised`. -/
def compileTerm (weights : List (String × String)) (t : String) : Except Stop Term := do
  let (n, b) := Criteria.stripNeg t.toList
  let body ← compileBase weights (String.ofList b)
  pure ⟨n % 2 == 1, body⟩

/-- A yardstick, compiled: its main KEY's terms and each LIMITING DOMAIN's, in declared
order, each beginning with `SR1` (the grammar's rule, which `Criteria.wellFormed` checks
and the compiler checks again: SR9 C1 rests on it). -/
structure Compiled where
  main : List Term
  limiting : List (String × List Term)
  main_head : main.head? = some sr1Term
  limiting_head : ∀ p ∈ limiting, p.2.head? = some sr1Term

/-- The LIMITING DOMAINs, as v1's entry lists them: sorted, each once. -/
def Compiled.domains (y : Compiled) : List String :=
  (y.limiting.map (·.1)).eraseDups.mergeSort Strike.idLe

/-! ## Reading the Criteria Set -/

/-- The objects of a part that holds a list. -/
def objects : Option Value → List Entry
  | some (.arr xs) => xs.filterMap fun | .obj o => some o | _ => none
  | _ => []

/-- The Criteria Set's CONSTANTS by NAME, read as `Criteria.problems` reads them: the first
constant of a NAME gives its VALUE. v1's `dict` kept the last; a well-formed Criteria Set
has no NAME twice, so the two agree wherever a yardstick is compiled. -/
def constants (tms : Value) : List (String × String) :=
  match tms with
  | .obj z => (entries "TMS CONSTANTS" ((get? z "CONSTANTS").getD (.arr []))).1.filterMap fun e =>
      match getStr? e "NAME", getStr? e "VALUE" with
      | some n, some v => some (n, v)
      | _, _ => none
  | _ => []

/-- The first yardstick whose NAME is `name`, compared as written, among the yardsticks
`Criteria.problems` checks. -/
def findYardstick (tms : Value) (name : String) : Option Entry :=
  match tms with
  | .obj z => (entries "TMS YARDSTICKS" ((get? z "YARDSTICKS").getD (.arr []))).1.find?
      (getStr? · "NAME" == some name)
  | _ => none

/-- A yardstick's main KEY, as `Criteria.yardstickProblems` checks it: the strings of a KEY
of the right type (a well-formed yardstick's KEY always is). -/
def keyTerms (y : Entry) : List String :=
  match get? y "KEY" with
  | some v => if typeOk "KEY" v then strItems v else []
  | none => []

/-- v1's `_build`, without its key: refused when the Criteria Set is not well formed or
names no such yardstick, owed when its verdict is owed. The Criteria Set's checks never
consult `units`, which `Criteria.wellFormed` takes for the other zones. -/
def compile (units : UnitHook) (tms : Value) (name : String) : Except Stop Compiled := do
  match Criteria.wellFormed units tms with
  | .owed o => throw (.owed (.zone o))
  | .checked ps => if !ps.isEmpty then throw (.refused "TMS is not well-formed")
  let some y := findYardstick tms name | throw (refuseShown ("no yardstick named " ++ name))
  let weights := constants tms
  let main ← (keyTerms y).mapM (compileTerm weights)
  let limiting ← (objects (get? y "LIMITING")).mapM fun le => do
    let some d := getStr? le "DOMAIN" | throw .raised
    let terms ← (strItems ((get? le "KEY").getD (.arr []))).mapM (compileTerm weights)
    pure (text d, terms)
  -- A well-formed KEY begins with SR1 (`Criteria.checkKey`), so this never refuses.
  if h : main.head? = some sr1Term ∧ ∀ p ∈ limiting, p.2.head? = some sr1Term then
    pure ⟨main, limiting, h.1, h.2⟩
  else throw (.refused "TMS is not well-formed")

/-! ## Values -/

/-- What a key reads of a record: whether it fails SR1, `a(r)` (`none` where SR4 raised),
its steps, and the U_C its field-table row holds, if the row holds a string. -/
structure View where
  sr1Fail : Bool
  a : Option Nat
  steps : Nat
  uC : Option String

/-- A U_C cell's value: a string that is its own canonical decimal (v1: `type(v) is str and
canon_decimal(v) == v`). -/
def uCValue : Option String → Option Rat
  | some u => if Decimal.canon u == some u then Decimal.value u else none
  | none => none

/-- An atom's value on a record. -/
def atomValue (rid : String) (v : View) : Atom → Except Stop Rat
  | .sr1 => pure (if v.sr1Fail then 1 else 0)
  | .a => match v.a with
    | some n => pure n
    | none => throw .raised
  | .s => pure v.steps
  | .uC => match uCValue v.uC with
    | some q => pure q
    | none => throw (refuseShown ("FIELD U_C has no value for " ++ rid))

/-- A value as v1 accumulated it: the exact value, and whether any step v1 computed in
doubles overflowed (an infinity or NaN there, which no later step makes finite). -/
structure Acc where
  value : Rat
  over : Bool

/-- One weighted atom added: the atom, the product and the sum are each one of v1's
doubles. -/
def Acc.add (acc : Acc) (w x : Rat) : Acc :=
  let p := w * x
  let s := acc.value + p
  ⟨s, acc.over || overflows x || overflows p || overflows s⟩

/-- A body's value from its atoms' values, as v1 accumulated it. -/
def Body.acc : Body → (Atom → Rat) → Acc
  | .atom x, val => ⟨val x, overflows (val x)⟩
  | .wsum parts, val => parts.foldl (fun acc (w, x) => acc.add w (val x)) ⟨0, false⟩

/-- The atoms a body reads, in v1's order. -/
def Body.atoms : Body → List Atom
  | .atom x => [x]
  | .wsum parts => parts.map (·.2)

/-- An atom's value where it has one, 0 elsewhere: the valuation a term's value is
computed from once its atoms are read. -/
def valuation (rid : String) (v : View) (x : Atom) : Rat :=
  match atomValue rid v x with
  | .ok q => q
  | .error _ => 0

/-- v1's `_value`: a term's value on a record, refused when it is not finite as a double.
The atoms are read in order, so a missing U_C is refused before an overflow in the same term
is; the value is then the body's, negated for `NEG:`. -/
def termValue (rid : String) (v : View) (t : Term) : Except Stop Rat := do
  let _ ← t.body.atoms.mapM (atomValue rid v)
  let acc := t.body.acc (valuation rid v)
  if acc.over then throw (.refused "a yardstick value is not finite")
  pure (if t.neg then -acc.value else acc.value)

/-- The terms keying a record of DOMAIN `domain`: a LIMITING KEY when the DOMAIN, after v1's
`_text` (line endings, then NFC), is that LIMITING DOMAIN, itself after `_text` (`compile`);
the main KEY otherwise. It never stops; the record's identifier is the evaluation's. -/
def termsFor (y : Compiled) (_rid domain : String) : Except Stop (List Term) :=
  if y.limiting.isEmpty then pure y.main
  else pure (((y.limiting.reverse).lookup (text domain)).getD y.main)

/-- The key of a record: its terms' values, in order. -/
def keyOfView (y : Compiled) (rid domain : String) (v : View) : Except Stop (List Rat) := do
  let terms ← termsFor y rid domain
  terms.mapM (termValue rid v)

/-! ## Every key begins with the record's SR1 rank -/

/-- 0 and 1 are far inside the double range. -/
theorem overflows_sr1 (b : Bool) : overflows (if b then 1 else 0) = false := by
  cases b <;> decide +kernel

/-- What `lookup` finds is in the list. -/
theorem mem_of_lookup {α β : Type} [BEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → ∃ k, (k, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; exact ⟨k, List.mem_cons_self ..⟩
    · obtain ⟨k', hk⟩ := mem_of_lookup h
      exact ⟨k', List.mem_cons_of_mem _ hk⟩

/-- The term `SR1` is the record's SR1 rank, 1 when it fails SR1 and 0 when it passes. -/
theorem termValue_sr1 (rid : String) (v : View) :
    termValue rid v sr1Term = .ok (if v.sr1Fail then 1 else 0) := by
  have h := overflows_sr1 v.sr1Fail
  cases hf : v.sr1Fail <;>
    simp_all [termValue, sr1Term, Body.atoms, Body.acc, valuation, atomValue, List.mapM_cons,
      List.mapM_nil, bind, Except.bind, pure, Except.pure]

/-- The terms keying a record begin with `SR1`. -/
theorem termsFor_head {y : Compiled} {rid domain : String} {ts : List Term}
    (h : termsFor y rid domain = .ok ts) : ts.head? = some sr1Term := by
  unfold termsFor at h
  split at h
  · cases h; exact y.main_head
  · cases h
    cases hl : (y.limiting.reverse).lookup (text domain) with
    | none => simp only [Option.getD_none]; exact y.main_head
    | some ts' =>
      simp only [Option.getD_some]
      obtain ⟨k, hk⟩ := mem_of_lookup hl
      exact y.limiting_head (k, ts') (List.mem_reverse.mp hk)

/-- A key begins with the record's SR1 rank. -/
theorem keyOfView_head {y : Compiled} {rid domain : String} {v : View} {k : List Rat}
    (h : keyOfView y rid domain v = .ok k) :
    ∃ ks, k = (if v.sr1Fail then 1 else 0) :: ks := by
  unfold keyOfView at h
  cases ht : termsFor y rid domain with
  | error e => simp [ht, bind, Except.bind] at h
  | ok ts =>
    have hh := termsFor_head ht
    match ts, hh with
    | t :: rest, hh =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [ht, bind, Except.bind, List.mapM_cons, termValue_sr1, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i ks _
        cases h
        exact ⟨ks, rfl⟩

/-! ## How a key moves with A -/

/-- The weight sum of a WSUM's A parts, added to `c`. -/
def aWeights (parts : List (Rat × Atom)) (c : Rat) : Rat :=
  parts.foldl (fun c p => if p.2 = .a then c + p.1 else c) c

/-- A's coefficient in a term: how far its value moves when `a(r)` moves by one. -/
def Term.aCoef (t : Term) : Rat :=
  let c := match t.body with
    | .atom x => if x = .a then 1 else 0
    | .wsum parts => aWeights parts 0
  if t.neg then -c else c

/-- The static rule of SR9 C2 (`Criteria.checkKey` with `c2`, on a main KEY): the first term
whose value moves with A moves up with it. -/
def staticC2 : List Term → Bool
  | [] => true
  | t :: ts => if t.aCoef = 0 then staticC2 ts else decide (0 < t.aCoef)

/-- The static rule on the corpus's keys: `SR1, A, S` passes; `SR1, NEG:A` (more is better)
fails; a WSUM is judged by its A weight's sign; a key no term of which moves with A passes. -/
example : staticC2 [sr1Term, ⟨false, .atom .a⟩, ⟨false, .atom .s⟩] = true := by decide
example : staticC2 [sr1Term, ⟨true, .atom .a⟩] = false := by decide
example : staticC2 [sr1Term, ⟨false, .wsum [(1, .a), (1 / 2, .s)]⟩] = true := by decide +kernel
example : staticC2 [sr1Term, ⟨false, .wsum [(-1, .a)]⟩, ⟨false, .atom .a⟩] = false := by decide +kernel
example : staticC2 [sr1Term, ⟨false, .atom .uC⟩, ⟨true, .atom .s⟩] = true := by decide

/-- A term's value from a valuation of its atoms. -/
def Term.valueWith (t : Term) (val : Atom → Rat) : Rat :=
  let acc := t.body.acc val
  if t.neg then -acc.value else acc.value

/-- A term that has a value has the value its valuation gives. -/
theorem termValue_ok {rid : String} {v : View} {t : Term} {q : Rat}
    (h : termValue rid v t = .ok q) : q = t.valueWith (valuation rid v) := by
  unfold termValue at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · cases h; rfl

/-- A weighted sum's value: the starting value plus each weight times its atom. -/
theorem foldl_add_value (parts : List (Rat × Atom)) (val : Atom → Rat) (acc : Acc) :
    (parts.foldl (fun acc p => acc.add p.1 (val p.2)) acc).value =
      parts.foldl (fun s p => s + p.1 * val p.2) acc.value := by
  induction parts generalizing acc with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- Two weighted sums over valuations that differ only at A differ by A's weights times
that difference. -/
theorem foldl_sum_diff (parts : List (Rat × Atom)) (val val' : Atom → Rat)
    (hv : ∀ x, x ≠ .a → val' x = val x) (s s' c : Rat) :
    parts.foldl (fun s p => s + p.1 * val' p.2) s' - parts.foldl (fun s p => s + p.1 * val p.2) s =
      (s' - s) + (aWeights parts c - c) * (val' .a - val .a) := by
  induction parts generalizing s s' c with
  | nil => simp [aWeights]; grind
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (s + p.1 * val p.2) (s' + p.1 * val' p.2) (if p.2 = .a then c + p.1 else c)]
    unfold aWeights
    simp only [List.foldl_cons]
    by_cases hx : p.2 = .a
    · rw [hx]; simp only [ite_true]; grind
    · rw [hv _ hx]; simp only [hx, ite_false]; grind

/-- A term's value moves with A by exactly A's coefficient: over two valuations that differ
only at A, the values differ by the coefficient times that difference. -/
theorem valueWith_diff (t : Term) (val val' : Atom → Rat) (hv : ∀ x, x ≠ .a → val' x = val x) :
    t.valueWith val' - t.valueWith val = t.aCoef * (val' .a - val .a) := by
  have hb : (t.body.acc val').value - (t.body.acc val).value =
      (match t.body with
        | .atom x => if x = .a then (1 : Rat) else 0
        | .wsum parts => aWeights parts 0) * (val' .a - val .a) := by
    cases hbody : t.body with
    | atom x =>
      simp only [Body.acc]
      by_cases hx : x = .a
      · subst hx; simp
      · rw [hv x hx]; simp [hx]; grind
    | wsum parts =>
      simp only [Body.acc]
      rw [foldl_add_value, foldl_add_value]
      have := foldl_sum_diff parts val val' hv 0 0 0
      grind
  unfold Term.valueWith Term.aCoef
  cases hn : t.neg
  · simp only [Bool.false_eq_true, ite_false]; exact hb
  · simp only [ite_true]; grind

/-! ## A decimal's sign, two ways

`Criteria.aSign` reads a weight's sign from its canonical spelling (`Decimal.sign`); the
compiled term holds its exact value (`Decimal.value`). The two agree (`rsign_value`). -/

/-- The sign of a rational: 1, -1 or 0. -/
def rsign (q : Rat) : Int := if 0 < q then 1 else if q < 0 then -1 else 0

/-- What `span`'s loop keeps is what it was given, or what passes the test. -/
theorem span_loop_fst {p : Char → Bool} :
    ∀ (l acc : List Char), ∀ c ∈ (List.span.loop p l acc).1, c ∈ acc ∨ p c = true
  | [], acc, c, h => by simp [List.span.loop] at h; exact .inl h
  | a :: as, acc, c, h => by
    simp only [List.span.loop] at h
    split at h
    · rename_i hp
      rcases span_loop_fst as (a :: acc) c h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr hp
        · exact .inl h
      · exact .inr h
    · simp at h; exact .inl h

/-- What `span` keeps passes the test. -/
theorem span_fst {p : Char → Bool} {l : List Char} : ∀ c ∈ (l.span p).1, p c = true := by
  intro c h
  rcases span_loop_fst l [] c h with h | h
  · simp at h
  · exact h

/-- What `span` keeps passes the test, read from its result. -/
theorem span_eq_fst {l a b : List Char} (h : l.span Char.isDigit = (a, b)) :
    ∀ c ∈ a, c.isDigit = true :=
  fun c hm => span_fst (l := l) c (by rw [h]; exact hm)

/-- A decimal's digits are digits. -/
theorem readParts_digits {cs : List Char} {p : Decimal.Parts} (h : Decimal.readParts cs = some p) :
    ∀ c ∈ p.ip ++ p.fp, c.isDigit = true := by
  unfold Decimal.readParts at h
  repeat' split at h
  all_goals first
    | cases h
    | obtain ⟨ex, -, rfl⟩ := Option.map_eq_some_iff.mp h
      intro c hm
      simp only [List.append_nil, List.mem_append] at hm
      first
        | exact span_eq_fst (by assumption) c hm
        | rcases hm with hm | hm <;> exact span_eq_fst (by assumption) c hm

/-- A digit whose value is 0 is `'0'`. -/
theorem digit_zero {c : Char} (hd : c.isDigit = true) (h0 : c.toNat - '0'.toNat = 0) : c = '0' := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  apply Char.ext
  apply UInt32.toNat_inj.mp
  have h1 : '0'.val.toNat ≤ c.val.toNat := hd.1
  have h2 : c.toNat - '0'.toNat = 0 := h0
  simp only [Char.toNat] at h2
  omega

/-- Digits read as zero exactly when every one is `'0'` and nothing came before them. -/
theorem ofDigitChars_eq_zero : ∀ (l : List Char) (init : Nat), (∀ c ∈ l, c.isDigit = true) →
    (Nat.ofDigitChars 10 l init = 0 ↔ init = 0 ∧ ∀ c ∈ l, c = '0')
  | [], init, _ => by simp [Nat.ofDigitChars]
  | c :: l, init, hd => by
    have ih := ofDigitChars_eq_zero l (10 * init + (c.toNat - '0'.toNat))
      (fun c' h => hd c' (List.mem_cons_of_mem _ h))
    simp only [Nat.ofDigitChars, List.foldl_cons] at ih ⊢
    rw [ih]
    have hc := hd c (List.mem_cons_self ..)
    constructor
    · rintro ⟨h0, hl⟩
      refine ⟨by omega, ?_⟩
      intro c' hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact digit_zero hc (by omega)
      · exact hl c' hm
    · rintro ⟨rfl, hl⟩
      have := hl c (List.mem_cons_self ..)
      subst this
      exact ⟨by decide, fun c' h => hl c' (List.mem_cons_of_mem _ h)⟩

/-- Dropping the leading zeros leaves nothing exactly when every character is `'0'`. -/
theorem dropWhile_zero_eq_nil : ∀ (l : List Char),
    l.dropWhile (fun c => decide (c = '0')) = [] ↔ ∀ c ∈ l, c = '0'
  | [] => by simp
  | c :: l => by
    have ih := dropWhile_zero_eq_nil l
    by_cases hc : c = '0'
    · subst hc; simp [ih]
    · simp [hc]

/-- A list whose last element fails the test is not all taken by `takeWhile`. -/
theorem takeWhile_length_lt {p : Char → Bool} : ∀ {l : List Char} {a : Char},
    p a = false → ((l ++ [a]).takeWhile p).length < (l ++ [a]).length
  | [], a, h => by simp [h]
  | b :: l, a, h => by
    simp only [List.cons_append, List.takeWhile, List.length_cons]
    split
    · simp only [List.length_cons]
      have := takeWhile_length_lt (l := l) h
      omega
    · simp

/-- The canonical spelling of a decimal whose digits are not all zero: a minus sign exactly
when it is negative, and never `0`. -/
theorem canonChars_sign {p : Decimal.Parts} (hd : ∀ c ∈ p.ip ++ p.fp, c.isDigit = true)
    (hne : (Decimal.significant p).1 ≠ []) :
    Decimal.canonChars p ≠ ['0'] ∧ (['-'] <+: Decimal.canonChars p ↔ p.neg = true) := by
  unfold Decimal.canonChars
  generalize hsig : Decimal.significant p = sig
  obtain ⟨ds, t⟩ := sig
  rw [hsig] at hne
  simp only at hne ⊢
  simp only [hne, ite_false]
  -- ds is the digits after the leading zeros: its first is a digit other than '0'.
  have hds : ds = (p.ip ++ p.fp).dropWhile (fun c => decide (c = '0')) := by
    unfold Decimal.significant at hsig; simp only [Prod.mk.injEq] at hsig; exact hsig.1.symm
  have hht : t = (ds.reverse.takeWhile (fun c => decide (c = '0'))).length := by
    unfold Decimal.significant at hsig; simp only [Prod.mk.injEq] at hsig; rw [← hsig.2, hds]
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have hd0 : d ≠ '0' := by
    have := List.head_dropWhile_not (fun c => decide (c = '0')) (l := p.ip ++ p.fp)
      (by rw [← hds]; simp)
    simp only [← hds, List.head_cons, decide_eq_false_iff_not] at this
    exact this
  have hdig : d.isDigit = true := by
    have hsub : d ∈ p.ip ++ p.fp := by
      have : d ∈ (p.ip ++ p.fp).dropWhile (fun c => decide (c = '0')) := by
        rw [← hds]; exact List.mem_cons_self ..
      have hte := List.takeWhile_append_dropWhile (p := fun c => decide (c = '0'))
        (l := p.ip ++ p.fp)
      rw [← hte]; exact List.mem_append_right _ this
    exact hd d hsub
  have hdm : d ≠ '-' := fun h => by subst h; simp [Char.isDigit] at hdig
  have htl : t < (d :: ds').length := by
    rw [hht, List.reverse_cons]
    have := takeWhile_length_lt (p := fun c => decide (c = '0')) (l := ds'.reverse) (a := d)
      (by simp [hd0])
    simpa using this
  obtain ⟨k, hk⟩ : ∃ k, (d :: ds').length - t = k + 1 := ⟨(d :: ds').length - t - 1, by omega⟩
  rw [hk, List.take_succ_cons]
  cases hn : p.neg
  · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
    refine ⟨fun h => hd0 (List.cons.inj h).1, ?_⟩
    simp only [List.cons_prefix_cons, iff_false, not_and]
    intro h; exact absurd h.symm hdm
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine ⟨fun h => by simp at h, ?_⟩
    simp [List.cons_prefix_cons]

/-- **A weight's sign, two ways.** The sign of a decimal's exact value is the sign
`Decimal.sign` reads from its canonical spelling. -/
theorem rsign_value {v : String} {w : Rat} (h : Decimal.value v = some w) :
    rsign w = Decimal.sign v := by
  unfold Decimal.value at h
  cases hp : Decimal.readParts v.toList with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst h
    have hd := readParts_digits hp
    have hpos : 0 < Decimal.pow10 (p.ex - p.fp.length) := Rat.zpow_pos (by decide)
    unfold Decimal.sign Decimal.canon
    simp only [hp, Option.map_some]
    by_cases hz : (Decimal.significant p).1 = []
    · -- every digit is '0': the value is 0 and the spelling is "0"
      have hall : ∀ c ∈ p.ip ++ p.fp, c = '0' := by
        unfold Decimal.significant at hz; exact (dropWhile_zero_eq_nil _).mp hz
      have hm : Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 = 0 := ((ofDigitChars_eq_zero _ 0 hd).mpr ⟨rfl, hall⟩)
      have hc : Decimal.canonChars p = ['0'] := by
        unfold Decimal.canonChars
        generalize hsig : Decimal.significant p = sig at hz
        obtain ⟨ds, t⟩ := sig
        simp only at hz ⊢
        simp [hz]
      rw [hc, hm]
      simp [rsign]
    · obtain ⟨hn0, hneg⟩ := canonChars_sign hd hz
      have hm : Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 ≠ 0 := by
        intro h0
        have := ((ofDigitChars_eq_zero _ 0 hd).mp h0).2
        exact hz (by unfold Decimal.significant; exact (dropWhile_zero_eq_nil _).mpr this)
      have hmpos : (0 : Rat) < (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) := by
        exact_mod_cast Nat.pos_of_ne_zero hm
      have hprod : 0 < ((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
          Decimal.pow10 (p.ex - p.fp.length) := Rat.mul_pos hmpos hpos
      have hs0 : String.ofList (Decimal.canonChars p) ≠ "0" := by
        intro h
        apply hn0
        have : String.ofList (Decimal.canonChars p) = String.ofList ['0'] := h
        exact String.ofList_inj.mp this
      simp only [hs0, ite_false]
      have hsw : (String.ofList (Decimal.canonChars p)).startsWith "-" = p.neg := by
        cases hn : p.neg
        · rw [String.startsWith_string_eq_false_iff]
          simp only [String.toList_ofList]
          intro h; exact absurd (hneg.mp h) (by simp [hn])
        · rw [String.startsWith_string_iff]
          simp only [String.toList_ofList]
          exact hneg.mpr hn
      rw [hsw]
      cases hn : p.neg
      · simp [rsign, hprod]
      · have : ¬ (0 < -(((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            Decimal.pow10 (p.ex - p.fp.length))) := by grind
        have h2 : -(((Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat) : Rat) *
            Decimal.pow10 (p.ex - p.fp.length)) < 0 := by grind
        simp [rsign, this, h2]

/-! ## The static rule, two ways

`Criteria.checkKey` decides SR9 C2 on a main KEY's spelling, reading each weight's sign from
its constant's canonical spelling (`Criteria.aSign`); `staticC2` decides it on the compiled
terms, from A's exact coefficient. On every yardstick `compile` accepts, the two agree: its
compiled main KEY passes `staticC2` (`compile_staticC2`). -/

/-- A body's A coefficient: how far its value moves when `a(r)` moves by one. -/
def Body.aCoef : Body → Rat
  | .atom x => if x = .a then 1 else 0
  | .wsum parts => aWeights parts 0

theorem Term.aCoef_eq (t : Term) : t.aCoef = if t.neg then -t.body.aCoef else t.body.aCoef := by
  obtain ⟨neg, body⟩ := t
  cases body <;> rfl

/-- The atom `A` is spelled `A`. -/
theorem atomOf_a {s : String} {x : Atom} (h : atomOf? s = some x) : x = .a ↔ s = "A" := by
  unfold atomOf? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp_all

/-- A weighted atom that compiles: its constant has a VALUE, the weight is that VALUE's exact
value, and the atom is the one spelled. -/
theorem compileWeighted_ok {weights : List (String × String)} {wt : String × String}
    {w : Rat} {x : Atom} (h : compileWeighted weights wt = .ok (w, x)) :
    ∃ v, weights.lookup wt.2 = some v ∧ Decimal.value v = some w ∧ atomOf? wt.1 = some x := by
  unfold compileWeighted at h
  cases hl : weights.lookup wt.2 with
  | none => simp [hl, throw, throwThe, MonadExceptOf.throw] at h
  | some v =>
    cases hv : Decimal.value v with
    | none => simp [hl, hv, throw, throwThe, MonadExceptOf.throw] at h
    | some w' =>
      cases ha : atomOf? wt.1 with
      | none =>
        simp [hl, hv, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        split at h <;> cases h
      | some x' =>
        simp [hl, hv, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
          Except.pure] at h
        split at h
        · cases h
        · cases h; exact ⟨v, rfl, hv, rfl⟩

/-- A's weight in a compiled WSUM: nothing when no weighted atom is A, and the weight's exact
value when one is. -/
theorem aWeights_mapM {weights : List (String × String)} :
    ∀ {l : List (String × String)} {parts : List (Rat × Atom)} (c : Rat),
      l.mapM (compileWeighted weights) = .ok parts →
      (l.filter (·.1 == "A") = [] → aWeights parts c = c) ∧
      (∀ x, l.filter (·.1 == "A") = [x] →
        ∃ v w, weights.lookup x.2 = some v ∧ Decimal.value v = some w ∧ aWeights parts c = c + w)
  | [], parts, c, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [aWeights]
  | wt :: l, parts, c, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i wx hwx
      split at h
      · cases h
      · rename_i parts' hparts
        cases h
        obtain ⟨w, x⟩ := wx
        obtain ⟨v, hl, hv, hx⟩ := compileWeighted_ok hwx
        have hxa := atomOf_a hx
        have step : aWeights ((w, x) :: parts') c = aWeights parts' (if x = .a then c + w else c) := by
          simp [aWeights]
        rw [step]
        by_cases ha : (wt.1 == "A") = true
        · have hx' : x = .a := hxa.mpr (by simpa using ha)
          simp only [List.filter_cons, ha, hx', ite_true]
          refine ⟨fun h => absurd h (List.cons_ne_nil _ _), ?_⟩
          intro y hy
          simp only [List.cons.injEq] at hy
          obtain ⟨rfl, hnil⟩ := hy
          exact ⟨v, w, hl, hv, (aWeights_mapM (c + w) hparts).1 hnil⟩
        · have hx' : x ≠ .a := fun he => ha (by simp [hxa.mp he])
          have ha' : (wt.1 == "A") = false := by simpa using ha
          simp only [List.filter_cons, ha', hx', Bool.false_eq_true, ite_false]
          exact aWeights_mapM c hparts

/-- A WSUM's weighted atoms name each atom once. -/
theorem readWts_nodup : ∀ {l seen : List String} {wts : List (String × String)},
    Criteria.readWts l seen = some wts → (wts.map (·.1)).Nodup ∧ ∀ wt ∈ wts, wt.1 ∉ seen
  | [], seen, wts, h => by
    simp only [Criteria.readWts, Option.some.injEq] at h
    subst h
    simp
  | wt :: l, seen, wts, h => by
    simp only [Criteria.readWts] at h
    split at h
    · rename_i c a _
      split at h
      · cases h
      · rename_i hc
        obtain ⟨wts', h', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ih1, ih2⟩ := readWts_nodup h'
        have hsa : a ∉ seen := fun hm => hc (by simp [hm])
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih1⟩
          intro hm
          obtain ⟨x, hx, hxa⟩ := List.mem_map.mp hm
          exact ih2 x hx (by rw [hxa]; exact List.mem_cons_self ..)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hsa
          · exact fun hm => ih2 x hx (List.mem_cons_of_mem _ hm)
    · cases h

/-- With each atom named once, at most one weighted atom is A. -/
theorem filter_A_cases : ∀ {wts : List (String × String)}, (wts.map (·.1)).Nodup →
    wts.filter (·.1 == "A") = [] ∨ ∃ x, wts.filter (·.1 == "A") = [x]
  | [], _ => .inl rfl
  | wt :: ws, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases ha : (wt.1 == "A") = true
    · right
      refine ⟨wt, ?_⟩
      simp only [List.filter_cons, ha, ite_true, List.cons.injEq, true_and]
      apply List.filter_eq_nil_iff.mpr
      intro x hx hxa
      apply hnd.1
      have h1 : wt.1 = "A" := by simpa using ha
      have h2 : x.1 = "A" := by simpa using hxa
      exact List.mem_map.mpr ⟨x, hx, by rw [h1, h2]⟩
    · have ha' : (wt.1 == "A") = false := by simpa using ha
      simp only [List.filter_cons, ha', Bool.false_eq_true, ite_false]
      exact filter_A_cases hnd.2

/-- `insertWt` puts its atom somewhere in the list. -/
theorem insertWt_perm (x : String × String) : ∀ l, (Criteria.insertWt x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold Criteria.insertWt
    split
    · exact List.Perm.refl _
    · exact ((insertWt_perm x ys).cons y).trans (List.Perm.swap x y ys)

/-- Sorting the weighted atoms keeps every one of them. -/
theorem foldl_insertWt_perm : ∀ (l acc : List (String × String)),
    (l.foldl (fun acc w => Criteria.insertWt w acc) acc).Perm (l ++ acc)
  | [], _ => List.Perm.refl _
  | w :: ws, acc => by
    simp only [List.foldl_cons, List.cons_append]
    exact (foldl_insertWt_perm ws _).trans
      (((insertWt_perm w acc).append_left ws).trans List.perm_middle)

/-- The contributions of A `Criteria.parseBase` lists for a WSUM: one per weighted atom A. -/
theorem filterMap_A {F : String × String → Option (Int × Option String)}
    (hF : ∀ a c, F (a, c) = if a == "A" then some (1, some c) else none) :
    ∀ (wts : List (String × String)),
      wts.filterMap F = (wts.filter (·.1 == "A")).map fun wt => (1, some wt.2)
  | [] => rfl
  | wt :: ws => by
    obtain ⟨a, c⟩ := wt
    by_cases ha : (a == "A") = true
    · rw [List.filterMap_cons, hF, List.filter_cons_of_pos (by simpa using ha)]
      simp [ha, filterMap_A hF ws]
    · rw [List.filterMap_cons, hF, List.filter_cons_of_neg (by simpa using ha)]
      simp [ha, filterMap_A hF ws]

/-- A compiled base moves with A as its spelling says: not at all, by one, or by one
constant's VALUE. -/
theorem compileBase_contrib {weights : List (String × String)} {b : String} {body : Body}
    (h : compileBase weights b = .ok body) :
    ((Criteria.parseBase b).contrib = [] ∧ body.aCoef = 0) ∨
    ((Criteria.parseBase b).contrib = [(1, none)] ∧ body.aCoef = 1) ∨
    (∃ k v, (Criteria.parseBase b).contrib = [(1, some k)] ∧ weights.lookup k = some v ∧
      Decimal.value v = some body.aCoef) := by
  unfold compileBase at h
  unfold Criteria.parseBase
  cases h1 : (b == "SR1")
  · cases h2 : (b == "S")
    · cases h3 : (b == "A")
      · cases h4 : b.startsWith "FIELD:"
        · cases h5 : b.startsWith "WSUM:"
          · simp [h1, h2, h3, h4, h5, throw, throwThe, MonadExceptOf.throw] at h
          · simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false, ite_true] at h ⊢
            cases hr : Criteria.readWts ((b.drop 5).toString.splitOn ";") [] with
            | none =>
              simp only [hr] at h
              simp [throw, throwThe, MonadExceptOf.throw] at h
            | some wts =>
              simp only [hr] at h ⊢
              simp only [bind, Except.bind] at h
              split at h
              · cases h
              · split at h
                · cases h
                · rename_i parts hparts
                  simp only [pure, Except.pure, Except.ok.injEq] at h
                  subst h
                  rw [filterMap_A (F := fun x => if (x.fst == "A") = true then some (1, some x.snd)
                    else none) (fun _ _ => rfl)]
                  have hnd := (readWts_nodup hr).1
                  have hperm := ((foldl_insertWt_perm wts []).filter (·.1 == "A"))
                  rw [List.append_nil] at hperm
                  have hw := aWeights_mapM 0 hparts
                  simp only [Body.aCoef]
                  rcases filter_A_cases hnd with hn | ⟨x, hx⟩
                  · left
                    rw [hn] at hperm
                    rw [hperm.eq_nil] at hw
                    exact ⟨by rw [hn]; rfl, hw.1 rfl⟩
                  · right; right
                    rw [hx] at hperm
                    obtain ⟨v, w, hl, hv, hs⟩ := hw.2 x (List.perm_singleton.mp hperm)
                    refine ⟨x.2, v, by rw [hx]; rfl, hl, ?_⟩
                    rw [hs, Rat.zero_add]; exact hv
        · simp only [h1, h2, h3, h4, Bool.false_eq_true, ite_false, ite_true] at h ⊢
          left
          refine ⟨by simp, ?_⟩
          simp only [bind, Except.bind] at h
          split at h
          · cases h
          · cases hx : atomOf? b with
            | none => simp [hx, throw, throwThe, MonadExceptOf.throw] at h
            | some x =>
              simp only [hx, pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hxa : x ≠ .a := fun he => by
                have := (atomOf_a hx).mp he
                subst this
                simp at h3
              simp [Body.aCoef, hxa]
      · simp only [h1, h2, h3, Bool.false_eq_true, ite_false, ite_true, pure, Except.pure,
          Except.ok.injEq] at h ⊢
        subst h
        right; left
        simp [Body.aCoef]
    · simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true, pure, Except.pure,
        Except.ok.injEq] at h ⊢
      subst h
      left
      simp [Body.aCoef]
  · simp only [h1, ite_true, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    left
    simp [Body.aCoef]

/-- A rational's sign is 1, -1 or 0. -/
theorem rsign_cases (q : Rat) : rsign q = 1 ∨ rsign q = -1 ∨ rsign q = 0 := by
  unfold rsign
  split
  · simp
  · split <;> simp

theorem rsign_zero : rsign 0 = 0 := by
  simp [rsign, Rat.lt_irrefl]

theorem rsign_one : rsign 1 = 1 := by
  have h : (0 : Rat) < 1 := by decide +kernel
  simp [rsign, h]

/-- A negated rational's sign. -/
theorem rsign_neg (q : Rat) : rsign (-q) = -rsign q := by
  unfold rsign
  by_cases h1 : 0 < q
  · have h3 : ¬ (0 < -q) := by grind
    have h4 : -q < 0 := by grind
    simp [h1, h3, h4]
  · by_cases h2 : q < 0
    · have h3 : 0 < -q := by grind
      simp [h1, h2, h3]
    · have h3 : q = 0 := by grind
      subst h3
      simp

/-- A sign that is neither negative nor zero is positive. -/
theorem rsign_pos {q : Rat} (h1 : ¬ rsign q < 0) (h2 : rsign q ≠ 0) : 0 < q := by
  unfold rsign at h1 h2
  by_cases hp : 0 < q
  · exact hp
  · by_cases hn : q < 0
    · simp [hp, hn] at h1
    · simp [hp, hn] at h2

/-- A zero sign is a zero. -/
theorem rsign_eq_zero {q : Rat} (h : rsign q = 0) : q = 0 := by
  unfold rsign at h
  by_cases hp : 0 < q
  · simp [hp] at h
  · by_cases hn : q < 0
    · simp [hp, hn] at h
    · grind

/-- **One term, two ways.** A compiled well-formed term's A coefficient has the sign
`Criteria.aSign` reads from its spelling and the CONSTANTS. -/
theorem compileTerm_aSign {weights : List (String × String)} {t : String} {term : Term}
    (h : compileTerm weights t = .ok term) (hok : (Criteria.parseTerm t).ok = true) :
    rsign term.aCoef = Criteria.aSign (Criteria.parseTerm t).contrib weights := by
  unfold compileTerm at h
  unfold Criteria.parseTerm at hok ⊢
  rcases hs : Criteria.stripNeg t.toList with ⟨n, b⟩
  simp only [hs] at h hok ⊢
  cases hb : compileBase weights (String.ofList b) with
  | error e => simp [hb, bind, Except.bind] at h
  | ok body =>
    simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hpok : (Criteria.parseBase (String.ofList b)).ok = true := by
      cases hp : (Criteria.parseBase (String.ofList b)).ok
      · simp [hp] at hok
      · rfl
    simp only [hpok, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [Term.aCoef_eq]
    have key : rsign body.aCoef =
          Criteria.aSign (Criteria.parseBase (String.ofList b)).contrib weights ∧
        rsign (-body.aCoef) = Criteria.aSign
          ((Criteria.parseBase (String.ofList b)).contrib.map fun x => (-x.1, x.2)) weights := by
      rw [rsign_neg]
      rcases compileBase_contrib hb with ⟨hc, ha⟩ | ⟨hc, ha⟩ | ⟨k, v, hc, hl, hv⟩
      · rw [hc, ha, rsign_zero]
        simp [Criteria.aSign]
      · rw [hc, ha, rsign_one]
        simp [Criteria.aSign]
      · have hr := rsign_value hv
        rw [hc]
        simp only [List.map_cons, List.map_nil, Criteria.aSign, List.foldl_cons, List.foldl_nil,
          hl, Option.getD_some, ← hr]
        rcases rsign_cases body.aCoef with h | h | h <;> simp [h]
    by_cases hn : n % 2 = 1
    · simp [hn, key.2]
    · simp [hn, key.1]

/-- **A KEY, two ways.** A main KEY with no problem in `Criteria.checkKey`'s walk compiles to
terms that pass `staticC2`. -/
theorem go_static {tag : String} {consts : List (String × String)} :
    ∀ (key : List String) (i : Nat) (terms : List Term),
      Criteria.checkKey.go tag consts true i false key = [] →
      key.mapM (compileTerm consts) = .ok terms → staticC2 terms = true
  | [], _, terms, _, hm => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    rfl
  | t :: ts, i, terms, hg, hm => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hm
    split at hm
    · cases hm
    · rename_i term hterm
      split at hm
      · cases hm
      · rename_i terms' hterms
        cases hm
        simp only [Criteria.checkKey.go] at hg
        split at hg
        · cases hg
        · rename_i hok
          have hok' : (Criteria.parseTerm t).ok = true := by simpa using hok
          have hsa := compileTerm_aSign hterm hok'
          split at hg
          · split at hg
            · rename_i hs0
              have hpos : ¬ Criteria.aSign (Criteria.parseTerm t).contrib consts < 0 := by
                intro hlt
                simp [hlt] at hg
              have hne : Criteria.aSign (Criteria.parseTerm t).contrib consts ≠ 0 := by
                simpa using hs0
              rw [← hsa] at hpos hne
              have hc := rsign_pos hpos hne
              have hc0 : term.aCoef ≠ 0 := fun h => by rw [h] at hc; exact Rat.lt_irrefl hc
              unfold staticC2
              simp [hc0, hc]
            · rename_i hs0
              have h0 : Criteria.aSign (Criteria.parseTerm t).contrib consts = 0 := by
                simpa using hs0
              rw [← hsa] at h0
              have hc := rsign_eq_zero h0
              unfold staticC2
              simp only [hc, ite_true]
              exact go_static ts (i + 1) terms' (List.append_eq_nil_iff.mp hg).2 hterms
          · rename_i hmiss
            have h1 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hg).1).2
            rw [List.map_eq_nil_iff] at h1
            simp [h1] at hmiss

/-- A KEY `Criteria.checkKey` passes with `c2` compiles to terms that pass `staticC2`. -/
theorem checkKey_static {tag : String} {consts : List (String × String)} {key : List String}
    {terms : List Term} (h : Criteria.checkKey tag key consts true = [])
    (hm : key.mapM (compileTerm consts) = .ok terms) : staticC2 terms = true := by
  unfold Criteria.checkKey at h
  split at h
  · cases h
  · simp only [List.append_eq_nil_iff] at h
    exact go_static _ 0 terms h.2 hm

/-- A yardstick with no problem has a main KEY that passes `staticC2` once compiled. -/
theorem yardstickProblems_static {units : UnitHook} {consts : List (String × String)}
    {e : Entry} {terms : List Term} (h : Criteria.yardstickProblems units consts e = [])
    (hm : (keyTerms e).mapM (compileTerm consts) = .ok terms) : staticC2 terms = true := by
  unfold Criteria.yardstickProblems at h
  simp only [List.append_eq_nil_iff] at h
  obtain ⟨⟨_, hkey⟩, _⟩ := h
  unfold keyTerms at hm
  split at hkey
  · rename_i v hv
    simp only [hv] at hm
    split at hkey
    · rename_i ht
      simp only [ht, ite_true] at hm
      exact checkKey_static hkey hm
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ite_false, List.mapM_nil, pure, Except.pure,
        Except.ok.injEq] at hm
      subst hm
      rfl
  · rename_i hv
    simp only [hv, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    rfl

/-- Inserting a problem leaves a problem. -/
theorem insertStr_ne_nil (x : String) : ∀ l, insertStr x l ≠ []
  | [] => by simp [insertStr]
  | y :: ys => by
    unfold insertStr
    split
    · simp
    · split <;> simp

/-- Problems inserted into a list that has one leave a list that has one. -/
theorem foldl_insertStr_ne_nil : ∀ (l acc : List String), acc ≠ [] →
    l.foldl (fun acc p => insertStr p acc) acc ≠ []
  | [], _, h => h
  | p :: ps, acc, _ => foldl_insertStr_ne_nil ps _ (insertStr_ne_nil p acc)

/-- `done` reports a problem whenever there is one. -/
theorem done_eq_nil {ps : List String} (h : done ps = []) : ps = [] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    unfold done at h
    simp only [List.map_cons, List.foldl_cons] at h
    exact absurd h (foldl_insertStr_ne_nil _ _ (insertStr_ne_nil _ _))

/-- A checked verdict is `done` of the problems. -/
theorem wellFormed_checked {units : UnitHook} {tms : Value} {ps : List String}
    (h : Criteria.wellFormed units tms = .checked ps) : ps = done (Criteria.problems units tms) := by
  unfold Criteria.wellFormed at h
  split at h
  · cases h
  · cases h; rfl

/-- In a Criteria Set with no problem, the yardstick `findYardstick` finds has none, judged
against the CONSTANTS `constants` reads. -/
theorem problems_yardstick {units : UnitHook} {tms : Value} {name : String} {e : Entry}
    (h : Criteria.problems units tms = []) (hf : findYardstick tms name = some e) :
    Criteria.yardstickProblems units (constants tms) e = [] := by
  cases tms with
  | obj z =>
    unfold Criteria.problems at h
    rcases hc : entries "TMS CONSTANTS" ((get? z "CONSTANTS").getD (.arr [])) with
      ⟨cons, consShape⟩
    rcases hy : entries "TMS YARDSTICKS" ((get? z "YARDSTICKS").getD (.arr [])) with
      ⟨yards, yardShape⟩
    simp only [hc, hy, List.append_eq_nil_iff] at h
    simp only [findYardstick, hy] at hf
    have hmem := List.mem_of_find?_eq_some hf
    have he := List.flatMap_eq_nil_iff.mp h.1.2 e hmem
    simp only [constants, hc]
    exact he
  | _ => simp [findYardstick] at hf

/-- **The static rule holds on every compiled yardstick.** `compile` accepts only a
well-formed Criteria Set, whose main KEY `Criteria.checkKey` passed with `c2`; its compiled
terms then pass `staticC2`. -/
theorem compile_staticC2 {units : UnitHook} {tms : Value} {name : String} {y : Compiled}
    (h : compile units tms name = .ok y) : staticC2 y.main = true := by
  unfold compile at h
  cases hw : Criteria.wellFormed units tms with
  | owed o => simp [hw, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | checked ps =>
    simp only [hw] at h
    have hps := wellFormed_checked hw
    cases he : ps.isEmpty
    · simp [he, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [he, Bool.not_true, Bool.false_eq_true, ite_false] at h
      have hp0 : ps = [] := List.isEmpty_iff.mp he
      subst hp0
      have hprob := done_eq_nil hps.symm
      cases hf : findYardstick tms name with
      | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
      | some e =>
        simp only [hf] at h
        have hyp := problems_yardstick hprob hf
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i main hmain
          split at h
          · cases h
          · split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              exact yardstickProblems_static hyp hmain
            · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The SR9 entry -/

open Principia.Strike Principia.Strike.SR9

/-- The U_C a record's field-table row holds, if it holds a string. -/
def uCOf (r : SuiteRecord) : Option String := r.fields.lookup "U_C"

/-- v1's `key(rid, records, tfk)`: the key of record `rid` among `recs`. -/
def keyOf (y : Compiled) (rid : String) (recs : SuiteRecords) (tfk : List String) :
    Except Stop (List Rat) := do
  let some r := recs.lookup rid | throw .raised
  keyOfView y rid r.domain ⟨r.sr1Fail, aOf rid recs tfk, r.steps, uCOf r⟩

/-- The key as SR9 reads it: `none` wherever the evaluation stops. The checks run only after
`firstStop` has found no stop, so there `none` means only a record the suite lacks. -/
def entryKey (y : Compiled) : KeyFn := fun rid recs tfk => (keyOf y rid recs tfk).toOption

/-- The SR9 entry of a compiled yardstick: its key, SR7 for an L-M pair and SR5 on the key
otherwise, and its LIMITING DOMAINs. -/
def entry (y : Compiled) : SR9.Entry :=
  ⟨entryKey y, resolveRegimeAware (entryKey y), y.domains⟩

/-- v1's `_placed`: each record carries the field table's row for it, and no other (a table
that is not an object, or a row that is not one, holds no U_C: `[]`). -/
def placed (recs : SuiteRecords) (table : List (String × List (String × String))) :
    SuiteRecords :=
  recs.map fun (rid, r) => (rid, { r with fields := (table.lookup rid).getD [] })

/-- The keys v1's checks evaluate, in v1's order, each with the records it is evaluated
among. C1 evaluates nothing when no record fails SR1; otherwise the first failing record,
then each passing record, then the other failing records (a key evaluated again stops, or
not, as it did the first time). C2 evaluates, for each record in code point order, `r+` and
then `r`, among the records with `r+` added (`SR9.c2One`'s transform). C4 evaluates no key:
the resolution is SR7 for an L-M pair, and C4 skips a pair within one regime. -/
def evaluated (s : Suite) : List (String × SuiteRecords) :=
  let fails := s.ids.filter s.fails
  let passes := s.ids.filter (!s.fails ·)
  let c1 := match fails with
    | [] => []
    | f :: fs => (f :: passes ++ fs).map (·, s.records)
  let c2 := s.ids.flatMap fun rid =>
    match s.records.lookup rid with
    | some r =>
      let recs2 := (rid ++ "+", { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] }) ::
        s.records
      [(rid ++ "+", recs2), (rid, recs2)]
    | none => []
  c1 ++ c2

/-- The first stop v1's checks reach, in v1's order: the refusal (or owed result) a
`yardstick_checks` call returns. -/
def firstStop (y : Compiled) (s : Suite) : Option Stop :=
  (evaluated s).findSome? fun (rid, recs) =>
    match keyOf y rid recs s.assembly with
    | .error e => some e
    | .ok _ => none

/-! ## SR9 C1 and C4 for every compiled yardstick -/

/-- An entry key begins with the record's SR1 rank. -/
theorem entryKey_head {y : Compiled} {rid : String} {recs : SuiteRecords} {tfk : List String}
    {k : Key} (h : entryKey y rid recs tfk = some k) :
    ∃ r ks, recs.lookup rid = some r ∧ k = sr1Rank r :: ks := by
  simp only [entryKey, keyOf] at h
  cases hr : recs.lookup rid with
  | none => simp [hr, Except.toOption, throw, throwThe, MonadExceptOf.throw] at h
  | some r =>
    simp only [hr] at h
    cases hk : keyOfView y rid r.domain ⟨r.sr1Fail, aOf rid recs tfk, r.steps, uCOf r⟩ with
    | error e => simp [hk, Except.toOption] at h
    | ok k' =>
      simp only [hk, Except.toOption, Option.some.injEq] at h
      subst h
      obtain ⟨ks, rfl⟩ := keyOfView_head hk
      exact ⟨r, ks, rfl, rfl⟩

/-- C1's witnesses for a compiled yardstick: none, when the failing records fail SR1 and the
passing ones pass it. -/
theorem c1Witnesses_entry (y : Compiled) (s : Suite) (passes : List String)
    (hp : ∀ p ∈ passes, s.fails p = false) :
    ∀ (fails : List String) (w : List String), (∀ f ∈ fails, s.fails f = true) →
      c1Witnesses ((entry y).key · s.records s.assembly) passes fails = some w → w = [] := by
  intro fails
  induction fails with
  | nil => intro w _ h; simp [c1Witnesses] at h; exact h
  | cons f fs ih =>
    intro w hf h
    simp only [c1Witnesses, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨kf, hkf, wf, hwf, rest, hrest, rfl⟩ := h
    have hr := ih rest (fun q hq => hf q (List.mem_cons_of_mem _ hq)) hrest
    obtain ⟨r, ks, hr1, rfl⟩ := entryKey_head hkf
    have hfail : r.sr1Fail = true := by
      have := hf f (List.mem_cons_self ..)
      simp [Suite.fails, hr1] at this
      exact this
    have hw : wf = [] := by
      refine c1Against_nil (kfs := ks) (by simp [sr1Rank, hfail]) passes wf ?_ hwf
      intro p hpm kp hkp
      obtain ⟨rp, kps, hrp, rfl⟩ := entryKey_head hkp
      have hpass := hp p hpm
      simp [Suite.fails, hrp] at hpass
      exact ⟨_, _, rfl, by simp [sr1Rank, hpass]⟩
    simp [hw, hr]

/-- **SR9 C1 for the yardstick grammar.** On every suite it runs on, a compiled yardstick
ranks no record failing SR1 above one passing it: every KEY begins with SR1. -/
theorem yardstick_c1 (y : Compiled) (s : Suite) {r : Bool × List String}
    (h : sr9C1 (entry y) s = some r) : r = (true, []) := by
  simp only [sr9C1, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨w, hw, rfl⟩ := h
  have := c1Witnesses_entry y s _ (fun p hp => by simpa using (List.mem_filter.mp hp).2) _ w
    (fun f hf => (List.mem_filter.mp hf).2) hw
  subst this
  simp

/-- **SR9 C4 for the yardstick grammar.** On every suite it runs on, a compiled yardstick
never lets an M contradiction strike an L derivation: its resolution is fixed to SR7 for an
L-M pair. -/
theorem yardstick_c4 (y : Compiled) (s : Suite) {r : Bool × List String}
    (h : sr9C4 (entry y) s = some r) : r = (true, []) :=
  regimeAware_c4 (entryKey y) y.domains s h

/-! ## SR9 C2 for the yardstick grammar

`Criteria.checkKey` decides C2 statically on a main KEY (`staticC2`): the first term whose
value moves with A must move up with it. SR1, S and FIELD do not move with the assumption
count, and C2's `r+` keeps `r`'s SR1 verdict, steps, DOMAIN and field row, so `r+` and `r`
differ only in `a`. Adding an assumption never lowers `a(r)` (`monotone_holds`, from SR4's
closure walk, `Strike.aOfR_mono`), so the static rule leaves no C2 violation; and every
yardstick `compile` accepts passes the static rule (`compile_staticC2`). -/

/-- Away from A, an atom's value does not depend on the record's identifier or its
assumptions: only its SR1 verdict, steps and U_C. -/
theorem valuation_eq {rid rid' : String} {v v' : View} (h1 : v'.sr1Fail = v.sr1Fail)
    (h2 : v'.steps = v.steps) (h3 : v'.uC = v.uC) (x : Atom) (hx : x ≠ .a) :
    valuation rid' v' x = valuation rid v x := by
  cases x with
  | a => exact absurd rfl hx
  | sr1 => simp [valuation, atomValue, h1]
  | s => simp [valuation, atomValue, h2]
  | uC =>
    unfold valuation atomValue
    rw [h3]
    cases uCValue v.uC <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- A's valuation is `a(r)`, read as 0 where it is undefined (a key reading A is then not
evaluated at all). -/
theorem valuation_a (rid : String) (v : View) : valuation rid v .a = ((v.a.getD 0 : Nat) : Rat) := by
  cases h : v.a <;> simp [valuation, atomValue, h, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

/-- A key that has a value is its terms' values under the record's valuation. -/
theorem mapM_termValue {rid : String} {v : View} :
    ∀ {ts : List Term} {ks : List Rat}, ts.mapM (termValue rid v) = .ok ks →
      ks = ts.map (·.valueWith (valuation rid v))
  | [], ks, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | t :: ts, ks, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i qs hqs
        cases h
        rw [termValue_ok hq, mapM_termValue hqs]
        rfl

/-- Over two valuations that differ only at A, A larger in the second, a KEY that passes the
static rule is not lower under the second. -/
theorem keyLt_static (ts : List Term) (val val' : Atom → Rat)
    (hv : ∀ x, x ≠ .a → val' x = val x) (hd : val .a ≤ val' .a) (hs : staticC2 ts = true) :
    keyLt (ts.map (·.valueWith val')) (ts.map (·.valueWith val)) = false := by
  by_cases h0 : val' .a = val .a
  · have : val' = val := funext fun x => by
      by_cases hx : x = .a
      · subst hx; exact h0
      · exact hv x hx
    rw [this]; exact keyLt_irrefl _
  · have hlt : val .a < val' .a := by
      rcases Rat.le_iff_lt_or_eq.mp hd with h | h
      · exact h
      · exact absurd h.symm h0
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      have hdiff := valueWith_diff t val val' hv
      simp only [List.map_cons, keyLt]
      unfold staticC2 at hs
      by_cases hc : t.aCoef = 0
      · simp only [hc, ite_true] at hs
        have heq : t.valueWith val' = t.valueWith val := by
          rw [hc] at hdiff; grind
        rw [heq]
        simp [Rat.lt_irrefl, ih hs]
      · simp only [hc, ite_false, decide_eq_true_eq] at hs
        have hpos : 0 < t.aCoef * (val' .a - val .a) := Rat.mul_pos hs (by grind)
        have hgt : t.valueWith val < t.valueWith val' := by grind
        have hne : (t.valueWith val' == t.valueWith val) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; grind
        simp [Rat.not_lt.mpr (Rat.le_of_lt hgt), hne]

/-- The terms keying a record do not depend on the identifier the key is asked for. -/
theorem termsFor_rid {y : Compiled} {rid rid' domain : String} {ts : List Term}
    (h : termsFor y rid domain = .ok ts) : termsFor y rid' domain = .ok ts := by
  unfold termsFor at h ⊢
  exact h

/-- C2's added record never has the identifier of the record it is built from. -/
theorem ne_plus (rid : String) : (rid == rid ++ "+") = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h
  have := congrArg String.length h
  simp [String.length_append] at this

/-- C2's records: the suite's, with `r+` added in front (`SR9.c2One`'s transform). -/
def plusRecords (s : Suite) (rid : String) (r : SuiteRecord) : SuiteRecords :=
  (rid ++ "+", { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] }) :: s.records

/-- SR4's monotonicity at one record, as C2 needs it: `a(r+) ≥ a(r)` among C2's records,
an undefined `a` read as 0 (then neither key that reads A has a value). -/
def Monotone (s : Suite) (rid : String) (r : SuiteRecord) : Prop :=
  (aOf rid (plusRecords s rid r) s.assembly).getD 0 ≤
    (aOf (rid ++ "+") (plusRecords s rid r) s.assembly).getD 0

/-- `lookup` among the records SR4 reads of a suite. -/
theorem lookup_strike (recs : SuiteRecords) (x : String) :
    (recs.map fun p => (p.1, p.2.toStrikeRecord)).lookup x = (recs.lookup x).map (·.toStrikeRecord) := by
  induction recs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.lookup]
    cases x == k <;> simp [ih]

/-- **SR4's monotonicity holds at every record** (`Strike.aOfR_mono`): C2's `r+` has the same
CITES as `r` and every one of its ASSUMPTIONS, so `a(r+) ≥ a(r)`. -/
theorem monotone_holds (s : Suite) (rid : String) (r : SuiteRecord)
    (hr : s.records.lookup rid = some r) : Monotone s rid r := by
  unfold Monotone
  cases ha : aOf rid (plusRecords s rid r) s.assembly with
  | none => simp
  | some n =>
    have hl1 : (plusRecords s rid r).lookup (rid ++ "+") =
        some { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] } := by
      simp [plusRecords]
    have hl2 : (plusRecords s rid r).lookup rid = some r := by
      simp only [plusRecords, List.lookup_cons, ne_plus]; exact hr
    unfold aOf at ha
    obtain ⟨n', hn', hle⟩ := aOfR_mono (rid := rid) (rid' := rid ++ "+")
      (r := r.toStrikeRecord)
      (r' := ({ r with assumptions := r.assumptions ++ [freshPrefix ++ rid] } : SuiteRecord).toStrikeRecord)
      (by rw [lookup_strike, hl2]; rfl) (by rw [lookup_strike, hl1]; rfl) rfl
      (fun a h => List.mem_append_left _ h) s.assembly ha
    simp only [aOf, hn', Option.getD_some]
    exact hle

/-- **SR9 C2 for one record.** A record keyed by its yardstick's main KEY, which passes the
static rule, is never a C2 violation (nor an exempt case). -/
theorem c2One_static (y : Compiled) (s : Suite) (rid : String) (r : SuiteRecord)
    (hr : s.records.lookup rid = some r) (hs : staticC2 y.main = true)
    (hm : termsFor y rid r.domain = .ok y.main)
    {v : Option Bool} (h : c2One (entry y) s rid = some v) : v = none := by
  have hmono := monotone_holds s rid r hr
  simp only [c2One, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨kP, hkP, k, hk, rfl⟩ := h
  unfold Monotone at hmono
  generalize hrecs : plusRecords s rid r = recs2 at hmono
  have hl1 : recs2.lookup (rid ++ "+") =
      some { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] } := by
    rw [← hrecs]; simp [plusRecords]
  have hl2 : recs2.lookup rid = some r := by
    rw [← hrecs]; simp only [plusRecords, List.lookup_cons, ne_plus]; exact hr
  change (keyOf y (rid ++ "+") ((rid ++ "+", { r with assumptions := r.assumptions ++
    [freshPrefix ++ rid] }) :: s.records) s.assembly).toOption = some kP at hkP
  change (keyOf y rid ((rid ++ "+", { r with assumptions := r.assumptions ++
    [freshPrefix ++ rid] }) :: s.records) s.assembly).toOption = some k at hk
  have e2 : ((rid ++ "+", { r with assumptions := r.assumptions ++ [freshPrefix ++ rid] }) ::
      s.records) = recs2 := hrecs
  rw [e2] at hkP hk
  simp only [keyOf, hl1, hl2] at hkP hk
  change (keyOfView y (rid ++ "+") r.domain
    ⟨r.sr1Fail, aOf (rid ++ "+") recs2 s.assembly, r.steps, uCOf r⟩).toOption = some kP at hkP
  -- Both keys are the main KEY's values.
  have hmP : termsFor y (rid ++ "+") r.domain = .ok y.main := termsFor_rid hm
  cases hP : keyOfView y (rid ++ "+") r.domain
      ⟨r.sr1Fail, aOf (rid ++ "+") recs2 s.assembly, r.steps, uCOf r⟩ with
  | error e => simp [hP, Except.toOption] at hkP
  | ok kP' =>
    cases hK : keyOfView y rid r.domain ⟨r.sr1Fail, aOf rid recs2 s.assembly, r.steps, uCOf r⟩ with
    | error e => simp [hK, Except.toOption] at hk
    | ok k' =>
      simp only [hP, hK, Except.toOption, Option.some.injEq] at hkP hk
      subst hkP hk
      unfold keyOfView at hP hK
      simp only [hmP, hm, bind, Except.bind] at hP hK
      have eP := mapM_termValue hP
      have eK := mapM_termValue hK
      subst eP eK
      -- The two valuations differ only at A, and A is not lower for r+.
      have hv : ∀ x, x ≠ .a →
          valuation (rid ++ "+") ⟨r.sr1Fail, aOf (rid ++ "+") recs2 s.assembly, r.steps, uCOf r⟩ x =
            valuation rid ⟨r.sr1Fail, aOf rid recs2 s.assembly, r.steps, uCOf r⟩ x :=
        fun x hx => valuation_eq
          (v := ⟨r.sr1Fail, aOf rid recs2 s.assembly, r.steps, uCOf r⟩)
          (v' := ⟨r.sr1Fail, aOf (rid ++ "+") recs2 s.assembly, r.steps, uCOf r⟩) rfl rfl rfl x hx
      have hd : valuation rid ⟨r.sr1Fail, aOf rid recs2 s.assembly, r.steps, uCOf r⟩ .a ≤
          valuation (rid ++ "+") ⟨r.sr1Fail, aOf (rid ++ "+") recs2 s.assembly, r.steps, uCOf r⟩ .a := by
        rw [valuation_a, valuation_a]
        exact_mod_cast hmono
      simp [keyLt_static y.main _ _ hv hd hs]

/-- Every C2 verdict of such a yardstick is "no improvement". -/
theorem c2_verdicts_none (y : Compiled) (s : Suite) (hs : staticC2 y.main = true)
    (hlim : y.limiting = []) {vs : List (String × Option Bool)}
    (h : s.ids.mapM (fun rid => do let v ← c2One (entry y) s rid; pure (rid, v)) = some vs) :
    ∀ p ∈ vs, p.2 = none := by
  intro p hp
  obtain ⟨rid, _, hrid⟩ := exists_of_mapM_some h p hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hrid
  obtain ⟨v, hv, rfl⟩ := hrid
  -- A record the suite lacks has no verdict at all.
  cases hr : s.records.lookup rid with
  | none => simp [c2One, hr] at hv
  | some r =>
    have hm : termsFor y rid r.domain = .ok y.main := by simp [termsFor, hlim, pure, Except.pure]
    exact c2One_static y s rid r hr hs hm hv

/-- **SR9 C2 for a yardstick whose main KEY passes the static rule.** On every suite, such a
yardstick with no LIMITING cases has no C2 violation. -/
theorem yardstick_c2 (y : Compiled) (s : Suite) (hs : staticC2 y.main = true)
    (hlim : y.limiting = []) {res : Bool × List String × List String} (h : sr9C2 (entry y) s = some res) :
    res = (true, [], []) := by
  simp only [sr9C2, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨vs, hvs, rfl⟩ := h
  have hnone := c2_verdicts_none y s hs hlim hvs
  have h1 : vs.filter (·.2 == some true) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by simp [hnone p hp]
  have h2 : vs.filter (·.2 == some false) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by simp [hnone p hp]
  simp [h1, h2]

/-- **SR9 C2 for the yardstick grammar.** On every suite, a yardstick `compile` accepts with
no LIMITING cases has no C2 violation: the static check `Criteria.checkKey` makes at entry
is exact for SR1, A, S, FIELD and WSUM. -/
theorem yardstick_c2_compiled {units : UnitHook} {tms : Value} {name : String} {y : Compiled}
    (hc : compile units tms name = .ok y) (s : Suite) (hlim : y.limiting = [])
    {res : Bool × List String × List String} (h : sr9C2 (entry y) s = some res) :
    res = (true, [], []) :=
  yardstick_c2 y s (compile_staticC2 hc) hlim h

/-! ## v1's functions -/

/-- v1's `yardstick_key`: the key of record `rid`, the field table placed on the records;
`none` where v1 raised. -/
def yardstickKey (units : UnitHook) (tms : Value) (name rid : String) (recs : SuiteRecords)
    (tfk : List String) (table : List (String × List (String × String))) :
    Option (Outcome (List Rat)) :=
  Outcome.of do
    let y ← compile units tms name
    keyOf y rid (placed recs table) tfk

/-- The three checks' results: C1 `(pass, witnesses)`, C2 `(pass, violations, exempt)`, C4
`(pass, witnesses)`. -/
abbrev Checks := (Bool × List String) × (Bool × List String × List String) × (Bool × List String)

/-- v1's `yardstick_checks`: SR9 C1, C2 and C4 of the yardstick on the suite, the field table
placed on its records; `none` where v1 raised. -/
def yardstickChecks (units : UnitHook) (tms : Value) (name : String) (s : Suite)
    (table : List (String × List (String × String))) : Option (Outcome Checks) :=
  let s := { s with records := placed s.records table }
  match compile units tms name with
  | .error e => Outcome.of (.error e)
  | .ok y =>
    match firstStop y s with
    | some e => Outcome.of (.error e)
    | none => do
      let c1 ← sr9C1 (entry y) s
      let c2 ← sr9C2 (entry y) s
      let c4 ← sr9C4 (entry y) s
      pure (.ok (c1, c2, c4))

/-- v1's `yardstick_harness`: C1, C2 and C4 passed, and the count of violations, for the
gate; a refusal or an owed result as `yardstick_checks` gives it. -/
def yardstickHarness (units : UnitHook) (tms : Value) (name : String) (s : Suite)
    (table : List (String × List (String × String))) :
    Option (Outcome (Bool × Bool × Bool × Nat)) :=
  (yardstickChecks units tms name s table).map fun
    | .ok (c1, c2, c4) => .ok (c1.1, c2.1, c4.1, c1.2.length + c2.2.1.length + c4.2.length)
    | .refused r => .refused r
    | .owed o => .owed o

end Principia.Yardstick
