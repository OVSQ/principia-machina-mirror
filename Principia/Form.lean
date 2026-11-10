import Principia.Form.Grammar
import Principia.Form.Homogeneity
import Principia.Form.Arithmetic
import Principia.Form.Checks
import Principia.Form.Evaluation
import Principia.Form.Within

/-!
# Declared forms

v1's `tpc_form` 0.2.1 (S14, S32), ported: the declared form of a
LAW (EQUATION), a BOUNDARY (CONDITION) and a SIGNATURE (FORM, IMAGE_FORM).

* `Principia.Form.Grammar`: the grammar, its parser and canonical spelling (`parseForm`,
  `formTree`, `formNames`, `parseField`), with the bound on a form's length and S14's computed
  exponents;
* `Principia.Form.Homogeneity`: dimensions and totality (`formDimension`,
  `formTotality`);
* `Principia.Form.Checks`: the checks that read a zone (`namesCheck`, `formCoverage`,
  `dVariables`, `dVariableCheck`, `t4Homogeneity`, `t6Totality`, `ic4aSignature`);
* `Principia.Form.Evaluation`: `evalForm` and `t3Laws`, the ground fragment;
* `Principia.Form.Within`: the evaluator's operations within the bound on an exact value
  (the bound on the size of an exact number), operation by operation;
* `Principia.Form.Arithmetic` and `Principia.Form.Interval`: the evaluator's numbers, exact
  where they have an exact form here and otherwise enclosed between outward-rounded
  bounds.

Corpora: the form corpus (v1's, 555 cases) and the form numbers corpus
(written by hand, the enclosures), run by the form test runner.

A form is read as v1 read it, after line-ending normalization and NFC at Unicode 15.1.0
(`Principia.Zone.textChars`). What the Calculator does not answer
yet is owed, never guessed: a value whose sign, range or twelve digits no bounds up to 4096
bits settle (the Declarer's choice of exact values).

PROVED here: v1's 33 grammar witnesses, each canonical spelling reading back to itself;
reading a form is never owed, it is read or refused; the text read is the form's NFC, and
two forms with one NFC read alike; the length bound, counted on the NFC, refuses before
any token is read; the literal zero takes any dimension; D of
a bound identifier is 0. In `Principia.Form.Interval`: rounding is outward, and `+ - * /`
and the reciprocal on bounds enclose the operation on any numbers the bounds hold.
-/

namespace Principia.Form

/-! ## The grammar witnesses, proved

v1 asserted its 33 witnesses each time it loaded. Here the kernel checks them once: each
text reads in its mode to the spelling given, or is refused, and each canonical spelling
reads back to itself. -/

/-- v1's count of witnesses. -/
def grammarWitnessCount : Nat := 33

theorem grammarWitnesses_count : grammarWitnesses.length = grammarWitnessCount := by decide

theorem grammarWitnesses_hold : grammarWitnesses.all witnessHolds = true := by decide +kernel

/-! ## Reading, dimensions, evaluation -/

/-- Every form is answered: read or refused, never owed. -/
theorem parse_not_owed (text : String) (mode : Mode) (w : Owed) : parse text mode ≠ .owed w := by
  simp only [parse]
  split
  · simp
  · unfold Answer.ofExcept
    split <;> simp

/-- The text a form is read in is its NFC, line endings as LF first (v1's `_text`). -/
theorem canonicalText_nfc (text : String) :
    canonicalText text = Unicode.nfcList (Zone.eolChars text.toList) :=
  Zone.textChars_eq text

/-- Two forms with one canonical text read alike, in every mode: a form in NFD and its NFC
have one reading, as in v1. -/
theorem parse_of_canonicalText {a b : String} (h : canonicalText a = canonicalText b)
    (mode : Mode) : parse a mode = parse b mode := by
  simp only [parse, h]

/-- A form whose canonical text (its NFC) is longer than 4096 code points is refused
for that, before any token is read. -/
theorem parse_long {text : String} (hl : (canonicalText text).length > maxCodePoints)
    (mode : Mode) :
    parse text mode = .refused s!"the form is longer than {maxCodePoints} code points" := by
  simp [parse, boundsFault, hl]

/-- The literal zero has every dimension: adding it changes nothing (S4). -/
theorem dims_add_zero (t : DimTable) (e : Expr) :
    (Expr.bin .add e (.num "0")).dims t = e.dims t := by
  simp only [Expr.dims]
  cases e.dims t with
  | error m => rfl
  | ok a => cases a <;> rfl

/-- A parenthesis changes neither a dimension nor the names. -/
theorem dims_paren (t : DimTable) (e : Expr) : (Expr.paren e).dims t = e.dims t := rfl

theorem names_paren (e : Expr) : (Expr.paren e).names = e.names := rfl

/-- D of a bound identifier is 0, whatever its variable (S7). -/
theorem eval_deriv_bound {b : Bindings} {x s : String} {n : Nat} {bd : Bound}
    (h : b.lookup x = some bd) (hk : inRange true bd.kind = .ok bd.kind)
    (budget : Option Nat) (steps : Nat) :
    (Expr.deriv x s n).eval budget b steps = .ok (Num.zero, bd.kind, steps) := by
  simp [Expr.eval, h, kindRange, hk]
  rfl


end Principia.Form
