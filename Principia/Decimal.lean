import Principia.Dimension

/-!
# Decimals

A VALUE, an UNCERTAINTY and the Criteria Set's K are decimal strings (zone schemas 5.6;
v1's tpc_zone 0.4.1: `canon_decimal`, `_dec_sign`, `_is_pos_finite`).

- Accepted: an optional minus sign, one or more ASCII digits, optionally a point and one
  or more digits, optionally `e` or `E` with an optional sign and one to four digits
  (`-?[0-9]+(\.[0-9]+)?([eE][-+]?[0-9]{1,4})?`). No leading `+`, no bare point.
- Canonical: `0` for zero; otherwise the digits with no leading or trailing zero, a minus
  sign before them when negative, and `e<exponent>` after them when the exponent is not
  zero: `0.050` is `5e-2`, `1500` is `15e2`, `-0` is `0`. String arithmetic only, as in
  v1. Trailing zeros carry no precision here; an UNCERTAINTY carries it.

A decimal's value is exact (`Rat`); v1 parsed it to the nearest IEEE double where it
computed with it. `isPosFinite`, v1's test that a positive decimal's nearest double is
positive and finite, is in `Principia.Exact`, beside the double range's bounds.
-/

namespace Principia.Decimal

/-- A decimal as written: its sign, its integer digits, its fraction digits (possibly
none) and its written exponent (zero when none is written). -/
structure Parts where
  neg : Bool
  ip : List Char
  fp : List Char
  ex : Int
  deriving DecidableEq, Repr

/-- The exponent after `e` or `E`: an optional sign, then one to four digits. -/
def readExponent : List Char → Option Int
  | [] => none
  | c :: ds =>
    if c = '+' then (Dimension.readDigits ds).map Int.ofNat
    else if c = '-' then (Dimension.readDigits ds).map fun k => -(k : Int)
    else (Dimension.readDigits (c :: ds)).map Int.ofNat

/-- What follows the digits: nothing, or an exponent. -/
def readTail : List Char → Option Int
  | [] => some 0
  | c :: r => if c = 'e' || c = 'E' then readExponent r else none

/-- A decimal's parts, or `none` when it does not read. -/
def readParts (cs : List Char) : Option Parts :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (ip, r) := cs.span Char.isDigit
  if ip = [] then none
  else
    match r with
    | '.' :: r' =>
      let (fp, r'') := r'.span Char.isDigit
      if fp = [] then none
      else (readTail r'').map fun ex => { neg, ip, fp, ex }
    | _ => (readTail r).map fun ex => { neg, ip, fp := [], ex }

/-- The digits with leading zeros removed, then the number of trailing zeros. -/
def significant (p : Parts) : List Char × Nat :=
  let ds := (p.ip ++ p.fp).dropWhile (· = '0')
  (ds, (ds.reverse.takeWhile (· = '0')).length)

/-- The canonical spelling of a decimal's parts. -/
def canonChars (p : Parts) : List Char :=
  let (ds, t) := significant p
  if ds = [] then ['0']
  else
    let e : Int := p.ex - p.fp.length + t
    (if p.neg then ['-'] else []) ++ ds.take (ds.length - t) ++
      (if e = 0 then [] else 'e' :: (toString e).toList)

/-- The canonical form of a decimal, or `none` when it does not read (v1's
`canon_decimal`). -/
def canon (s : String) : Option String :=
  (readParts s.toList).map fun p => String.ofList (canonChars p)

/-- -1, 0 or 1 for a decimal's sign; 0 when it does not read (v1's `_dec_sign`). -/
def sign (s : String) : Int :=
  match canon s with
  | none => 0
  | some c => if c = "0" then 0 else if c.startsWith "-" then -1 else 1

/-- A power of ten as an exact rational. -/
def pow10 (e : Int) : Rat := (10 : Rat) ^ e

/-- A decimal's exact value, or `none` when it does not read. -/
def value (s : String) : Option Rat :=
  (readParts s.toList).map fun p =>
    let m : Rat := (Nat.ofDigitChars 10 (p.ip ++ p.fp) 0 : Nat)
    let v := m * pow10 (p.ex - p.fp.length)
    if p.neg then -v else v

/-! ## Worked examples from v1's corpus -/

example : canon "0.050" = some "5e-2" := by decide
example : canon "1500" = some "15e2" := by decide
example : canon "-1.5E+3" = some "-15e2" := by decide
example : canon "-0" = some "0" := by decide
example : canon "5." = none := by decide
example : canon "+1" = none := by decide

/-! A canonical form need not read again: a written exponent has at most four digits, but
the canonical exponent also counts the fraction digits and the trailing zeros, so it can
pass 9999. v1 accepts such a decimal; S15 bounded only the DIMENSION's exponents. -/
example : canon "0.001e-9999" = some "1e-10002" := by decide
example : canon "1e-10002" = none := by decide

end Principia.Decimal
