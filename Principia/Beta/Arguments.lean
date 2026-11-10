import Principia.Canonical

/-!
# Reading v1's arguments: the Beta layer's and the reliability score's

v1's `tpc_beta` and `tpc_score` took Python values decoded from JSON and checked their
kinds at run time, refusing an argument with a short fixed word (`ERROR:shape`,
`ERROR:params:HALF-LIFE`). The readers here take an argument as the Calculator reads a
request (`Canonical.Value`) and give the same word for the same argument, in v1's order.

* A number is an integer or a number literal, never a boolean (v1's `_num`), read exactly
  as the decimal it spells. v1 first rounded it to the nearest double; the Calculator keeps
  its exact value (the Calculator's choice of exact values). A literal v1 read as an infinite double is refused by
  the reader before any function sees it (`Canonical.readText`).
* An integer is an integer literal, never a boolean or a number written with a point or an
  exponent (v1's `_is_int`: `type(x) is int`).
* A name is a nonempty string (v1's `_is_name`).
* An object has every required key and no key outside the required and the optional ones
  (v1's `_keys_are`).
-/

namespace Principia.Beta

open Principia.Canonical

/-- A decimal's exact value. -/
def decimalRat (x : Decimal) : Rat :=
  if 0 ≤ x.exponent then ((x.mantissa * 10 ^ x.exponent.toNat : Int) : Rat)
  else mkRat x.mantissa (10 ^ (-x.exponent).toNat)

/-- A number, exactly: an integer or a number literal (v1 `_num`). -/
def numberOf? : Value → Option Rat
  | .int n => some n
  | .num x => some (decimalRat x)
  | _ => none

/-- An integer literal within `[lo, hi]` (v1 `_is_int`). -/
def intIn? (v : Value) (lo hi : Int) : Option Int :=
  match v with
  | .int n => if lo ≤ n ∧ n ≤ hi then some n else none
  | _ => none

/-- A nonempty string (v1 `_is_name`). -/
def nameOf? : Value → Option String
  | .str s => if s.isEmpty then none else some s
  | _ => none

/-- A boolean. -/
def boolOf? : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- An object's members, when it holds every key of `required` and none outside `required`
and `optional` (v1 `_keys_are`). -/
def keysAre? (v : Value) (required : List String) (optional : List String := []) :
    Option (List (String × Value)) :=
  match v with
  | .obj ms =>
    if required.all (fun k => ms.any (·.1 == k)) &&
        ms.all (fun m => required.contains m.1 || optional.contains m.1) then some ms
    else none
  | _ => none

/-- A member's value, `null` when absent (Python's `dict.get`). -/
def member (ms : List (String × Value)) (k : String) : Value :=
  (ms.lookup k).getD .null

/-- Refuse with v1's word unless the value is there. -/
def need {α : Type} (o : Option α) (word : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error word

/-- Refuse with v1's word unless the condition holds. -/
def check (c : Bool) (word : String) : Except String Unit :=
  if c then .ok () else .error word

/-! ## Declared parameters (v1 `_pf`, `_pi`, `_pb`, `_pflag`) -/

/-- The parameter `key` of a params object, or v1's refusal `params:<key>`. -/
def param (params : Value) (key : String) : Except String Value :=
  match params with
  | .obj ms => need (ms.lookup key) ("params:" ++ key)
  | _ => .error ("params:" ++ key)

/-- A number parameter within `[lo, hi]`, either end open (v1 `_pf`). -/
def paramNumber (params : Value) (key : String) (lo hi : Rat) (loOpen hiOpen : Bool := false) :
    Except String Rat := do
  let v ← need (numberOf? (← param params key)) ("params:" ++ key)
  check (lo ≤ v && v ≤ hi && !(loOpen && v == lo) && !(hiOpen && v == hi)) ("params:" ++ key)
  return v

/-- An integer parameter within `[lo, hi]` (v1 `_pi`). -/
def paramInt (params : Value) (key : String) (lo hi : Int) : Except String Int := do
  need (intIn? (← param params key) lo hi) ("params:" ++ key)

/-- A boolean parameter (v1 `_pb`). -/
def paramBool (params : Value) (key : String) : Except String Bool := do
  need (boolOf? (← param params key)) ("params:" ++ key)

/-- A switch with a fraction, `{on, fraction}`, the fraction in `(0, 1]` (v1 `_pflag`). -/
def paramFlag (params : Value) (key : String) : Except String (Bool × Rat) := do
  let ms ← need (keysAre? (← param params key) ["on", "fraction"]) ("params:" ++ key)
  let on ← need (boolOf? (member ms "on")) ("params:" ++ key)
  let f ← need (numberOf? (member ms "fraction")) ("params:" ++ key)
  check (0 < f && f ≤ 1) ("params:" ++ key)
  return (on, f)

end Principia.Beta
