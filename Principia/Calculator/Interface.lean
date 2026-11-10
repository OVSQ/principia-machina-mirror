import Principia.CanonicalReader
import Principia.ValueBound

/-!
# The Calculator's interface

What every family's calls share (`pcalc`, JSON in on stdin, JSON out on
stdout, deterministic). A call takes the request, one JSON value read by
`Canonical.readText`, and answers one value, which `pcalc` writes as canonical JSON, or
a `Refusal`.

A request is an object of named arguments, each named as the function's argument is
(v1's name where a function ports v1's); a request with a member the function does not
take, or without one it needs, is refused. A function's own refusals that v1 wrote as
values (`["REFUSED", problems]`) stay values; a `Refusal` is for a request the function
cannot take, or one whose answer the Calculator does not compute yet (`OWED`): a family
joins `pcalc` as soon as part of it is computed, and an owed answer is refused, never guessed,
its detail saying in the Public's words what is owed.
-/

namespace Principia.Calculator

open Principia.Canonical

/-- Why `pcalc` gives no answer. -/
inductive RefusalCode where
  /-- `pcalc` was not called as `pcalc <family> <function>` or `pcalc version`. -/
  | usage
  /-- No family of that name. -/
  | unknownFamily
  /-- The family has no function of that name. -/
  | unknownFunction
  /-- The request's text is not one JSON value the reader takes. -/
  | text (e : ReadError)
  /-- The request is not the function's argument object, or an argument is not of the
  kind the function takes. -/
  | badArgument
  /-- The answer has no canonical JSON (an object holding a key twice). -/
  | noCanonicalText
  /-- The answer is owed: the Calculator does not compute it yet. -/
  | owed
  deriving DecidableEq, Repr

/-- A refusal code's wire word: the reader's own word for a refused text. -/
def RefusalCode.word : RefusalCode → String
  | .usage => "USAGE"
  | .unknownFamily => "UNKNOWN_FAMILY"
  | .unknownFunction => "UNKNOWN_FUNCTION"
  | .text e => WireWord.toWire e
  | .badArgument => "BAD_ARGUMENT"
  | .noCanonicalText => "NO_CANONICAL_TEXT"
  | .owed => "OWED"

/-- A refusal: its code and a sentence that says what was refused. -/
structure Refusal where
  code : RefusalCode
  detail : String
  deriving Repr

/-- `pcalc`'s exit code for a refusal: 2 for how it was called, 1 for what it read. -/
def Refusal.exitCode (r : Refusal) : UInt32 :=
  match r.code with
  | .usage | .unknownFamily | .unknownFunction => 2
  | _ => 1

/-- A refusal as `pcalc` writes it: `{"detail": ..., "refused": ...}`. -/
def Refusal.value (r : Refusal) : Value :=
  .obj [("detail", .str r.detail), ("refused", .str r.code.word)]

/-- A function of a family: the request in, the answer out. -/
abbrev Call := Value → Except Refusal Value

/-- A family's functions, by name. -/
abbrev Family := List (String × Call)

/-! ## Reading a request's arguments -/

/-- Refuse a request's argument. -/
def badArgument {α : Type} (detail : String) : Except Refusal α :=
  .error ⟨.badArgument, detail⟩

/-- The arguments `names`, in that order, from a request that holds them and nothing
else. -/
def arguments (names : List String) (v : Value) : Except Refusal (List Value) :=
  match v with
  | .obj ms =>
    match ms.find? (fun m => !names.contains m.1) with
    | some m => badArgument s!"the function takes no argument {quote m.1}"
    | none =>
      names.mapM fun n =>
        match ms.lookup n with
        | some x => .ok x
        | none => badArgument s!"the argument {quote n} is missing"
  | _ => badArgument "the request is not an object of arguments"

/-- A request of one argument. -/
def argument1 (a : String) (v : Value) : Except Refusal Value := do
  match ← arguments [a] v with
  | [x] => pure x
  | _ => badArgument "the arguments do not read"

/-- A request of two arguments. -/
def argument2 (a b : String) (v : Value) : Except Refusal (Value × Value) := do
  match ← arguments [a, b] v with
  | [x, y] => pure (x, y)
  | _ => badArgument "the arguments do not read"

/-- A request of three arguments. -/
def argument3 (a b c : String) (v : Value) : Except Refusal (Value × Value × Value) := do
  match ← arguments [a, b, c] v with
  | [x, y, z] => pure (x, y, z)
  | _ => badArgument "the arguments do not read"

/-- A string argument. -/
def asString (what : String) : Value → Except Refusal String
  | .str s => .ok s
  | _ => badArgument s!"{what} is not a string"

/-- A boolean argument. -/
def asBool (what : String) : Value → Except Refusal Bool
  | .bool b => .ok b
  | _ => badArgument s!"{what} is not true or false"

/-- An integer argument: a number written without a fraction or an exponent. -/
def asInteger (what : String) : Value → Except Refusal Int
  | .int n => .ok n
  | _ => badArgument s!"{what} is not an integer"

/-- A list argument. -/
def asList (what : String) : Value → Except Refusal (List Value)
  | .arr xs => .ok xs
  | _ => badArgument s!"{what} is not a list"

/-- A request's members, each named in `names` (any of them may be absent); a member not
named is refused. -/
def membersOf (names : List String) (v : Value) : Except Refusal (List (String × Value)) :=
  match v with
  | .obj ms =>
    match ms.find? (fun m => !names.contains m.1) with
    | some m => badArgument s!"the function takes no argument {quote m.1}"
    | none => .ok ms
  | _ => badArgument "the request is not an object of arguments"

/-- A member the function needs. -/
def needed (ms : List (String × Value)) (name : String) : Except Refusal Value :=
  match ms.lookup name with
  | some x => .ok x
  | none => badArgument s!"the argument {quote name} is missing"

/-- A member the function may go without: `none` when absent or `null`. -/
def optional (ms : List (String × Value)) (name : String) : Option Value :=
  match ms.lookup name with
  | some .null | none => none
  | some x => some x

/-- A number argument, exactly: an integer, or a decimal `m × 10^e` as the rational it is
(the reader has bounded `m` and `e`). -/
def asNumber (what : String) : Value → Except Refusal Rat
  | .int n => .ok n
  | .num x =>
    if 0 ≤ x.exponent then .ok ((x.mantissa * 10 ^ x.exponent.toNat : Int) : Rat)
    else .ok (mkRat x.mantissa (10 ^ (-x.exponent).toNat))
  | _ => badArgument s!"{what} is not a number"

/-- A count argument: an integer written without a fraction or an exponent, at least 0. -/
def asCount (what : String) : Value → Except Refusal Nat
  | .int n => if 0 ≤ n then .ok n.toNat else badArgument s!"{what} is negative"
  | _ => badArgument s!"{what} is not an integer"

/-- An object argument's members; nested members are read by name, others ignored. -/
def asObject (what : String) : Value → Except Refusal (List (String × Value))
  | .obj ms => .ok ms
  | _ => badArgument s!"{what} is not an object"

/-- A list of strings. -/
def asStrings (what : String) (v : Value) : Except Refusal (List String) := do
  (← asList what v).mapM (asString s!"an entry of {what}")

/-! ## A family's bounds

The reader bounds a request's size, nesting and numbers; a function whose cost grows
faster than its input (a sort by insertion, exact sums over many fractions) also states
the most it takes, measured, and refuses more. -/

/-- At most `n` entries of `what`. -/
def atMost {α : Type} (what : String) (n : Nat) (xs : List α) : Except Refusal Unit :=
  if n < xs.length then badArgument s!"{what} holds more than {n} entries (the Calculator's bound)"
  else .ok ()

/-- The digits of a number's integer or mantissa. -/
def numberDigits : Value → Nat
  | .int n => (toString n.natAbs).length
  | .num x => (toString x.mantissa.natAbs).length
  | _ => 0

/-- A number of at most `n` significant digits. -/
def asShortNumber (what : String) (n : Nat) (v : Value) : Except Refusal Rat :=
  if n < numberDigits v then
    badArgument s!"{what} has more than {n} digits (the Calculator's bound)"
  else asNumber what v

/-- A computation within the bound on an exact value: its refusal, "exact value too large",
is a refusal of what was read. -/
def bounded {α : Type} : Principia.ValueBound.Bounded α → Except Refusal α
  | .ok a => .ok a
  | .error e => badArgument e

/-- A wire word of a closed enumeration, compared byte for byte. -/
def asWord (α : Type) [WireWord α] (what : String) (v : Value) : Except Refusal α := do
  let s ← asString what v
  match (WireWord.ofWire? s : Option α) with
  | some a => pure a
  | none => badArgument s!"{quote s} is not {what}"

end Principia.Calculator
