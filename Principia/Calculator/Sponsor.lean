import Principia.Calculator.Identity
import Principia.Sponsor
import Principia.ValueBound

/-!
# Family `sponsor`: CONDUCT EVENTS, the user evidence and the WHITEWASH count

Version 1's sponsor functions (`Principia.Sponsor`), one function each, named and taking
its arguments as version 1 names them:

* `conduct_resolve {"event", "facts"}`: `resolution|reason`.
* `user_evidence {"events", "ages", "g", "h", "a0", "b0", "half_life"}`:
  `F_u|A_u|n_u|E_u|lo|hi`, each number in version 1's twelve-digit form.
* `whitewash_count {"admissions", "retirements", "states", "window"}`: the line `count|n`,
  then one line `match|admitted|retired` per admission that counts, each name escaped as
  version 1 escaped it (`|` and `\` behind a backslash, a control as `\xNN`).

The answer is version 1's text of the result; a request version 1 refused is refused with
version 1's word as the detail, its checks made in its order. Every number is exact: the
aged weights and their sums are exact sums of rational multiples of powers of 2, and the
mean and the interval's ends are given by bounds narrowed until their twelve digits
settle. A number whose bounds up to 4096 bits do not settle its twelve digits is owed:
the answer is refused as `OWED`. No case of version 1's has one.

**The bound on an exact value.** The user evidence forms exact values from the request's
numbers: each aged weight `w 2^(-age / half_life)`, held as `w 2^n` beside the fraction
`-age / half_life - n` (`n` the whole part), their sums on each side, the shapes
`a0 + F_u` and `b0 + A_u`, and the mean when it is rational. Each is checked from the
sizes of what it is formed from before it is formed (`evidenceFits`): one whose numerator
or denominator could pass 65,536 bits is refused, "exact value too large".

Bounds, measured. The interval's ends are found by narrowing bounds on the Beta
distribution's quantiles, which costs more as the shapes hold more terms (each event aged
by an exponent of its own adds one), as they grow, and as they shrink toward 0, where the
ends approach 0 and 1 by many powers of ten: `user_evidence` takes at most `maxEvents`
events and ages, each number of at most `maxDigits` digits, and each shape `a0 + F_u`,
`b0 + A_u` from `minShape` to `maxShape`; the slowest requests found within them take
about 1.8 s. `whitewash_count` matches each admission against every retirement and finds
each retirement's state among the states: at most `maxAgents` of each, about 0.3 s.
`conduct_resolve` reads objects of a fixed form.
-/

namespace Principia.Calculator.Sponsor

open Principia.Canonical
open Principia.Sponsor
open Principia.Score (PowSum)
open Principia.Beta (Quantity)
open Principia.ValueBound (maxBits tooLarge)

/-! ## The family's bounds, measured -/

/-- The most events `user_evidence` ages and sums: 50, each aged by an exponent of its own
and all on one side, with the shapes near their bounds, take about 1.8 s; 100 took 2.5 s
and 1000 took 14.5 s. -/
def maxEvents : Nat := 50

/-- The most digits of a number `user_evidence` reads, the strike family's bound on a
measurement's: 50 events whose weights, `a0`, `b0` and half-life each carry 30 take about
1.5 s. -/
def maxDigits : Nat := 30

/-- The least shape `a0 + F_u` or `b0 + A_u` the interval is computed for: the lower end of
the interval of `Beta(a, 1)` is `0.025^(1/a)`, so `Beta(0.1, 0.1)` takes about
0.6 s, `Beta(0.01, 1)` 1.5 s and, with 50 events, more than 4 s, and `Beta(0.001, 1)` was
not settled at 4096 bits after 110 s. -/
def minShape : Rat := 1 / 10

/-- The largest shape `a0 + F_u` or `b0 + A_u` the interval is computed for: with 50 events
on both sides, shapes near 975 take about 1.7 s, near 9,900 about 2.7 s. -/
def maxShape : Rat := 1000

/-- The most admissions, retirements and states `whitewash_count` reads: 4000 of each,
none matched, take about 0.3 s; 6000 took 1.1 s. -/
def maxAgents : Nat := 4000

/-! ## The bound on an exact value -/

/-- `c 2^f` added to normalized terms, as the user evidence adds it, each sum checked
against the bound before it is formed. -/
def insertChecked (f c : Rat) : List (Rat × Rat) → ValueBound.Bounded (List (Rat × Rat))
  | [] => pure (if c = 0 then [] else [(f, c)])
  | (g, d) :: rest =>
    if f < g then pure (if c = 0 then (g, d) :: rest else (f, c) :: (g, d) :: rest)
    else if f = g then do
      let s ← ValueBound.add c d
      pure (if s = 0 then rest else (g, s) :: rest)
    else return (g, d) :: (← insertChecked f c rest)

/-- The sum of two sums of terms, checked. -/
def addChecked (x y : List (Rat × Rat)) : ValueBound.Bounded (List (Rat × Rat)) :=
  y.foldlM (fun acc t => insertChecked t.1 t.2 acc) x

/-- An event's aged weight `w 2^(-age / half_life)`, checked: the exponent, its whole part
`n` (refused when `2^n` alone would pass the bound), `w 2^n` and the fraction left. -/
def agedChecked (halfLife : Rat) (x : Weighed) : ValueBound.Bounded (List (Rat × Rat)) := do
  let e ← ValueBound.div (-(x.age : Rat)) halfLife
  x.weight.terms.foldlM (fun acc t => do
    let s ← ValueBound.add t.1 e
    let n := s.floor
    if maxBits < n.natAbs + 1 then throw tooLarge
    let g ← ValueBound.sub s n
    let c ← ValueBound.mul t.2 ((2 : Rat) ^ n)
    addChecked acc [(g, c)]) []

/-- The aged weights of one side's events, summed, checked. -/
def sideChecked (events : List Weighed) (s : Principia.Score.Side) (halfLife : Rat) :
    ValueBound.Bounded (List (Rat × Rat)) :=
  (events.filter (·.side == some s)).foldlM (fun acc x => do addChecked acc (← agedChecked halfLife x)) []

/-- A sum of terms that is a rational. -/
def ratOf? : List (Rat × Rat) → Option Rat
  | [] => some 0
  | [(f, c)] => if f = 0 then some c else none
  | _ => none

/-- Every exact value the user evidence forms, checked against the bound before it is
formed, in the order it forms them: the aged weights and their sums `F_u` and `A_u`, the
shapes, their sum, and the mean when it is rational or a rational multiple. -/
def evidenceFits (events : List Weighed) (a0 b0 halfLife : Rat) : ValueBound.Bounded Unit := do
  let f ← sideChecked events .supporting halfLife
  let a ← sideChecked events .opposing halfLife
  let sa ← addChecked (PowSum.ofRat a0).terms f
  let sb ← addChecked (PowSum.ofRat b0).terms a
  let total ← addChecked sa sb
  match ratOf? sa, ratOf? total with
  | some p, some q => let _ ← ValueBound.div p q
  | _, _ =>
    match sa, total with
    | (f1, c) :: _, (g1, d) :: _ =>
      let k ← ValueBound.div c d
      if f1 = g1 then
        for t in total do
          let _ ← ValueBound.mul k t.2
    | _, _ => pure ()

/-- A shape within `minShape` and `maxShape`, judged from its bounds at 64 bits (a shape
that is a rational, exactly): one within about `2^-64` of a bound may be refused. -/
def shapeWithin (x : PowSum) : Bool :=
  match x.isRat? with
  | some q => minShape ≤ q && q ≤ maxShape
  | none =>
    match x.enc 64 with
    | some i => minShape ≤ i.lo && i.hi ≤ maxShape
    | none => false

/-! ## Version 1's texts -/

/-- Version 1's `render_resolve`. -/
def renderResolve (r : Resolved) : String := WireWord.toWire r.1 ++ "|" ++ WireWord.toWire r.2

/-- Version 1's `render_whitewash`. -/
def renderWhitewash (ms : List (String × String)) : String :=
  "\n".intercalate (s!"count|{ms.length}" ::
    ms.map fun (adm, ret) => s!"match|{Identity.esc adm}|{Identity.esc ret}")

/-- What is owed when a number does not settle. -/
def unsettled : Refusal :=
  ⟨.owed, "a number of the user evidence whose bounds up to 4096 bits do not settle its twelve digits"⟩

/-- Version 1's `render_evidence`, or owed when a number does not settle. -/
def renderEvidence (r : Posterior) : Except Refusal Value :=
  match [r.f.toQuantity, r.a.toQuantity, r.e, r.lo, r.hi].mapM Quantity.twelve? with
  | some [f, a, e, lo, hi] => .ok (.str ("|".intercalate [f, a, toString r.n, e, lo, hi]))
  | _ => .error unsettled

/-- Version 1's word as a refusal. -/
def refused {α : Type} : Except String α → Except Refusal α
  | .ok a => .ok a
  | .error w => badArgument w

/-- The request's members, each one the function needs. -/
def read (names : List String) (v : Value) : Except Refusal (String → Value) := do
  let ms ← membersOf names v
  for n in names do
    let _ ← needed ms n
  pure fun k => (ms.lookup k).getD .null

/-- The number of entries of a list or an object, `0` for anything else. -/
def entries : Value → Nat
  | .arr xs => xs.length
  | .obj ms => ms.length
  | _ => 0

/-- Every number a value holds within `maxDigits` digits. -/
partial def digitsWithin (what : String) : Value → Except Refusal Unit
  | .arr xs => xs.forM (digitsWithin what)
  | .obj ms => ms.forM fun m => digitsWithin what m.2
  | v =>
    if maxDigits < numberDigits v then
      badArgument s!"a number of {what} has more than {maxDigits} digits (the Calculator's bound)"
    else .ok ()

/-- `user_evidence`: version 1's checks, the bounds, then the posterior. -/
def userEvidenceCall (v : Value) : Except Refusal Value := do
  let g ← read ["events", "ages", "g", "h", "a0", "b0", "half_life"] v
  atMost "events" maxEvents (List.replicate (entries (g "events")) ())
  atMost "ages" maxEvents (List.replicate (entries (g "ages")) ())
  for k in ["events", "g", "h", "a0", "b0", "half_life"] do
    digitsWithin k (g k)
  let (ws, a0, b0, hl) ← refused (readEvidence (g "events") (g "ages") (g "g") (g "h") (g "a0")
    (g "b0") (g "half_life"))
  bounded (evidenceFits ws a0 b0 hl)
  let p := posteriorOf ws a0 b0 hl
  unless shapeWithin (PowSum.add (PowSum.ofRat a0) p.f) &&
      shapeWithin (PowSum.add (PowSum.ofRat b0) p.a) do
    badArgument s!"a shape a0 + F_u or b0 + A_u is less than 1/10 or more than {maxShape} (the Calculator's bound)"
  renderEvidence p

/-- The family's functions. -/
def calls : Family := [
  ("conduct_resolve", fun v => do
    let g ← read ["event", "facts"] v
    .str <$> renderResolve <$> refused (conductResolve (g "event") (g "facts"))),
  ("user_evidence", userEvidenceCall),
  ("whitewash_count", fun v => do
    let g ← read ["admissions", "retirements", "states", "window"] v
    for k in ["admissions", "retirements", "states"] do
      atMost k maxAgents (List.replicate (entries (g k)) ())
    .str <$> renderWhitewash <$>
      refused (whitewashCount (g "admissions") (g "retirements") (g "states") (g "window"))),
]

end Principia.Calculator.Sponsor
