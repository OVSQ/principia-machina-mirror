import Principia.Falcon.Canon

/-!
# The per-kind stop

v1's `tpc_falcon` 0.2.0 (FM-14): `falcon_stop(counts, limits)`, whether
TPX may put out a falcon of a kind now (SP1 to SP6 in v1's text). A falcon's share is its
DECLINED and UNRESOLVED items over its items, over the last `window` falcons finished
since the kind's declaration or its latest resumption; the kind stops at the first
FINISHED after which the share passes the FALCON BREAKER (strictly above it, compared
exactly in ten-thousandths) and stays stopped until RESUMED; after a resumption one
falcon goes out alone first. A record TPX could not have made is refused (`counts`).
Integers throughout; no decision open.
-/

namespace Principia.Falcon.Stop

open Principia.Canonical (Value)
open Principia.Falcon

/-- The largest count v1 reads (v1's `COUNT_MAX`). -/
def countMax : Int := 1000000000

/-- v1's `_breaker`: the FALCON BREAKER, `0`, `0.` and one to four digits, `1`, or `1.`
and one to four zeros, as ten-thousandths. -/
def breaker (v : Value) : Option Nat :=
  match v with
  | .str s =>
    match s.toList with
    | ['0'] => some 0
    | '0' :: '.' :: ds =>
      if 1 ≤ ds.length && ds.length ≤ 4 && ds.all Char.isDigit then
        some ((ds ++ List.replicate (4 - ds.length) '0').foldl
          (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
      else none
    | ['1'] => some 10000
    | '1' :: '.' :: zs =>
      if 1 ≤ zs.length && zs.length ≤ 4 && zs.all (· == '0') then some 10000 else none
    | _ => none
  | _ => none

/-- Who goes out alone after a resumption: nobody waits (`none`), the first falcon is
awaited (`waiting`), or it is in flight (`falcon`). -/
inductive Alone where
  | waiting
  | falcon (id : String)
  deriving DecidableEq, Repr

/-- The running state (v1's locals). -/
structure Run where
  stopped : Bool := false
  epoch : Nat := 0
  flying : List (String × Nat) := []
  closed : List String := []
  window : List (Nat × Nat) := []
  alone : Option Alone := none

/-- The last `w` entries of a list (Python's `x[-w:]`). -/
def lastN {α : Type} (w : Nat) (xs : List α) : List α := xs.drop (xs.length - w)

/-- One record applied, or `none` when TPX could not have made it. -/
def Run.step (wmax b4 : Nat) (r : Run) (e : Value) : Option Run :=
  match e with
  | .arr [.str "ISSUED", x] =>
    match x with
    | .str id =>
      if id == "" || r.flying.any (·.1 == id) || r.closed.contains id || r.stopped then none
      else
        let alone? : Option (Option Alone) :=
          match r.alone with
          | none => some none
          | some a => if a != .waiting || !r.flying.isEmpty then none else some (some (.falcon id))
        alone?.map fun alone => { r with alone := alone, flying := r.flying ++ [(id, r.epoch)] }
    | _ => none
  | .arr [.str "FINISHED", x, items, declined, unresolved] =>
    match x with
    | .str id =>
      if id == "" then none
      else
        match r.flying.lookup id with
        | none => none
        | some ep =>
          if !([items, declined, unresolved].all fun v => isInt v 0 countMax) then none
          else
            let (n, d, u) := (natOf items, natOf declined, natOf unresolved)
            if n < d + u then none
            else
              let r := { r with flying := r.flying.filter (·.1 != id),
                                closed := r.closed ++ [id] }
              if ep != r.epoch then some r
              else
                let r := { r with window := r.window ++ [(n, d + u)],
                                  alone := if r.alone == some (Alone.falcon id) then none else r.alone }
                if r.stopped then some r
                else
                  let w := lastN wmax r.window
                  let total := (w.map (·.1)).sum
                  let bad := (w.map (·.2)).sum
                  some (if 0 < total && b4 * total < bad * 10000 then { r with stopped := true }
                    else r)
    | _ => none
  | .arr [.str "RESUMED"] =>
    some (if r.stopped then
      { r with stopped := false, epoch := r.epoch + 1, window := [], alone := some .waiting }
      else r)
  | _ => none

/-- The stop's result (v1's dict). -/
structure Stop where
  issuing : Bool
  bad : Nat
  total : Nat
  falcons : Nat
  alone : Option Alone
  inFlight : Nat

/-- v1's `falcon_stop(counts, limits)`. -/
def falconStop (counts limits : Value) : Result Stop := do
  if !keysAreV limits ["breaker", "window"] [] then refuse "limits"
  let ms := (members? limits).getD []
  let some b4 := (field? ms "breaker").bind breaker | refuse "limits"
  let wv := (field? ms "window").getD .null
  if !isInt wv 1 1000 then refuse "limits"
  let wmax := natOf wv
  let some es := (match counts with | .arr es => some es | _ => none) | refuse "counts"
  let some r := es.foldlM (Run.step wmax b4) ({} : Run) | refuse "counts"
  let issuing := !r.stopped &&
    (match r.alone with
      | none => true
      | some a => a == .waiting && r.flying.isEmpty)
  let w := lastN wmax r.window
  return { issuing := issuing, bad := (w.map (·.2)).sum, total := (w.map (·.1)).sum,
           falcons := w.length, alone := r.alone, inFlight := r.flying.length }

/-- v1's `render_stop`. -/
def renderStop (d : Stop) : String :=
  let alone := match d.alone with
    | none => "-"
    | some .waiting => "waiting"
    | some (.falcon a) => esc a
  s!"stop|{if d.issuing then "ISSUING" else "STOPPED"}\nshare|{d.bad}|{d.total}|{d.falcons}\n" ++
    s!"alone|{alone}\nin_flight|{d.inFlight}"

end Principia.Falcon.Stop
