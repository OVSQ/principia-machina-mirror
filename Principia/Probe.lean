import Principia.Digest
import Principia.Exact
import Principia.Form.Grammar
import Principia.Strike
import Principia.Strike.Bounded

/-!
# Probes and their comparison

v1's tpc_probe 0.2.0: the comparison of a reproduction with its target,
LOAD and EXPECTED LOSS, the PARROT RATIO's epoch, the CANARY SCHEDULE's tier, bursts and
gaps, the probe draw, the RESET's end by state, and the historical view of a register
revision. Each function takes its arguments as v1 took them, JSON-shaped (`Datum`), and
refuses what v1 refused with v1's fixed message (`ERROR:<message>` in its text).

**The draws.** v1's uniform value is `m / 2^52`, `m` the first 13 hexadecimal
digits of the SHA-256 of the netstring of `[tag, "1", r, counter]` (`drawBits`; SHA-256 is
`Principia.Sha256`, the Declarer's choice of SHA-256 under every digest): a rational in `[0, 1)` (`uniformValue_lt_one`), which v1's
double held exactly. Every number a draw compares it with is exact (the Declarer's choice of exact values),
where v1 computed it in doubles: the running sum of the PARROT RATIO's weights, `1 / rate`,
`k / (1 + k)` and the CONSISTENCY SHARE, each the exact value of the decimal given, and the
scaled count `udiscrete(lo, hi, u) = min(hi, lo + floor(u (hi - lo + 1)))`, whose floor is
taken exactly (`udiscrete`); v1's `min` is kept, as its text writes it, and never acts
(`udiscrete_floor_le`). On every case of v1's corpus the exact comparisons and v1's doubles
fall the same way (a script measured how far each lies from falling apart). Nothing is owed: every function answers.

A TEXT FINDING is canonical when it holds no carriage return and is its own NFC, as v1's
`unicodedata.is_normalized` found it, at Unicode 15.1.0 (`Principia.Unicode.isNfc`;
the Declarer's choice of the Unicode version of the normal form).

An EQUATION finding is canonical when the declared forms' `parse_form` gives it back
unchanged (`Principia.Form.parseForm`, read as an equation), as v1's `tpc_form` did.

Numbers are exact. Where v1's text printed a double (`canon_float`, C's `%.12g`), the text
here prints the exact value correctly rounded to twelve significant digits
(`Exact.printRat12`, `Exact.printSqrt12`). SR8's scale factor and SR3's test are the
strike rule's (`Principia.Strike`). An M comparison forms its values within the bound on an
exact value (`Principia.Strike.Bounded`, `Principia.ValueBound`): one whose values would
cross it is refused, "exact value too large".
-/

namespace Principia.Probe

/-! ## Arguments as v1 took them -/

/-- A JSON value as v1's functions received it: a number written as an integer is an
`int` (Python's `int`), one written with a fraction a `real` (Python's `float`). An
object keeps one value per key. -/
inductive Datum where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | real (q : Rat)
  | str (s : String)
  | arr (xs : List Datum)
  | obj (kvs : List (String × Datum))
  deriving Repr, Inhabited

namespace Datum

/-- A member of an object. -/
def get? : Datum → String → Option Datum
  | obj kvs, k => kvs.lookup k
  | _, _ => none

/-- A member of an object, `null` when absent (v1's `dict.get`). -/
def getD (d : Datum) (k : String) : Datum := (d.get? k).getD .null

/-- v1's `_keys_are`: an object holding every required key and no key outside the
required and optional ones. -/
def keysAre (d : Datum) (required : List String) (optional : List String := []) : Bool :=
  match d with
  | obj kvs =>
    required.all (fun k => kvs.any (·.1 == k)) &&
      kvs.all fun kv => required.contains kv.1 || optional.contains kv.1
  | _ => false

/-- v1's `_is_int`: an integer (not a boolean, not a float) within `lo..hi`. -/
def intIn? (d : Datum) (lo hi : Int) : Option Int :=
  match d with
  | int n => if lo ≤ n ∧ n ≤ hi then some n else none
  | _ => none

/-- v1's `_num`: an integer or a float, never a boolean. -/
def num? : Datum → Option Rat
  | int n => some n
  | real q => some q
  | _ => none

/-- v1's `_is_name`: a non-empty string. -/
def name? : Datum → Option String
  | str s => if s = "" then none else some s
  | _ => none

def str? : Datum → Option String
  | str s => some s
  | _ => none

def bool? : Datum → Option Bool
  | bool b => some b
  | _ => none

def arr? : Datum → Option (List Datum)
  | arr xs => some xs
  | _ => none

end Datum

open Datum

/-- An answer: computed, or refused with v1's message. -/
inductive Answer (α : Type) where
  | ok (a : α)
  | refused (message : String)
  deriving Repr

namespace Answer

def bind {α β : Type} : Answer α → (α → Answer β) → Answer β
  | ok a, f => f a
  | refused m, _ => refused m

instance : Monad Answer where
  pure := ok
  bind := bind

def map {α β : Type} (a : Answer α) (f : α → β) : Answer β := a.bind fun x => ok (f x)

/-- v1's text of an answer: the render, or `ERROR:` and the message. -/
def text {α : Type} (render : α → String) : Answer α → String
  | ok a => render a
  | refused m => "ERROR:" ++ m

end Answer

/-- Refuse with v1's message unless the value is there. -/
def need {α : Type} (o : Option α) (message : String) : Answer α :=
  match o with
  | some a => .ok a
  | none => .refused message

/-- Refuse with v1's message unless the condition holds. -/
def check (c : Bool) (message : String) : Answer Unit :=
  if c then .ok () else .refused message

/-- v1's bounds on counts and times. -/
def countMax : Int := 1000000000

/-- v1's `_esc`: a bar and a backslash escaped by a backslash, a control character or DEL
as `\xNN` in lower-case hexadecimal. -/
def esc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c = '|' ∨ c = '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 ∨ c.toNat = 0x7F then
      let ds := Nat.toDigits 16 c.toNat
      "\\x" ++ String.ofList (List.replicate (2 - ds.length) '0' ++ ds)
    else c.toString)

/-- v1's text of a boolean. -/
def boolText (b : Bool) : String := if b then "true" else "false"

/-- v1's `_is_hex(r, 32)`: 32 lower-case hexadecimal digits. -/
def isHex32 (d : Datum) : Bool :=
  match d with
  | str s => s.length = 32 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  | _ => false

/-! ## compare (SR3; SR8) -/

/-- A computation refused for the bound on an exact value, as an answer: refused with the
bound's word. -/
def bounded {α : Type} : ValueBound.Bounded α → Answer α
  | .ok a => .ok a
  | .error e => .refused e

/-- A canonical DECIMAL as the zone serialization writes it (tpm_zone_schemas 5.6):
`0`, or `-?[1-9]([0-9]*[1-9])?(e-?[1-9][0-9]*)?`. -/
def canonDecimalOk (s : String) : Bool :=
  let cs := s.toList
  if cs = ['0'] then true
  else
    let cs := match cs with
      | '-' :: r => r
      | r => r
    let (mant, rest) := cs.span Char.isDigit
    let mantOk := match mant with
      | [] => false
      | d :: _ => d != '0' && mant.getLast? != some '0'
    let expOk := match rest with
      | [] => true
      | 'e' :: r =>
        let r := match r with
          | '-' :: r' => r'
          | r' => r'
        match r with
        | d :: _ => d != '0' && r.all Char.isDigit
        | [] => false
      | _ => false
    mantOk && expOk

/-- A canonical TEXT (NFC with LF line endings): no carriage return, and its own NFC (v1's
`_canon_text_ok`). Lean's strings hold no surrogate, which v1 also refused. -/
def canonText (s : String) : Answer Bool :=
  if s.toList.any (· = '\r') then .ok false
  else .ok (Unicode.isNfc s)

/-- A canonical EQUATION: `parse_form(value, "equation")` gives the value back unchanged
(the declared forms' canonical spelling). A refusal of the form is a value not canonical;
reading a form is never owed (`Form.parse_not_owed`), so the last case is never met. -/
def canonEquation (s : String) : Answer Bool :=
  match Form.parseForm s .equation with
  | .ok c => .ok (c == s)
  | .refused _ => .ok false
  | .owed _ => .ok false

/-- v1's `_finding`: an L record's FINDING, its type and its canonical value. -/
def finding (o : Datum) : Answer (String × String) := do
  check (o.keysAre ["finding"]) "record"
  let f := o.getD "finding"
  let ty ← need ((f.getD "type").str?.filter fun t => t = "TEXT" ∨ t = "DECIMAL" ∨ t = "EQUATION")
    "record"
  check (f.keysAre ["type", "value"]) "record"
  let v ← need (f.getD "value").str? "record"
  let ok ← match ty with
    | "EQUATION" => canonEquation v
    | "TEXT" => canonText v
    | _ => .ok (canonDecimalOk v)
  check ok "CANON"
  return (ty, v)

/-- v1's `_mrec`: an M record's value, uncertainty and UNIT. -/
def mrec (o : Datum) : Answer (Rat × Rat × String) := do
  check (o.keysAre ["x", "u", "unit"]) "record"
  match (o.getD "x").num?, (o.getD "u").num?, (o.getD "unit").str? with
  | some x, some u, some unit => if u ≤ 0 then .refused "record" else .ok (x, u, unit)
  | _, _, _ => .refused "record"

/-- An M comparison: the two measurements, SR8's `S` (as `S²`), `k`, the SR3 statistic
(as its square), the UNIT, and, on a match, the uncertainty ratio. -/
structure MCompare where
  outcome : String
  x1 : Rat
  u1 : Rat
  x2 : Rat
  u2 : Rat
  sSquare : Rat
  k : Rat
  statSquare : Rat
  unit : String
  ratio : Option Rat
  deriving Repr

/-- A comparison's result. -/
inductive Comparison where
  | l (outcome original reproduction : String)
  | m (r : MCompare)
  deriving Repr

/-- v1's `compare`: an L comparison is byte equality of canonical FINDINGs (zero
tolerance); an M comparison is SR3's M-M test after SR8's scaling, in one UNIT, a material
difference of uncertainty noted on a match. -/
def compare (kind original reproduction standing k materialRatio : Datum) :
    Answer Comparison := do
  match kind with
  | .str "L" =>
    let (t1, v1) ← finding original
    let (t2, v2) ← finding reproduction
    check (t1 = t2) "form"
    return .l (if v1 = v2 then "MATCH" else "NON-CORROBORATION") v1 v2
  | .str "M" =>
    let (x1, u1, unit1) ← mrec original
    let (x2, u2, unit2) ← mrec reproduction
    check (unit1 = unit2) "UNIT"
    let kf ← need (k.num?.filter (0 < ·)) "k"
    let mr ← need (materialRatio.num?.filter (1 ≤ ·)) "material_ratio"
    let ms ← need standing.arr? "standing"
    let meas ← ms.mapM fun m => do
      check (m.keysAre ["x", "u"]) "standing"
      match (m.getD "x").num?, (m.getD "u").num? with
      | some x, some u =>
        if u ≤ 0 then Answer.refused "standing"
        else pure ({ value := x, uncertainty := u } : Strike.Measurement)
      | _, _ => .refused "standing"
    let S ← need (← bounded (Strike.Bounded.sr8ScaleFactor meas)) "standing"
    let statSquare ← bounded do
      let d ← ValueBound.sub x1 x2
      let dd ← ValueBound.mul d d
      let a ← ValueBound.mul u1 u1
      let b ← ValueBound.mul u2 u2
      let ab ← ValueBound.add a b
      ValueBound.div dd (← ValueBound.mul S.square ab)
    let base : MCompare := ⟨"", x1, u1, x2, u2, S.square, kf, statSquare, unit1, none⟩
    if ← bounded (Strike.Bounded.mmContradicts x1 u1 x2 u2 kf S) then
      return .m { base with outcome := "NON-CORROBORATION" }
    let ratio ← bounded (if u1 ≥ u2 then ValueBound.div u1 u2 else ValueBound.div u2 u1)
    return .m { base with
      outcome := if ratio ≥ mr then "MATCH WITH DIFFERENCE NOTED" else "MATCH",
      ratio := some ratio }
  | _ => .refused "kind"

/-- v1's `render_compare`. -/
def renderCompare : Comparison → String
  | .l outcome o r => "L|" ++ outcome ++ "|" ++ esc o ++ "|" ++ esc r
  | .m c =>
    "|".intercalate (["M", c.outcome] ++
      [c.x1, c.u1, c.x2, c.u2].map Exact.printRat12 ++
      [Exact.printSqrt12 c.sSquare, Exact.printRat12 c.k, Exact.printSqrt12 c.statSquare,
        esc c.unit]) ++
      match c.ratio with
      | some q => "|" ++ Exact.printRat12 q
      | none => ""

/-! ## LOAD and EXPECTED LOSS -/

/-- A record of the LOAD graph: its citations and ASSUMPTIONS, and whether it stands. -/
structure GraphRecord where
  edges : List String
  standing : Bool
  deriving Repr

/-- v1's `_graph`: the records, each checked. -/
def graph (records : Datum) : Answer (List (String × GraphRecord)) := do
  let kvs ← match records with
    | .obj kvs => Answer.ok kvs
    | _ => .refused "records"
  kvs.mapM fun (rid, rec) => do
    check (rid ≠ "" && rec.keysAre ["cites", "assumptions", "standing"]) "records"
    let cites ← need (rec.getD "cites").arr? "records"
    let assumptions ← need (rec.getD "assumptions").arr? "records"
    let standing ← need (rec.getD "standing").bool? "records"
    let edges ← (cites ++ assumptions).mapM fun x => need x.name? "records"
    return (rid, ⟨edges, standing⟩)

/-- The walk of `reaches`: pop an identifier; one seen before, or outside the records, is
skipped; a record not seen before is visited, `true` when it cites or assumes `target`,
else its edges are pushed. A visit spends one `fuel`; a skip shortens the stack. -/
def reachesWalk (g : List (String × GraphRecord)) (target : String) :
    Nat → List String → List String → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => false
  | fuel + 1, cur :: stack, seen =>
    if seen.contains cur then reachesWalk g target (fuel + 1) stack seen
    else
      match g.lookup cur with
      | none => reachesWalk g target (fuel + 1) stack seen
      | some rec => if rec.edges.contains target then true
        else reachesWalk g target fuel (rec.edges ++ stack) (cur :: seen)
termination_by fuel stack => (fuel, stack.length)

/-- Whether `target`, a record, is reached from `start` over one or more citations or
ASSUMPTIONS, through any record; an identifier outside the records ends its path (v1's
`_closure`). Each record is visited once, so the fuel, one more than the records, is
never the limit. -/
def reaches (g : List (String × GraphRecord)) (start target : String) : Bool :=
  reachesWalk g target (g.length + 1) [start] []

/-- v1's `load`: the standing records other than `r` that reach `r` over citations and
ASSUMPTIONS, in code-point order, and their count. -/
def load (records rd : Datum) : Answer (Nat × List String) := do
  let g ← graph records
  let r ← need (rd.name?.filter fun r => (g.lookup r).isSome) "r"
  let ids := (g.map (·.1)).mergeSort fun a b => decide (a ≤ b)
  let reach := ids.filter fun s => s ≠ r && ((g.lookup s).map (·.standing)).getD false &&
    reaches g s r
  return (reach.length, reach)

/-- v1's `render_load`. -/
def renderLoad (d : Nat × List String) : String :=
  toString d.1 ++ "|" ++ ",".intercalate (d.2.map esc)

/-- v1's `expected_loss`: `(1 - e_lo) × LOAD`. -/
def expectedLoss (eLo loadD : Datum) : Answer Rat := do
  let e ← need (eLo.num?.filter fun e => 0 ≤ e ∧ e ≤ 1) "e_lo"
  let l ← need (loadD.intIn? 0 countMax) "load"
  return (1 - e) * l

/-! ## The RESET -/

/-- A reset: in force or not, and the canary passes counted under it. -/
structure Reset where
  inForce : Bool
  passes : Int
  deriving Repr

/-- v1's `_reset`. -/
def readReset (d : Datum) : Answer Reset := do
  check (d.keysAre ["in_force", "passes"]) "reset"
  let f ← need (d.getD "in_force").bool? "reset"
  let p ← need ((d.getD "passes").intIn? 0 countMax) "reset"
  return ⟨f, p⟩

/-- A reset after an event, and how it ended (`-` when it did not). -/
structure ResetUpdate where
  inForce : Bool
  passes : Int
  ending : String
  deriving Repr

/-- The reset rule on checked arguments: a NON-CORROBORATION starts (or restarts) the
reset; a CANARY PASS counts, ending it under GREEN or YELLOW at once and under ORANGE at
ORANGE PASSES consecutive passes, never under SUSPENDED; a CANARY FAIL ends it as CR6's
case; a PARROT PASS changes nothing; an AUDIT FINDING ends it under SUSPENDED only. -/
def resetRule (reset : Reset) (ev st : String) (orange : Int) : ResetUpdate :=
  if ev = "NON-CORROBORATION" then ⟨true, 0, "-"⟩
  else if !reset.inForce then ⟨false, 0, "-"⟩
  else if ev = "CANARY FAIL" then ⟨false, 0, "CR6"⟩
  else if ev = "PARROT PASS" then ⟨true, reset.passes, "-"⟩
  else if ev = "AUDIT FINDING" then
    if st = "SUSPENDED" then ⟨false, 0, "AUDIT"⟩ else ⟨true, reset.passes, "-"⟩
  else if st = "GREEN" ∨ st = "YELLOW" then ⟨false, 0, "PASS"⟩
  else if st = "ORANGE" ∧ reset.passes + 1 ≥ orange then ⟨false, 0, "PASSES"⟩
  else ⟨true, reset.passes + 1, "-"⟩

/-- v1's `reset_update`: the arguments checked, then `resetRule`. -/
def resetUpdate (resetD event accountState params : Datum) : Answer ResetUpdate := do
  let reset ← readReset resetD
  let ev ← need (event.str?.filter fun e => ["NON-CORROBORATION", "CANARY PASS", "CANARY FAIL",
    "PARROT PASS", "AUDIT FINDING"].contains e) "event"
  let st ← need (accountState.str?.filter fun s => ["GREEN", "YELLOW", "ORANGE",
    "SUSPENDED"].contains s) "account_state"
  let orange ← need ((params.get? "ORANGE PASSES").bind (·.intIn? 1 countMax))
    "params:ORANGE PASSES"
  return resetRule reset ev st orange

/-- v1's `render_reset`. -/
def renderReset (d : ResetUpdate) : String :=
  boolText d.inForce ++ "|" ++ toString d.passes ++ "|" ++ d.ending

/-! ## The HISTORICAL VIEW -/

/-- v1's `historical_view`: the last revision before the one that allocated `target`
(none when that is the first) and the identifiers allocated through it, in order. -/
def historicalView (revisions target : Datum) : Answer (Option Int × List String) := do
  let revs ← need revisions.arr? "revisions"
  let t ← need target.name? "revisions"
  let rows ← (revs.foldlM (fun (acc : List (Int × List String) × List String × Option Int)
      (rv : Datum) => do
    let (rows, seen, last) := acc
    check (rv.keysAre ["rev", "allocated"]) "revisions"
    let rev ← need ((rv.getD "rev").intIn? 0 countMax) "revisions"
    check (last.all (· < rev)) "revisions"
    let alloc ← need (rv.getD "allocated").arr? "revisions"
    let (ids, seen) ← alloc.foldlM (fun (acc : List String × List String) (x : Datum) => do
      let n ← need (x.name?.filter fun n => !acc.2.contains n) "revisions"
      return (acc.1 ++ [n], n :: acc.2)) ([], seen)
    return (rows ++ [(rev, ids)], seen, some rev)) ([], [], none)).map (·.1)
  let where_ ← need ((rows.find? fun r => r.2.contains t).map (·.1)) "target"
  let before := rows.filter (·.1 < where_)
  return (before.getLast?.map (·.1), before.flatMap (·.2))

/-- v1's `render_view`. -/
def renderView (d : Option Int × List String) : String :=
  (match d.1 with
    | some r => toString r
    | none => "-") ++ "|" ++ ",".intercalate (d.2.map esc)

/-! ## The draws

v1's `uniform`, `udiscrete`, `ratio_step`, `schedule_step`, `probe_draw` and `probe_step`.
Every check v1 makes before it draws is made first, in v1's order; the draws then use
SHA-256 and compare exactly. -/

/-- `2^52`: v1's `TWO52`, the denominator of every uniform value. -/
def two52 : Nat := 2 ^ 52

/-- The first 13 hexadecimal digits of a digest as a number: its first 52 bits, the six
first bytes and the high half of the seventh. -/
def top52 (d : ByteArray) : Nat :=
  ((d.get! 0).toNat * 2 ^ 48 + (d.get! 1).toNat * 2 ^ 40 + (d.get! 2).toNat * 2 ^ 32 +
    (d.get! 3).toNat * 2 ^ 24 + (d.get! 4).toNat * 2 ^ 16 + (d.get! 5).toNat * 2 ^ 8 +
    (d.get! 6).toNat) / 16

/-- v1's draw as the numerator of its uniform value: the first 13 hexadecimal digits
of the SHA-256 of the netstring of `[tag, "1", r, counter]` (v1's `_digest_fields`). -/
def drawBits (tag r : String) (counter : Nat) : Nat :=
  top52 (Sha256.digest (Digest.preimage [tag, "1", r, toString counter]).toUTF8)

/-- v1's uniform value `int(h[:13], 16) / 2^52`, exactly. -/
def uniformValue (tag r : String) (counter : Nat) : Rat :=
  (drawBits tag r counter : Rat) / (two52 : Rat)

/-- v1's `udiscrete(lo, hi, u)` at `u = m / 2^52`: `min(hi, lo + floor(u (hi - lo + 1)))`,
the floor taken exactly, `floor(m n / 2^52)` for `n = hi - lo + 1`. -/
def udiscrete (lo hi : Int) (m : Nat) : Int :=
  min hi (lo + ((m * (hi - lo + 1).toNat / two52 : Nat) : Int))

/-- The text of `r` once `isHex32` has accepted it. -/
def hexText : Datum → String
  | .str s => s
  | _ => ""

/-- v1's `uniform(tag, r, counter)`: its arguments checked, then the uniform value. -/
def uniform (tag r counter : Datum) : Answer Rat := do
  let t ← need tag.name? "tag"
  check (isHex32 r) "r"
  let c ← need (counter.intIn? 0 countMax) "counter"
  return uniformValue t (hexText r) c.toNat

/-- v1's `_pair`: two integers within `lo..hi`, in order. -/
def pair (params : Datum) (key : String) (lo hi : Int) (label : String) : Answer (Int × Int) := do
  let v ← need (params.get? key) ("params:" ++ label)
  let xs ← need v.arr? ("params:" ++ label)
  match xs with
  | [a, b] =>
    match a.intIn? lo hi, b.intIn? lo hi with
    | some a, some b => if a ≤ b then pure (a, b) else .refused ("params:" ++ label)
    | _, _ => .refused ("params:" ++ label)
  | _ => .refused ("params:" ++ label)

/-- v1's `_ratio_params`: the PARROT RATIO's set, weights (summing to 1 within 10^-9, as
v1 allowed for its floats) and epoch bounds. -/
def ratioParams (params : Datum) : Answer (List Rat × List Rat × Int × Int) := do
  let lbl := "params:PARROT RATIO"
  let pr ← need (params.get? "PARROT RATIO") lbl
  check (pr.keysAre ["set", "weights", "epoch"]) lbl
  let st ← need (pr.getD "set").arr? lbl
  let ws ← need (pr.getD "weights").arr? lbl
  check (!st.isEmpty && st.length = ws.length) lbl
  let pairs ← (st.zip ws).mapM fun (kv, wv) =>
    match kv.num?, wv.num? with
    | some k, some w => if k ≤ 0 ∨ w < 0 then Answer.refused lbl else pure (k, w)
    | _, _ => .refused lbl
  let total := (pairs.map (·.2)).foldl (· + ·) 0
  let tol : Rat := 1 / 1000000000
  check (0 < total ∧ total - 1 ≤ tol ∧ 1 - total ≤ tol) lbl
  let (lo, hi) ← pair pr "epoch" 1 countMax "PARROT RATIO"
  return (pairs.map (·.1), pairs.map (·.2), lo, hi)

/-- RS1's `k`: the first member of the set whose cumulative weight exceeds `u`, the last
member when none does. The running sum is exact. -/
def pickK (u : Rat) (ks ws : List Rat) : Rat :=
  go 0 (ks.zip ws)
where
  go (cum : Rat) : List (Rat × Rat) → Rat
    | [] => ks.getLast?.getD 0
    | (k, w) :: rest => if u < cum + w then k else go (cum + w) rest

/-- A ratio step: `k` in force, the blocks left in the epoch, whether this block drew a new
epoch, and its length. -/
structure RatioStep where
  k : Rat
  remaining : Int
  drawn : Bool
  length : Option Int
  deriving Repr

/-- v1's `ratio_step`: inside an epoch the count goes down; a block that starts an epoch
draws its length (`TPC-RATIO-EPOCH`) and its `k` (`TPC-RATIO-K`), counter 0. -/
def ratioStep (state r params : Datum) : Answer RatioStep := do
  check (state.keysAre ["k", "remaining"]) "state"
  let k? ← match state.getD "k" with
    | .null => pure none
    | kd => match kd.num? with
      | some k => if 0 < k then pure (some k) else Answer.refused "state"
      | none => .refused "state"
  let remaining ← need ((state.getD "remaining").intIn? 0 countMax) "state"
  check (isHex32 r) "r"
  let (ks, ws, lo, hi) ← ratioParams params
  match k? with
  | some k => if remaining ≠ 0 then return ⟨k, remaining - 1, false, none⟩ else pure ()
  | none => pure ()
  let rs := hexText r
  let length := udiscrete lo hi (drawBits "TPC-RATIO-EPOCH" rs 0)
  let k := pickK (uniformValue "TPC-RATIO-K" rs 0) ks ws
  return ⟨k, length - 1, true, some length⟩

/-- v1's `render_ratio`. -/
def renderRatio (d : RatioStep) : String :=
  Exact.printRat12 d.k ++ "|" ++ toString d.remaining ++ "|" ++ boolText d.drawn ++ "|" ++
    (match d.length with
      | some l => toString l
      | none => "-")

/-- A row of the CANARY SCHEDULE: its first block, its last (none for the last row) and
its rate. -/
structure Tier where
  first : Int
  last : Option Int
  rate : Int
  deriving Repr

/-- v1's `_schedule_params`. -/
def scheduleParams (params : Datum) :
    Answer (List Tier × List Int × (Int × Int) × (Int × Int)) := do
  let lbl := "params:CANARY SCHEDULE"
  let cs ← need (params.get? "CANARY SCHEDULE") lbl
  check (cs.keysAre ["tiers", "burst_rates", "burst_duration", "burst_gap"]) lbl
  let tiers ← need ((cs.getD "tiers").arr?.filter (!·.isEmpty)) lbl
  let n := tiers.length
  let (rows, _) ← tiers.zipIdx.foldlM (fun (acc : List Tier × Int) (t, i) => do
    let (rows, expect) := acc
    let xs ← need t.arr? lbl
    match xs with
    | [frm, to, rate] =>
      let f ← need (frm.intIn? 1 countMax) lbl
      check (f = expect) lbl
      let rt ← need (rate.intIn? 1 countMax) lbl
      if i + 1 = n then
        match to with
        | .null => pure (rows ++ [⟨f, none, rt⟩], expect)
        | _ => .refused lbl
      else
        let tt ← need (to.intIn? f countMax) lbl
        pure (rows ++ [⟨f, some tt, rt⟩], tt + 1)
    | _ => .refused lbl) ([], 1)
  let br ← need ((cs.getD "burst_rates").arr?.filter (!·.isEmpty)) lbl
  let brs ← br.mapM fun x => need (x.intIn? 1 countMax) lbl
  let dur ← pair cs "burst_duration" 1 countMax "CANARY SCHEDULE"
  let gap ← pair cs "burst_gap" 1 countMax "CANARY SCHEDULE"
  return (rows, brs, dur, gap)

/-- A schedule step: this block's tenure number, tier and rate, whether it is in a burst,
and the new state (the burst in force as rate and blocks left, and the gap). -/
structure ScheduleStep where
  blocks : Int
  tier : Nat
  rate : Int
  burst : Bool
  newBurst : Option (Int × Int)
  newGap : Option Int
  deriving Repr

/-- v1's `schedule_step`: the block's tier by its tenure number; from the last row's first
block, bursts and gaps (SC2): in a burst, its rate, and at its end a gap drawn
(`TPC-SCHEDULE-GAP`, counter 0); else the gap in force or one drawn on entering the burst
regime, counted down, and at 0 a burst starting here, its rate by even odds among the
burst rates (`TPC-SCHEDULE-RATE`) and its duration (`TPC-SCHEDULE-DURATION`), a duration of 1
ending it here and drawing the next gap (`TPC-SCHEDULE-GAP`, counter 1). -/
def scheduleStep (state r params : Datum) : Answer ScheduleStep := do
  check (state.keysAre ["blocks", "burst", "gap"]) "state"
  let blocks ← need ((state.getD "blocks").intIn? 0 (countMax - 1)) "state"
  let burst ← match state.getD "burst" with
    | .null => pure none
    | b => do
      check (b.keysAre ["rate", "remaining"]) "state"
      let rt ← need ((b.getD "rate").intIn? 1 countMax) "state"
      let rem ← need ((b.getD "remaining").intIn? 1 countMax) "state"
      pure (some (rt, rem))
  let gap ← match state.getD "gap" with
    | .null => pure none
    | g => (need (g.intIn? 1 countMax) "state").map some
  check (burst.isNone || gap.isNone) "state"
  check (isHex32 r) "r"
  let (rows, brates, dur, gp) ← scheduleParams params
  let rs := hexText r
  let b := blocks + 1
  let lastRow := rows.getLast?.getD ⟨1, none, 1⟩
  let (tier, tierRate) := match (rows.zipIdx.find? fun (t, _) =>
      t.first ≤ b ∧ t.last.all (b ≤ ·)) with
    | some (t, i) => (i + 1, t.rate)
    | none => (0, lastRow.rate)
  let gapDrawn (counter : Nat) := udiscrete gp.1 gp.2 (drawBits "TPC-SCHEDULE-GAP" rs counter)
  if b < lastRow.first then return ⟨b, tier, tierRate, false, none, none⟩
  match burst with
  | some (rt, rem) =>
    if rem - 1 = 0 then return ⟨b, tier, rt, true, none, some (gapDrawn 0)⟩
    else return ⟨b, tier, rt, true, some (rt, rem - 1), none⟩
  | none =>
    let g := (match gap with
      | some g => g
      | none => gapDrawn 0) - 1
    if g ≠ 0 then return ⟨b, tier, tierRate, false, none, some g⟩
    let idx := udiscrete 0 (brates.length - 1) (drawBits "TPC-SCHEDULE-RATE" rs 0)
    let length := udiscrete dur.1 dur.2 (drawBits "TPC-SCHEDULE-DURATION" rs 0)
    let rate := brates.getD idx.toNat 0
    if length - 1 = 0 then return ⟨b, tier, rate, true, none, some (gapDrawn 1)⟩
    else return ⟨b, tier, rate, true, some (rate, length - 1), none⟩

/-- v1's `render_schedule`. -/
def renderSchedule (d : ScheduleStep) : String :=
  "|".intercalate [toString d.blocks, toString d.tier, toString d.rate, boolText d.burst,
    (match d.newBurst with
      | some (rt, rem) => toString rt ++ "/" ++ toString rem
      | none => "-"),
    (match d.newGap with
      | some g => toString g
      | none => "-")]

/-- A probe draw's recording form: whether the block is probed, the probe's kind, and the
tier, burst, rate, ratio and reset it was drawn under. -/
structure ProbeDraw where
  probe : Bool
  kind : Option String
  tier : Int
  burst : Bool
  rate : Int
  ratio : Rat
  reset : Bool
  deriving Repr

/-- PD1 to PD3 on checked arguments, exactly: probe when `u0 < 1 / rate`; a parrot when
`u1 < k / (1 + k)`, else a CANARY; a CONSISTENCY PARROT when `u2 < CONSISTENCY SHARE` and
the account has an eligible own record, else a CORROBORATION PARROT (`TPC-PROBE`, counters
0, 1 and 2). -/
def probeKind (rs : String) (rate : Int) (k share : Rat) (ownRecord : Bool) :
    Bool × Option String :=
  if uniformValue "TPC-PROBE" rs 0 < 1 / (rate : Rat) then
    if uniformValue "TPC-PROBE" rs 1 < k / (1 + k) then
      if uniformValue "TPC-PROBE" rs 2 < share && ownRecord then (true, some "CONSISTENCY PARROT")
      else (true, some "CORROBORATION PARROT")
    else (true, some "CANARY")
  else (false, none)

/-- v1's `probe_draw`: its arguments checked, then PD1 to PD3 (`probeKind`) at the RESET
RULE's rate when the reset is in force, else at the schedule's. -/
def probeDraw (schedule ratioK reset hasOwnRecord r params : Datum) : Answer ProbeDraw := do
  check (schedule.keysAre ["tier", "rate", "burst"]) "schedule"
  let tier ← need ((schedule.getD "tier").intIn? 1 countMax) "schedule"
  let srate ← need ((schedule.getD "rate").intIn? 1 countMax) "schedule"
  let burst ← need (schedule.getD "burst").bool? "schedule"
  let k ← need (ratioK.num?.filter (0 < ·)) "ratio"
  let rst ← readReset reset
  let own ← need hasOwnRecord.bool? "has_own_record"
  check (isHex32 r) "r"
  check ((params.get? "RESET RULE").isSome && (params.get? "CONSISTENCY SHARE").isSome)
    "params:RESET RULE"
  let resetRate ← need ((params.getD "RESET RULE").intIn? 1 countMax) "params:RESET RULE"
  let share ← need ((params.getD "CONSISTENCY SHARE").num?.filter fun s => 0 ≤ s ∧ s ≤ 1)
    "params:CONSISTENCY SHARE"
  let rate := if rst.inForce then resetRate else srate
  let (probe, kind) := probeKind (hexText r) rate k share own
  return ⟨probe, kind, tier, burst, rate, k, rst.inForce⟩

/-- v1's `render_probe`. -/
def renderProbe (d : ProbeDraw) : String :=
  "|".intercalate [boolText d.probe, d.kind.getD "-", toString d.tier, boolText d.burst,
    toString d.rate, Exact.printRat12 d.ratio, boolText d.reset]

/-- A probe step: the probe draw, the ratio step and the schedule step of one block. -/
structure ProbeStep where
  probe : ProbeDraw
  ratio : RatioStep
  schedule : ScheduleStep
  deriving Repr

/-- v1's `probe_step`: `ratio_step`, `schedule_step` and `probe_draw` on one state, in that
order, the probe drawn under the schedule's tier, rate and burst and the ratio's `k`. -/
def probeStep (state r params hasOwnRecord : Datum) : Answer ProbeStep := do
  check (state.keysAre ["schedule", "ratio", "reset"]) "state"
  let rs ← ratioStep (state.getD "ratio") r params
  let sc ← scheduleStep (state.getD "schedule") r params
  let pd ← probeDraw
    (.obj [("tier", .int sc.tier), ("rate", .int sc.rate), ("burst", .bool sc.burst)])
    (.real rs.k) (state.getD "reset") hasOwnRecord r params
  return ⟨pd, rs, sc⟩

/-- v1's `render_step`: the probe, the ratio and the schedule, one line each. -/
def renderStep (d : ProbeStep) : String :=
  "\n".intercalate [renderProbe d.probe, renderRatio d.ratio, renderSchedule d.schedule]

end Principia.Probe

namespace Principia.Probe

/-! ## PROVED -/

@[simp] theorem need_some {α : Type} (a : α) (m : String) : need (some a) m = .ok a := rfl
@[simp] theorem need_none {α : Type} (m : String) : need (none : Option α) m = .refused m := rfl
@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Answer β) : (Answer.ok a >>= f) = f a :=
  rfl
@[simp] theorem refused_bind {α β : Type} (m : String) (f : α → Answer β) :
    (Answer.refused m >>= f) = .refused m := rfl
@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Answer α) = .ok a := rfl

/-- An answer chained is computed exactly when each link is. -/
theorem bind_eq_ok {α β : Type} {a : Answer α} {f : α → Answer β} {b : β} :
    (a >>= f) = .ok b ↔ ∃ x, a = .ok x ∧ f x = .ok b := by
  cases a with
  | ok x => simp
  | refused m => simp

@[simp] theorem check_eq_ok {c : Bool} {m : String} {u : Unit} :
    check c m = .ok u ↔ c = true := by
  unfold check; split <;> simp_all

theorem Datum.intIn?_bounds {d : Datum} {lo hi n : Int} (h : d.intIn? lo hi = some n) :
    lo ≤ n ∧ n ≤ hi := by
  unfold Datum.intIn? at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-! ### The draws -/

/-- The first 13 hexadecimal digits of a digest are below `2^52`. -/
theorem top52_lt (d : ByteArray) : top52 d < two52 := by
  unfold top52 two52
  have h0 := (d.get! 0).toNat_lt
  have h1 := (d.get! 1).toNat_lt
  have h2 := (d.get! 2).toNat_lt
  have h3 := (d.get! 3).toNat_lt
  have h4 := (d.get! 4).toNat_lt
  have h5 := (d.get! 5).toNat_lt
  have h6 := (d.get! 6).toNat_lt
  omega

theorem drawBits_lt (tag r : String) (counter : Nat) : drawBits tag r counter < two52 :=
  top52_lt _

theorem two52_pos : (0 : Rat) < (two52 : Rat) := by
  rw [show (0 : Rat) = ((0 : Nat) : Rat) from rfl, Rat.natCast_lt_natCast]; decide

/-- A uniform value is at least 0. -/
theorem uniformValue_nonneg (tag r : String) (counter : Nat) :
    0 ≤ uniformValue tag r counter := by
  unfold uniformValue
  apply Rat.not_lt.mp
  rw [Rat.div_lt_iff two52_pos, Rat.zero_mul]
  exact Rat.not_lt.mpr Rat.natCast_nonneg

/-- A uniform value is below 1. -/
theorem uniformValue_lt_one (tag r : String) (counter : Nat) :
    uniformValue tag r counter < 1 := by
  unfold uniformValue
  rw [Rat.div_lt_iff two52_pos, Rat.one_mul, Rat.natCast_lt_natCast]
  exact drawBits_lt tag r counter

/-- PD1 compares integers: the uniform value is below `1 / rate` exactly when its 52 bits
times the rate are below `2^52`. -/
theorem uniformValue_lt_inv {tag r : String} {counter rate : Nat} (hr : 0 < rate) :
    uniformValue tag r counter < 1 / (rate : Rat) ↔ drawBits tag r counter * rate < two52 := by
  have hr' : (0 : Rat) < (rate : Rat) := by
    rw [show (0 : Rat) = ((0 : Nat) : Rat) from rfl, Rat.natCast_lt_natCast]; exact hr
  unfold uniformValue
  rw [Rat.lt_div_iff hr', Rat.div_def, Rat.mul_assoc, Rat.mul_comm _ (rate : Rat),
    ← Rat.mul_assoc, ← Rat.div_def, Rat.div_lt_iff two52_pos, Rat.one_mul,
    ← Rat.natCast_mul, Rat.natCast_lt_natCast]

/-- A drawn count lies in its range. -/
theorem udiscrete_mem {lo hi : Int} (m : Nat) (h : lo ≤ hi) :
    lo ≤ udiscrete lo hi m ∧ udiscrete lo hi m ≤ hi := by
  unfold udiscrete
  have : (0 : Int) ≤ ((m * (hi - lo + 1).toNat / two52 : Nat) : Int) := Int.natCast_nonneg _
  exact ⟨Int.le_min.mpr ⟨h, by omega⟩, Int.min_le_left _ _⟩

/-- v1's `min(hi, ...)` never acts on an exact value: the exact floor of `u (hi - lo + 1)` is
at most `hi - lo` for every uniform value. (It guarded v1's double product.) -/
theorem udiscrete_floor_le {lo hi : Int} {m : Nat} (h : lo ≤ hi) (hm : m < two52) :
    lo + ((m * (hi - lo + 1).toNat / two52 : Nat) : Int) ≤ hi := by
  have hn : 0 < (hi - lo + 1).toNat := by omega
  have hlt : m * (hi - lo + 1).toNat / two52 < (hi - lo + 1).toNat := by
    rw [Nat.div_lt_iff_lt_mul (by unfold two52; decide), Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left hm hn
  omega

/-- A burst rate drawn by even odds is an index of the list: `udiscrete 0 (n - 1)` lies
below `n`. -/
theorem udiscrete_index_lt {n : Nat} (m : Nat) (hn : 0 < n) :
    (udiscrete 0 ((n : Int) - 1) m).toNat < n := by
  have := udiscrete_mem (lo := 0) (hi := (n : Int) - 1) m (by omega)
  omega

theorem pickK_go_mem (u : Rat) (ks : List Rat) (hk : ks ≠ []) :
    ∀ (cum : Rat) (ps : List (Rat × Rat)), (∀ p ∈ ps, p.1 ∈ ks) → pickK.go u ks cum ps ∈ ks
  | _, [], _ => by
    simp only [pickK.go]
    cases h : ks.getLast? with
    | none => simp_all
    | some x => exact List.mem_of_getLast? h
  | cum, (k, w) :: rest, h => by
    simp only [pickK.go]
    split
    · exact h _ List.mem_cons_self
    · exact pickK_go_mem u ks hk _ rest fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- RS1's `k` is a member of the PARROT RATIO's set. -/
theorem pickK_mem (u : Rat) (ks ws : List Rat) (hk : ks ≠ []) : pickK u ks ws ∈ ks :=
  pickK_go_mem u ks hk 0 _ fun _ hp => (List.of_mem_zip hp).1

/-- A NON-CORROBORATION always starts the reset afresh. -/
theorem resetRule_nonCorroboration (r : Reset) (st : String) (o : Int) :
    resetRule r "NON-CORROBORATION" st o = ⟨true, 0, "-"⟩ := by
  simp [resetRule]

/-- A passed parrot never ends a reset. -/
theorem resetRule_parrotPass (r : Reset) (st : String) (o : Int) (h : r.inForce = true) :
    (resetRule r "PARROT PASS" st o).inForce = true := by
  simp [resetRule, h]

/-- Under SUSPENDED no canary pass ends a reset; only the audit finding does. -/
theorem resetRule_suspended_pass (r : Reset) (o : Int) (h : r.inForce = true) :
    (resetRule r "CANARY PASS" "SUSPENDED" o).inForce = true := by
  simp [resetRule, h]

/-- No event starts a reset but a NON-CORROBORATION. -/
theorem resetRule_starts_only_by_nonCorroboration (r : Reset) (ev st : String) (o : Int)
    (h : r.inForce = false) (hs : (resetRule r ev st o).inForce = true) :
    ev = "NON-CORROBORATION" := by
  unfold resetRule at hs
  by_cases hev : ev = "NON-CORROBORATION"
  · exact hev
  · simp [hev, h] at hs

/-- EXPECTED LOSS, when given, lies between 0 and the LOAD. -/
theorem expectedLoss_bounds {eLo loadD : Datum} {v : Rat}
    (h : expectedLoss eLo loadD = .ok v) :
    ∃ e : Rat, ∃ l : Int, 0 ≤ e ∧ e ≤ 1 ∧ 0 ≤ l ∧ v = (1 - e) * l := by
  unfold expectedLoss at h
  cases he : eLo.num?.filter (fun e => decide (0 ≤ e ∧ e ≤ 1)) with
  | none => rw [he] at h; simp at h
  | some e =>
    rw [he] at h
    cases hl : loadD.intIn? 0 countMax with
    | none => rw [hl] at h; simp at h
    | some l =>
      rw [hl] at h
      simp only [need_some, ok_bind, pure_eq, Answer.ok.injEq] at h
      have he' := Option.filter_eq_some_iff.mp he
      simp only [decide_eq_true_eq] at he'
      exact ⟨e, l, he'.2.1, he'.2.2, (Datum.intIn?_bounds hl).1, h.symm⟩

/-- A TEXT judged canonical holds no carriage return and is its own NFC. -/
theorem canonText_ok_true {s : String} (h : canonText s = .ok true) :
    (∀ c ∈ s.toList, c ≠ '\r') ∧ Unicode.nfc s = s := by
  unfold canonText at h
  split at h
  · cases h
  · rename_i h1
    simp only [Answer.ok.injEq] at h
    simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at h1
    exact ⟨h1, by simpa [Unicode.isNfc] using h⟩

/-- An EQUATION judged canonical is its own `parse_form` spelling. -/
theorem canonEquation_ok_true {s : String} (h : canonEquation s = .ok true) :
    Form.parseForm s .equation = .ok s := by
  unfold canonEquation at h
  split at h
  · rename_i c hc
    simp only [Answer.ok.injEq, beq_iff_eq] at h
    rw [hc, h]
  · cases h
  · cases h

/-- A FINDING accepted: its type, and the test its value passed. -/
theorem finding_ok {o : Datum} {ty v : String} (h : finding o = .ok (ty, v)) :
    (ty = "EQUATION" ∧ canonEquation v = .ok true) ∨ (ty = "TEXT" ∧ canonText v = .ok true) ∨
      (ty ≠ "EQUATION" ∧ ty ≠ "TEXT" ∧ canonDecimalOk v = true) := by
  unfold finding at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, t, _, _, _, w, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok, check_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hok, _, rfl, rfl, rfl⟩ := h
    exact .inl ⟨rfl, hok⟩
  · simp only [bind_eq_ok, check_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hok, _, rfl, rfl, rfl⟩ := h
    exact .inr (.inl ⟨rfl, hok⟩)
  · rename_i hE hT
    simp only [bind_eq_ok, check_eq_ok, pure_eq, Answer.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hok, _, rfl, rfl, rfl⟩ := h
    exact .inr (.inr ⟨hE, hT, hok⟩)

/-- An EQUATION finding is accepted only in the declared forms' canonical spelling:
`parse_form` gives it back unchanged. -/
theorem finding_equation {o : Datum} {v : String} (h : finding o = .ok ("EQUATION", v)) :
    Form.parseForm v .equation = .ok v := by
  rcases finding_ok h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
  · exact canonEquation_ok_true h
  · simp at h
  · exact absurd rfl h

/-- A TEXT finding is accepted only with no carriage return and in NFC: text that is not its
own NFC is never accepted. -/
theorem finding_text {o : Datum} {v : String} (h : finding o = .ok ("TEXT", v)) :
    (∀ c ∈ v.toList, c ≠ '\r') ∧ Unicode.nfc v = v := by
  rcases finding_ok h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩
  · simp at h
  · exact canonText_ok_true h
  · exact absurd rfl h

end Principia.Probe
