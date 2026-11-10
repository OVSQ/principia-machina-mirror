import Principia.Digest
import Principia.Falcon.Canon

/-!
# The falcon draw

v1's `tpc_falcon` 0.2.0: `falcon_draw(candidates, n, state, r)`, the new
assignees of a falcon (DW1 to DW7 in v1's text): the eligible accounts in ORDER, the first
rung of T1 to T5 that some set of `n` of them satisfies, and within it the set with the
fewest shared sponsors, then families, then snapshots, then the earliest in ORDER; or
SHORT, or WAIT.

**The order and its digest.** DW2 orders the eligible accounts by FALCON
WINDOW, then by on-time share (exact, by cross-multiplication), then by `h`, the SHA-256
over the netstring of `TPC-FALCON-DRAW`, `1`, `r` and the account (`drawKey`, v1's
`_digest_fields`; SHA-256 is `Principia.Sha256`), its 64 lower-case hexadecimal
characters compared as text, as v1 compared them, then by the account. Of any two
accounts one comes first (`before_total`), and two accounts each first of the other are
one account (`before_antisymm`): no two eligible accounts are left unordered. No number in
the draw is inexact: windows, counts and shares are integers, the shares compared by
cross-multiplication, as v1 compared them.
-/

namespace Principia.Falcon.Draw

open Principia.Canonical (Value)
open Principia.Falcon

/-- The largest count v1 reads (v1's `COUNT_MAX`). -/
def countMax : Int := 1000000000

/-- The last second v1 reads (v1's `TIME_MAX`). -/
def timeMax : Int := 253402300799

/-- A candidate's keys (v1's `_CKEYS`). -/
def candidateKeys : List String :=
  ["account", "sponsor", "family", "snapshot", "tier", "good_standing", "sandbox",
    "over_cap", "window", "ontime", "assigned"]

/-- The state's keys (v1's `_SKEYS`). -/
def stateKeys : List String := ["kept", "prior", "drafted", "now", "falcon_wait"]

/-- One candidate account. -/
structure Candidate where
  account : String
  sponsor : String
  family : String
  snapshot : String
  tier : Bool
  goodStanding : Bool
  sandbox : Bool
  overCap : Bool
  window : Nat
  ontime : Nat
  assigned : Nat
  deriving DecidableEq, Repr

/-- A candidate as v1's `_draw_check` accepts it. -/
def candidateOf (v : Value) : Option Candidate := do
  if !keysAreV v candidateKeys [] then none
  let ms ← members? v
  let name (k : String) : Option String := match field? ms k with
    | some (.str s) => if s ≠ "" then some s else none
    | _ => none
  let flag (k : String) : Option Bool := match field? ms k with
    | some (.bool b) => some b
    | _ => none
  let count (k : String) : Option Nat := match field? ms k with
    | some x => if isInt x 0 countMax then some (natOf x) else none
    | none => none
  let c : Candidate :=
    { account := (← name "account"), sponsor := (← name "sponsor"),
      family := (← name "family"), snapshot := (← name "snapshot"), tier := (← flag "tier"),
      goodStanding := (← flag "good_standing"), sandbox := (← flag "sandbox"),
      overCap := (← flag "over_cap"), window := (← count "window"),
      ontime := (← count "ontime"), assigned := (← count "assigned") }
  if c.assigned < c.ontime then none
  return c

/-- The draw's state. -/
structure State where
  kept : List String
  prior : List String
  drafted : Nat
  now : Nat
  falconWait : Nat

/-- A list of distinct names. -/
def namesOf (v : Value) : Option (List String) :=
  match strings? v with
  | some ss => if ss.all (· ≠ "") && distinct ss then some ss else none
  | none => none

/-- The state as v1's `_draw_check` accepts it, the kept accounts among the candidates. -/
def stateOf (accounts : List String) (v : Value) : Option State := do
  if !keysAreV v stateKeys [] then none
  let ms ← members? v
  let kept ← namesOf ((field? ms "kept").getD .null)
  let prior ← namesOf ((field? ms "prior").getD .null)
  if !kept.all accounts.contains then none
  let time (k : String) : Option Nat := match field? ms k with
    | some x => if isInt x 0 timeMax then some (natOf x) else none
    | none => none
  let s : State :=
    { kept := kept, prior := prior, drafted := (← time "drafted"),
      now := (← time "now"), falconWait := (← time "falcon_wait") }
  if s.now < s.drafted then none
  return s

/-- `r`: 32 lower-case hexadecimal characters. -/
def rOk : Value → Bool
  | .str s => s.length == 32 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  | _ => false

/-- A candidate's on-time share as a fraction; no assignment counts as share 1. -/
def share (c : Candidate) : Nat × Nat := if 0 < c.assigned then (c.ontime, c.assigned) else (1, 1)

/-- DW2's `h`: SHA-256 over the netstring of `TPC-FALCON-DRAW`, `1`, `r` and the account, in
lower-case hexadecimal (v1's `_digest_fields`). -/
def drawKey (r account : String) : String :=
  Digest.digestFields [.text "TPC-FALCON-DRAW", .text "1", .text r, .text account]

/-- Every `h` is 64 characters. -/
theorem drawKey_length (r account : String) : (drawKey r account).length = 64 :=
  Digest.ofPreimage_length _

/-- DW2's order on an eligible account and its `h` (v1's `_order_cmp`): window ascending,
then share descending, then `h` ascending, then the account. -/
def before (a b : Candidate × String) : Bool :=
  if a.1.window != b.1.window then a.1.window < b.1.window
  else
    let x := (share a.1).1 * (share b.1).2
    let y := (share b.1).1 * (share a.1).2
    if x != y then y < x
    else if a.2 != b.2 then decide (a.2 < b.2)
    else decide (a.1.account ≤ b.1.account)

/-- The index sets of size `n`, 1 to 3, in lexicographic order (v1's `_combos`). -/
def combos (m n : Nat) : List (List Nat) :=
  match n with
  | 1 => (List.range m).map fun i => [i]
  | 2 => (List.range m).flatMap fun i => ((List.range m).filter (i < ·)).map fun j => [i, j]
  | _ => (List.range m).flatMap fun i => ((List.range m).filter (i < ·)).flatMap fun j =>
      ((List.range m).filter (j < ·)).map fun k => [i, j, k]

/-- A set's key: the rung (0 for T1 to 4 for T5), the pairs sharing a sponsor, of one
family and of one snapshot; and whether it satisfies T3. -/
def setKey (kept : List Candidate) (keptTier : Bool) (s : List Candidate) :
    (Nat × Nat × Nat × Nat) × Bool :=
  let idx := List.range s.length
  let newPairs := idx.flatMap fun i => (idx.filter (i < ·)).filterMap fun j =>
    match s[i]?, s[j]? with
    | some a, some b => some (a, b)
    | _, _ => none
  let pairs := newPairs ++ s.flatMap fun x => kept.map fun k => (x, k)
  let shared := pairs.filter fun (a, b) => a.sponsor == b.sponsor
  let t3 := shared.isEmpty
  let rung :=
    if t3 then
      if s.all (·.tier) then 0 else if keptTier || s.any (·.tier) then 1 else 2
    else if shared.all (fun (a, b) => a.tier && b.tier) then 3
    else 4
  let fam := (pairs.filter fun (a, b) => a.family == b.family).length
  let snap := (pairs.filter fun (a, b) => a.snapshot == b.snapshot).length
  ((rung, shared.length, fam, snap), t3)

/-- Lexicographic order on the keys. -/
def keyLt (a b : Nat × Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 &&
    (a.2.2.1 < b.2.2.1 || (a.2.2.1 == b.2.2.1 && a.2.2.2 < b.2.2.2)))))

/-- The draw's result (v1's dict). -/
structure Draw where
  status : String
  rung : Nat
  marks : List String
  accounts : List String
  thin : Bool
  eligible : Nat
  sponsors : Nat

/-- v1's `falcon_draw(candidates, n, state, r)`. -/
def falconDraw (candidates n state r : Value) : Result Draw := do
  let some cs := (match candidates with
      | .arr vs => vs.mapM candidateOf
      | _ => none) | refuse "candidates"
  if !distinct (cs.map (·.account)) then refuse "candidates"
  if !isInt n 1 3 then refuse "n"
  let n := natOf n
  let some st := stateOf (cs.map (·.account)) state | refuse "state"
  if st.kept.length + n < 2 then refuse "n"
  if !rOk r then refuse "r"
  let kept := st.kept.filterMap fun a => cs.find? (·.account == a)
  let excluded := st.kept ++ st.prior
  let rs := match r with
    | .str s => s
    | _ => ""
  let elig := cs.filter fun c =>
    c.goodStanding && !c.sandbox && !c.overCap && !excluded.contains c.account
  let order := ((elig.map fun c => (c, drawKey rs c.account)).mergeSort before).map (·.1)
  let sponsors := (order.map (·.sponsor)).eraseDups.length
  let waited := st.falconWait ≤ st.now - st.drafted
  let base : Draw := { status := "", rung := 0, marks := [], accounts := [], thin := false,
                       eligible := order.length, sponsors := sponsors }
  if order.length < n then
    return { base with status := "SHORT", thin := sponsors < 2 || waited }
  let keptTier := kept.any (·.tier)
  let scored := (combos order.length n).map fun idxs =>
    (idxs, setKey kept keptTier (idxs.filterMap (order[·]?)))
  let anyT3 := scored.any (·.2.2)
  let best := scored.foldl (fun best (idxs, key, _) =>
    match best with
    | some (_, bk) => if keyLt key bk then some (idxs, key) else best
    | none => some (idxs, key)) none
  let thin := sponsors < 2 || (waited && !anyT3)
  let some (idxs, (rung, nshared, fam, snap)) := best | refuse "n"
  if rung == 4 && !thin then
    return { base with status := "WAIT", thin := thin }
  let marks := (if 0 < nshared then ["SAME-SPONSOR"] else []) ++
    (if 0 < fam then ["SAME-VENDOR"] else []) ++ (if 0 < snap then ["SAME-MODEL"] else [])
  return { base with
    status := "OK", rung := rung, marks := marks, thin := thin,
    accounts := idxs.filterMap fun i => (order[i]?).map (·.account) }

/-- v1's `render_draw`. -/
def renderDraw (d : Draw) : String :=
  let ok := d.status == "OK"
  let head := "draw|" ++ d.status ++ (if ok then s!"|T{d.rung + 1}" else "")
  let body := if ok then
      d.accounts.map (fun a => "assignee|" ++ esc a) ++
        ["marks|" ++ (if d.marks.isEmpty then "-" else ",".intercalate d.marks)]
    else []
  "\n".intercalate ([head] ++ body ++
    ["thin|" ++ (if d.thin then "true" else "false"), s!"pool|{d.eligible}|{d.sponsors}"])

/-! ## The order -/

/-- DW2's order is total: of any two accounts, one comes first. -/
theorem before_total (a b : Candidate × String) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases hw : a.1.window = b.1.window
  · by_cases hx : (share a.1).1 * (share b.1).2 = (share b.1).1 * (share a.1).2
    · by_cases hh : a.2 = b.2
      · simp only [hw, hx, hh, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          decide_eq_true_eq]
        exact String.le_total _ _
      · have hh' : b.2 ≠ a.2 := fun h => hh h.symm
        simp only [hw, hx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq,
          hh, hh', not_false_eq_true, decide_eq_true_eq]
        by_cases h : a.2 < b.2
        · exact .inl h
        · exact .inr (String.not_le.mp fun h' => hh (String.le_antisymm h' (String.not_lt.mp h)))
    · have hx' : ¬(share b.1).1 * (share a.1).2 = (share a.1).1 * (share b.1).2 :=
        fun h => hx h.symm
      simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, hx,
        hx', not_false_eq_true, decide_eq_true_eq]
      omega
  · have hw' : ¬b.1.window = a.1.window := fun h => hw h.symm
    simp only [bne_iff_ne, ne_eq, hw, hw', not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

/-- DW2's order decides between any two distinct accounts: two candidates each first of the
other are one account. -/
theorem before_antisymm {a b : Candidate × String} (hab : before a b = true)
    (hba : before b a = true) : a.1.account = b.1.account := by
  unfold before at hab hba
  by_cases hw : a.1.window = b.1.window
  · by_cases hx : (share a.1).1 * (share b.1).2 = (share b.1).1 * (share a.1).2
    · by_cases hh : a.2 = b.2
      · simp only [hw, hx, hh, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          decide_eq_true_eq] at hab hba
        exact String.le_antisymm hab hba
      · have hh' : b.2 ≠ a.2 := fun h => hh h.symm
        simp only [hw, hx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq,
          hh, hh', not_false_eq_true, decide_eq_true_eq] at hab hba
        exact absurd hba (String.lt_asymm hab)
    · have hx' : ¬(share b.1).1 * (share a.1).2 = (share a.1).1 * (share b.1).2 :=
        fun h => hx h.symm
      simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq, hx,
        hx', not_false_eq_true, decide_eq_true_eq] at hab hba
      omega
  · have hw' : ¬b.1.window = a.1.window := fun h => hw h.symm
    simp only [bne_iff_ne, ne_eq, hw, hw', not_false_eq_true, ↓reduceIte,
      decide_eq_true_eq] at hab hba
    omega

end Principia.Falcon.Draw
