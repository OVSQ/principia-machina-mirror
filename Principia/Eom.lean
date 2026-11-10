import Principia.Zone
import Principia.Decimal
import Principia.Canonical
import Principia.Strike.Conditions
import Principia.Form.Grammar

/-!
# The structure check of the equations of motion

v1's `tpc_eom` (TPC-PY 0.3.0, `tpc_eom` 0.2.0; tpm_eom_check 0.1.0
section 3; tpm_record_functions 0.2.0 section 12), ported operation for operation:
`eomMap`, `eomFindings`, `eomClass`, `eomRegisterTest` and `settlementCheck`.

The check reads the Starting Set's DOFs, CONSTANTs, CONSTRAINTs and LAWs, propagates the
FIXed zeros through each law's form, matches the laws that enter (EOM, CONSTRAINT,
CONSTITUTIVE, DEFINITION) against the unknown DOFs, splits the graph into its
Dulmage-Mendelsohn parts (UNDER, SQUARE, OVER), chooses in each part the matching v1
chooses (greatest order, then most role agreements, then least names; a Hungarian
assignment and the least tight one), runs Pryce's signature method on SQUARE, and writes
the findings, each with its question for the Declarer.

A law's form is read by the declared forms' `form_tree` (v1 `tpc_form`, S32;
`Principia.Form.formTree`) through `FormHook.calculator`, after NFC as v1 read it. A form
the declared forms owe (a value beyond the Calculator's exact bounds) is owed here with
their reason, never answered: the reading stops there, since v1 refuses at the first problem
and an unread form may be it. A refusal is escaped by general category, as v1 escaped it
(`Principia.Strike.showMessage`). `FormHook.owed` reads no form, every reading that reaches
one being owed.

v1's explicit stacks kept deep forms within Python's recursion limit; here a form is
walked by structural recursion, which visits the same nodes. Every order v1 sorts by is
code point order (`idLe`). No number is computed but integer orders and offsets.

Vectors: the equations-of-motion corpus and the settlement corpus, run by the
equations-of-motion test runner.
-/

namespace Principia.Eom

open Principia.Strike (idLe)

/-! ## Forms -/

/-- A form as v1's `form_tree` gives it (S32): `["eq", l, r]`, `["num", s]`, `["id", n]`,
`["neg", a]`, `["paren", a]`, `["bin", op, a, b]`, `["pow", a, [p, q]]`, `["fn", f, a]`,
`["D", x, s, n]`. -/
inductive Tree where
  | eq (l r : Tree)
  | num (s : String)
  | id (n : String)
  | neg (a : Tree)
  | paren (a : Tree)
  | bin (op : String) (a b : Tree)
  | pow (a : Tree) (p q : Int)
  | fn (f : String) (a : Tree)
  | d (x s : String) (n : Nat)
  deriving Repr, Inhabited

/-- The declared forms' parser, as the check calls it: `form_tree(text, "equation")`, the
tree or the refusal's reason; an error when the form is owed, with the reason. -/
structure FormHook where
  equation : String → Except String (Except String Tree)

/-- No parser: every form is owed to the declared forms. -/
def FormHook.owed : FormHook := ⟨fun _ => .error Zone.Owed.forms.message⟩

/-- A declared forms' expression in v1's tree shapes. -/
def ofFormExpr : Form.Expr → Tree
  | .num c => .num c
  | .ident n => .id n
  | .neg e => .neg (ofFormExpr e)
  | .paren e => .paren (ofFormExpr e)
  | .bin op l r => .bin op.symbol (ofFormExpr l) (ofFormExpr r)
  | .pow b p q => .pow (ofFormExpr b) p q
  | .fn f a => .fn f.name (ofFormExpr a)
  | .deriv x s n => .d x s n

/-- The Calculator's parser: `Form.formTree` in equation mode, which gives an equation or a
refusal (parse_form's text); its owed reasons kept. -/
def FormHook.calculator : FormHook := ⟨fun s =>
  match Form.formTree s .equation with
  | .ok (.eq l r) => .ok (.ok (.eq (ofFormExpr l) (ofFormExpr r)))
  | .ok _ => .error "internal: form_tree gave no equation in equation mode"
  | .refused r => .ok (.error r)
  | .owed (.exact what) => .error ("exact: " ++ what)⟩

/-- Every identifier of a form, a derivative's operand and variable included. -/
def Tree.idents : Tree → List String
  | .eq l r => l.idents ++ r.idents
  | .num _ => []
  | .id n => [n]
  | .neg a | .paren a | .pow a _ _ | .fn _ a => a.idents
  | .bin _ a b => a.idents ++ b.idents
  | .d x s _ => [x, s]

/-- The variables of every derivative of a form. -/
def Tree.dvars : Tree → List String
  | .eq l r => l.dvars ++ r.dvars
  | .neg a | .paren a | .pow a _ _ | .fn _ a => a.dvars
  | .bin _ a b => a.dvars ++ b.dvars
  | .d _ s _ => [s]
  | _ => []

/-- Whether a form holds a derivative of `q`. -/
def Tree.hasDOf (q : String) : Tree → Bool
  | .eq l r => l.hasDOf q || r.hasDOf q
  | .neg a | .paren a | .pow a _ _ | .fn _ a => a.hasDOf q
  | .bin _ a b => a.hasDOf q || b.hasDOf q
  | .d x _ _ => x == q
  | _ => false

/-- Distinct strings in code point order. -/
def sortedSet (xs : List String) : List String := xs.eraseDups.mergeSort idLe

/-! ## Reading -/

/-- Why a reading stops: a refusal (its reason unescaped), or owed, with the reason. -/
inductive Halt where
  | refused (reason : String)
  | owed (why : String)

/-- A reading that may stop. -/
abbrev Read := Except Halt

def refuse {α : Type} (msg : String) : Read α := .error (.refused msg)

/-- A ROLE: EOM of a DOF, or one of the other four. -/
inductive Role where
  | eom (q : String)
  | constraint
  | constitutive
  | invariant
  | definition
  deriving DecidableEq, Repr, Inhabited

/-- v1's kind word of a role (EOM's without its DOF). -/
def Role.kind : Role → String
  | .eom _ => "EOM"
  | .constraint => "CONSTRAINT"
  | .constitutive => "CONSTITUTIVE"
  | .invariant => "INVARIANT"
  | .definition => "DEFINITION"

/-- Whether the role enters the matching (v1's ENTER). -/
def Role.enters : Role → Bool
  | .invariant => false
  | _ => true

/-- The DOF of an EOM role. -/
def Role.q? : Role → Option String
  | .eom q => some q
  | _ => none

/-- A law as the check reads it: its NAME (or a record's ID), its ROLE, its form or, without
one, its REFS. -/
structure Law where
  name : String
  role : Role
  tree : Option Tree
  refs : List String
  deriving Inhabited

/-- What the check reads of the Starting Set. -/
structure Reading where
  dofs : List String
  inputs : List String
  consts : List String
  valued : List String
  fixed : List String
  zerofix : List String
  removed : List String
  declared : List String
  laws : List Law
  deriving Inhabited

/-- v1's `_kind`: the entries of a kind of the Starting Set; none when absent. -/
def kindEntries (tpk : Zone.Entry) (kind : String) : Read (List Zone.Entry) :=
  match Zone.get? tpk kind with
  | none => pure []
  | some (.arr xs) =>
    match Strike.objects xs with
    | some es => pure es
    | none => refuse ("TPK kind " ++ kind ++ ": entry is not an object")
  | some _ => refuse ("TPK kind " ++ kind ++ " is not a list")

/-- v1's `_field_str`. -/
def fieldStr (tag : String) (e : Zone.Entry) (f : String) : Read String :=
  match Zone.get? e f with
  | none => refuse (tag ++ ": missing field " ++ f)
  | some (.str s) => pure s
  | some _ => refuse (tag ++ ": field " ++ f ++ " has the wrong type")

/-- v1's `_name_of`: the NAME, an identifier. -/
def nameOf (tag : String) (e : Zone.Entry) : Read String := do
  let n ← fieldStr tag e "NAME"
  if Zone.isIdent n then pure n else refuse (tag ++ ": NAME " ++ n ++ " is not an identifier")

/-- v1's `_role`: `EOM(<identifier>)`, `CONSTRAINT`, `CONSTITUTIVE`, `INVARIANT` or
`DEFINITION`, spelled exactly so; EOM's identifier a DOF. -/
def readRole (tag r : String) (dofs : List String) : Read Role :=
  match r with
  | "CONSTRAINT" => pure .constraint
  | "CONSTITUTIVE" => pure .constitutive
  | "INVARIANT" => pure .invariant
  | "DEFINITION" => pure .definition
  | _ =>
    if r.startsWith "EOM(" && r.endsWith ")" && r.length ≥ 5 then
      let q := String.ofList ((r.toList.drop 4).dropLast)
      if Zone.isIdent q then
        if dofs.contains q then pure (.eom q)
        else refuse (tag ++ ": ROLE " ++ r ++ ": " ++ q ++ " is not a DOF")
      else refuse (tag ++ ": ROLE " ++ r ++ " is not a role")
    else refuse (tag ++ ": ROLE " ++ r ++ " is not a role")

/-- v1's `_form`: an EQUATION read by the declared forms, naming only DOFs and CONSTANTs
(the least other name refused). -/
def readForm (forms : FormHook) (tag : String) (text : Zone.Value) (declared : List String) :
    Read Tree := do
  let .str s := text | refuse (tag ++ ": field EQUATION has the wrong type")
  match forms.equation s with
  | .error why => .error (.owed why)
  | .ok (.error r) => refuse (tag ++ ": EQUATION does not parse: " ++ r)
  | .ok (.ok tree) =>
    match (sortedSet tree.idents).find? (!declared.contains ·) with
    | some n => refuse (tag ++ ": EQUATION names " ++ n ++ ", which is not a DOF or CONSTANT")
    | none => pure tree

/-- The first name of a list that occurs earlier in it: the duplicates, sorted. -/
def duplicates (names : List String) : List String :=
  let rec go : List String → List String → List String
    | [], _ => []
    | x :: xs, seen => if seen.contains x then x :: go xs seen else go xs (x :: seen)
  sortedSet (go names [])

/-- v1's `_read`, in its order, the first problem refusing. -/
def readTfk (forms : FormHook) (tfk : Zone.Value) : Read Reading := do
  let .obj tfkE := tfk | refuse "TFK is not an object"
  let some (.obj tpk) := Zone.get? tfkE "TPK" | refuse "TPK: zone is not an object"
  let mut dofs : List String := []
  let mut inputs : List String := []
  for e in ← kindEntries tpk "DOF" do
    let tag := "DOF:" ++ Zone.nameOf e
    let n ← nameOf tag e
    match Zone.get? e "ROLE" with
    | none => pure ()
    | some (.str r) =>
      if r != "INPUT" then refuse (tag ++ ": ROLE " ++ r ++ " is not INPUT")
      inputs := inputs ++ [n]
    | some _ => refuse (tag ++ ": field ROLE has the wrong type")
    dofs := dofs ++ [n]
  let mut cnames : List String := []
  let mut valued : List String := []
  for e in ← kindEntries tpk "CONSTANT" do
    let tag := "CONSTANT:" ++ Zone.nameOf e
    let n ← nameOf tag e
    match Zone.get? e "VALUE" with
    | none => pure ()
    | some (.str _) => valued := valued ++ [n]
    | some _ => refuse (tag ++ ": field VALUE has the wrong type")
    cnames := cnames ++ [n]
  let mut raw : List (String × String × Zone.Entry) := []
  for e in ← kindEntries tpk "LAW" do
    let tag := "LAW:" ++ Zone.nameOf e
    raw := raw ++ [(← nameOf tag e, tag, e)]
  match duplicates (dofs ++ cnames ++ raw.map (·.1)) with
  | d :: _ => refuse ("TPK: duplicate name " ++ d)
  | [] => pure ()
  let mut fixes : List (String × List Bool) := []
  let mut removed : List String := []
  for e in ← kindEntries tpk "CONSTRAINT" do
    let tag := "CONSTRAINT:" ++ Zone.nameOf e
    let t ← fieldStr tag e "TARGET"
    let a ← fieldStr tag e "ACTION"
    if a != "FIX" && a != "REMOVE" then refuse (tag ++ ": ACTION " ++ a ++ " is not REMOVE or FIX")
    if !dofs.contains t then refuse (tag ++ ": TARGET " ++ t ++ " is not a DOF")
    if a == "FIX" then
      match Zone.get? e "VALUE" with
      | none => refuse (tag ++ ": FIX requires VALUE")
      | some (.str v) =>
        match Decimal.canon v with
        | none => refuse (tag ++ ": VALUE " ++ v ++ " is not a decimal")
        | some cv =>
          fixes := if (fixes.lookup t).isSome
            then fixes.map fun (k, zs) => if k == t then (k, zs ++ [cv == "0"]) else (k, zs)
            else fixes ++ [(t, [cv == "0"])]
      | some _ => refuse (tag ++ ": field VALUE has the wrong type")
    else removed := removed ++ [t]
  let declared := dofs ++ cnames
  let mut laws : List Law := []
  for (n, tag, e) in raw do
    let role ← readRole tag (← fieldStr tag e "ROLE") dofs
    match Zone.get? e "EQUATION" with
    | some text =>
      laws := laws ++ [{ name := n, role, tree := some (← readForm forms tag text declared), refs := [] }]
    | none =>
      match Zone.get? e "REFS" with
      | none => refuse (tag ++ ": missing field REFS")
      | some (.arr xs) =>
        match xs.mapM (fun | .str s => some s | _ => none) with
        | some refs => laws := laws ++ [{ name := n, role, tree := none, refs }]
        | none => refuse (tag ++ ": field REFS has the wrong type")
      | some _ => refuse (tag ++ ": field REFS has the wrong type")
  pure { dofs, inputs, consts := cnames, valued, fixed := fixes.map (·.1),
         zerofix := (fixes.filter (·.2.all id)).map (·.1), removed, declared, laws }

/-- v1's STATUS words; the first two stand. -/
def statusWords : List String := ["PROVISIONAL", "ESTABLISHED", "REFUTED", "WITHDRAWN", "HELD"]

/-- v1's `_RID`: `<identifier>-<n>`, `n` a positive integer without a leading zero. -/
def isRecordId (s : String) : Bool :=
  match s.splitOn "-" |>.reverse with
  | n :: rest@(_ :: _) =>
    let p := "-".intercalate rest.reverse
    Zone.isIdent p && !n.isEmpty && n.all Char.isDigit && !n.startsWith "0"
  | _ => false

/-- v1's `_read_records`: every record read whole; the standing ones declaring a ROLE that
enters the matching and an EQUATION enter as laws named by their IDs. -/
def readRecords (forms : FormHook) (records : Zone.Value) (K : Reading) : Read (List Law) := do
  let .arr rs := records | refuse "records is not a list"
  let mut seen : List String := []
  let mut entering : List Law := []
  for r in rs do
    let .obj e := r | refuse "records: entry is not an object"
    let tag := "RECORD:" ++ (Zone.getStr? e "ID").getD "?"
    let rid ← fieldStr tag e "ID"
    if !isRecordId rid then refuse (tag ++ ": ID " ++ rid ++ " is not a record identifier")
    if seen.contains rid then refuse ("records: duplicate ID " ++ rid)
    seen := seen ++ [rid]
    let st ← fieldStr tag e "STATUS"
    if !statusWords.contains st then refuse (tag ++ ": STATUS " ++ st ++ " is not a status word")
    let role ← match Zone.get? e "ROLE" with
      | none => pure none
      | some (.str s) => some <$> readRole tag s K.dofs
      | some _ => refuse (tag ++ ": field ROLE has the wrong type")
    let tree ← match Zone.get? e "EQUATION" with
      | none => pure none
      | some text => some <$> readForm forms tag text K.declared
    let standing := st == "PROVISIONAL" || st == "ESTABLISHED"
    match role, tree with
    | some ro, some t =>
      if standing && ro.enters then
        entering := entering ++ [{ name := rid, role := ro, tree := some t, refs := [] }]
    | _, _ => pure ()
  pure entering

/-! ## Zero propagation and the equation-of-motion shape -/

/-- `{name: order}`, the higher order kept. -/
abbrev Orders := List (String × Nat)

/-- v1's `_merge`: the union, the higher order kept. -/
def mergeOrders (a b : Orders) : Orders :=
  b.foldl (fun acc (k, v) =>
    match acc.lookup k with
    | none => acc ++ [(k, v)]
    | some w => if w < v then acc.map fun (k', w') => if k' == k then (k', v) else (k', w') else acc) a

/-- v1's `_prop` of an expression: whether it is zero after the FIXed zeros are applied, and
the names it keeps with their orders. -/
def prop (K : Reading) : Tree → Bool × Orders
  | .num s => (s == "0", [])
  | .id n => if K.zerofix.contains n then (true, []) else (false, [(n, 0)])
  | .d x s n =>
    if K.fixed.contains x then (true, [])
    else if x == s then (false, [(s, n)])
    else (false, [(s, 0), (x, n)])
  | .neg a | .paren a => prop K a
  | .bin op a b =>
    let (za, oa) := prop K a
    let (zb, ob) := prop K b
    let z := if op == "+" || op == "-" then za && zb
      else if op == "*" then za || zb
      else za && !zb
    if z then (true, []) else (false, mergeOrders oa ob)
  | .pow a p _ =>
    let (za, oa) := prop K a
    if za then (decide (0 < p), []) else (false, oa)
  | .fn f a =>
    let (za, oa) := prop K a
    if za then (["abs", "sqrt", "sin", "tan"].contains f, []) else (false, oa)
  | .eq _ _ => (false, [])

/-- v1's `_factors` of a side: the numerator and denominator factors of its product and
quotient, through parentheses and unary minus. -/
def factors : Tree → List Tree × List Tree
  | .paren a | .neg a => factors a
  | .bin "*" a b =>
    let (na, da) := factors a
    let (nb, db) := factors b
    (na ++ nb, da ++ db)
  | .bin "/" a b =>
    let (na, da) := factors a
    (na, b :: da)
  | t => ([t], [])

/-- Whether a factor is a derivative. -/
def Tree.isD : Tree → Bool
  | .d _ _ _ => true
  | _ => false

/-- v1's `_shapes`: the `(q, order)` of each side with the equation-of-motion shape: one
derivative of an unknown among the numerator's factors, every other factor naming only
CONSTANTs. -/
def shapes (K : Reading) (unknowns : List String) : Tree → List (String × Nat)
  | .eq l r =>
    [l, r].filterMap fun side =>
      let (num, den) := factors side
      match num.filter Tree.isD with
      | [.d x _ n] =>
        if unknowns.contains x &&
            ((num.filter (!·.isD)) ++ den).all (fun f => f.idents.all K.consts.contains)
        then some (x, n) else none
      | _ => none
  | _ => []

/-! ## Matching -/

/-- Kuhn's augmenting path from row `r`, through columns not yet visited: the columns
visited, and the matching grown by the path, if one was found. A column visited once is not
visited again in the same search, whether or not a path went through it, as in v1: no
augmenting path passes a column from which none was found, so each search visits each
column at most once. -/
def augment (adj : String → List String) : Nat → String → List String →
    List (String × String) → List (String × String) →
    List String × Option (List (String × String) × List (String × String))
  | 0, _, visited, _, _ => (visited, none)
  | fuel + 1, r, visited, mr, mc =>
    let rec tryCols : List String → List String →
        List String × Option (List (String × String) × List (String × String))
      | [], vis => (vis, none)
      | c :: cs, vis =>
        if vis.contains c then tryCols cs vis
        else
          let vis := c :: vis
          match mc.lookup c with
          | none => (vis, some ((r, c) :: mr.filter (·.1 != r), (c, r) :: mc.filter (·.1 != c)))
          | some r' =>
            match augment adj fuel r' vis mr mc with
            | (vis', some (mr', mc')) =>
              (vis', some ((r, c) :: mr'.filter (·.1 != r), (c, r) :: mc'.filter (·.1 != c)))
            | (vis', none) => tryCols cs vis'
    tryCols (adj r) visited

/-- A maximum matching: rows in order, each by an augmenting path. Any maximum matching
gives the same Dulmage-Mendelsohn parts. -/
def maxMatching (rows : List String) (adj : String → List String) (fuel : Nat) :
    List (String × String) × List (String × String) :=
  rows.foldl (fun (mr, mc) r =>
    match augment adj fuel r [] mr mc with
    | (_, some (mr', mc')) => (mr', mc')
    | (_, none) => (mr, mc)) ([], [])

/-- The closure of an alternating search: from `start`, each element's neighbours are added,
and each neighbour's partner joins the frontier. -/
def alternate (next : String → List String) (partner : String → Option String) :
    Nat → List String → List String → List String → List String × List String
  | 0, frontier, reached, side => (frontier, reached ++ side)
  | fuel + 1, frontier, reached, side =>
    match frontier with
    | [] => (side, reached)
    | x :: rest =>
      let new := (next x).filter (!reached.contains ·)
      let reached := reached ++ new
      let partners := new.filterMap partner |>.filter (!side.contains ·)
      alternate next partner fuel (rest ++ partners) reached (side ++ partners)

/-- v1's `_dm`: the Dulmage-Mendelsohn coarse parts. `(cu, ru)`: the columns reached by
alternating paths from an unmatched column and the rows beside them; `(ro, co)`: likewise
from an unmatched row. -/
def dm (rows cols : List String) (adj cadj : String → List String) :
    List String × List String × List String × List String :=
  let fuel := (rows.length + 1) * (cols.length + 1) + 2
  let (mr, mc) := maxMatching rows adj fuel
  let cu0 := cols.filter fun c => (mc.lookup c).isNone
  let (cu, ru) := alternate cadj (mr.lookup ·) fuel cu0 [] cu0
  let ro0 := rows.filter fun r => (mr.lookup r).isNone
  let (ro, co) := alternate adj (mc.lookup ·) fuel ro0 [] ro0
  (cu, ru, ro, co)

/-- v1's `_hungarian`, operation for operation (e-maxx form, 1-based potentials): a
min-cost perfect assignment of an `n × n` matrix whose entries are integers or `none` (no
edge). Of the columns of least reduced cost a free one is taken first, then the least
index. `none` when there is no assignment (v1's internal refusal). -/
def hungarian (n : Nat) (cost : Array (Array (Option Int))) :
    Option (Array Nat × Array Int × Array Int) := Id.run do
  let mut u : Array Int := Array.replicate (n + 1) 0
  let mut v : Array Int := Array.replicate (n + 1) 0
  let mut p : Array Nat := Array.replicate (n + 1) 0
  let mut way : Array Nat := Array.replicate (n + 1) 0
  for i in [1:n + 1] do
    p := p.set! 0 i
    let mut j0 : Nat := 0
    let mut minv : Array (Option Int) := Array.replicate (n + 1) none
    let mut used : Array Bool := Array.replicate (n + 1) false
    let mut settled := false
    for _ in [0:n + 2] do
      used := used.set! j0 true
      let i0 := p[j0]!
      let mut delta : Option Int := none
      let mut j1 : Option Nat := none
      let row := cost[i0 - 1]!
      for j in [1:n + 1] do
        if used[j]! then continue
        match row[j - 1]! with
        | some cij =>
          let cur := cij - u[i0]! - v[j]!
          match minv[j]! with
          | some m => if cur < m then
              minv := minv.set! j (some cur)
              way := way.set! j j0
          | none =>
            minv := minv.set! j (some cur)
            way := way.set! j j0
        | none => pure ()
        match minv[j]! with
        | some mj =>
          let better := match delta, j1 with
            | none, _ => true
            | some dl, some jj => mj < dl || (mj == dl && p[j]! == 0 && p[jj]! != 0)
            | some dl, none => mj < dl
          if better then
            delta := some mj
            j1 := some j
        | none => pure ()
      match delta, j1 with
      | some dl, some jj =>
        for j in [0:n + 1] do
          if used[j]! then
            u := u.set! p[j]! (u[p[j]!]! + dl)
            v := v.set! j (v[j]! - dl)
          else
            match minv[j]! with
            | some m => minv := minv.set! j (some (m - dl))
            | none => pure ()
        j0 := jj
        if p[j0]! == 0 then
          settled := true
          break
      | _, _ => return none
    if !settled then return none
    for _ in [0:n + 2] do
      let j1 := way[j0]!
      p := p.set! j0 p[j1]!
      j0 := j1
      if j0 == 0 then break
  let mut assign : Array Nat := Array.replicate n 0
  for j in [1:n + 1] do
    assign := assign.set! (p[j]! - 1) (j - 1)
  return some (assign, u, v)

/-- v1's `_best`: `A` (sorted) saturated into `B` (sorted), `|A| ≤ |B|`, with integer
weights: the greatest total weight, then the least sequence of partners reading `A` in
order, among the assignments tight under the Hungarian potentials. `none` when the part
has no assignment (v1's internal refusal). -/
def best (A B : List String) (w : String → String → Option Int) :
    Option (List (String × String)) := Id.run do
  let na := A.length
  let n := B.length
  if na == 0 then return some []
  let Aa := A.toArray
  let Ba := B.toArray
  let mut cost : Array (Array (Option Int)) := #[]
  for a in A do
    cost := cost.push (Ba.map fun b => (w a b).map (- ·))
  for _ in [0:n - na] do
    cost := cost.push (Array.replicate n (some 0))
  let some (assign0, u, v) := hungarian n cost | return none
  let mut assign := assign0
  let tight : Array (List Nat) := (Array.range n).map fun i =>
    (List.range n).filter fun j => match cost[i]![j]! with
      | some cij => u[i + 1]! + v[j + 1]! == cij
      | none => false
  let mut owner : Array Nat := Array.replicate n 0
  for i in [0:n] do
    owner := owner.set! assign[i]! i
  let mut fixedA : Array Bool := Array.replicate n false
  for i in [0:na] do
    let c0 := assign[i]!
    for j in tight[i]! do
      if j == c0 then break
      let r := owner[j]!
      if fixedA[r]! then continue
      -- a breadth-first search over the tight graph for a row that can take c0
      let mut via : List (Nat × (Nat × Nat)) := [(r, (i, j))]
      let mut queue : List Nat := [r]
      let mut found : Option Nat := none
      for _ in [0:n + 2] do
        if found.isSome then break
        match queue with
        | [] => break
        | x :: rest =>
          queue := rest
          for y in tight[x]! do
            if y == assign[x]! then continue
            if y == c0 then
              found := some x
              break
            let o := owner[y]!
            if fixedA[o]! || o == i || (via.lookup o).isSome then continue
            via := via ++ [(o, (x, y))]
            queue := queue ++ [o]
      match found with
      | none => continue
      | some f =>
        let mut cur := f
        let mut take := c0
        for _ in [0:n + 2] do
          assign := assign.set! cur take
          owner := owner.set! take cur
          let (pr, col) := (via.lookup cur).getD (i, c0)
          if pr == i then
            assign := assign.set! i col
            owner := owner.set! col i
            break
          cur := pr
          take := col
        break
    fixedA := fixedA.set! i true
  return some ((List.range na).map fun i => (Aa[i]!, Ba[assign[i]!]!))

/-- v1's `_components`: the connected blocks of the subgraph on `rows` and `cols`, in order
of their least member (columns first, then rows). -/
def components (rows cols : List String) (adj : String → List String) :
    List (List String × List String) := Id.run do
  let radj (r : String) : List String := (adj r).filter cols.contains
  let cadj (c : String) : List String := rows.filter fun r => (adj r).contains c
  let starts : List (Bool × String) :=
    ((cols.mergeSort idLe).map fun c => (false, c)) ++ ((rows.mergeSort idLe).map fun r => (true, r))
  let mut seen : List (Bool × String) := []
  let mut out : List (List String × List String) := []
  for st in starts do
    if seen.contains st then continue
    let mut br : List String := []
    let mut bc : List String := []
    let mut queue : List (Bool × String) := [st]
    seen := seen ++ [st]
    for _ in [0:rows.length + cols.length + 2] do
      match queue with
      | [] => break
      | (isRow, x) :: rest =>
        queue := rest
        let nxt := if isRow then (radj x).map fun y => (false, y) else (cadj x).map fun y => (true, y)
        if isRow then br := br ++ [x] else bc := bc ++ [x]
        for y in nxt do
          if !seen.contains y then
            seen := seen ++ [y]
            queue := queue ++ [y]
    out := out ++ [(br, bc)]
  return out

/-- v1's `_pryce`: the offsets `(c, d)` by the fixed point from `c = 0`; `none` when it does
not settle within `rows + 2` passes (v1's internal refusal). -/
def pryce (rows cols : List String) (sig : String → Orders) (T : List (String × String)) :
    Option (List (String × Int) × List (String × Int)) := Id.run do
  let mut c : List (String × Int) := rows.map fun r => (r, 0)
  for _ in [0:rows.length + 2] do
    let cOf (r : String) : Int := (c.lookup r).getD 0
    let d : List (String × Int) := cols.map fun j =>
      (j, (rows.filterMap fun r => ((sig r).lookup j).map fun o => (o : Int) + cOf r).foldl max
        (((rows.filterMap fun r => ((sig r).lookup j).map fun o => (o : Int) + cOf r).head?).getD 0))
    let c2 : List (String × Int) := rows.map fun r =>
      let t := (T.lookup r).getD ""
      (r, (d.lookup t).getD 0 - (((sig r).lookup t).getD 0 : Int))
    if c2 == c then return some (c, d)
    c := c2
  return none

/-! ## The questions for the Declarer -/

/-- A record's ID holds `-`; a law's NAME does not. -/
def isRec (n : String) : Bool := n.contains '-'

def subj (n : String) : String := (if isRec n then "RECORD " else "LAW ") ++ n

def phrase (names : List String) : String :=
  let laws := (names.filter (!isRec ·)).mergeSort idLe
  let recs := (names.filter isRec).mergeSort idLe
  let part (one many : String) (xs : List String) : List String :=
    if xs.isEmpty then [] else [(if xs.length == 1 then one else many) ++ ", ".intercalate xs]
  " and ".intercalate (part "LAW " "LAWs " laws ++ part "RECORD " "RECORDs " recs)

def unk (names : List String) : String :=
  let names := names.mergeSort idLe
  (if names.length == 1 then "the unknown " else "the unknowns ") ++ ", ".intercalate names

/-! ## The analysis -/

/-- A finding, with its question for the Declarer. -/
inductive Finding where
  | under (u : String) (cols rows : List String) (question : String)
  | overEom (q : String) (laws : List String) (question : String)
  | over (laws unknowns : List String) (question : String)
  | closed (law : String) (names : List String) (question : String)
  | mismatch (law q kind question : String)
  | prose (law : String) (unknowns : List String) (question : String)
  | noForm (unknowns : List String) (question : String)
  | pde (dvars : List String) (question : String)
  deriving Repr, Inhabited

/-- v1's CLASS_ORDER. -/
def classOrder : List String := ["UNDER", "OVER-EOM", "OVER", "CLOSED", "ROLE MISMATCH", "PROSE", "NO FORM", "PDE"]

def Finding.cls : Finding → String
  | .under .. => "UNDER" | .overEom .. => "OVER-EOM" | .over .. => "OVER"
  | .closed .. => "CLOSED" | .mismatch .. => "ROLE MISMATCH" | .prose .. => "PROSE"
  | .noForm .. => "NO FORM" | .pde .. => "PDE"

/-- v1's `fkey`: the class, then the subject, then a mismatch's kind. -/
def Finding.key (f : Finding) : Nat × String × Nat :=
  let k := classOrder.idxOf f.cls
  match f with
  | .over ls _ _ => (k, ls.headD "", 0)
  | .mismatch l _ kind _ => (k, l, if kind == "NO DERIVATIVE" then 0 else 1)
  | .noForm .. | .pde .. => (k, "", 0)
  | .under u .. => (k, u, 0)
  | .overEom q .. => (k, q, 0)
  | .closed l .. => (k, l, 0)
  | .prose l .. => (k, l, 0)

/-- Keys in order. -/
def keyLe (a b : Nat × String × Nat) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && (decide (a.2.1 < b.2.1) ||
    (a.2.1 == b.2.1 && decide (a.2.2 ≤ b.2.2))))

/-- What `eom_map` reports. -/
structure Analysis where
  analysis : String
  dvars : List String
  map : List (String × String × String)
  under : List String × List String
  square : List String × List String
  over : List String × List String
  index : Option Int
  initialValues : Option Int
  offsets : List (String × Int) × List (String × Int)
  closed : List (String × String)
  invariant : List String
  prose : List (String × List String)
  deriving Inhabited

/-- The analysis of a reading over `laws`: the report, the findings, the combined UNDER
unknowns (`none` unless the analysis runs) and the UNDER list. `none` on v1's internal
refusals, which no well-formed part reaches. -/
def analyse (K : Reading) (laws : List Law) :
    Option (Analysis × List Finding × Option (List String) × List String) := Id.run do
  let dofs := K.dofs.mergeSort idLe
  let dv := sortedSet (laws.flatMap fun l => (l.tree.map Tree.dvars).getD [])
  let knownOf (d : String) : Option String :=
    if K.fixed.contains d then some "FIXED"
    else if K.removed.contains d then some "REMOVED"
    else if K.inputs.contains d then some "INPUT"
    else if dv.contains d then some "INDEPENDENT"
    else none
  let unknowns := dofs.filter fun d => (knownOf d).isNone
  let formed := laws.filter (·.tree.isSome)
  let invariant := ((laws.filter (·.role == .invariant)).map (·.name)).mergeSort idLe
  let proseL : List (String × List String) :=
    (laws.filterMap fun l =>
      if l.tree.isNone && l.role.enters then
        let u := sortedSet (l.refs.filter unknowns.contains)
        if u.isEmpty then none else some (l.name, u)
      else none).mergeSort fun a b => idLe a.1 b.1
  let analysis := if formed.isEmpty then "NO FORM" else if dv.length ≥ 2 then "PDE" else "RUN"
  let mut fnd : List Finding := []
  for l in laws.mergeSort (fun a b => idLe a.name b.name) do
    match l.role with
    | .eom q =>
      if let some t := l.tree then
        if !t.hasDOf q then
          fnd := fnd ++ [.mismatch l.name q "NO DERIVATIVE"
            (s!"{subj l.name} declares ROLE EOM({q}), but its EQUATION has no derivative of {q}: " ++
              "which ROLE does it have?")]
      if let some k := knownOf q then
        fnd := fnd ++ [.mismatch l.name q "KNOWN"
          s!"{subj l.name} declares ROLE EOM({q}), but {q} is known ({k}): which ROLE does it have?"]
    | _ => pure ()
  for (name, u) in proseL do
    let rl := match (laws.find? (·.name == name)).map (·.role) with
      | some (.eom q) => s!"EOM({q})"
      | some r => r.kind
      | none => ""
    fnd := fnd ++ [.prose name u
      (s!"{subj name} (ROLE {rl}) has no EQUATION and names {unk u}: its equation is outside the " ++
        "analysis; can it be declared in form?")]
  let mut mp : List (String × String × String) := []
  let mut closedInfo : List (String × String) := []
  let mut parts : (List String × List String) × (List String × List String) × (List String × List String) :=
    (([], []), ([], []), ([], []))
  let mut index : Option Int := none
  let mut iv : Option Int := none
  let mut offs : List (String × Int) × List (String × Int) := ([], [])
  let mut underCols : Option (List String) := none
  let mut underList : List String := []
  if analysis == "NO FORM" then
    for d in dofs do
      mp := mp ++ [(d, (knownOf d).getD "NO LAW", "")]
    let q := if unknowns.isEmpty then
        "no LAW carries an EQUATION and the kernel has no unknown: is that intended?"
      else s!"no LAW carries an EQUATION: " ++
        (if unknowns.length == 1 then "which law gives the equation of"
         else "which laws give the equations of") ++ s!" {unk unknowns}?"
    fnd := fnd ++ [.noForm unknowns q]
  else if analysis == "PDE" then
    for d in dofs do
      mp := mp ++ [(d, (knownOf d).getD "NOT ANALYZED", "")]
    fnd := fnd ++ [.pde dv "PDE: not analyzed"]
  else
    let bound := K.valued ++ K.fixed
    let mut rows : List String := []
    let mut sigL : List (String × Orders) := []
    let mut roleL : List (String × Option String) := []
    let mut shapeOf : List (String × List (String × Nat)) := []
    for l in formed do
      if !l.role.enters then continue
      let some t := l.tree | continue
      let (zl, ol, zr, orr) := match t with
        | .eq a b => let (za, oa) := prop K a; let (zb, ob) := prop K b; (za, oa, zb, ob)
        | _ => (false, [], false, [])
      let occ := mergeOrders ol orr
      let us := occ.filter fun (n, _) => unknowns.contains n
      shapeOf := shapeOf ++ [(l.name, shapes K unknowns t)]
      if us.isEmpty then
        if zl && zr then closedInfo := closedInfo ++ [(l.name, "ZERO")]
        else if occ.all fun (n, _) => bound.contains n then
          closedInfo := closedInfo ++ [(l.name, "BOUND")]
        else
          let ub := sortedSet ((occ.map (·.1)).filter (!bound.contains ·))
          closedInfo := closedInfo ++ [(l.name, "UNBOUND")]
          let names := ", ".intercalate ub
          fnd := fnd ++ [.closed l.name ub
            (s!"{subj l.name} names no unknown once the fixed DOFs are applied, and depends on {names}, " ++
              s!"which the kernel does not bind: does it hold for every value of {names}, or is a force or " ++
              "an unknown missing?")]
        continue
      rows := rows ++ [l.name]
      sigL := sigL ++ [(l.name, us)]
      roleL := roleL ++ [(l.name, l.role.q?)]
    closedInfo := closedInfo.mergeSort fun a b => idLe a.1 b.1 && (a.1 != b.1 || idLe a.2 b.2)
    rows := rows.mergeSort idLe
    let cols := unknowns
    let sig (r : String) : Orders := (sigL.lookup r).getD []
    let roleOf (r : String) : Option String := (roleL.lookup r).getD none
    let adj (r : String) : List String := ((sig r).map (·.1)).mergeSort idLe
    let cadj (c : String) : List String := rows.filter fun r => (adj r).contains c
    let (cu, ru, ro, co) := dm rows cols adj cadj
    let rs := rows.filter fun r => !ru.contains r && !ro.contains r
    let cs := cols.filter fun c => !cu.contains c && !co.contains c
    let RU := ru.mergeSort idLe
    let CU := cu.mergeSort idLe
    let RS := rs.mergeSort idLe
    let CS := cs.mergeSort idLe
    let RO := ro.mergeSort idLe
    let CO := co.mergeSort idLe
    parts := ((CU, RU), (CS, RS), (CO, RO))
    let weights (A B : List String) (byRow : Bool) (a b : String) : Option Int :=
      let k : Int := A.length + B.length + 1
      let (r, c) := if byRow then (a, b) else (b, a)
      ((sig r).lookup c).map fun o => (o : Int) * k + (if roleOf r == some c then 1 else 0)
    let some mU := best RU CU (weights RU CU true) | return none
    let some mS := best RS CS (weights RS CS true) | return none
    let some mO := best CO RO (weights CO RO false) | return none
    let lawOf : List (String × String × String) :=
      (mU.map fun (r, c) => (c, "UNDER", r)) ++ (mS.map fun (r, c) => (c, "DETERMINED", r)) ++
        (mO.map fun (c, r) => (c, "OVER", r))
    for d in dofs do
      match knownOf d with
      | some k => mp := mp ++ [(d, k, "")]
      | none =>
        match lawOf.lookup d with
        | some (lbl, r) => mp := mp ++ [(d, lbl, r)]
        | none => mp := mp ++ [(d, "NO LAW", "")]
    if !RS.isEmpty then
      let sS (r : String) : Orders := (sig r).filter fun (c, _) => cs.contains c
      let some (cc, dd) := pryce RS CS sS mS | return none
      let cmax := (cc.map (·.2)).foldl max ((cc.head?.map (·.2)).getD 0)
      index := some (cmax + (if dd.any (·.2 == 0) then 1 else 0))
      iv := some ((dd.map (·.2)).sum - (cc.map (·.2)).sum)
      offs := (RS.map fun r => (r, (cc.lookup r).getD 0), CS.map fun j => (j, (dd.lookup j).getD 0))
    else
      index := some 0
      iv := some 0
    underCols := some cu
    let matchedU := mU.map (·.2)
    let comps := components ru cu adj
    for u in CU do
      if matchedU.contains u then continue
      underList := underList ++ [u]
      let (br, bc) := (comps.find? (·.2.contains u)).getD ([], [u])
      let bcs := bc.mergeSort idLe
      let q := if br.isEmpty then
          s!"unknown {u} is named by no law with a declared form: which equation determines {u}?"
        else
          s!"unknown {u} is determined by no law with a declared form ({phrase br} " ++
            (if br.length == 1 then "leaves" else "leave") ++ s!" {", ".intercalate bcs} " ++
            s!"under-determined): which equation determines {u}?"
      fnd := fnd ++ [.under u bcs (br.mergeSort idLe) q]
    -- OVER-EOM: the laws stating the motion of one unknown twice
    let mut oe : List (String × List String) := []
    let addOe (oe : List (String × List String)) (q : String) (g : List String) :=
      match oe.lookup q with
      | some _ => oe.map fun (k, v) => if k == q then (k, sortedSet (v ++ g)) else (k, v)
      | none => oe ++ [(q, sortedSet g)]
    let eomQs := sortedSet (formed.filterMap (·.role.q?))
    for q in eomQs do
      let g := (formed.filter (·.role.q? == some q)).map (·.name)
      if g.length ≥ 2 then oe := addOe oe q g
    let shapeList := (shapeOf.mergeSort fun a b => idLe a.1 b.1).flatMap fun (name, shs) =>
      shs.eraseDups.map fun sh => (sh, name)
    let shapeKeys := (shapeList.map (·.1)).eraseDups
    for sh in shapeKeys do
      let g := (shapeList.filter (·.1 == sh)).map (·.2)
      if g.length ≥ 2 then oe := addOe oe sh.1 g
    let mut aside : List String := []
    let mut kept : List String := []
    for (q, ls0) in oe.mergeSort fun a b => idLe a.1 b.1 do
      let ls := ls0.mergeSort idLe
      kept := kept ++ ls.take 1
      aside := aside ++ ls.drop 1
      fnd := fnd ++ [.overEom q ls
        s!"{phrase ls} each state the motion of {q}: are they one equation, or is one to be removed?"]
    aside := aside.filter (!kept.contains ·)
    let rrows := rows.filter (!aside.contains ·)
    let rcadj (c : String) : List String := (cadj c).filter (!aside.contains ·)
    let (_, _, ro2, co2) := dm rrows cols adj rcadj
    for (br, bc) in components ro2 co2 adj do
      let ls := br.mergeSort idLe
      let us := bc.mergeSort idLe
      fnd := fnd ++ [.over ls us
        (s!"{phrase ls} give more equations than {unk us} they determine: which law is implied by " ++
          "the others, or is one an independent claim?")]
  let fndSorted := fnd.mergeSort fun a b => keyLe a.key b.key
  let ((uc, ur), (sc, sr), (oc, or_)) := parts
  return some ({ analysis, dvars := dv, map := mp, under := (uc, ur), square := (sc, sr),
                 over := (oc, or_), index, initialValues := iv, offsets := offs,
                 closed := closedInfo, invariant, prose := proseL },
               fndSorted, (if analysis == "RUN" then underCols else none), underList)

/-! ## v1's results, as values -/

open Principia.Canonical (Value)

def strs (xs : List String) : Value := .arr (xs.map .str)

def Finding.toValue : Finding → Value
  | .under u cs rs q => .arr [.str "UNDER", .str u, strs cs, strs rs, .str q]
  | .overEom q ls question => .arr [.str "OVER-EOM", .str q, strs ls, .str question]
  | .over ls us q => .arr [.str "OVER", strs ls, strs us, .str q]
  | .closed l ns q => .arr [.str "CLOSED", .str l, strs ns, .str q]
  | .mismatch l q k question => .arr [.str "ROLE MISMATCH", .str l, .str q, .str k, .str question]
  | .prose l us q => .arr [.str "PROSE", .str l, strs us, .str q]
  | .noForm us q => .arr [.str "NO FORM", strs us, .str q]
  | .pde dv q => .arr [.str "PDE", strs dv, .str q]

def intOrNone : Option Int → Value
  | some i => .int i
  | none => .str "NONE"

def Analysis.toValue (a : Analysis) : Value :=
  .arr [.arr [.str "ANALYSIS", .str a.analysis], .arr [.str "D_VARIABLES", strs a.dvars],
    .arr [.str "MAP", .arr (a.map.map fun (d, l, w) => strs [d, l, w])],
    .arr [.str "PARTS", .arr [.str "UNDER", strs a.under.1, strs a.under.2],
      .arr [.str "SQUARE", strs a.square.1, strs a.square.2],
      .arr [.str "OVER", strs a.over.1, strs a.over.2]],
    .arr [.str "INDEX", intOrNone a.index], .arr [.str "INITIAL_VALUES", intOrNone a.initialValues],
    .arr [.str "OFFSETS", .arr (a.offsets.1.map fun (r, c) => .arr [.str r, .int c]),
      .arr (a.offsets.2.map fun (j, d) => .arr [.str j, .int d])],
    .arr [.str "CLOSED", .arr (a.closed.map fun (n, k) => strs [n, k])],
    .arr [.str "INVARIANT", strs a.invariant],
    .arr [.str "PROSE", .arr (a.prose.map fun (n, u) => .arr [.str n, strs u])]]

/-! ## The public functions -/

/-- A function's answer as v1 wrote it, or owed, with the reason (the zones' words for
theirs: `Zone.Owed.message`). -/
abbrev Result := Except String Value

/-- A stopped reading as v1 answers it: `["REFUSED", reason]`, the reason escaped (v1's
`_show`), or owed. -/
def halted (h : Halt) : Result :=
  match h with
  | .owed why => .error why
  | .refused r => .ok (.arr [.str "REFUSED", .str (Strike.showMessage false r)])

def internal : Halt := .refused "internal: no assignment in a part that has one"

/-- v1's `eom_map`. -/
def eomMap (forms : FormHook) (tfk : Zone.Value) : Result :=
  match readTfk forms tfk with
  | .error h => halted h
  | .ok K =>
    match analyse K K.laws with
    | some (R, _, _, _) => .ok (.arr [.str "OK", R.toValue])
    | none => halted internal

/-- v1's `eom_findings`. -/
def eomFindings (forms : FormHook) (tfk : Zone.Value) : Result :=
  match readTfk forms tfk with
  | .error h => halted h
  | .ok K =>
    match analyse K K.laws with
    | some (_, f, _, _) => .ok (.arr [.str "OK", .arr (f.map Finding.toValue)])
    | none => halted internal

/-- v1's REGULAR and NOT_VALIDATED. -/
def regular : String := "structurally regular"
def notValidated : String := "Structure not Validated at Inception"

/-- v1's `eom_class` (S30): STRUCTURE_CHECK read first (absent: ON); OFF reads no more. -/
def eomClass (forms : FormHook) (tfk : Zone.Value) : Result :=
  -- `none`: STRUCTURE_CHECK is OFF, and nothing else is read
  let found : Read (Option (List Finding)) := do
    let .obj tfkE := tfk | refuse "TFK is not an object"
    let some (.obj tms) := Zone.get? tfkE "TMS" | refuse "TMS: zone is not an object"
    let some (.obj params) := Zone.get? tms "PARAMETERS"
      | refuse "TMS: part PARAMETERS is not an object"
    let sc ← match Zone.get? params "STRUCTURE_CHECK" with
      | none => pure "ON"
      | some (.str s) => pure s
      | some _ => refuse "TMS: field STRUCTURE_CHECK has the wrong type"
    if sc != "ON" && sc != "OFF" then refuse ("TMS: STRUCTURE_CHECK " ++ sc ++ " is not ON or OFF")
    if sc == "OFF" then return none
    let K ← readTfk forms tfk
    match analyse K K.laws with
    | some (_, f, _, _) => pure (some f)
    | none => .error internal
  match found with
  | .error h => halted h
  | .ok none => .ok (.arr [.str "STRUCTURE", .str notValidated, strs ["CHECK OFF"]])
  | .ok (some fnd) =>
    let present := fnd.map Finding.cls
    let reasons := (if ["UNDER", "OVER-EOM", "OVER", "CLOSED", "ROLE MISMATCH"].any present.contains
        then ["FINDINGS"] else []) ++ (["PROSE", "PDE", "NO FORM"].filter present.contains)
    if reasons.isEmpty then .ok (.arr [.str "STRUCTURE", .str regular])
    else .ok (.arr [.str "STRUCTURE", .str notValidated, strs reasons])

/-- S30: with STRUCTURE_CHECK OFF the class is "Structure not Validated at Inception",
CHECK OFF, whatever the Starting Set holds and whether or not its forms can be read. -/
theorem eomClass_off (forms : FormHook) {e tms ps : Zone.Entry}
    (h1 : Zone.get? e "TMS" = some (.obj tms)) (h2 : Zone.get? tms "PARAMETERS" = some (.obj ps))
    (h3 : Zone.get? ps "STRUCTURE_CHECK" = some (.str "OFF")) :
    eomClass forms (.obj e) = .ok (.arr [.str "STRUCTURE", .str notValidated, strs ["CHECK OFF"]]) := by
  simp [eomClass, h1, h2, h3]
  rfl

/-- A ROLE read as EOM names a DOF. -/
theorem readRole_eom {tag r q : String} {dofs : List String}
    (h : readRole tag r dofs = .ok (.eom q)) : q ∈ dofs := by
  unfold readRole at h
  split at h <;> try (simp [pure, Except.pure] at h)
  repeat' split at h
  all_goals first
    | (simp [refuse] at h; done)
    | (simp only [Except.ok.injEq, Role.eom.injEq] at h
       subst h
       simp_all)

/-- v1's `_id_key`: the prefix, then the number's length, then the number. -/
def idKeyLe (a b : String) : Bool :=
  let split (s : String) : String × String :=
    match (s.splitOn "-").reverse with
    | n :: rest => ("-".intercalate rest.reverse, n)
    | [] => (s, "")
  let (pa, na) := split a
  let (pb, nb) := split b
  decide (pa < pb) || (pa == pb && (decide (na.length < nb.length) ||
    (na.length == nb.length && decide (na ≤ nb))))

/-- v1's `eom_register_test`: the TFK read first, then every record whole; the analysis of
the TFK alone gives the UNDER unknowns, the analysis with the entering records the whole. -/
def eomRegisterTestParts (forms : FormHook) (tfk records : Zone.Value) :
    Except Halt (Analysis × List Finding × List String × List String × List String) := do
  let K ← readTfk forms tfk
  let entering ← readRecords forms records K
  let some (_, _, _, under0) := analyse K K.laws | .error internal
  let some (R, fnd, cu, _) := analyse K (K.laws ++ entering) | .error internal
  let settled := match cu with
    | none => []
    | some cu => (under0.filter (!cu.contains ·)).mergeSort idLe
  let still := (under0.filter (!settled.contains ·)).mergeSort idLe
  let used := (entering.map (·.name)).mergeSort idKeyLe
  pure (R, fnd, used, settled, still)

def eomRegisterTest (forms : FormHook) (tfk records : Zone.Value) : Result :=
  match eomRegisterTestParts forms tfk records with
  | .error h => halted h
  | .ok (R, fnd, used, settled, still) =>
    .ok (.arr [.str "OK", R.toValue, .arr (fnd.map Finding.toValue), .arr [.str "USED", strs used],
      .arr [.str "SETTLED", strs settled], .arr [.str "OPEN", strs still]])

/-! ## Settlement (tpm_record_functions 0.2.0 section 12.2) -/

/-- A register function's refusal as tpc_record writes it: `["REFUSED", problems]`. -/
def refusedValue (probs : List (String × String × String)) : Value :=
  .arr [.str "REFUSED", .arr (probs.map fun (c, f, m) => strs [c, f, m])]

/-- One problem, its message escaped as v1's `_cshow` writes a slot (the message's own
words are ASCII, so escaping the whole is escaping the slot). -/
def problem (code msg : String) : Except String (String × String × String) :=
  .ok (code, "-", Strike.showMessage true msg)

/-- REC-50 as a result. -/
def refusedBad (argument : String) (v : Value) (what : String) : Result :=
  match (Strike.refuseBad argument v what : Strike.Answer Unit) with
  | .refused r => .ok r.toValue
  | .owed w => .error w
  | .ok _ => .error "internal: REC-50 answered"

/-- Problems in v1's order: sorted and without repeats. -/
def problemLe (a b : String × String × String) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && (decide (a.2.1 < b.2.1) ||
    (a.2.1 == b.2.1 && decide (a.2.2 ≤ b.2.2))))

/-- v1's `settlement_check`: what the structure test settles of the register's OPEN UNDER
gaps (BY_TEST), what the lead's naming of a standing record without a form settles
(BY_NAMING), what stays OPEN, and the records the test used. Refused: REC-50 (records,
words), REC-84 (naming), REC-85 (the structure test refused), REC-86 to REC-88 (a naming),
the last three reported together. -/
def settlementCheck (forms : FormHook) (tfk records words naming : Value) : Result := do
  let some keyed := Strike.keyedOf records
    | refusedBad "records" records "a register"
  let ws : Option (List (String × String)) := match words with
    | .obj ms => ms.mapM fun (k, v) => match v with
      | .str s => some (k, s)
      | _ => none
    | _ => none
  let some ws := ws
    | refusedBad "words" words "a map of status words"
  let pairs : Option (List (String × String)) := match naming with
    | .arr ps => ps.mapM fun
      | .arr [.str u, .str r] => some (u, r)
      | _ => none
    | _ => none
  let sortedPairs (ps : List (String × String)) : Bool :=
    (ps.zip (ps.drop 1)).all fun (a, b) => decide (a.1 < b.1)
  let some naming := pairs.filter sortedPairs
    | return refusedValue [("REC-84", "-", "naming is not a sorted list of [UNKNOWN, RECORD_ID] pairs")]
  let order : List String := match records with
    | .arr rs => rs.filterMap fun
      | .obj r => match Strike.field r "ID" with
        | some (.str i) => some i
        | _ => none
      | _ => none
    | _ => []
  let U := sortedSet (order.filterMap fun rid => do
    let r ← keyed.lookup rid
    guard (Strike.fieldIs r "CLASS" "NAMED_GAP" && Strike.fieldIs r "SOURCE" "UNDER" &&
      Strike.fieldIs r "STATE" "OPEN")
    match Strike.field r "AGAINST" with
    | some (.arr [.str a]) => some a
    | _ => none)
  let stands (rid : String) : Bool := Strike.standing ws rid
  let views : List Zone.Value := order.filterMap fun rid => do
    let r ← keyed.lookup rid
    let role ← Strike.field r "ROLE"
    let eqn ← Strike.field r "EQUATION"
    guard (stands rid)
    some (.obj [("ID", .str rid), ("STATUS", .str ((ws.lookup rid).getD "")),
      ("ROLE", Strike.toZoneValue role), ("EQUATION", Strike.toZoneValue eqn)])
  let (settled, used) ← match eomRegisterTestParts forms (Strike.toZoneValue tfk) (.arr views) with
    | .ok (_, _, used, settled, _) => pure (settled, used)
    | .error (.owed why) => throw why
    | .error (.refused r) =>
      return refusedValue
        [("REC-85", "-", "the structure test refused: " ++ Strike.showMessage false r)]
  let byTest := U.filter settled.contains
  let mut probs : List (String × String × String) := []
  let mut byNaming : List (String × String) := []
  for (u, rid) in naming do
    let mut bad := false
    if !U.contains u || byTest.contains u then
      probs := probs ++ [← problem "REC-86"
        s!"UNKNOWN {u} is not an OPEN UNDER gap's DOF left open by the test"]
      bad := true
    match keyed.lookup rid with
    | some r =>
      if !stands rid then
        probs := probs ++ [← problem "REC-87"
          s!"RECORD_ID {rid} is not a standing record of the register"]
        bad := true
      else if (Strike.field r "EQUATION").isSome then
        probs := probs ++ [← problem "REC-88"
          s!"RECORD_ID {rid} carries a form; it settles by the test alone"]
        bad := true
    | none =>
      probs := probs ++ [← problem "REC-87"
        s!"RECORD_ID {rid} is not a standing record of the register"]
      bad := true
    if !bad then byNaming := byNaming ++ [(u, rid)]
  if !probs.isEmpty then
    return refusedValue (probs.eraseDups.mergeSort problemLe)
  let named := byNaming.map (·.1)
  return .arr [.str "OK", .obj [("BY_TEST", strs byTest),
    ("BY_NAMING", .arr (byNaming.map fun (u, r) => strs [u, r])),
    ("OPEN", strs (U.filter fun u => !byTest.contains u && !named.contains u)),
    ("USED", strs used)]]

end Principia.Eom
