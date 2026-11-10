import Principia.Provision.Interview
import Principia.StartingSet.Tests

/-!
# Re-expansion, a draft's statuses, the use view and the checks before a PROVISION ADD

v1's `module_verify`, `draft_module_status`, `module_use_view` and `module_check`
(tpm_module_spec 0.2.0 6.5, 6.9-6.11; TPS 5.22.8, 5.22.11, 5.22.14, 5.22.16):

* `verify`: at the final pass every claim is re-expanded from its declared text, whatever its
  version's status, and the draft's Starting Set must be that expansion (MATCH), compared by
  D(TPK);
* `draftStatus`: each claim's status; a SUPERSEDED one with whether the OFFERED version's
  expansion on this draft is the SAME or DIFFERS; a WITHDRAWN one with the question put to the
  Declarer;
* `useView`: for each declared version, the certified containers whose PROVISIONS USED claim
  it, and the number claiming a WITHDRAWN version;
* `check`: before the Declarer's MODULE ADD or MODULE VERSION, the text parses, every EXCLUDES
  and INTERACTS_WITH entry matches a declared ID, each TEST_BINDING expands and passes the
  fundamental tests T1, T2, T5, T4 and T6 and T3 at depth 1, and with each other OFFERED
  Provision neither excludes, on each TEST_BINDING the two share, the pair expands in either
  order to one D(TPK) that passes the same checks; an AUTHOR parameter of one name in both is
  refused with two DIMENSIONs and raises the SHARED PARAMETER question with one.
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-- v1's `_show` of a text the answer carries. -/
def showRun (s : String) : Run String := pure (showReason s)

/-- v1's `_claims_declared`: each claim is of a declared version, its DIGEST the declared
one, and its text given. -/
def claimsDeclared (cls : List Claim) (texts : List Provision) (S : State) : Run Unit := do
  for c in cls do
    let some r := S.versions.find? (c.id, c.version) | refuse ("CLAIM " ++ c.cv ++ ": not declared")
    if c.digest != r.digest then refuse ("CLAIM " ++ c.cv ++ ": DIGEST does not match the declaration")
    if (textOf? texts c.id c.version).isNone then refuse ("CLAIM " ++ c.cv ++ ": no module text")

/-- The status of a declared version (one the checks before found). -/
def statusOf (S : State) (c : Claim) : Declared :=
  (S.versions.find? (c.id, c.version)).getD default

/-! ## module_verify (6.5) -/

/-- What `module_verify` answers: MATCH or not, D(TPK) of the expansion and of the draft's
Starting Set (or NOT WELL-FORMED), and each claim's status. -/
structure Verified where
  matched : Bool
  want : String
  got : String
  claims : List (String × String × Status)
  deriving DecidableEq, Repr

/-- v1's `module_verify`. -/
def verify (D : DigestHook) (base claims textsV lines draft : Value) : Answer Verified :=
  finish do
    let S ← readCatalogue lines
    let texts ← readTexts textsV
    declaredTexts D texts S
    let cls ← readClaims claims
    claimsDeclared cls texts S
    let x ← expandRun D base claims textsV
    let .obj d := draft | refuse "DRAFT: not an object"
    let some dt := get? d "TPK" | refuse "DRAFT: missing zone TPK"
    let want ← dTpk D x.tpk
    let got ← match ← t1First dt with
      | none => dTpk D dt
      | some _ => pure "NOT WELL-FORMED"
    pure ⟨want == got, want, got, cls.map fun c => (c.id, c.version, (statusOf S c).status)⟩

/-! ## draft_module_status (6.10) -/

/-- A claim's row: its status, with what it carries. -/
inductive ClaimStatus where
  | offered
  /-- SUPERSEDED, and no version of the ID OFFERED now. -/
  | noneOffered
  /-- SUPERSEDED by the OFFERED version: SAME, DIFFERS, or `NOT EXPANDED: <reason>`. -/
  | superseded (successor : String) (verdict : String)
  | retired (date : String)
  | withdrawn (date note : String)
  deriving DecidableEq, Repr

/-- What `draft_module_status` answers: each claim's row, and the Declarer's questions. -/
structure DraftStatus where
  claims : List (String × String × ClaimStatus)
  gate : List String
  deriving DecidableEq, Repr

/-- v1's `draft_module_status`. -/
def draftStatus (D : DigestHook) (base claims textsV lines : Value) : Answer DraftStatus :=
  finish do
    let S ← readCatalogue lines
    let texts ← readTexts textsV
    declaredTexts D texts S
    let cls ← readClaims claims
    claimsDeclared cls texts S
    let x ← expandRun D base claims textsV
    let mine ← dTpk D x.tpk
    let (bd, btpk) ← checkDraft base
    let mut rows : List (String × String × ClaimStatus) := []
    let mut gate : List String := []
    for c in cls do
      let st := statusOf S c
      match st.status with
      | .offered => rows := rows ++ [(c.id, c.version, .offered)]
      | .superseded =>
        let cur := (S.versions.filter fun (k, r) => k.1 == c.id && r.status == .offered).map (·.1)
        match cur with
        | [] => rows := rows ++ [(c.id, c.version, .noneOffered)]
        | ck :: _ =>
          if (textOf? texts ck.1 ck.2).isNone then
            refuse ("MODULES: no text of " ++ ck.1 ++ " " ++ ck.2 ++ " (OFFERED)")
          let dg := ((S.versions.find? ck).map (·.digest)).getD ""
          let alt := cls.map fun o => if o.id == c.id then { o with version := ck.2, digest := dg } else o
          let verdict ← match expandWith D bd btpk alt (textOf? texts) with
            | .ok y => do pure (if (← dTpk D y.tpk) == mine then "SAME" else "DIFFERS")
            | .error (.refused m) => showRun ("NOT EXPANDED: " ++ m)
            | .error (.owed w) => owe w
          rows := rows ++ [(c.id, c.version, .superseded ck.2 verdict)]
      | .retired => rows := rows ++ [(c.id, c.version, .retired st.date)]
      | .withdrawn =>
        rows := rows ++ [(c.id, c.version, .withdrawn st.date st.note)]
        gate := gate ++ ["This draft uses " ++ c.cv ++ ", withdrawn on " ++ st.date ++ " for: " ++ st.note ++
          ". Declare with it?"]
    pure ⟨rows, gate⟩

/-! ## module_use_view (6.11) -/

/-- What `module_use_view` answers: ID, VERSION, prefix and status, sorted; and the number of
certificates claiming a WITHDRAWN version. -/
structure UseView where
  rows : List (String × String × String × Status)
  onWithdrawn : Nat
  deriving DecidableEq, Repr

/-- Rows in code point order of ID, VERSION, prefix. -/
def useRowLe (a b : String × String × String × Status) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && (decide (a.2.1 < b.2.1) || (a.2.1 == b.2.1 && decide (a.2.2.1 ≤ b.2.2.1))))

/-- v1's `module_use_view`. -/
def useView (certificates lines : Value) : Answer UseView :=
  finish do
    let S ← readCatalogue lines
    let .arr cs := certificates | refuse "CERTIFICATES: not a list"
    let mut read : List (String × List (String × String × String)) := []
    let mut i := 0
    for cv in cs do
      i := i + 1
      let tag := s!"CERTIFICATE {i}"
      let .obj c := cv | refuse (tag ++ ": not an object")
      fields tag c ["PREFIX", "MODULES_USED"]
      let .str pre := field c "PREFIX" | refuse (tag ++ ": field PREFIX has the wrong type")
      let some used := triples? (field c "MODULES_USED") | refuse (tag ++ ": field MODULES_USED has the wrong type")
      unless Zone.isIdent pre do refuse (tag ++ ": PREFIX " ++ pre ++ " is not a prefix")
      read := read ++ [(pre, used)]
    if let some d := leastDup (read.map (·.1)) then refuse ("CERTIFICATES: duplicate prefix " ++ d)
    let mut rows : List (String × String × String × Status) := []
    let mut n := 0
    for (pre, used) in read do
      let tag := "CERTIFICATE " ++ pre
      if let some d := leastDup (used.map (·.1)) then refuse (tag ++ ": duplicate module " ++ d)
      let mut wd := false
      for (id, v, dg) in used do
        let some r := S.versions.find? (id, v) | refuse (tag ++ ": " ++ id ++ " " ++ v ++ " is not declared")
        if r.digest != dg then refuse (tag ++ ": " ++ id ++ " " ++ v ++ ": DIGEST does not match the declaration")
        wd := wd || r.status == .withdrawn
        rows := rows ++ [(id, v, pre, r.status)]
      if wd then n := n + 1
    pure ⟨rows.mergeSort useRowLe, n⟩

/-! ## module_check (6.9) -/

/-- v1's `_kernel_verdict`, the fundamental tests' verdict: the first test failed, with its first problem; then T3
at depth 1; else PASS. -/
def testsVerdict (tpk : Value) : Run String := do
  let ofOwing : StartingSet.Tests.Owing → Run String := fun
    | .zone o => owe (.exact o.message)
    | .digits => owe (.exact "a value's twelve-digit form is not decided at the precisions tried")
    | .exact w => owe (.exact w)
  match StartingSet.Tests.fundamentalTests tpk with
  | .error o => ofOwing o
  | .ok run =>
    if !run.pass then
      match run.rows.find? (·.state == .ran false) with
      | some row => pure (row.test ++ ": " ++ row.problems.headD "failed")
      | none => pure "kernel tests: not passed"
    else
      let tms : Value := .obj [("PARAMETERS", .obj [("S_MAX", .int 1)])]
      match StartingSet.Tests.t3Consistency tpk tms with
      | .error o => ofOwing o
      | .ok [] => pure "PASS"
      | .ok (p :: _) => pure ("T3: " ++ p)

/-- v1's `_binding_claim`: a TEST_BINDING as a claim of its own Provision, every question
raised by another of `others` answered NO where the binding leaves it. -/
def bindingClaim (D : DigestHook) (M : Provision) (b : Binding) (others : List String) : Run Claim := do
  let mut ans := b.answers
  for qd in M.questions do
    if others.any (idMatches qd.withPattern ·) && !has ans qd.qid then ans := ans ++ [(qd.qid, .str "NO")]
  pure ⟨M.id, M.version, ← M.digest D, b.bind, b.values, ans⟩

/-- The verdict of an expansion: the fundamental tests' verdict on its Starting Set, or the refusal. -/
def expansionVerdict (r : Run String) : Run String :=
  match r with
  | .ok v => pure v
  | .error (.refused m) => pure m
  | .error (.owed w) => owe w

/-- A row of `module_check`'s answer. -/
inductive CheckRow where
  | digest (d : String)
  | references (verdict : String)
  | binding (name verdict : String)
  | pairExcluded (id version : String)
  /-- A pair's verdict on a TEST_BINDING both share (`-` for none). -/
  | pair (id version binding verdict : String)
  | sharedParameter (id version otherId otherVersion name : String)
  | atomicity (assumptions : List String)
  deriving DecidableEq, Repr

/-- A row that fails the check. -/
def CheckRow.fails : CheckRow → Bool
  | .references v | .binding _ v | .pair _ _ _ v => v != "PASS" && v != "EXCLUDED"
  | _ => false

/-- What `module_check` answers: PASS or FAIL, and its rows. -/
structure Checked where
  pass : Bool
  rows : List CheckRow
  deriving DecidableEq, Repr

/-- v1's `module_check`. -/
def check (D : DigestHook) (text act date lines textsV : Value) : Answer Checked :=
  finish do
    match act with
    | .str "MODULE ADD" | .str "MODULE VERSION" => pure ()
    | .str a => refuse ("ACT: " ++ a ++ " is not MODULE ADD or MODULE VERSION")
    | _ => refuse "ACT: ? is not MODULE ADD or MODULE VERSION"
    let M ← parseText text
    let S ← readCatalogue lines
    let texts ← readTexts textsV
    declaredTexts D texts S
    for (i, v, _) in S.versions.offer do
      if (textOf? texts i v).isNone then refuse ("MODULES: no text of " ++ i ++ " " ++ v ++ " (OFFERED)")
    let dig ← M.digest D
    let line : Value := .obj [("ACT", act), ("ID", .str M.id), ("VERSION", .str M.version),
      ("DIGEST", .str dig), ("DATE", date)]
    let ls := match lines with
      | .arr xs => xs
      | _ => []
    let S2 ← readCatalogue (.arr (ls ++ [line]))
    let mut rows : List CheckRow := [.digest dig]
    let declared := sortedSet ((S2.versions.map (·.1.1)).filter (· != M.id))
    let mut ref := "PASS"
    for p in sortStrs M.excludes do
      if ref == "PASS" && !declared.any (idMatches p ·) then ref := "EXCLUDES " ++ p ++ " matches no declared module"
    if ref == "PASS" then
      for qd in M.questions do
        if ref == "PASS" && !declared.any (idMatches qd.withPattern ·) then
          ref := "WITH " ++ qd.withPattern ++ " matches no declared module"
    rows := rows ++ [.references ref]
    let base (b : Binding) : Entry := [("TPK", b.tpk)]
    for b in M.bindings do
      let verdict ← expansionVerdict do
        let claim ← bindingClaim D M b []
        let x ← expandWith D (base b) b.tpk [claim] (textOf? [M])
        testsVerdict x.tpk
      rows := rows ++ [.binding b.name (← showRun verdict)]
    let authors := (M.params.filter (·.supply == "AUTHOR")).map fun p => (p.name, p.dim)
    for (i, v, _) in S2.versions.offer do
      if i == M.id then continue
      let some B := textOf? texts i v | refuse ("MODULES: no text of " ++ i ++ " " ++ v ++ " (OFFERED)")
      if excludesPair M B then
        rows := rows ++ [.pairExcluded i v]
        continue
      let shared := sortStrs ((B.params.filter fun p => p.supply == "AUTHOR" && (authors.lookup p.name).isSome).map (·.name))
      let differ := shared.filter fun n => authors.lookup n != (B.paramOf? n).map (·.dim)
      if let n :: _ := differ then
        rows := rows ++ [.pair i v "-" ("SHARED PARAMETER " ++ n ++ ": DIMENSION " ++ (authors.lookup n).getD "" ++
          " in " ++ M.cv ++ ", " ++ ((B.paramOf? n).map (·.dim)).getD "" ++ " in " ++ i ++ " " ++ v)]
        continue
      let mut anyShared := false
      for b in M.bindings do
        let some bb := B.bindings.find? (·.name == b.name) | continue
        if (← dTpk D bb.tpk) != (← dTpk D b.tpk) then continue
        anyShared := true
        let verdict ← expansionVerdict do
          let ca ← bindingClaim D M b [i]
          let cb ← bindingClaim D B bb [M.id]
          let x1 ← expandWith D (base b) b.tpk (sortClaims [ca, cb]) (textOf? [M, B])
          let x2 ← expandWith D (base b) b.tpk (sortClaims [cb, ca]) (textOf? [B, M])
          if (← dTpk D x1.tpk) != (← dTpk D x2.tpk) then pure "TWO SELECTION ORDERS GIVE TWO D(TPK)"
          else testsVerdict x1.tpk
        rows := rows ++ [.pair i v b.name (← showRun verdict)]
      if !anyShared then rows := rows ++ [.pair i v "-" "NO SHARED BINDING"]
      for n in shared do
        rows := rows ++ [.sharedParameter M.id M.version i v n]
    rows := rows ++ [.atomicity (M.assumptions.map (·.name))]
    pure ⟨!rows.any CheckRow.fails, rows⟩

end Principia.Provision
