import Principia.Provision.Reader
import Principia.Digest

/-!
# The catalogue: the PROVISION DECLARATION lines and their state

v1's `catalogue_state` and `_state` (tpm_module_spec 0.2.0 5.3, 6.8; TPS 5.22.9, 5.22.10). The
Declarer's five acts, in chain order: MODULE ADD declares a new ID at its first version,
OFFERED; MODULE VERSION a new version of a declared ID, greater than every version of it,
OFFERED, the ID's OFFERED version becoming SUPERSEDED in the same act; MODULE RETIRE makes the
OFFERED version RETIRED; MODULE WITHDRAW makes a version found defective WITHDRAWN with its
reason, and may offer again a SUPERSEDED or RETIRED version of the ID; MODULE REINSTATE makes a
SUPERSEDED or RETIRED version OFFERED again. The acts keep v1's wire words (PMA's terminology
map renames them PROVISION ADD and so on; the lines the Calculator reads today are v1's).

The OFFER is the OFFERED versions in ID order with their digests; after every line a state
digest names it, SHA-256 over `["TPC-MODULE-OFFER", "1", ID, VERSION, DIGEST, ...]`, taken through the `DigestHook`. v1 computed the state digest after every line
wherever it read a catalogue; only `catalogue_state` answers with it, so here it is taken there
alone, and the other functions, which never read it, need no digest of the catalogue.

Proved below: at most one version of an ID is OFFERED after any accepted lines, and a
WITHDRAWN version stays WITHDRAWN.
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-! ## Statuses and acts -/

/-- A declared version's status (TPS 1.1). -/
inductive Status where
  | offered | superseded | retired | withdrawn
  deriving DecidableEq, Repr, Inhabited

/-- A status's wire word. -/
def Status.word : Status → String
  | .offered => "OFFERED"
  | .superseded => "SUPERSEDED"
  | .retired => "RETIRED"
  | .withdrawn => "WITHDRAWN"

/-- The five acts. -/
inductive Act where
  | add | version | retire | withdraw | reinstate
  deriving DecidableEq, Repr, Inhabited

/-- An act's wire word, as v1 spells it. -/
def Act.word : Act → String
  | .add => "MODULE ADD"
  | .version => "MODULE VERSION"
  | .retire => "MODULE RETIRE"
  | .withdraw => "MODULE WITHDRAW"
  | .reinstate => "MODULE REINSTATE"

/-- An act by its wire word. -/
def Act.ofWord? : String → Option Act
  | "MODULE ADD" => some .add
  | "MODULE VERSION" => some .version
  | "MODULE RETIRE" => some .retire
  | "MODULE WITHDRAW" => some .withdraw
  | "MODULE REINSTATE" => some .reinstate
  | _ => none

/-- An act's fields besides ACT, in v1's order. -/
def Act.fields : Act → List String
  | .add | .version => ["ID", "VERSION", "DIGEST", "DATE"]
  | .retire | .reinstate => ["ID", "VERSION", "DATE"]
  | .withdraw => ["ID", "VERSION", "REASON", "DATE"]

/-- A line, read. -/
structure Line where
  act : Act
  id : String
  version : String
  /-- The DIGEST of MODULE ADD and MODULE VERSION; empty for the other acts. -/
  digest : String
  date : String
  /-- The REASON of MODULE WITHDRAW; empty for the other acts. -/
  reason : String
  replacedBy : Option String
  deriving Repr, Inhabited

/-- A declared version's record. -/
structure Declared where
  digest : String
  status : Status
  date : String
  note : String
  deriving DecidableEq, Repr, Inhabited

/-- The declared versions in the order they were first declared, keyed by (ID, VERSION). -/
abbrev Catalogue := List ((String × String) × Declared)

/-- A version's record. -/
def Catalogue.find? (V : Catalogue) (key : String × String) : Option Declared := V.lookup key

/-- Set the status and date of every record a test picks. -/
def Catalogue.restate (V : Catalogue) (pick : (String × String) → Declared → Bool)
    (st : Status) (date : String) : Catalogue :=
  V.map fun e => (e.1, if pick e.1 e.2 then { e.2 with status := st, date } else e.2)

/-- Change the record of one version. -/
def Catalogue.setAt (V : Catalogue) (key : String × String) (g : Declared → Declared) : Catalogue :=
  V.map fun e => (e.1, if e.1 == key then g e.2 else e.2)

/-- v1's `_offer`: the OFFERED versions in (ID, VERSION) order, with their digests. -/
def Catalogue.offer (V : Catalogue) : List (String × String × String) :=
  ((V.filter fun (_, r) => r.status == .offered).map fun ((i, v), r) => (i, v, r.digest)).mergeSort
    fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2.1 ≤ b.2.1))

/-- The keys in code point order of (ID, VERSION). -/
def Catalogue.sortedKeys (V : Catalogue) : List (String × String) :=
  (V.map (·.1)).mergeSort fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-! ## One line -/

/-- v1's checks of one line before its act: its fields, their types and forms, its date. -/
def readLine (n : Nat) (ln : Value) (prev : Option String) : Run Line := do
  let tag := s!"LINE {n}"
  let .obj o := ln | refuse (tag ++ ": not an object")
  let some actV := get? o "ACT" | refuse (tag ++ ": missing field ACT")
  let .str actW := actV | refuse (tag ++ ": field ACT has the wrong type")
  let some act := Act.ofWord? actW | refuse (tag ++ ": ACT " ++ actW ++ " is not a module act")
  let opt := if act == .withdraw then ["REPLACED_BY"] else []
  for k in keysOf o do
    if k != "ACT" && !act.fields.contains k && !opt.contains k then refuse (tag ++ ": unknown field " ++ k)
  for f in act.fields do
    unless has o f do
      if f == "REASON" then refuse (tag ++ ": MODULE WITHDRAW without a reason")
      refuse (tag ++ ": missing field " ++ f)
  for f in act.fields ++ opt do
    match get? o f with
    | some (.str _) | none => pure ()
    | some _ => refuse (tag ++ ": field " ++ f ++ " has the wrong type")
  let s (f : String) : String := (getStr? o f).getD ""
  if act == .withdraw then
    if let some b ← firstBad (s "REASON") then refuse (tag ++ ": field REASON contains disallowed character " ++ b)
  let mid := s "ID"
  let ver := s "VERSION"
  let date := s "DATE"
  unless isProvisionId mid do refuse (tag ++ ": ID " ++ mid ++ " is not a module ID")
  unless isVersion ver do refuse (tag ++ ": VERSION " ++ ver ++ " is not a version")
  let rep := getStr? o "REPLACED_BY"
  if let some r := rep then
    unless isVersion r do refuse (tag ++ ": REPLACED_BY " ++ r ++ " is not a version")
  if act.fields.contains "DIGEST" && !isDigest (s "DIGEST") then refuse (tag ++ ": DIGEST is not a digest")
  unless isDate date do refuse (tag ++ ": DATE " ++ date ++ " is not a date")
  if act == .withdraw && Zone.blank (s "REASON") then refuse (tag ++ ": MODULE WITHDRAW without a reason")
  if let some p := prev then
    if decide (date < p) then refuse (tag ++ ": DATE " ++ date ++ " is before the previous line's")
  pure ⟨act, mid, ver, s "DIGEST", date, s "REASON", rep⟩

/-- The greatest version of an ID's versions, compared as integers. -/
def maxVersion (vs : List String) : Option String :=
  vs.foldl (fun m v => match m with
    | none => some v
    | some w => if keyLt (versionKey w) (versionKey v) then some v else some w) none

/-- The OFFERED version of an ID becomes SUPERSEDED. -/
def supersede (V : Catalogue) (mid date : String) : Catalogue :=
  V.restate (fun k r => k.1 == mid && r.status == .offered) .superseded date

/-- v1's refusal of an act on the catalogue, the line read (5.3, TPS 5.22.10), or none. -/
def refusal (n : Nat) (V : Catalogue) (ln : Line) : Option String :=
  let tag := s!"LINE {n}"
  let mid := ln.id
  let key := (mid, ln.version)
  let mine := (V.map (·.1)).filter (·.1 == mid)
  let notDeclared := tag ++ ": " ++ mid ++ " " ++ ln.version ++ " is not declared"
  let vmax := (maxVersion (mine.map (·.2))).getD ""
  match ln.act with
  | .add | .version =>
    if ln.act == .add && !mine.isEmpty then
      some (tag ++ ": MODULE ADD of " ++ mid ++ ", an ID already declared (no ID is reissued)")
    else if ln.act == .version && mine.isEmpty then
      some (tag ++ ": MODULE VERSION of " ++ mid ++ ", an ID never added")
    else if ln.act == .version && (V.find? key).isSome then
      some (tag ++ ": " ++ mid ++ " " ++ ln.version ++ " is already declared (no version is reissued)")
    else if ln.act == .version && !keyLt (versionKey vmax) (versionKey ln.version) then
      some (tag ++ ": " ++ mid ++ " " ++ ln.version ++ " is not greater than " ++ mid ++ " " ++ vmax)
    else (V.sortedKeys.find? fun k => ((V.find? k).map (·.digest)) == some ln.digest).map fun k =>
      tag ++ ": DIGEST already declared for " ++ k.1 ++ " " ++ k.2
  | .retire =>
    match V.find? key with
    | none => some notDeclared
    | some r =>
      if r.status != .offered then
        some (tag ++ ": MODULE RETIRE of " ++ mid ++ " " ++ ln.version ++ ", which is " ++ r.status.word ++ ", not OFFERED")
      else none
  | .withdraw =>
    match V.find? key with
    | none => some notDeclared
    | some r =>
      if r.status == .withdrawn then
        some (tag ++ ": " ++ mid ++ " " ++ ln.version ++ " is already WITHDRAWN (WITHDRAWN is final)")
      else match ln.replacedBy with
        | none => none
        | some rep =>
          if r.status != .offered then
            some (tag ++ ": REPLACED_BY needs " ++ mid ++ " " ++ ln.version ++ " OFFERED; it is " ++ r.status.word)
          else match V.find? (mid, rep) with
            | none => some (tag ++ ": REPLACED_BY " ++ mid ++ " " ++ rep ++ " is not declared")
            | some rr =>
              if rr.status == .superseded || rr.status == .retired then none
              else some (tag ++ ": REPLACED_BY " ++ mid ++ " " ++ rep ++ " is " ++ rr.status.word ++
                ", not SUPERSEDED or RETIRED")
  | .reinstate =>
    match V.find? key with
    | none => some notDeclared
    | some r =>
      if r.status == .withdrawn then
        some (tag ++ ": MODULE REINSTATE of " ++ mid ++ " " ++ ln.version ++ ", which is WITHDRAWN (WITHDRAWN is final)")
      else if r.status == .offered then
        some (tag ++ ": MODULE REINSTATE of " ++ mid ++ " " ++ ln.version ++ ", which is already OFFERED")
      else none

/-- A record given a new status on a date. -/
def restatus (st : Status) (date : String) (x : Declared) : Declared := { x with status := st, date }

/-- A record withdrawn by a line, with its reason. -/
def withdrawn (ln : Line) (x : Declared) : Declared :=
  { x with status := .withdrawn, date := ln.date, note := ln.reason }

/-- What an accepted act does to the catalogue. -/
def effect (V : Catalogue) (ln : Line) : Catalogue :=
  let key := (ln.id, ln.version)
  match ln.act with
  | .add | .version => supersede V ln.id ln.date ++ [(key, ⟨ln.digest, .offered, ln.date, ""⟩)]
  | .retire => V.setAt key (restatus .retired ln.date)
  | .withdraw =>
    match ln.replacedBy with
    | none => V.setAt key (withdrawn ln)
    | some rep => (V.setAt key (withdrawn ln)).setAt (ln.id, rep) (restatus .offered ln.date)
  | .reinstate => (supersede V ln.id ln.date).setAt key (restatus .offered ln.date)

/-- v1's act on the catalogue: refused, or done. -/
def step (n : Nat) (V : Catalogue) (ln : Line) : Except String Catalogue :=
  match refusal n V ln with
  | some m => .error m
  | none => .ok (effect V ln)

/-! ## The lines -/

/-- A catalogue read from its lines: the declared versions, and the OFFER after each line
(`offers[0]` before any). -/
structure State where
  versions : Catalogue
  offers : List (List (String × String × String))
  deriving Repr, Inhabited

/-- The number of lines read. -/
def State.lines (S : State) : Nat := S.offers.length - 1

/-- The OFFER after `at` lines. -/
def State.offerAt (S : State) (at_ : Nat) : List (String × String × String) := S.offers.getD at_ []

/-- The lines from the `n`-th on, over the catalogue `V`: the catalogue after them, and the
OFFER after each. -/
def stateFrom (n : Nat) (V : Catalogue) (prev : Option String) :
    List Value → Run (Catalogue × List (List (String × String × String)))
  | [] => pure (V, [])
  | lv :: rest => do
    let ln ← readLine n lv prev
    match step n V ln with
    | .error m => refuse m
    | .ok V' =>
      let (W, offs) ← stateFrom (n + 1) V' (some ln.date) rest
      pure (W, V'.offer :: offs)

/-- v1's `_state`: the lines in chain order, each read and then acted. -/
def readState (lines : Value) : Run State := do
  let .arr ls := lines | refuse "LINES: not a list"
  let (V, offs) ← stateFrom 1 [] none ls
  pure ⟨V, [] :: offs⟩

/-- v1's `_catalogue`: the state, a refusal prefixed `CATALOGUE: `. -/
def readCatalogue (lines : Value) : Run State :=
  match readState lines with
  | .error (.refused m) => refuse ("CATALOGUE: " ++ m)
  | r => r

/-- The preimage of a state digest. -/
def offerPreimage (offer : List (String × String × String)) : String :=
  Digest.preimage (["TPC-MODULE-OFFER", "1"] ++ offer.flatMap fun (i, v, d) => [i, v, d])

/-- What `catalogue_state` answers. -/
structure CatalogueState where
  /-- Every declared version in (ID, VERSION) order: ID, VERSION, DIGEST, status, date, note. -/
  versions : List (String × String × String × Status × String × String)
  /-- The OFFER. -/
  offered : List (String × String × String)
  /-- After each line, its number and the state digest. -/
  states : List (Nat × String)
  deriving Repr

/-- v1's `catalogue_state`. -/
def catalogueState (D : DigestHook) (lines : Value) : Answer CatalogueState :=
  finish do
    let S ← readState lines
    let V := S.versions
    let versions := V.sortedKeys.filterMap fun k =>
      (V.find? k).map fun r => (k.1, k.2, r.digest, r.status, r.date, r.note)
    let mut states : List (Nat × String) := []
    for i in List.range S.lines do
      states := states ++ [(i + 1, ← D.digest (offerPreimage (S.offerAt (i + 1))))]
    pure ⟨versions, V.offer, states⟩

/-! ## The catalogue's guarantees -/

/-- No two different versions of one ID are both OFFERED (TPS 5.22.10: "At most one version
per ID is OFFERED"). -/
def Catalogue.oneOffered (V : Catalogue) : Prop :=
  ∀ e₁ ∈ V, ∀ e₂ ∈ V, e₁.1.1 = e₂.1.1 → e₁.2.status = .offered → e₂.2.status = .offered → e₁.1 = e₂.1

/-- A record found is a member. -/
theorem Catalogue.mem_of_find? {V : Catalogue} {k : String × String} {r : Declared}
    (h : V.find? k = some r) : (k, r) ∈ V := by
  induction V with
  | nil => simp [Catalogue.find?, List.lookup] at h
  | cons e t ih =>
    obtain ⟨k', x⟩ := e
    simp only [Catalogue.find?, List.lookup] at h
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      have : k = k' := by simpa using hk
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- A record found after a change of each record by its key. -/
theorem Catalogue.find?_map {V : Catalogue} {k : String × String} (f : (String × String) → Declared → Declared) :
    Catalogue.find? (V.map fun e => (e.1, f e.1 e.2)) k = (V.find? k).map (f k) := by
  induction V with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨k', x⟩ := e
    simp only [Catalogue.find?, List.map, List.lookup] at ih ⊢
    by_cases hk : k = k'
    · subst hk; simp
    · have : (k == k') = false := by simpa using hk
      simp [this, ih]

/-- A record found after `setAt`. -/
theorem Catalogue.find?_setAt (V : Catalogue) (key : String × String) (g : Declared → Declared)
    (k : String × String) : (V.setAt key g).find? k = (V.find? k).map fun x => if k == key then g x else x :=
  Catalogue.find?_map (V := V) (fun k' x => if k' == key then g x else x)

/-- A record found after `restate`. -/
theorem Catalogue.find?_restate (V : Catalogue) (pick : (String × String) → Declared → Bool) (st : Status)
    (date : String) (k : String × String) :
    (V.restate pick st date).find? k = (V.find? k).map fun x => if pick k x then { x with status := st, date } else x :=
  Catalogue.find?_map (V := V) (fun k' x => if pick k' x then { x with status := st, date } else x)

/-- A record found is found again after more records are added. -/
theorem Catalogue.find?_append {V W : Catalogue} {k : String × String} {r : Declared}
    (h : V.find? k = some r) : Catalogue.find? (V ++ W) k = some r := by
  induction V with
  | nil => simp [Catalogue.find?, List.lookup] at h
  | cons e t ih =>
    obtain ⟨k', x⟩ := e
    simp only [Catalogue.find?, List.cons_append, List.lookup] at h ih ⊢
    split at h
    · simp [h]
    · simp [ih h]

/-- What `refusal` leaves for MODULE WITHDRAW naming REPLACED_BY: the version withdrawn is
OFFERED, and the version offered again is SUPERSEDED or RETIRED. -/
theorem refusal_withdraw_some {n : Nat} {V : Catalogue} {ln : Line} {rep : String}
    (hr : refusal n V ln = none) (ha : ln.act = .withdraw) (hp : ln.replacedBy = some rep) :
    (∃ r, V.find? (ln.id, ln.version) = some r ∧ r.status = .offered) ∧
      (∃ rr, V.find? (ln.id, rep) = some rr ∧ (rr.status = .superseded ∨ rr.status = .retired)) := by
  unfold refusal at hr
  simp only [ha, hp] at hr
  split at hr
  · simp at hr
  · rename_i r hfind
    split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · rename_i hoff
        split at hr
        · simp at hr
        · rename_i rr hrr
          split at hr
          · rename_i hst
            refine ⟨⟨r, hfind, by simpa using hoff⟩, ⟨rr, hrr, ?_⟩⟩
            simpa [Bool.or_eq_true, beq_iff_eq] using hst
          · simp at hr

/-- What `refusal` leaves for every act but MODULE ADD and MODULE VERSION: the version is
declared, and not WITHDRAWN. -/
theorem refusal_declared {n : Nat} {V : Catalogue} {ln : Line}
    (hr : refusal n V ln = none) (ha : ln.act ≠ .add ∧ ln.act ≠ .version) :
    ∃ r, V.find? (ln.id, ln.version) = some r ∧ r.status ≠ .withdrawn ∧
      (ln.act = .retire → r.status = .offered) ∧ (ln.act = .reinstate → r.status ≠ .offered) := by
  unfold refusal at hr
  cases hact : ln.act with
  | add => exact absurd hact ha.1
  | version => exact absurd hact ha.2
  | retire =>
    simp only [hact] at hr
    split at hr
    · simp at hr
    · rename_i r hfind
      split at hr
      · simp at hr
      · rename_i hoff
        have : r.status = .offered := by simpa using hoff
        exact ⟨r, hfind, by simp [this], fun _ => this, fun h => by simp at h⟩
  | withdraw =>
    simp only [hact] at hr
    split at hr
    · simp at hr
    · rename_i r hfind
      split at hr
      · simp at hr
      · rename_i hw
        exact ⟨r, hfind, by simpa using hw, fun h => by simp at h, fun h => by simp at h⟩
  | reinstate =>
    simp only [hact] at hr
    split at hr
    · simp at hr
    · rename_i r hfind
      split at hr
      · simp at hr
      · rename_i hw
        split at hr
        · simp at hr
        · rename_i hoff
          exact ⟨r, hfind, by simpa using hw, fun h => by simp at h, fun _ => by simpa using hoff⟩

/-- A record after `setAt` is the key's, changed, or another unchanged. -/
theorem Catalogue.mem_setAt {V : Catalogue} {key : String × String} {g : Declared → Declared}
    {e : (String × String) × Declared} (h : e ∈ V.setAt key g) :
    (e.1 = key ∧ ∃ x, (key, x) ∈ V ∧ e.2 = g x) ∨ (e ∈ V ∧ e.1 ≠ key) := by
  simp only [Catalogue.setAt, List.mem_map] at h
  obtain ⟨⟨k, x⟩, hm, rfl⟩ := h
  by_cases hk : k = key
  · subst hk; exact .inl ⟨rfl, x, hm, by simp⟩
  · exact .inr ⟨by simpa [hk] using hm, hk⟩

/-- An OFFERED record after `supersede` was OFFERED before, under another ID. -/
theorem mem_supersede {V : Catalogue} {mid date : String} {e : (String × String) × Declared}
    (h : e ∈ supersede V mid date) (ho : e.2.status = .offered) : e ∈ V ∧ e.1.1 ≠ mid := by
  simp only [supersede, Catalogue.restate, List.mem_map] at h
  obtain ⟨⟨k, x⟩, hm, rfl⟩ := h
  simp only at ho ⊢
  by_cases hp : k.1 = mid ∧ x.status = .offered
  · simp [hp.1, hp.2] at ho
  · have hq : ¬(k.1 = mid ∧ x.status = Status.offered) := hp
    simp only [Bool.and_eq_true, beq_iff_eq, hq, ite_false] at ho ⊢
    refine ⟨hm, fun hk => hq ⟨hk, ho⟩⟩

/-- An accepted act keeps at most one version of each ID OFFERED. -/
theorem effect_oneOffered {n : Nat} {V : Catalogue} {ln : Line} (hr : refusal n V ln = none)
    (h : V.oneOffered) : (effect V ln).oneOffered := by
  intro e₁ h₁ e₂ h₂ hid s₁ s₂
  cases hact : ln.act with
  | add | version =>
    simp only [effect, hact, List.mem_append, List.mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | rfl
    · exact h e₁ (mem_supersede h₁ s₁).1 e₂ (mem_supersede h₂ s₂).1 hid s₁ s₂
    · exact absurd hid (mem_supersede h₁ s₁).2
    · exact absurd hid.symm (mem_supersede h₂ s₂).2
    · rfl
  | retire =>
    simp only [effect, hact] at h₁ h₂
    rcases Catalogue.mem_setAt h₁ with ⟨_, _, _, he₁⟩ | ⟨m₁, _⟩
    · simp [he₁, restatus] at s₁
    rcases Catalogue.mem_setAt h₂ with ⟨_, _, _, he₂⟩ | ⟨m₂, _⟩
    · simp [he₂, restatus] at s₂
    exact h e₁ m₁ e₂ m₂ hid s₁ s₂
  | withdraw =>
    cases hp : ln.replacedBy with
    | none =>
      simp only [effect, hact, hp] at h₁ h₂
      rcases Catalogue.mem_setAt h₁ with ⟨_, _, _, he₁⟩ | ⟨m₁, _⟩
      · simp [he₁, withdrawn] at s₁
      rcases Catalogue.mem_setAt h₂ with ⟨_, _, _, he₂⟩ | ⟨m₂, _⟩
      · simp [he₂, withdrawn] at s₂
      exact h e₁ m₁ e₂ m₂ hid s₁ s₂
    | some rep =>
      obtain ⟨⟨r, hr₁, hro⟩, _⟩ := refusal_withdraw_some hr hact hp
      have hkey := Catalogue.mem_of_find? hr₁
      simp only [effect, hact, hp] at h₁ h₂
      -- an OFFERED record is the one offered again, or an OFFERED one of before other than the
      -- one withdrawn
      have back : ∀ e, e ∈ (V.setAt (ln.id, ln.version) (withdrawn ln)).setAt (ln.id, rep)
          (restatus .offered ln.date) → e.2.status = .offered →
          e.1 = (ln.id, rep) ∨ (e ∈ V ∧ e.1 ≠ (ln.id, ln.version)) := by
        intro e he hs
        rcases Catalogue.mem_setAt he with ⟨hk, _⟩ | ⟨m, _⟩
        · exact .inl hk
        rcases Catalogue.mem_setAt m with ⟨_, _, _, hw⟩ | ⟨m', hk'⟩
        · simp [hw, withdrawn] at hs
        exact .inr ⟨m', hk'⟩
      rcases back e₁ h₁ s₁ with k₁ | ⟨m₁, n₁⟩ <;> rcases back e₂ h₂ s₂ with k₂ | ⟨m₂, n₂⟩
      · rw [k₁, k₂]
      · exact absurd (h e₂ m₂ _ hkey (by rw [← hid, k₁]) s₂ hro) n₂
      · exact absurd (h e₁ m₁ _ hkey (by rw [hid, k₂]) s₁ hro) n₁
      · exact h e₁ m₁ e₂ m₂ hid s₁ s₂
  | reinstate =>
    simp only [effect, hact] at h₁ h₂
    rcases Catalogue.mem_setAt h₁ with ⟨k₁, _⟩ | ⟨m₁, _⟩ <;>
      rcases Catalogue.mem_setAt h₂ with ⟨k₂, _⟩ | ⟨m₂, _⟩
    · rw [k₁, k₂]
    · exact absurd (by rw [← hid, k₁]) (mem_supersede m₂ s₂).2
    · exact absurd (by rw [hid, k₂]) (mem_supersede m₁ s₁).2
    · exact h e₁ (mem_supersede m₁ s₁).1 e₂ (mem_supersede m₂ s₂).1 hid s₁ s₂

/-- An accepted line keeps at most one version of each ID OFFERED. -/
theorem step_oneOffered {n : Nat} {V V' : Catalogue} {ln : Line} (hs : step n V ln = .ok V')
    (h : V.oneOffered) : V'.oneOffered := by
  unfold step at hs
  split at hs
  · cases hs
  · rename_i hr
    cases hs
    exact effect_oneOffered hr h

/-- Lines read one after another keep at most one version of each ID OFFERED. -/
theorem stateFrom_oneOffered : ∀ (ls : List Value) {n : Nat} {V W : Catalogue} {p : Option String}
    {offs : List (List (String × String × String))},
    stateFrom n V p ls = .ok (W, offs) → V.oneOffered → W.oneOffered
  | [], _, _, _, _, _, hs, h => by
    simp only [stateFrom, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
    rw [← hs.1]; exact h
  | lv :: rest, n, V, W, p, offs, hs, h => by
    simp only [stateFrom, bind, Except.bind] at hs
    cases hl : readLine n lv p with
    | error e => simp [hl] at hs
    | ok ln =>
      simp only [hl] at hs
      cases hst : step n V ln with
      | error m => simp [hst, refuse, throw, throwThe, MonadExceptOf.throw] at hs
      | ok V' =>
        simp only [hst] at hs
        cases hr : stateFrom (n + 1) V' (some ln.date) rest with
        | error e => simp [hr] at hs
        | ok res =>
          obtain ⟨W', offs'⟩ := res
          simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
          rw [← hs.1]
          exact stateFrom_oneOffered rest hr (step_oneOffered hst h)

/-- After any lines the Calculator accepts, no two versions of one ID are both OFFERED. -/
theorem readState_oneOffered {lines : Value} {S : State} (h : readState lines = .ok S) :
    S.versions.oneOffered := by
  unfold readState at h
  split at h
  · rename_i ls
    simp only [bind, Except.bind] at h
    cases hr : stateFrom 1 [] none ls with
    | error e => simp [hr] at h
    | ok res =>
      obtain ⟨W, offs⟩ := res
      simp only [hr, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      exact stateFrom_oneOffered ls hr (by intro e₁ h₁; simp at h₁)
  · simp [refuse, throw, throwThe, MonadExceptOf.throw] at h

/-! ### WITHDRAWN is final -/

/-- A WITHDRAWN version keeps its record through an accepted act. -/
theorem effect_withdrawn {n : Nat} {V : Catalogue} {ln : Line} {k : String × String} {r : Declared}
    (hr : refusal n V ln = none) (hk : V.find? k = some r) (hw : r.status = .withdrawn) :
    (effect V ln).find? k = some r := by
  have unchanged : ∀ (W : Catalogue) (key : String × String) (g : Declared → Declared),
      W.find? k = some r → k ≠ key → (W.setAt key g).find? k = some r := by
    intro W key g hW hne
    rw [Catalogue.find?_setAt, hW]
    simp [hne]
  have sup : (supersede V ln.id ln.date).find? k = some r := by
    rw [supersede, Catalogue.find?_restate, hk]
    simp [hw]
  cases hact : ln.act with
  | add | version =>
    simp only [effect, hact]
    exact Catalogue.find?_append sup
  | retire | withdraw | reinstate =>
    obtain ⟨r₀, h₀, hnw, hret, _⟩ := refusal_declared hr (by simp [hact])
    have hne : k ≠ (ln.id, ln.version) := by
      intro he; rw [he, h₀] at hk; cases hk; exact hnw hw
    simp only [effect, hact]
    first
    | exact unchanged V _ _ hk hne
    | exact unchanged _ _ _ sup hne
    | (cases hp : ln.replacedBy with
        | none => exact unchanged V _ _ hk hne
        | some rep =>
          obtain ⟨_, ⟨rr, hrr, hst⟩⟩ := refusal_withdraw_some hr hact hp
          have hne' : k ≠ (ln.id, rep) := by
            intro he; rw [he, hrr] at hk; cases hk; rcases hst with h' | h' <;> simp [h'] at hw
          exact unchanged _ _ _ (unchanged V _ _ hk hne) hne')

/-- A WITHDRAWN version keeps its record through any lines read after it: WITHDRAWN is final
(TPS 5.22.10). -/
theorem stateFrom_withdrawn : ∀ (ls : List Value) {n : Nat} {V W : Catalogue} {p : Option String}
    {offs : List (List (String × String × String))} {k : String × String} {r : Declared},
    stateFrom n V p ls = .ok (W, offs) → V.find? k = some r → r.status = .withdrawn → W.find? k = some r
  | [], _, _, _, _, _, _, _, hs, hk, _ => by
    simp only [stateFrom, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
    rw [← hs.1]; exact hk
  | lv :: rest, n, V, W, p, offs, k, r, hs, hk, hw => by
    simp only [stateFrom, bind, Except.bind] at hs
    cases hl : readLine n lv p with
    | error e => simp [hl] at hs
    | ok ln =>
      simp only [hl] at hs
      cases hst : step n V ln with
      | error m => simp [hst, refuse, throw, throwThe, MonadExceptOf.throw] at hs
      | ok V' =>
        simp only [hst] at hs
        cases hr : stateFrom (n + 1) V' (some ln.date) rest with
        | error e => simp [hr] at hs
        | ok res =>
          obtain ⟨W', offs'⟩ := res
          simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
          rw [← hs.1]
          have hV' : V'.find? k = some r := by
            unfold step at hst
            split at hst
            · cases hst
            · rename_i hn; cases hst; exact effect_withdrawn hn hk hw
          exact stateFrom_withdrawn rest hr hV' hw

end Principia.Provision
