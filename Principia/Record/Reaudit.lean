import Principia.Record.Register
import Principia.Record.Measured
import Principia.ResearchAssembly
import Principia.Eom
import Principia.Strike.Conditions
import Principia.Zone.Preimage

/-!
# The successor's re-audit in one call

`reauditBatch`, the Calculator's half of the successor's re-audit (version 1 TPS 4.1.9,
3.4.7, 5.3.49; the re-audit strikes nothing). It takes what Custos holds, the predecessor's
and the successor's Research Assemblies whole (`{"TPK", "TrM", "TMS"}`) and their registers
whole, and answers what Custos writes: the successor's register after the re-audit. It is
composed of the register functions that exist, in this order:

1. Each Research Assembly as `reaudit_scope` reads it, `{"D_TPK", "D_TRM", "TMS"}`
   (`assemblyZones`: the zone digests `digest_starting_set` and
   `digest_correspondence_table` form, and the assembly's Criteria Set); then
   `reauditScope src dst`: the checks the changed zones and parameters require. An
   assembly whose zones do not read is handed to the scope as it was given less any
   `D_TPK` or `D_TRM` member of its own (`scopeForm`), and the scope's refusal is the
   answer: a zone digest the scope compares is always one the batch formed, never the
   caller's.
2. Each register read (`readRegister`), the successor's then the predecessor's, and its
   status words as `status_words` forms them (`Register.words`): a register that does not
   read is refused before any record is re-checked or any DOF of an assembly read.
3. When the scope names any check: `recordCheckM` at the stage `LANDED` against the
   successor's assembly and, for a RESULT or an ASSUMPTION, `recordFormCheck`, over every
   inherited record of the successor (a keyed record carrying `INHERITS`, of a class that
   carries a STATUS) whose status word is neither REFUTED nor WITHDRAWN: those stay as the
   copy set them (4.1.9).
4. A record either check refuses has its STATUS set by `statusNextOf` on the event `HOLD`
   (nothing is struck by the re-audit), and its status word with it. A failed record whose
   STATUS `HOLD` does not apply to (a STATUS its class does not carry) is refused as
   `status_next` refuses it, REC-54: it is never left out of the changes while its gap opens.
5. When a record failed, the gap records `gapRecords prefix ic2 under trigger landed tps`
   are opened; they are the successor's open audits. `ic2` and `under` are read from the
   successor's assembly as version 1's gate read them for the instantiation certificate:
   `ic2` the DOFs the final checks (`ResearchAssembly.finalChecks`) leave untied, the
   assembly passing them (PASS or GAP); `under` the unknowns the equations-of-motion
   analysis (`Eom.analyse`, the analysis `eom_map` and `eom_findings` report) finds
   determined by no form, none when the Criteria Set's STRUCTURE_CHECK is OFF. A gap ID
   already an ID of the successor's register (a keyed record's `ID` or a positional record's
   first item) is refused, REC-57: `gap_records` numbers from 2 under the prefix it is given.
6. `repromoteBatch` over the successor's words as step 4 left them, with those open audits.
7. `promotionRecord` over what it promoted, when it promoted anything. A PROMOTION ID
   already an ID of the successor's register or a gap ID is refused, REC-57: REGISTER would
   hold two records of one ID.
8. The successor's register after the re-audit (`registerOf`): its records as given, in
   their order, each record step 4 held replaced by itself with STATUS set and DIGEST formed
   again by `recordDigestM`, the definition `record_digest` answers; then the gap records;
   then the PROMOTION record, when there is one.

The answer is `["OK", {"CHECKS", "STATUS", "GAPS", "PROMOTED", "PROMOTION", "REGISTER"}]`:
the scope's checks, the `[id, STATUS]` pairs step 4 set, the gap records, the promoted
triples, the PROMOTION record (`null` when nothing was promoted) and the register of step 8,
which Custos writes whole. A refusal of any step is the batch's answer, unchanged: nothing
of the batch is written.

Not composed here: the strike family's per-check functions (`sr6_independence_count`,
`sr8_scale_factor`), whose inputs are not fields of a record; the scope's list names them
for the job to read.
-/

namespace Principia.Record

open Principia.Canonical (Value)
open Principia.Record.Table

/-- The STATUS a failed re-check gives a record: `status_next` on `HOLD`, from its STATUS
(`UNMARKED` when absent). -/
def heldStatusOf (r : Value) : Option String :=
  match V.getStr? r "CLASS" with
  | some c => statusNextOf c ((V.getStr? r "STATUS").getD "UNMARKED") "HOLD"
  | none => none

/-- The `[id, STATUS]` pairs a list of failed records is given, in the list's order. -/
def heldChanges (reg : Register) (failed : List String) : List (String × String) :=
  failed.filterMap fun rid => (reg.get? rid).bind fun r => (heldStatusOf r).map (rid, ·)

/-- A words map with the changes applied, in order. -/
def applyWords (ws changes : List (String × String)) : List (String × String) :=
  changes.foldl (fun w p => setWord w p.1 p.2) ws

/-- A words map as the value `repromoteBatch` reads. -/
def wordsValue (ws : List (String × String)) : Value :=
  .obj (ws.map fun (k, w) => (k, .str w))

/-- A register function's answer `["OK", ...]`. -/
def isOk : Value → Bool
  | .arr (.str "OK" :: _) => true
  | _ => false

/-- A record the re-audit re-checks: inherited, of a class that carries a STATUS, its word
neither REFUTED nor WITHDRAWN. -/
def recheckable (ws : List (String × String)) (reg : Register) (rid : String) (r : Value) : Bool :=
  (V.getStr? r "INHERITS").isSome &&
    !(statusesOf ((V.getStr? r "CLASS").getD "")).isEmpty &&
    let w := (ws.lookup rid).getD (reg.word rid)
    !(w == "REFUTED" || w == "WITHDRAWN")

/-- Whether a record fails its re-check: the record check at `LANDED`, then, for a RESULT or
an ASSUMPTION, the declared form's check. -/
def recheckFails (r tfk setting : Value) : M Bool := do
  let c ← recordCheckM r tfk setting (.str "LANDED")
  unless c.problems.isEmpty do return true
  let cls := V.getStr? r "CLASS"
  if cls == some "RESULT" || cls == some "ASSUMPTION" then
    return !isOk (← recordFormCheck r tfk)
  return false

/-! ## What the batch forms from the assemblies -/

/-- A Research Assembly as `reaudit_scope` reads it: `{"D_TPK", "D_TRM", "TMS"}`, the zone
digests as `digest_starting_set` and `digest_correspondence_table` form them; none when the
assembly is not an object holding the three zones or a zone digest is not formed. -/
def assemblyZones (tfk : Value) : Option Value :=
  match V.get? tfk "TPK", V.get? tfk "TrM", V.get? tfk "TMS" with
  | some tpk, some trm, some tms =>
    match Zone.dTpk (Strike.toZoneValue tpk), Zone.dTrm (Strike.toZoneValue trm) with
    | .ok dp, .ok dr => some (.obj [("D_TPK", .str dp), ("D_TRM", .str dr), ("TMS", tms)])
    | _, _ => none
  | _, _, _ => none

/-- An assembly as the batch hands it to `reaudit_scope`: `assemblyZones`' form; or, when
the zones do not read, the value given less any `D_TPK` and `D_TRM` member of its own, which
the scope refuses (it reads only an object holding `D_TPK`, `D_TRM` and `TMS`). A digest the
caller wrote is never compared as a zone's. -/
def scopeForm (tfk : Value) : Value :=
  (assemblyZones tfk).getD (V.erase (V.erase tfk "D_TPK") "D_TRM")

/-- A member absent from a value is absent once any member is erased. -/
theorem get?_erase_of_none {v : Value} {k j : String} (h : V.get? v j = none) :
    V.get? (V.erase v k) j = none := by
  cases v with
  | obj ms =>
    simp only [V.erase, V.get?] at h ⊢
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      by_cases hj : j = m.1
      · subst hj; simp at h
      · have hj' : (j == m.1) = false := beq_false_of_ne hj
        simp only [List.lookup, hj'] at h
        by_cases hk : (m.1 != k) = true
        · simp only [List.filter_cons, hk, ↓reduceIte, List.lookup, hj']
          exact ih h
        · simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
          exact ih h
  | _ => simp_all [V.erase]

/-- What `assemblyZones` forms: the three zones are the assembly's members, `D_TPK` and
`D_TRM` the digests `Zone.dTpk` and `Zone.dTrm` form of its Starting Set and Correspondence
Table, `TMS` its Criteria Set. -/
theorem assemblyZones_some {tfk z : Value} (h : assemblyZones tfk = some z) :
    ∃ tpk trm tms dp dr, V.get? tfk "TPK" = some tpk ∧ V.get? tfk "TrM" = some trm ∧
      V.get? tfk "TMS" = some tms ∧ Zone.dTpk (Strike.toZoneValue tpk) = .ok dp ∧
      Zone.dTrm (Strike.toZoneValue trm) = .ok dr ∧
      z = .obj [("D_TPK", .str dp), ("D_TRM", .str dr), ("TMS", tms)] := by
  unfold assemblyZones at h
  split at h
  · rename_i tpk trm tms h1 h2 h3
    split at h
    · rename_i dp dr hp hr
      exact ⟨tpk, trm, tms, dp, dr, h1, h2, h3, hp, hr, (Option.some.inj h).symm⟩
    · simp at h
  · simp at h

/-- **The scope compares only the batch's digests.** Where the value `scopeForm` hands the
scope holds a `D_TPK` member (and `reaudit_scope` reads no other), it is `assemblyZones`'
form: its digests are formed from the assembly's zones, never written by the caller. -/
theorem scopeForm_dTpk {tfk x : Value} (h : V.get? (scopeForm tfk) "D_TPK" = some x) :
    assemblyZones tfk = some (scopeForm tfk) := by
  unfold scopeForm at h ⊢
  cases ha : assemblyZones tfk with
  | some z => rfl
  | none =>
    rw [ha] at h
    have h1 : V.get? (V.erase tfk "D_TPK") "D_TPK" = none := by
      cases tfk with
      | obj ms => exact V.get?_erase_self ms "D_TPK"
      | _ => rfl
    simp only [Option.getD_none, get?_erase_of_none h1] at h
    exact absurd h (by simp)

/-- Where `scopeForm` has no assembly form, the scope refuses the value it is handed: it
holds no `D_TPK` member. -/
theorem scopeForm_none {tfk : Value} (h : assemblyZones tfk = none) :
    V.has (scopeForm tfk) "D_TPK" = false := by
  cases hx : V.get? (scopeForm tfk) "D_TPK" with
  | none => simp [V.has, hx]
  | some x => rw [scopeForm_dTpk hx] at h; simp at h

/-- The DOF an IC2 gap of the final checks names: `IC2: DOF <d> is untied`. -/
def ic2Dof (g : String) : Option String :=
  let pre := "IC2: DOF "
  let post := " is untied"
  if g.startsWith pre && g.endsWith post then
    some (String.ofList ((g.toList.drop pre.length).take (g.length - pre.length - post.length)))
  else none

/-- The successor's IC2 DOFs: those the final checks leave untied, when the assembly passes
them (PASS, or GAP under IC2_POLICY GAP); refused REC-39 otherwise. -/
def ic2Of (tfk : Value) : M (Except Value (List String)) :=
  match ResearchAssembly.finalChecks (Strike.toZoneValue tfk) with
  | .error o => throw (.number s!"the final checks owe their verdict: {o.message}")
  | .ok r =>
    match r.verdict with
    | .pass | .gap => pure (.ok (r.gaps.filterMap ic2Dof))
    | _ => pure (.error (one "REC-39" "-" "the TFK does not pass its final checks"))

/-- Whether the Criteria Set's STRUCTURE_CHECK is OFF (absent: ON). -/
def structureOff (tfk : Value) : Bool :=
  V.getStr? (getOr (getOr tfk "TMS") "PARAMETERS") "STRUCTURE_CHECK" == some "OFF"

/-- The successor's UNDER DOFs: the unknowns the equations-of-motion analysis finds
determined by no form; none when STRUCTURE_CHECK is OFF; refused REC-39 when the TFK's
equations of motion do not read (`Eom.readTfk` refuses them, or `Eom.analyse` gives no
analysis). The batch calls it only after `ic2Of` has passed the final checks; no assembly
found passes them and has equations of motion that do not read (each probed is refused by
the final checks first, RX24), so both refusals are reached only by `underOf` called alone
(RU01; none reaches `analyse`'s), and either answers a refusal, never a gap left out
(`underOf_analyse_none`, `underOf_under`). The `.owed` arm is never taken: `readTfk`
through the Calculator's parser never owes (`readTfk_ne_owed`, `underOf_ok`). -/
def underOf (tfk : Value) : M (Except Value (List String)) :=
  if structureOff tfk then pure (.ok []) else
  match Eom.readTfk Eom.FormHook.calculator (Strike.toZoneValue tfk) with
  | .error (.owed why) => throw (.number s!"the equations of motion owe their reading: {why}")
  | .error (.refused _) =>
    pure (.error (one "REC-39" "-" "the TFK's equations of motion do not read"))
  | .ok K =>
    match Eom.analyse K K.laws with
    | some (_, _, _, u) => pure (.ok u)
    | none => pure (.error (one "REC-39" "-" "the TFK's equations of motion do not read"))

/-! ## The register after the re-audit -/

/-- A held record: STATUS set to `s`, then DIGEST formed again over it by `recordDigestM`,
the definition `record_digest` answers; its refusal otherwise. -/
def heldRecord (r : Value) (s : String) : M (Except Value Value) := do
  let r1 := V.set r "STATUS" (.str s)
  match ← recordDigestM r1 with
  | .arr [.str "OK", d] => return .ok (V.set r1 "DIGEST" d)
  | other => return .error other

/-- Each change's held record, by ID, in the changes' order. -/
def heldRecords (reg : Register) : List (String × String) → M (Except Value (List (String × Value)))
  | [] => pure (.ok [])
  | (rid, s) :: cs => do
    match reg.get? rid with
    | none => heldRecords reg cs
    | some r =>
      match ← heldRecord r s with
      | .error b => return .error b
      | .ok r' =>
        match ← heldRecords reg cs with
        | .error b => return .error b
        | .ok hs => return .ok ((rid, r') :: hs)

/-- A record of the register, replaced by its held record when it has one. -/
def replaceHeld (hs : List (String × Value)) (r : Value) : Value :=
  match V.getStr? r "ID" with
  | some i => (hs.lookup i).getD r
  | none => r

/-- The PROMOTION record as a list: none when it is `null`. -/
def promotionList : Value → List Value
  | .null => []
  | p => [p]

/-- The successor's register after the re-audit: its records with the held ones replaced,
then the gap records, then the PROMOTION record. -/
def registerAfter (rs : List Value) (hs : List (String × Value)) (gaps : List Value)
    (promotion : Value) : List Value :=
  rs.map (replaceHeld hs) ++ gaps ++ promotionList promotion

/-- The register after the re-audit, or the refusal of a held record's digest. -/
def registerOf (reg : Register) (rs : List Value) (changes : List (String × String))
    (gaps : List Value) (promotion : Value) : M (Except Value (List Value)) := do
  match ← heldRecords reg changes with
  | .error b => return .error b
  | .ok hs => return .ok (registerAfter rs hs gaps promotion)

/-- The records of a register as given: its items. -/
def recordsOf : Value → List Value
  | .arr rs => rs
  | _ => []

/-! ## The IDs REGISTER holds -/

/-- The ID of a register member: a positional record's first item, a keyed record's `ID`. -/
def memberId : Value → Option String
  | .arr (.str i :: _) => some i
  | r => V.getStr? r "ID"

/-- The IDs of a list of register members, in order. -/
def memberIds (rs : List Value) : List String := rs.filterMap memberId

/-- The first of `xs` that is one of `ids`: an ID REGISTER would hold twice. -/
def clashOf (xs ids : List String) : Option String := xs.find? (ids.contains ·)

/-- `clashOf` finds nothing: no member of `xs` is one of `ids`. -/
theorem clashOf_none {xs ids : List String} (h : clashOf xs ids = none) : ∀ i ∈ xs, i ∉ ids := by
  intro i hi hm
  have := List.find?_eq_none.1 h i hi
  simp_all

/-! ## The changes the re-check makes -/

/-- The `[id, STATUS]` change of each failed ID, in order: `status_next` on `HOLD` over the
register's record of the ID. The record of the first failed ID that `HOLD` does not apply to
otherwise (`null` for an ID the register does not hold): the batch refuses it as
`status_next` refuses it, so no failed record is left out of the changes. -/
def holdChanges (reg : Register) : List String → Except Value (List (String × String))
  | [] => .ok []
  | rid :: fs =>
    match reg.get? rid with
    | none => .error .null
    | some r =>
      match heldStatusOf r with
      | none => .error r
      | some s => (holdChanges reg fs).map ((rid, s) :: ·)

/-! ## The batch -/

/-- What the batch's steps 1 to 7 give step 8, with what they establish: the successor's
register is `readRegister`'s over `dstRecords`; every failed ID has its change; no gap ID and
no PROMOTION ID is already an ID of the successor's register, nor the PROMOTION ID a gap ID. -/
structure ReauditSteps (dstRecords : Value) where
  checks : List Value
  reg : Register
  failed : List String
  changes : List (String × String)
  gaps : List Value
  promoted : List Value
  promotion : Value
  read : readRegister dstRecords "dst_records" = .ok (.ok reg)
  held : holdChanges reg failed = .ok changes
  gapsFresh : clashOf (memberIds gaps) (memberIds (recordsOf dstRecords)) = none
  promotionFresh :
    clashOf (memberIds (promotionList promotion)) (memberIds (recordsOf dstRecords ++ gaps)) = none

/-- Steps 5 to 7 of `reaudit_batch`, from the two registers read and the changes. -/
def reauditTail (srcRecords dstRecords dstTfk promotionId landingBlock pre trigger landed tps
    : Value) (checks : List Value) (srcReg reg : Register)
    (hr : readRegister dstRecords "dst_records" = .ok (.ok reg)) (failed : List String)
    (changes : List (String × String)) (hh : holdChanges reg failed = .ok changes) :
    M (Except Value (ReauditSteps dstRecords)) := do
  let mut gaps : List Value := []
  unless failed.isEmpty do
    let ic2 ← match ← ic2Of dstTfk with
      | .error b => return .error b
      | .ok l => pure l
    let under ← match ← underOf dstTfk with
      | .error b => return .error b
      | .ok l => pure l
    match ← gapRecords pre (V.strs ic2) (V.strs under) trigger landed tps with
    | .arr [.str "OK", .arr gs] => gaps := gs
    | other => return .error other
  let gapIds := gaps.filterMap (V.getStr? · "ID")
  match hg : clashOf (memberIds gaps) (memberIds (recordsOf dstRecords)) with
  | some g =>
    return .error (one "REC-57" "prefix" s!"gap ID {← showSlot g} is already in the register")
  | none =>
  let audits := V.strs gapIds
  let promoted ← match ← repromoteBatch srcRecords (wordsValue srcReg.words) dstRecords
      (wordsValue (applyWords reg.words changes)) dstTfk audits with
    | .arr [.str "OK", .arr ps] => pure ps
    | other => return .error other
  let promotion ← if promoted.isEmpty then pure Value.null else
    match ← promotionRecord promotionId landingBlock (.arr promoted) with
    | .arr [.str "OK", p] => pure p
    | other => return .error other
  match hp : clashOf (memberIds (promotionList promotion))
      (memberIds (recordsOf dstRecords ++ gaps)) with
  | some i =>
    return .error (one "REC-57" "promotion_id"
      s!"PROMOTION ID {← showSlot i} is already in the register")
  | none =>
  return .ok (ReauditSteps.mk checks reg failed changes gaps promoted promotion hr hh hg hp)

/-- Steps 1 to 7 of `reaudit_batch`, or the refusal of the first step that refuses. -/
def reauditSteps (srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
    trigger landed tps : Value) : M (Except Value (ReauditSteps dstRecords)) := do
  let src := scopeForm srcTfk
  let dst := scopeForm dstTfk
  let checks ← match ← reauditScope src dst with
    | .arr [.str "OK", .arr cs] => pure cs
    | other => return .error other
  match hr : readRegister dstRecords "dst_records" with
  | .error e => throw e
  | .ok (.error b) => return .error b
  | .ok (.ok reg) =>
  let srcReg ← match ← readRegister srcRecords "src_records" with
    | .error b => return .error b
    | .ok r => pure r
  let ws := reg.words
  unless dstTfk != .null && assemblyOk dstTfk do
    return .error (one "REC-39" "-" "the TFK is not readable")
  let mut failed : List String := []
  unless checks.isEmpty do
    for (rid, r) in reg.keyed do
      if recheckable ws reg rid r then
        if ← recheckFails r dstTfk setting then failed := failed ++ [rid]
  match hh : holdChanges reg (sortStrings failed) with
  | .error r =>
    return .error (← statusNext (getOr r "CLASS")
      ((V.get? r "STATUS").getD (.str "UNMARKED")) (.str "HOLD"))
  | .ok changes =>
    reauditTail srcRecords dstRecords dstTfk promotionId landingBlock pre trigger landed tps
      checks srcReg reg hr (sortStrings failed) changes hh

/-- The batch's answer from its steps and the register of step 8. -/
def reauditAnswer {d : Value} (st : ReauditSteps d) (xs : List Value) : Value :=
  okWith [.obj [("CHECKS", .arr st.checks),
    ("STATUS", .arr (st.changes.map fun (i, s) => V.strs [i, s])), ("GAPS", .arr st.gaps),
    ("PROMOTED", .arr st.promoted), ("PROMOTION", st.promotion), ("REGISTER", .arr xs)]]

/-- `reaudit_batch`: the successor's re-audit in one call. -/
def reauditBatch (srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
    trigger landed tps : Value) : M Value := do
  match ← reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock
      pre trigger landed tps with
  | .error b => return b
  | .ok st =>
    match ← registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion with
    | .error b => return b
    | .ok xs => return reauditAnswer st xs

/-! ## A record's status word changes only by `status_next` -/

/-- Every STATUS the re-audit sets is `status_next` of the record's class and STATUS on
`HOLD`. -/
theorem heldChanges_statusNext {reg : Register} {failed : List String} {p : String × String}
    (h : p ∈ heldChanges reg failed) :
    ∃ r c, reg.get? p.1 = some r ∧ V.getStr? r "CLASS" = some c ∧
      statusNextOf c ((V.getStr? r "STATUS").getD "UNMARKED") "HOLD" = some p.2 := by
  unfold heldChanges at h
  obtain ⟨rid, _, hb⟩ := List.mem_filterMap.mp h
  cases hr : reg.get? rid with
  | none => simp [hr] at hb
  | some r =>
    simp only [hr, Option.bind_some] at hb
    cases hs : heldStatusOf r with
    | none => simp [hs] at hb
    | some s =>
      simp only [hs, Option.map_some, Option.some.injEq] at hb
      subst hb
      unfold heldStatusOf at hs
      split at hs
      · rename_i c hc
        exact ⟨r, c, hr, hc, hs⟩
      · simp at hs

/-- `HOLD` never strikes: it gives HELD, or keeps REFUTED. -/
theorem statusNextOf_hold {c s o : String} (h : statusNextOf c s "HOLD" = some o) :
    o = "HELD" ∨ (s = "REFUTED" ∧ o = "REFUTED") := by
  unfold statusNextOf at h
  split at h
  · simp at h
  · split at h
    · split at h
      · rename_i hs
        exact .inr ⟨by simpa using hs, (Option.some.inj h).symm⟩
      · exact .inl (Option.some.inj h).symm
    · rename_i hc
      simp at hc

/-- Setting a word leaves every other word, and writes only the word given. -/
theorem mem_setWord {ws : List (String × String)} {k w : String} {q : String × String}
    (h : q ∈ setWord ws k w) : q ∈ ws ∨ q = (k, w) := by
  unfold setWord at h
  split at h
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    split at he
    · exact .inr he.symm
    · exact .inl (he ▸ hp)
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · exact .inr (List.mem_singleton.mp h)

/-- The words the re-promotion reads are the successor's words or the changes the re-check
made: a record's status word changes only by `status_next`. -/
theorem mem_applyWords {ws changes : List (String × String)} {q : String × String}
    (h : q ∈ applyWords ws changes) : q ∈ ws ∨ q ∈ changes := by
  unfold applyWords at h
  induction changes generalizing ws with
  | nil => exact .inl h
  | cons p ps ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with h | h
    · rcases mem_setWord h with h | h
      · exact .inl h
      · exact .inr (h ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

/-! ## The register after the re-audit, proved

A held record's DIGEST is the one `record_digest` forms over the record as it stands; a
record the batch did not hold is in REGISTER as it was given; REGISTER holds the successor's
records, then the gap records, then the PROMOTION record when there is one. -/

/-- Members without the key `k`: a list with no member `k` is itself. -/
theorem filter_key_of_lookup_none {k : String} :
    ∀ {ms : List (String × Value)}, ms.lookup k = none → ms.filter (·.1 != k) = ms
  | [], _ => rfl
  | (a, b) :: t, h => by
    have hl : List.lookup k ((a, b) :: t) =
        (match k == a with | true => some b | false => List.lookup k t) := rfl
    by_cases hk : k = a
    · subst hk; simp [hl] at h
    · have hb : (k == a) = false := by simpa using hk
      rw [hl, hb] at h
      have ha : (a != k) = true := by simpa [bne_iff_ne] using Ne.symm hk
      simp [List.filter, ha, filter_key_of_lookup_none h]

/-- Members without the key `k`, after the member `k` is set: as before. -/
theorem filter_key_map_set (k : String) (x : Value) :
    ∀ ms : List (String × Value),
      (ms.map fun m => if m.1 == k then (k, x) else m).filter (·.1 != k) = ms.filter (·.1 != k)
  | [] => rfl
  | (a, b) :: t => by
    by_cases h : a = k
    · subst h
      simp only [List.map_cons, beq_self_eq_true, ite_true, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ite_false]
      exact filter_key_map_set a x t
    · have ha : (a != k) = true := by simpa [bne_iff_ne] using h
      have hb : (a == k) = false := by simpa using h
      simp only [List.map_cons, hb, List.filter_cons, ha, ite_true, Bool.false_eq_true, ite_false,
        filter_key_map_set k x t]

/-- Erasing a member after setting it is erasing it. -/
theorem erase_set (r : Value) (k : String) (x : Value) :
    V.erase (V.set r k x) k = V.erase r k := by
  cases r with
  | obj ms =>
    simp only [V.set]
    split
    · simp only [V.erase, Value.obj.injEq]
      exact filter_key_map_set k x ms
    · simp [V.erase, List.filter_append]
  | _ => rfl

/-- The preimage's first step, a record without its DIGEST, is erasing it. -/
theorem withoutDigest (r : Value) :
    (if V.has r "DIGEST" then V.erase r "DIGEST" else r) = V.erase r "DIGEST" := by
  split
  · rfl
  · rename_i h
    cases r with
    | obj ms =>
      simp only [V.has, V.get?, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h
      simp [V.erase, filter_key_of_lookup_none h]
    | _ => rfl

/-- **Setting a DIGEST changes no digest**: `record_digest` forms the same digest over a
record whatever its DIGEST holds. -/
theorem recordDigestM_set_digest (r d : Value) :
    recordDigestM (V.set r "DIGEST" d) = recordDigestM r := by
  simp only [recordDigestM, recordPreimageM, withoutDigest]
  simp only [erase_set]

/-- **A held record carries the DIGEST `record_digest` forms over it**: the record with its
STATUS set and its DIGEST formed again, whose digest is that DIGEST. -/
theorem heldRecord_digest {r : Value} {s : String} {r' : Value}
    (h : heldRecord r s = .ok (.ok r')) :
    ∃ d, r' = V.set (V.set r "STATUS" (.str s)) "DIGEST" d ∧
      recordDigestM r' = .ok (okWith [d]) := by
  unfold heldRecord at h
  cases hd : recordDigestM (V.set r "STATUS" (.str s)) with
  | error e => simp [hd, bind, Except.bind] at h
  | ok v =>
    simp only [hd, bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i d
      have he : V.set (V.set r "STATUS" (.str s)) "DIGEST" d = r' := by
        simpa using h
      subst he
      exact ⟨d, rfl, by rw [recordDigestM_set_digest, hd]; rfl⟩
    · simp at h

/-- A pair a list's lookup gives is a member of the list. -/
theorem mem_of_lookup {k : String} {v : Value} :
    ∀ {l : List (String × Value)}, l.lookup k = some v → (k, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: t, h => by
    have hl : List.lookup k ((a, b) :: t) =
        (match k == a with | true => some b | false => List.lookup k t) := rfl
    by_cases hk : k = a
    · subst hk
      have hb : b = v := by simpa [hl] using h
      subst hb
      exact List.mem_cons_self
    · have hb : (k == a) = false := by simpa using hk
      rw [hl, hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- Each held record is a change's: its ID is a change's, the record is the register's and
the held record is `heldRecord`'s. -/
theorem heldRecords_mem {reg : Register} :
    ∀ {cs : List (String × String)} {hs : List (String × Value)},
      heldRecords reg cs = .ok (.ok hs) → ∀ p ∈ hs,
        ∃ s r, (p.1, s) ∈ cs ∧ reg.get? p.1 = some r ∧ heldRecord r s = .ok (.ok p.2)
  | [], hs, h, p, hp => by
    simp only [heldRecords, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hp
  | (rid, s) :: cs, hs, h, p, hp => by
    simp only [heldRecords] at h
    cases hg : reg.get? rid with
    | none =>
      rw [hg] at h
      obtain ⟨s', r, hm, hr, hh⟩ := heldRecords_mem h p hp
      exact ⟨s', r, List.mem_cons_of_mem _ hm, hr, hh⟩
    | some r =>
      rw [hg] at h
      simp only [bind, Except.bind] at h
      cases hr : heldRecord r s with
      | error e => rw [hr] at h; cases h
      | ok y =>
        rw [hr] at h
        cases y with
        | error b => simp [pure, Except.pure] at h
        | ok r' =>
          simp only at h
          cases ht : heldRecords reg cs with
          | error e => rw [ht] at h; cases h
          | ok z =>
            rw [ht] at h
            cases z with
            | error b => simp [pure, Except.pure] at h
            | ok hs' =>
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              rcases List.mem_cons.mp hp with he | hm
              · subst he
                exact ⟨s, r, List.mem_cons_self, hg, hr⟩
              · obtain ⟨s', r'', hm', hr', hh'⟩ := heldRecords_mem ht p hm
                exact ⟨s', r'', List.mem_cons_of_mem _ hm', hr', hh'⟩

/-- REGISTER as `registerOf` forms it: `registerAfter` over the held records. -/
theorem registerOf_ok {reg : Register} {rs : List Value} {cs : List (String × String)}
    {gaps : List Value} {p : Value} {xs : List Value}
    (h : registerOf reg rs cs gaps p = .ok (.ok xs)) :
    ∃ hs, heldRecords reg cs = .ok (.ok hs) ∧ xs = registerAfter rs hs gaps p := by
  unfold registerOf at h
  simp only [bind, Except.bind] at h
  cases ht : heldRecords reg cs with
  | error e => rw [ht] at h; cases h
  | ok z =>
    rw [ht] at h
    cases z with
    | error b => simp [pure, Except.pure] at h
    | ok hs =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨hs, rfl, h.symm⟩

/-- At the place of one of the successor's records, REGISTER holds that record, replaced by
its held record when it has one. -/
theorem registerAfter_getElem? {rs : List Value} {hs : List (String × Value)}
    {gaps : List Value} {p : Value} {i : Nat} {y : Value} (hy : rs[i]? = some y) :
    (registerAfter rs hs gaps p)[i]? = some (replaceHeld hs y) := by
  have hi : i < (rs.map (replaceHeld hs)).length := by
    simpa using (List.getElem?_eq_some_iff.mp hy).1
  unfold registerAfter
  rw [List.append_assoc, List.getElem?_append_left hi, List.getElem?_map, hy]
  rfl

/-- **A record the batch changed carries the DIGEST `record_digest` forms over it**: a record
of REGISTER, at the place of one of the successor's records, that is not that record as given
is a change's record of the register with STATUS set and DIGEST formed again, and
`record_digest` forms that DIGEST over it. -/
theorem registerOf_changed {reg : Register} {rs : List Value} {cs : List (String × String)}
    {gaps : List Value} {p : Value} {xs : List Value}
    (h : registerOf reg rs cs gaps p = .ok (.ok xs)) {i : Nat} {x y : Value}
    (hy : rs[i]? = some y) (hx : xs[i]? = some x) (hne : x ≠ y) :
    ∃ rid s r d, V.getStr? y "ID" = some rid ∧ (rid, s) ∈ cs ∧ reg.get? rid = some r ∧
      x = V.set (V.set r "STATUS" (.str s)) "DIGEST" d ∧ recordDigestM x = .ok (okWith [d]) := by
  obtain ⟨hs, hh, rfl⟩ := registerOf_ok h
  have hxi : x = replaceHeld hs y := by
    have := registerAfter_getElem? (hs := hs) (gaps := gaps) (p := p) hy
    rw [hx] at this
    exact Option.some.inj this
  unfold replaceHeld at hxi
  cases hid : V.getStr? y "ID" with
  | none => simp only [hid] at hxi; exact absurd hxi hne
  | some rid =>
    simp only [hid] at hxi
    cases hl : hs.lookup rid with
    | none => simp only [hl, Option.getD_none] at hxi; exact absurd hxi hne
    | some r' =>
      simp only [hl, Option.getD_some] at hxi
      obtain ⟨s, r, hm, hr, hd⟩ := heldRecords_mem hh (rid, r') (mem_of_lookup hl)
      obtain ⟨d, he, hdig⟩ := heldRecord_digest hd
      exact ⟨rid, s, r, d, rfl, hm, hr, hxi.trans he, by rw [hxi]; exact hdig⟩

/-- **A record the batch did not change is in REGISTER as it was given**: one of the
successor's records whose ID no change names is at its place in REGISTER, unchanged. -/
theorem registerOf_unchanged {reg : Register} {rs : List Value} {cs : List (String × String)}
    {gaps : List Value} {p : Value} {xs : List Value}
    (h : registerOf reg rs cs gaps p = .ok (.ok xs)) {i : Nat} {y : Value}
    (hy : rs[i]? = some y) (hn : ∀ rid, V.getStr? y "ID" = some rid → ∀ s, (rid, s) ∉ cs) :
    xs[i]? = some y := by
  obtain ⟨hs, hh, rfl⟩ := registerOf_ok h
  rw [registerAfter_getElem? hy]
  unfold replaceHeld
  cases hid : V.getStr? y "ID" with
  | none => rfl
  | some rid =>
    cases hl : hs.lookup rid with
    | none => simp [hl]
    | some r' =>
      obtain ⟨s, _, hm, _, _⟩ := heldRecords_mem hh (rid, r') (mem_of_lookup hl)
      exact absurd hm (hn rid hid s)

/-- **REGISTER's length**: the successor's records, then the gap records, then one more
when the PROMOTION record is not null. -/
theorem registerOf_length {reg : Register} {rs : List Value} {cs : List (String × String)}
    {gaps : List Value} {p : Value} {xs : List Value}
    (h : registerOf reg rs cs gaps p = .ok (.ok xs)) :
    xs.length = rs.length + gaps.length + (match p with | .null => 0 | _ => 1) := by
  obtain ⟨hs, _, rfl⟩ := registerOf_ok h
  cases p <;> simp [registerAfter, promotionList, Nat.add_assoc]

/-- The batch answers through its steps: the refusal of steps 1 to 7, the refusal of a held
record's digest, or the answer whose REGISTER is `registerOf`'s over the successor's records
as given. -/
theorem reauditBatch_cases {srcTfk dstTfk srcRecords dstRecords setting promotionId
    landingBlock pre trigger landed tps v : Value}
    (h : reauditBatch srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
      trigger landed tps = .ok v) :
    (reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
        trigger landed tps = .ok (.error v)) ∨
    (∃ st, reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock
        pre trigger landed tps = .ok (.ok st) ∧
      registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion = .ok (.error v)) ∨
    (∃ st xs, reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock
        pre trigger landed tps = .ok (.ok st) ∧
      registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion = .ok (.ok xs) ∧
      v = reauditAnswer st xs) := by
  unfold reauditBatch at h
  simp only [bind, Except.bind] at h
  cases hs : reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock
      pre trigger landed tps with
  | error e => rw [hs] at h; cases h
  | ok z =>
    rw [hs] at h
    cases z with
    | error b =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact .inl (by rw [h])
    | ok st =>
      simp only at h
      cases hr : registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion with
      | error e => rw [hr] at h; cases h
      | ok y =>
        rw [hr] at h
        cases y with
        | error b =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          exact .inr (.inl ⟨st, rfl, by rw [hr, h]⟩)
        | ok xs =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          exact .inr (.inr ⟨st, xs, rfl, hr, h.symm⟩)

/-- When steps 1 to 7 answer and every held record's digest is formed, the batch answers
with the register of step 8 as REGISTER. -/
theorem reauditBatch_answer {srcTfk dstTfk srcRecords dstRecords setting promotionId
    landingBlock pre trigger landed tps : Value} {st : ReauditSteps dstRecords} {xs : List Value}
    (hs : reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
      trigger landed tps = .ok (.ok st))
    (hr : registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion =
      .ok (.ok xs)) :
    reauditBatch srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
      trigger landed tps = .ok (reauditAnswer st xs) := by
  simp only [reauditBatch, bind, Except.bind, hs, hr, pure, Except.pure]

/-- The answer's REGISTER is the register of step 8. -/
theorem reauditAnswer_register {d : Value} (st : ReauditSteps d) (xs : List Value) :
    ∃ ms, reauditAnswer st xs = okWith [.obj ms] ∧ ms.lookup "REGISTER" = some (.arr xs) := by
  exact ⟨_, rfl, by simp [List.lookup]⟩

/-! ## No change is dropped

`heldRecords` skips a change whose ID is not in the register, and `heldChanges` one whose
record `HOLD` does not apply to. Neither happens in the batch: every change names a record of
the register it read, which `registerOf` reads again; and the batch's changes are
`holdChanges`', which refuses a failed record whose STATUS `HOLD` does not apply to
(`ReauditSteps.changes_ids`, `ReauditSteps.failed_held` below). -/

/-- Every change names a record of the register. -/
theorem heldChanges_registered {reg : Register} {failed : List String} {p : String × String}
    (h : p ∈ heldChanges reg failed) : (reg.get? p.1).isSome := by
  obtain ⟨r, _, hr, _, _⟩ := heldChanges_statusNext h
  simp [hr]

/-- Every failed record of the register whose STATUS `HOLD` applies to is given its change,
in order: no failed record is dropped. -/
theorem heldChanges_ids {reg : Register} :
    ∀ {failed : List String},
      (∀ rid ∈ failed, ∃ r s, reg.get? rid = some r ∧ heldStatusOf r = some s) →
      (heldChanges reg failed).map Prod.fst = failed
  | [], _ => rfl
  | rid :: fs, h => by
    obtain ⟨r, s, hr, hs⟩ := h rid List.mem_cons_self
    have ih := heldChanges_ids (reg := reg) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold heldChanges at ih ⊢
    simp only [List.filterMap_cons, hr, Option.bind_some, hs, Option.map_some, List.map_cons, ih]

/-- Each change whose ID is in the register gets its held record, in order: `heldRecords`
drops no change. -/
theorem heldRecords_ids {reg : Register} :
    ∀ {cs : List (String × String)} {hs : List (String × Value)},
      (∀ p ∈ cs, (reg.get? p.1).isSome) →
      heldRecords reg cs = .ok (.ok hs) → hs.map Prod.fst = cs.map Prod.fst
  | [], hs, _, h => by
    simp only [heldRecords, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | (rid, s) :: cs, hs, hc, h => by
    simp only [heldRecords] at h
    cases hg : reg.get? rid with
    | none =>
      have := hc (rid, s) List.mem_cons_self
      simp [hg] at this
    | some r =>
      rw [hg] at h
      simp only [bind, Except.bind] at h
      cases hr : heldRecord r s with
      | error e => rw [hr] at h; cases h
      | ok y =>
        rw [hr] at h
        cases y with
        | error b => simp [pure, Except.pure] at h
        | ok r' =>
          simp only at h
          cases ht : heldRecords reg cs with
          | error e => rw [ht] at h; cases h
          | ok z =>
            rw [ht] at h
            cases z with
            | error b => simp [pure, Except.pure] at h
            | ok hs' =>
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp only [List.map_cons]
              rw [heldRecords_ids (fun p hp => hc p (List.mem_cons_of_mem _ hp)) ht]

/-- **The batch's held records are its changes**: over the changes `heldChanges` gives, the
held records `heldRecords` forms are one per change, in order. -/
theorem heldRecords_heldChanges {reg : Register} {failed : List String}
    {hs : List (String × Value)}
    (h : heldRecords reg (heldChanges reg failed) = .ok (.ok hs)) :
    hs.map Prod.fst = (heldChanges reg failed).map Prod.fst :=
  heldRecords_ids (fun _ hp => heldChanges_registered hp) h

/-! ## The equations-of-motion reading never owes

`underOf` throws when `Eom.readTfk` owes a reading. `readTfk` owes only where the
Calculator's parser errs. That parser never errs: the declared forms' grammar never owes a
form, and in equation mode every tree it reads is an equation (`Parser.top` refuses a form
without `=`). So `readTfk` through the Calculator's parser reads or refuses, never owes
(`readTfk_ne_owed`), and `underOf` never throws (`underOf_ok`). -/

/-- The grammar's answer from an `Except` is never owed. -/
theorem ofExcept_ne_owed {α : Type} (e : Except String α) (w : Form.Owed) :
    Form.Answer.ofExcept e ≠ .owed w := by
  cases e <;> simp [Form.Answer.ofExcept]

/-- Escaping a refusal owes nothing new. -/
theorem escaped_ne_owed {α : Type} {a : Form.Answer α} {w : Form.Owed} (h : a ≠ .owed w) :
    a.escaped ≠ .owed w := by
  cases a <;> simp_all [Form.Answer.escaped]

/-- **`form_tree` never owes**: it reads a form or refuses it. -/
theorem formTree_ne_owed (s : String) (m : Form.Mode) (w : Form.Owed) :
    Form.formTree s m ≠ .owed w := by
  unfold Form.formTree
  apply escaped_ne_owed
  simp only [Form.parse]
  cases hb : Form.boundsFault (Form.canonicalText s) with
  | some r => simp
  | none => exact ofExcept_ne_owed _ w

/-- The Calculator's parser errs only where `form_tree` gives no equation in equation mode,
never for an owed form. -/
theorem calculator_equation_error {s e : String}
    (h : Eom.FormHook.calculator.equation s = .error e) :
    e = "internal: form_tree gave no equation in equation mode" := by
  simp only [Eom.FormHook.calculator] at h
  split at h
  · simp at h
  · exact (Except.error.inj h).symm
  · simp at h
  · rename_i heq
    exact absurd heq (formTree_ne_owed _ _ _)

/-- **The grammar reads an equation in equation mode**: a tree `Parser.top` gives there is
`l = r`. -/
theorem top_equation {ts : Array Form.Token} {t : Form.Tree}
    (h : Form.Parser.top ⟨ts, .equation⟩ = .ok t) : ∃ a b, t = .eq a b := by
  unfold Form.Parser.top at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (simp_all; done) | skip
  injection h with h
  exact ⟨_, _, h.symm⟩

/-- A tree `form_tree` reads in equation mode is an equation. -/
theorem formTree_equation {s : String} {t : Form.Tree}
    (h : Form.formTree s .equation = .ok t) : ∃ a b, t = .eq a b := by
  simp only [Form.formTree, Form.parse] at h
  split at h
  · simp [Form.Answer.escaped] at h
  · cases he : (Form.tokens (Form.canonicalText s) >>= fun ts =>
        Form.Parser.top ⟨ts.toArray, .equation⟩ : Except String Form.Tree) with
    | error e => simp [he, Form.Answer.ofExcept, Form.Answer.escaped] at h
    | ok t' =>
      simp only [he, Form.Answer.ofExcept, Form.Answer.escaped, Form.Answer.ok.injEq] at h
      subst h
      simp only [bind, Except.bind] at he
      split at he
      · simp at he
      · exact top_equation he

/-- **The Calculator's parser never errs**: it gives an equation or a refusal. -/
theorem calculator_ne_error (s e : String) : Eom.FormHook.calculator.equation s ≠ .error e := by
  intro h
  simp only [Eom.FormHook.calculator] at h
  split at h
  · simp at h
  · rename_i t heq hne
    obtain ⟨a, b, rfl⟩ := formTree_equation hne
    exact heq a b rfl
  · simp at h
  · rename_i heq
    exact absurd heq (formTree_ne_owed _ _ _)

/-- A reading that never owes: it reads or refuses. A structure, so that the proofs' tactic
loops below do not unfold it. -/
structure ReadNoOwed {α : Type} (x : Eom.Read α) : Prop where
  ne : ∀ w, x ≠ .error (.owed w)

theorem ReadNoOwed.pure' {α : Type} (a : α) : ReadNoOwed (pure a : Eom.Read α) :=
  ⟨fun _ h => by cases h⟩

theorem ReadNoOwed.refuse' {α : Type} (m : String) : ReadNoOwed (Eom.refuse m : Eom.Read α) :=
  ⟨fun _ h => by cases h⟩

theorem ReadNoOwed.bind' {α β : Type} {x : Eom.Read α} {f : α → Eom.Read β}
    (hx : ReadNoOwed x) (hf : ∀ a, ReadNoOwed (f a)) : ReadNoOwed (x >>= f) := by
  refine ⟨fun w h => ?_⟩
  cases hx' : x with
  | error e =>
    rw [hx'] at h
    cases e with
    | refused r => cases h
    | owed w' => exact hx.ne w' hx'
  | ok a => rw [hx'] at h; exact (hf a).ne w h

theorem ReadNoOwed.forIn' {α β : Type} (xs : List α) (b : β)
    (f : α → β → Eom.Read (ForInStep β)) (hf : ∀ a b, ReadNoOwed (f a b)) :
    ReadNoOwed (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact ReadNoOwed.pure' _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply ReadNoOwed.bind' (hf x b)
    intro s
    cases s with
    | done b' => exact ReadNoOwed.pure' _
    | yield b' => exact ih b'

theorem kindEntries_noOwed (t : Zone.Entry) (k : String) :
    ReadNoOwed (Eom.kindEntries t k) := by
  unfold Eom.kindEntries
  repeat' (first | exact ReadNoOwed.pure' _ | exact ReadNoOwed.refuse' _ | split)

theorem fieldStr_noOwed (g : String) (e : Zone.Entry) (f : String) :
    ReadNoOwed (Eom.fieldStr g e f) := by
  unfold Eom.fieldStr
  repeat' (first | exact ReadNoOwed.pure' _ | exact ReadNoOwed.refuse' _ | split)

theorem nameOf_noOwed (g : String) (e : Zone.Entry) : ReadNoOwed (Eom.nameOf g e) := by
  unfold Eom.nameOf
  repeat' (first
    | exact fieldStr_noOwed _ _ _
    | exact ReadNoOwed.pure' _
    | exact ReadNoOwed.refuse' _
    | apply ReadNoOwed.bind'
    | intro _
    | split)

theorem readRole_noOwed (g r : String) (d : List String) : ReadNoOwed (Eom.readRole g r d) := by
  unfold Eom.readRole
  repeat' (first | exact ReadNoOwed.pure' _ | exact ReadNoOwed.refuse' _ | split | dsimp only)

theorem readForm_noOwed (tag : String) (text : Zone.Value) (d : List String) :
    ReadNoOwed (Eom.readForm Eom.FormHook.calculator tag text d) := by
  unfold Eom.readForm
  split
  · split
    · rename_i e he; exact absurd he (calculator_ne_error _ _)
    · exact ReadNoOwed.refuse' _
    · split
      · exact ReadNoOwed.refuse' _
      · exact ReadNoOwed.pure' _
  · exact ReadNoOwed.refuse' _

/-- **`readTfk` never owes** through the Calculator's parser: it reads the TFK's equations
of motion or refuses them. -/
theorem readTfk_ne_owed (tfk : Zone.Value) (w : String) :
    Eom.readTfk Eom.FormHook.calculator tfk ≠ .error (.owed w) := by
  have h : ReadNoOwed (Eom.readTfk Eom.FormHook.calculator tfk) := by
    unfold Eom.readTfk
    repeat' (first
      | exact readForm_noOwed _ _ _
      | exact kindEntries_noOwed _ _
      | exact fieldStr_noOwed _ _ _
      | exact nameOf_noOwed _ _
      | exact readRole_noOwed _ _ _
      | exact ReadNoOwed.pure' _
      | exact ReadNoOwed.refuse' _
      | apply ReadNoOwed.bind'
      | apply ReadNoOwed.forIn'
      | intro _
      | split
      | dsimp only)
  exact h.ne w

/-- **`underOf` never throws**: its `.owed` arm is unreachable, so the batch's UNDER reading
never answers OWED. -/
theorem underOf_ok (tfk : Value) : ∃ r, underOf tfk = .ok r := by
  unfold underOf
  split
  · exact ⟨_, rfl⟩
  · split
    · rename_i w h; exact absurd h (readTfk_ne_owed _ _)
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

/-- `underOf`'s arm for an analysis that gives none answers REC-39, never a UNDER list. -/
theorem underOf_analyse_none {tfk : Value} {K : Eom.Reading} (hs : structureOff tfk = false)
    (h : Eom.readTfk Eom.FormHook.calculator (Strike.toZoneValue tfk) = .ok K)
    (ha : Eom.analyse K K.laws = none) :
    underOf tfk = .ok (.error (one "REC-39" "-" "the TFK's equations of motion do not read")) := by
  simp only [underOf, hs, h, ha, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **A UNDER list comes only from the analysis**: `underOf` gives a list only when
STRUCTURE_CHECK is OFF (the list empty) or the equations-of-motion analysis gives that list
as its UNDER. -/
theorem underOf_under {tfk : Value} {u : List String} (h : underOf tfk = .ok (.ok u)) :
    (structureOff tfk = true ∧ u = []) ∨
      ∃ K a f c, Eom.readTfk Eom.FormHook.calculator (Strike.toZoneValue tfk) = .ok K ∧
        Eom.analyse K K.laws = some (a, f, c, u) := by
  unfold underOf at h
  split at h
  · rename_i hs
    exact .inl ⟨hs, by injection h with h; injection h with h; exact h.symm⟩
  · split at h
    · cases h
    · cases h
    · rename_i K hK
      split at h
      · rename_i a f c u' ha
        injection h with h; injection h with h; subst h
        exact .inr ⟨K, a, f, c, hK, ha⟩
      · cases h

/-! ## A register read holds each ID once

`readMember` takes a keyed record only when its ID is not one the register already holds;
anything else is not a register (REC-50). So every register `readRegister` answers holds
each ID once, and `Register.get?`, `heldRecords` and `replaceHeld` find the one record of
an ID: a second record of one ID is refused with the register, never replaced by the held
record of the first. -/

/-- An `if` that answers `some` only on its `then` side. -/
theorem ite_some_none_some {α : Type} {p : Prop} [Decidable p] {a b : α}
    (h : (if p then some a else none) = some b) : p ∧ a = b := by
  by_cases hp : p <;> simp_all

/-- An `if` that answers `some` only on its `else` side. -/
theorem ite_none_some_some {α : Type} {p : Prop} [Decidable p] {a b : Option α} {c : α}
    (h : (if p then a else b) = some c) (ha : a = none) : ¬p ∧ b = some c := by
  by_cases hp : p <;> simp_all

/-- One member read keeps the IDs distinct. -/
theorem readMember_nodup {reg reg' : Register} {v : Value}
    (h : readMember reg v = some reg') (hn : (reg.keyed.map Prod.fst).Nodup) :
    (reg'.keyed.map Prod.fst).Nodup := by
  unfold readMember at h
  split at h
  · split at h
    · obtain ⟨hc, rfl⟩ := ite_some_none_some h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hc
      obtain ⟨⟨⟨_, hnot⟩, _⟩, _⟩ := hc
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨hn, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      obtain ⟨⟨x, y⟩, hxy, hx⟩ := List.mem_map.1 ha
      have := hnot (x, y) hxy
      simp_all
    · cases h
  · split at h
    · obtain ⟨_, h⟩ := ite_none_some_some h rfl
      obtain ⟨_, h⟩ := ite_none_some_some h rfl
      obtain ⟨_, h⟩ := ite_none_some_some h rfl
      simp only [Option.some.injEq] at h
      subst h
      exact hn
    · cases h
  · cases h

/-- A register read member by member holds each ID once. -/
theorem foldlM_readMember_nodup :
    ∀ {rs : List Value} {reg reg' : Register},
      rs.foldlM readMember reg = some reg' → (reg.keyed.map Prod.fst).Nodup →
      (reg'.keyed.map Prod.fst).Nodup
  | [], reg, reg', h, hn => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    exact hn
  | r :: rs, reg, reg', h, hn => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hm : readMember reg r with
    | none => rw [hm] at h; cases h
    | some reg1 =>
      rw [hm] at h
      exact foldlM_readMember_nodup h (readMember_nodup hm hn)

/-- **Every register read holds each ID once**: `readRegister` answers a register only from
its member-by-member read, which keeps the IDs distinct. -/
theorem readRegister_nodup {v : Value} {arg : String} {reg : Register}
    (h : readRegister v arg = .ok (.ok reg)) : (reg.keyed.map Prod.fst).Nodup := by
  unfold readRegister at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i heq
        simp only [pure, Except.pure, Except.ok.injEq, Except.ok.injEq] at h
        subst h
        exact foldlM_readMember_nodup heq List.nodup_nil
      · simp [pure, Except.pure] at h
    · simp [pure, Except.pure] at h

/-! ## The IC2 gaps the final checks give

Every gap the final checks give is `IC2: DOF <d> is untied` (the isomorphism checks' only
gaps), and `ic2Dof` reads `<d>` back from it: `ic2Of`'s `filterMap` drops no gap. -/

/-- A gap of the form `IC2: DOF <d> is untied`. -/
def IsUntied (g : String) : Prop := ∃ d, g = "IC2: DOF " ++ d ++ " is untied"

/-- A member of an insertion is the one inserted or a member before. -/
theorem mem_insertStr {x y : String} :
    ∀ {l : List String}, y ∈ Zone.insertStr x l → y = x ∨ y ∈ l
  | [], h => by simp [Zone.insertStr] at h; exact .inl h
  | z :: zs, h => by
    simp only [Zone.insertStr] at h
    split at h
    · simpa using h
    · split at h
      · exact .inr h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact .inr (h ▸ List.mem_cons_self)
        · rcases mem_insertStr h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

/-- A member of a sorted insertion is a member of the list or of the start. -/
theorem mem_foldl_insertStr {y : String} :
    ∀ {l acc : List String}, y ∈ l.foldl (fun acc p => Zone.insertStr p acc) acc → y ∈ l ∨ y ∈ acc
  | [], _, h => .inr h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_foldl_insertStr h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rcases mem_insertStr h with h | h
      · exact .inl (h ▸ List.mem_cons_self)
      · exact .inr h

/-- The isomorphism checks' body gives only untied-DOF gaps. -/
theorem icBody_gaps {trm tpk : Zone.Value} {ic4a : List String} :
    ∀ g ∈ (Correspondence.icBody trm tpk ic4a).gaps, IsUntied g := by
  intro g hg
  simp only [Correspondence.icBody, Correspondence.icVerdict] at hg
  rcases mem_foldl_insertStr hg with h | h
  · obtain ⟨d, _, hd⟩ := List.mem_filterMap.1 h
    split at hd
    · cases hd
    · exact ⟨d, (Option.some.inj hd).symm⟩
  · simp at h

/-- The isomorphism checks give only untied-DOF gaps. -/
theorem isomorphismChecks_gaps {trm tpk : Zone.Value} {r : Correspondence.IcResult}
    (h : Correspondence.isomorphismChecks trm tpk = .ok r) : ∀ g ∈ r.gaps, IsUntied g := by
  unfold Correspondence.isomorphismChecks at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact icBody_gaps

/-- **The final checks give only untied-DOF gaps.** -/
theorem finalChecks_gaps {tfk : Zone.Value} {r : Correspondence.IcResult}
    (h : ResearchAssembly.finalChecks tfk = .ok r) : ∀ g ∈ r.gaps, IsUntied g := by
  intro g hg
  unfold ResearchAssembly.finalChecks at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq] at h; subst h; simp at hg; done)
    | (simp only [Except.ok.injEq] at h
       subst h
       simp only [Correspondence.icVerdict] at hg
       rcases mem_foldl_insertStr hg with hg | hg
       · exact isomorphismChecks_gaps (by assumption) g hg
       · simp at hg)

/-- `ic2Dof` reads the DOF back from an untied-DOF gap. -/
theorem ic2Dof_untied (d : String) : ic2Dof ("IC2: DOF " ++ d ++ " is untied") = some d := by
  have hs : ("IC2: DOF " ++ d ++ " is untied").startsWith "IC2: DOF " = true :=
    String.startsWith_string_iff.2 ⟨d.toList ++ " is untied".toList, by simp [String.toList_append]⟩
  have he : ("IC2: DOF " ++ d ++ " is untied").endsWith " is untied" = true := by
    unfold String.endsWith
    rw [String.Slice.endsWith_string_iff]
    exact ⟨"IC2: DOF ".toList ++ d.toList, by simp [String.toList_append]⟩
  have hl : ∀ a b c : Nat, a + b + c - a - c = b := by intro a b c; omega
  simp only [ic2Dof, hs, he, Bool.and_self, ite_true, Option.some.injEq, String.toList_append,
    String.length_append, List.append_assoc]
  rw [hl, List.drop_left' (by rfl), List.take_left' String.length_toList, String.ofList_toList]

/-- **`ic2Of` drops no gap**: every gap of the final checks names its DOF to `ic2Dof`. -/
theorem ic2Dof_finalChecks {tfk : Zone.Value} {r : Correspondence.IcResult}
    (h : ResearchAssembly.finalChecks tfk = .ok r) : ∀ g ∈ r.gaps, (ic2Dof g).isSome := by
  intro g hg
  obtain ⟨d, rfl⟩ := finalChecks_gaps h g hg
  simp [ic2Dof_untied]

/-! ## What the steps establish, proved

The batch's steps carry, in `ReauditSteps`, the facts below: every failed ID has its change
and its held record; a failed record `HOLD` does not apply to is refused as `status_next`
refuses it; every record of the successor's register that carries an ID is the register's
record of that ID, so a record REGISTER changes is that record with STATUS set and DIGEST
formed again; and no gap ID nor PROMOTION ID is already an ID of the register. -/

/-- **No failed ID is dropped**: the changes name the failed IDs, in order. -/
theorem holdChanges_ids {reg : Register} :
    ∀ {fs : List String} {cs : List (String × String)},
      holdChanges reg fs = .ok cs → cs.map Prod.fst = fs
  | [], cs, h => by simp only [holdChanges, Except.ok.injEq] at h; subst h; rfl
  | rid :: fs, cs, h => by
    simp only [holdChanges] at h
    cases hg : reg.get? rid with
    | none => simp [hg] at h
    | some r =>
      cases hs : heldStatusOf r with
      | none => simp [hg, hs] at h
      | some s =>
        simp only [hg, hs] at h
        cases ht : holdChanges reg fs with
        | error e => simp [ht, Except.map] at h
        | ok cs' =>
          simp only [ht, Except.map, Except.ok.injEq] at h
          subst h
          simp [holdChanges_ids ht]

/-- The changes `holdChanges` gives are `heldChanges`' over the same IDs. -/
theorem holdChanges_eq {reg : Register} :
    ∀ {fs : List String} {cs : List (String × String)},
      holdChanges reg fs = .ok cs → cs = heldChanges reg fs
  | [], cs, h => by simp only [holdChanges, Except.ok.injEq] at h; subst h; rfl
  | rid :: fs, cs, h => by
    simp only [holdChanges] at h
    cases hg : reg.get? rid with
    | none => simp [hg] at h
    | some r =>
      cases hs : heldStatusOf r with
      | none => simp [hg, hs] at h
      | some s =>
        simp only [hg, hs] at h
        cases ht : holdChanges reg fs with
        | error e => simp [ht, Except.map] at h
        | ok cs' =>
          simp only [ht, Except.map, Except.ok.injEq] at h
          subst h
          simp only [heldChanges, List.filterMap_cons, hg, Option.bind_some, hs, Option.map_some]
          rw [holdChanges_eq ht]; rfl

/-- **Every failed ID is a record of the register and has its change**, the STATUS
`status_next` gives it on `HOLD`. -/
theorem holdChanges_mem {reg : Register} :
    ∀ {fs : List String} {cs : List (String × String)},
      holdChanges reg fs = .ok cs → ∀ rid ∈ fs,
        ∃ r s, reg.get? rid = some r ∧ heldStatusOf r = some s ∧ (rid, s) ∈ cs
  | [], _, _, rid, hm => by simp at hm
  | x :: fs, cs, h, rid, hm => by
    simp only [holdChanges] at h
    cases hg : reg.get? x with
    | none => simp [hg] at h
    | some r =>
      cases hs : heldStatusOf r with
      | none => simp [hg, hs] at h
      | some s =>
        simp only [hg, hs] at h
        cases ht : holdChanges reg fs with
        | error e => simp [ht, Except.map] at h
        | ok cs' =>
          simp only [ht, Except.map, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hm with he | hm
          · subst he; exact ⟨r, s, hg, hs, List.mem_cons_self⟩
          · obtain ⟨r', s', h1, h2, h3⟩ := holdChanges_mem ht rid hm
            exact ⟨r', s', h1, h2, List.mem_cons_of_mem _ h3⟩

/-- `holdChanges` refuses only a record `HOLD` does not apply to (`null` for an ID the
register does not hold, to which `HOLD` applies neither). -/
theorem holdChanges_error {reg : Register} :
    ∀ {fs : List String} {r : Value}, holdChanges reg fs = .error r → heldStatusOf r = none
  | [], r, h => by simp [holdChanges] at h
  | x :: fs, r, h => by
    simp only [holdChanges] at h
    cases hg : reg.get? x with
    | none =>
      simp only [hg, Except.error.injEq] at h
      subst h; rfl
    | some r' =>
      cases hs : heldStatusOf r' with
      | none =>
        simp only [hg, hs, Except.error.injEq] at h
        subst h; exact hs
      | some s =>
        simp only [hg, hs] at h
        cases ht : holdChanges reg fs with
        | error e =>
          simp only [ht, Except.map, Except.error.injEq] at h
          subst h; exact holdChanges_error ht
        | ok cs' => simp [ht, Except.map] at h

/-- `classArg`'s answer, when it has one, is a refusal. -/
theorem classArg_some {c r : Value} (h : classArg c = .ok (some r)) :
    ∃ a b m, r = one a b m := by
  unfold classArg at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Option.some.injEq] at h; done)
    | (simp only [Except.ok.injEq, Option.some.injEq] at h; exact ⟨_, _, _, h.symm⟩)

/-- `classArg` passes only a string. -/
theorem classArg_none {c : Value} (h : classArg c = .ok none) : ∃ s, c = .str s := by
  unfold classArg at h
  split at h
  · exact ⟨_, rfl⟩
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h <;> simp at h

/-- `status_next` answers a refusal, or `["OK", o]` where `statusNextOf` gives `o` over the
class and STATUS it was given. -/
theorem statusNext_ok {c st ev v : Value} (hv : statusNext c st ev = .ok v) :
    (∃ a b m, v = one a b m) ∨
      ∃ cs ss o, c = .str cs ∧ st = .str ss ∧ statusNextOf (strOf c) ss (strOf ev) = some o ∧
        v = okWith [.str o] := by
  unfold statusNext at hv
  simp only [bind, Except.bind, pure, Except.pure] at hv
  generalize hF : statusNextOf = F at hv
  generalize statusesOf = S at hv
  cases hc : classArg c with
  | error e => rw [hc] at hv; cases hv
  | ok o =>
    rw [hc] at hv
    cases o with
    | some r =>
      left
      simp only [Except.ok.injEq] at hv
      subst hv
      exact classArg_some hc
    | none =>
      obtain ⟨cs, hcs⟩ := classArg_none hc
      dsimp only at hv
      split at hv
      · left; simp only [Except.ok.injEq] at hv; exact ⟨_, _, _, hv.symm⟩
      · split at hv
        · cases st with
          | str ss =>
            split at hv
            · rename_i o ho
              right
              simp only [Except.ok.injEq] at hv
              exact ⟨cs, ss, o, hcs, rfl, ho, hv.symm⟩
            · left
              split at hv
              · cases hv
              · simp only [Except.ok.injEq] at hv; exact ⟨_, _, _, hv.symm⟩
          | _ =>
            left
            dsimp only at hv
            split at hv
            · cases hv
            · simp only [Except.ok.injEq] at hv; exact ⟨_, _, _, hv.symm⟩
        · left
          split at hv
          · cases hv
          · simp only [Except.ok.injEq] at hv; exact ⟨_, _, _, hv.symm⟩

/-- **A failed record `HOLD` does not apply to is refused**: where `heldStatusOf` gives no
STATUS, `status_next` on `HOLD` over the record's CLASS and STATUS answers a refusal, never
`["OK", ...]`; so the batch's answer on `holdChanges`' refusal is a refusal. -/
theorem statusNext_hold_refused {r v : Value} (h : heldStatusOf r = none)
    (hv : statusNext (getOr r "CLASS") ((V.get? r "STATUS").getD (.str "UNMARKED")) (.str "HOLD")
      = .ok v) : ∃ ps, v = refused ps := by
  rcases statusNext_ok hv with ⟨a, b, m, rfl⟩ | ⟨cs, ss, o, hc, hs, ho, _⟩
  · exact ⟨_, rfl⟩
  · exfalso
    have hcs : V.getStr? r "CLASS" = some cs := by
      unfold getOr at hc
      unfold V.getStr?
      revert hc
      cases V.get? r "CLASS" with
      | none => intro hc; cases hc
      | some w => intro hc; simp only [Option.getD_some] at hc; subst hc; rfl
    have hss : (V.getStr? r "STATUS").getD "UNMARKED" = ss := by
      unfold V.getStr?
      revert hs
      cases V.get? r "STATUS" with
      | none => intro hs; cases hs; rfl
      | some w => intro hs; simp only [Option.getD_some] at hs; subst hs; rfl
    rw [hc] at ho
    change statusNextOf cs ss "HOLD" = some o at ho
    unfold heldStatusOf at h
    rw [hcs, hss] at h
    dsimp only at h
    rw [h] at ho
    cases ho

/-- The keyed record of an ID found in a list's prefix is found in the whole list. -/
theorem lookup_append_some {k : String} {v : Value} :
    ∀ {l : List (String × Value)} (l2 : List (String × Value)), l.lookup k = some v →
      (l ++ l2).lookup k = some v
  | [], _, h => by simp [List.lookup] at h
  | (a, b) :: t, l2, h => by
    have hl : ∀ m : List (String × Value), List.lookup k ((a, b) :: m) =
        (match k == a with | true => some b | false => List.lookup k m) := fun _ => rfl
    rw [List.cons_append, hl]
    rw [hl] at h
    cases hk : (k == a) with
    | true => rw [hk] at h; exact h
    | false => rw [hk] at h; exact lookup_append_some l2 h

/-- An ID no member carries is found after the list, in what follows it. -/
theorem lookup_append_none {k : String} :
    ∀ {l : List (String × Value)} (l2 : List (String × Value)), l.any (·.1 == k) = false →
      (l ++ l2).lookup k = l2.lookup k
  | [], _, _ => rfl
  | (a, b) :: t, l2, h => by
    have hl : List.lookup k ((a, b) :: (t ++ l2)) =
        (match k == a with | true => some b | false => List.lookup k (t ++ l2)) := rfl
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hk : (k == a) = false := by
      have : a ≠ k := by simpa using h.1
      simpa using Ne.symm this
    rw [List.cons_append, hl, hk]
    exact lookup_append_none l2 h.2

/-- One member read: a positional record, which carries no `ID` member, leaves the keyed
records as they were; a keyed record is added under its own ID, one the register did not hold. -/
theorem readMember_cases {reg reg' : Register} {v : Value} (h : readMember reg v = some reg') :
    (reg'.keyed = reg.keyed ∧ V.getStr? v "ID" = none) ∨
      ∃ rid, V.getStr? v "ID" = some rid ∧ reg.keyed.any (·.1 == rid) = false ∧
        reg'.keyed = reg.keyed ++ [(rid, v)] := by
  unfold readMember at h
  split at h
  · split at h
    · rename_i _ _ rid _ _ hi _
      obtain ⟨hc, rfl⟩ := ite_some_none_some h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      right
      exact ⟨rid, by simp [V.getStr?, V.str?, hi], hc.1.1.2, rfl⟩
    · cases h
  · left
    split at h
    · obtain ⟨_, h⟩ := ite_none_some_some h rfl
      obtain ⟨_, h⟩ := ite_none_some_some h rfl
      obtain ⟨_, h⟩ := ite_none_some_some h rfl
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- One member read keeps every member read so far the register's record of its ID, and makes
the member read the record of its own. -/
theorem readMember_raw {reg reg' : Register} {v : Value} {ys : List Value}
    (h : readMember reg v = some reg')
    (hP : ∀ y ∈ ys, ∀ rid, V.getStr? y "ID" = some rid → reg.get? rid = some y) :
    ∀ y ∈ ys ++ [v], ∀ rid, V.getStr? y "ID" = some rid → reg'.get? rid = some y := by
  intro y hy rid hid
  simp only [Register.get?]
  rcases readMember_cases h with ⟨hk, hv⟩ | ⟨rid0, hv, hany, hk⟩
  · rw [hk]
    rcases List.mem_append.mp hy with hy | hy
    · exact hP y hy rid hid
    · simp only [List.mem_singleton] at hy
      subst hy
      rw [hv] at hid
      cases hid
  · rw [hk]
    rcases List.mem_append.mp hy with hy | hy
    · exact lookup_append_some _ (hP y hy rid hid)
    · simp only [List.mem_singleton] at hy
      subst hy
      rw [hv] at hid
      cases hid
      rw [lookup_append_none _ hany]
      simp [List.lookup]

/-- A register read member by member holds each member that carries an ID as the record of
that ID. -/
theorem foldlM_readMember_raw :
    ∀ {rs ys : List Value} {reg reg' : Register},
      rs.foldlM readMember reg = some reg' →
      (∀ y ∈ ys, ∀ rid, V.getStr? y "ID" = some rid → reg.get? rid = some y) →
      ∀ y ∈ ys ++ rs, ∀ rid, V.getStr? y "ID" = some rid → reg'.get? rid = some y
  | [], ys, reg, reg', h, hP => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    simpa using hP
  | r :: rs, ys, reg, reg', h, hP => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases hm : readMember reg r with
    | none => rw [hm] at h; cases h
    | some reg1 =>
      rw [hm] at h
      have := foldlM_readMember_raw (ys := ys ++ [r]) h (readMember_raw hm hP)
      simpa using this

/-- **Every record of a register read that carries an ID is the register's record of that
ID**: a positional record carries no `ID` member, and no other member can stand for a keyed
record, so `replaceHeld` replaces only the keyed record it was formed from. -/
theorem readRegister_raw {v : Value} {arg : String} {reg : Register}
    (h : readRegister v arg = .ok (.ok reg)) :
    ∀ y ∈ recordsOf v, ∀ rid, V.getStr? y "ID" = some rid → reg.get? rid = some y := by
  unfold readRegister at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · rename_i rs
      split at h
      · rename_i heq
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro y hy rid hid
        exact foldlM_readMember_raw (ys := []) heq (by simp) y (by simpa [recordsOf] using hy)
          rid hid
      · simp [pure, Except.pure] at h
    · simp [pure, Except.pure] at h

namespace ReauditSteps

variable {d : Value} (st : ReauditSteps d)

/-- **No failed ID is dropped**: the batch's changes name its failed IDs, in order. -/
theorem changes_ids : st.changes.map Prod.fst = st.failed := holdChanges_ids st.held

/-- **Every failed ID is a record of the successor's register and has its change.** -/
theorem failed_held : ∀ rid ∈ st.failed,
    ∃ r s, st.reg.get? rid = some r ∧ heldStatusOf r = some s ∧ (rid, s) ∈ st.changes :=
  holdChanges_mem st.held

/-- **Every change has its held record**: over the batch's changes, the held records
`heldRecords` forms are one per failed ID, in order. -/
theorem heldRecords_failed {hs : List (String × Value)}
    (h : heldRecords st.reg st.changes = .ok (.ok hs)) : hs.map Prod.fst = st.failed := by
  have hc := holdChanges_eq st.held
  rw [hc] at h
  rw [heldRecords_heldChanges h, ← hc, changes_ids]

/-- **A record REGISTER changes is the successor's record, STATUS set and DIGEST formed
again**: at the place of a record of the successor's register, REGISTER holds that record as
given, or that very record with the STATUS of its change and the DIGEST `record_digest` forms
over the result. -/
theorem registerOf_changed {xs : List Value}
    (h : registerOf st.reg (recordsOf d) st.changes st.gaps st.promotion = .ok (.ok xs))
    {i : Nat} {x y : Value} (hy : (recordsOf d)[i]? = some y) (hx : xs[i]? = some x)
    (hne : x ≠ y) :
    ∃ rid s dg, V.getStr? y "ID" = some rid ∧ (rid, s) ∈ st.changes ∧
      x = V.set (V.set y "STATUS" (.str s)) "DIGEST" dg ∧ recordDigestM x = .ok (okWith [dg]) := by
  obtain ⟨rid, s, r, dg, hid, hm, hr, hxe, hdg⟩ := Record.registerOf_changed h hy hx hne
  have hry := readRegister_raw st.read y (List.mem_of_getElem? hy) rid hid
  rw [hry] at hr
  cases hr
  exact ⟨rid, s, dg, hid, hm, hxe, hdg⟩

/-- **No gap ID is already an ID of the successor's register.** -/
theorem gaps_fresh : ∀ i ∈ memberIds st.gaps, i ∉ memberIds (recordsOf d) :=
  clashOf_none st.gapsFresh

/-- **The PROMOTION ID is no other ID of REGISTER**: neither one of the successor's register
nor a gap ID. -/
theorem promotion_fresh :
    ∀ i ∈ memberIds (promotionList st.promotion), i ∉ memberIds (recordsOf d ++ st.gaps) :=
  clashOf_none st.promotionFresh

end ReauditSteps

/-- **What the batch answers.** Every answer of `reaudit_batch` is the refusal of steps 1 to 7,
the refusal of a held record's digest, or `["OK", {..., "REGISTER": xs}]` whose REGISTER
meets the three properties together: a record of it at the place of a record of the
successor's register that differs from it is that record with the STATUS of its change and
the DIGEST `record_digest` forms over the result; a record whose ID no change names is at its
place as given; and its length is the successor's record count plus the gap records plus one
when PROMOTION is not null (`promotionList`: none for `null`, else the one record). -/
theorem reauditBatch_register {srcTfk dstTfk srcRecords dstRecords setting promotionId
    landingBlock pre trigger landed tps v : Value}
    (h : reauditBatch srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
      trigger landed tps = .ok v) :
    (reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock pre
        trigger landed tps = .ok (.error v)) ∨
    (∃ st, reauditSteps srcTfk dstTfk srcRecords dstRecords setting promotionId landingBlock
        pre trigger landed tps = .ok (.ok st) ∧
      registerOf st.reg (recordsOf dstRecords) st.changes st.gaps st.promotion = .ok (.error v)) ∨
    (∃ st : ReauditSteps dstRecords, ∃ xs : List Value, v = reauditAnswer st xs ∧
      (∀ (i : Nat) (x y : Value), (recordsOf dstRecords)[i]? = some y → xs[i]? = some x → x ≠ y →
        ∃ rid s dg, V.getStr? y "ID" = some rid ∧ (rid, s) ∈ st.changes ∧
          x = V.set (V.set y "STATUS" (.str s)) "DIGEST" dg ∧
          recordDigestM x = .ok (okWith [dg])) ∧
      (∀ (i : Nat) (y : Value), (recordsOf dstRecords)[i]? = some y →
        (∀ rid, V.getStr? y "ID" = some rid → ∀ s, (rid, s) ∉ st.changes) → xs[i]? = some y) ∧
      xs.length = (recordsOf dstRecords).length + st.gaps.length +
        (promotionList st.promotion).length) := by
  rcases reauditBatch_cases h with h1 | h2 | ⟨st, xs, _, hr, hv⟩
  · exact .inl h1
  · exact .inr (.inl h2)
  · exact .inr (.inr ⟨st, xs, hv,
      fun _ _ _ hy hx hne => st.registerOf_changed hr hy hx hne,
      fun _ _ hy hn => registerOf_unchanged hr hy hn,
      by obtain ⟨_, _, rfl⟩ := registerOf_ok hr; simp [registerAfter, Nat.add_assoc]⟩)

end Principia.Record
