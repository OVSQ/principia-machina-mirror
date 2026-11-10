import Principia.Record.Register
import Principia.Record.Measured

/-!
# The successor's re-audit in one call

`reauditBatch`, the Calculator's half of the successor's re-audit (version 1 TPS 4.1.9,
3.4.7, 5.3.49; the re-audit strikes nothing), composed of the register functions
that exist, in this order:

1. `reauditScope src dst`: the checks the changed zones and parameters require.
2. When the scope names any check: `recordCheckM` at the stage `LANDED` and, for a RESULT
   or an ASSUMPTION, `recordFormCheck`, over every inherited record of the successor (a
   keyed record carrying `INHERITS`, of a class that carries a STATUS) whose status word is
   neither REFUTED nor WITHDRAWN: those stay as the copy set them (4.1.9).
3. A record either check refuses has its STATUS set by `statusNextOf` on the event `HOLD`
   (nothing is struck by the re-audit), and its status word with it.
4. When a record failed, the gap records `gapRecords prefix ic2 under trigger landed tps`
   are opened; they are the successor's open audits. A gap ID already in the
   successor's register is refused, REC-57: `gap_records` numbers from 2 under the prefix
   it is given.
5. `repromoteBatch` over the successor's words as step 3 left them, with those open audits.
6. `promotionRecord` over what it promoted, when it promoted anything.

The answer is `["OK", {"CHECKS", "STATUS", "GAPS", "PROMOTED", "PROMOTION"}]`: the scope's
checks, the `[id, STATUS]` pairs step 3 set, the gap records, the promoted triples and the
PROMOTION record (`null` when nothing was promoted). A refusal of any step is the batch's
answer, unchanged: nothing of the batch is written.

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

/-- `reaudit_batch`: the successor's re-audit in one call. -/
def reauditBatch (src dst srcRecords srcWords dstRecords dstWords tfk setting promotionId
    landingBlock pre ic2 under trigger landed tps : Value) : M Value := do
  let checks ← match ← reauditScope src dst with
    | .arr [.str "OK", .arr cs] => pure cs
    | other => return other
  let reg ← match ← readRegister dstRecords "dst_records" with
    | .error b => return b
    | .ok reg => pure reg
  let some ws := wordsArg? dstWords | return ← badArg "dst_words" dstWords "a map of status words"
  unless tfk != .null && assemblyOk tfk do return one "REC-39" "-" "the TFK is not readable"
  let mut failed : List String := []
  unless checks.isEmpty do
    for (rid, r) in reg.keyed do
      if recheckable ws reg rid r then
        if ← recheckFails r tfk setting then failed := failed ++ [rid]
  let changes := heldChanges reg (sortStrings failed)
  let gaps ← if failed.isEmpty then pure [] else
    match ← gapRecords pre ic2 under trigger landed tps with
    | .arr [.str "OK", .arr gs] => pure gs
    | other => return other
  let gapIds := gaps.filterMap (V.getStr? · "ID")
  for g in gapIds do
    if (reg.get? g).isSome then
      return one "REC-57" "prefix" s!"gap ID {← showSlot g} is already in the register"
  let audits := V.strs gapIds
  let promoted ← match ← repromoteBatch srcRecords srcWords dstRecords
      (wordsValue (applyWords ws changes)) tfk audits with
    | .arr [.str "OK", .arr ps] => pure ps
    | other => return other
  let promotion ← if promoted.isEmpty then pure Value.null else
    match ← promotionRecord promotionId landingBlock (.arr promoted) with
    | .arr [.str "OK", p] => pure p
    | other => return other
  return okWith [.obj [("CHECKS", .arr checks),
    ("STATUS", .arr (changes.map fun (i, s) => V.strs [i, s])), ("GAPS", .arr gaps),
    ("PROMOTED", .arr promoted), ("PROMOTION", promotion)]]

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

end Principia.Record
