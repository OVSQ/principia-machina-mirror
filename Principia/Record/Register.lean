import Principia.Record.Check

/-!
# The register functions

v1's `tpc_record` 0.1.0, the functions of tpm_record_functions 0.3.0 that read a register
(a list of records, keyed and positional) or write a positional record:

* grade and status (section 4): `gradeValuesOf`, `statusValuesOf`, `gradeNow`,
  `statusWords`, `isStanding`, `statusWord`, `gradeNext`, `statusNext`, `inheritGrade`;
* citations (5): `citationCheck`;
* the withdrawal (6): `withdrawalScope`, `withdrawalPreimage`, `withdrawalRecord`;
* named gaps (13): `gapRecords`, `gapRecord`, `gapView`, `gapState`, `eom0Open`;
* verification (14): `verificationOrder`;
* promotion, the entry view, successors (15): `promotionEligible`, `promotionPass`,
  `promotionRecord`, `entryView`, `reauditScope`, `repromoteBatch`.

A register is read as v1's `_register` reads it: a list of keyed records (an object of a
keyed class with a string ID not seen before and a grade of GRADE_VALUES, its STATUS a
string when present) and positional records (HOLD, RELEASE, WITHDRAWAL, PROMOTION; a
WITHDRAWAL of 14 items, a PROMOTION of 5); anything else is REC-50. A closure over the
register (the withdrawal's reach, the ASSUMPTIONS closure, the promotion's rounds) takes
at most one round more than the register has records, and is computed so, without
`partial`.

A function that writes a digest (`withdrawalRecord`, `gapRecords`, `gapRecord`,
`promotionRecord`) computes it: SHA-256 over its field list's netstring
(`Principia.Digest.digestFields`).
-/

namespace Principia.Record

open Principia.Canonical (Value)
open Principia.Record.Table

/-! ## Reading a register (v1 `_register`) -/

/-- v1's `RANK` of a grade a positional record gives. -/
def rankOf : String → Nat
  | "REFUTED" => 3
  | "WITHDRAWN" => 2
  | "ESTABLISHED" => 1
  | _ => 0

/-- v1's `LIST_CLASSES`. -/
def listClasses : List String := ["HOLD", "RELEASE", "WITHDRAWAL", "PROMOTION"]

/-- v1's `STATUS_WORDS`. -/
def statusWordList : List String :=
  ["PROVISIONAL", "ESTABLISHED", "REFUTED", "WITHDRAWN", "HELD", "NOT GRADED"]

/-- v1's `STATUS_VALUES`. -/
def statusValueList : List String := ["UNMARKED", "HELD", "REFUTED"]

/-- v1's `_pairs_ok`: a list of `[string, string]`. -/
def pairsOk : Value → Bool
  | .arr ps => ps.all (fun | .arr [.str _, .str _] => true | _ => false)
  | _ => false

/-- The pairs of a `_pairs_ok` list. -/
def pairsOf : Value → List (String × String)
  | .arr ps => ps.filterMap (fun | .arr [.str a, .str b] => some (a, b) | _ => none)
  | _ => []

/-- A register as v1 reads it: the keyed records by ID, in order, and the positional
records. -/
structure Register where
  keyed : List (String × Value)
  lists : List (List Value)

/-- A keyed record of the register. -/
def Register.get? (reg : Register) (rid : String) : Option Value := reg.keyed.lookup rid

/-- A keyed record's CLASS. -/
def Register.cls (reg : Register) (rid : String) : Option String :=
  (reg.get? rid).bind fun r => V.getStr? r "CLASS"

/-- The keyed IDs, in code point order. -/
def Register.sortedIds (reg : Register) : List String := sortStrings (reg.keyed.map Prod.fst)

/-- One register member read. -/
def readMember (reg : Register) : Value → Option Register
  | r@(.obj _) =>
    match V.get? r "CLASS", V.get? r "ID", V.get? r "GRADE", V.get? r "STATUS" with
    | some (.str c), some (.str rid), some (.str g), st =>
      if keyed.contains c && !(reg.keyed.any (·.1 == rid)) && gradeValues.contains g &&
          (match st with | none | some (.str _) => true | _ => false) then
        some { reg with keyed := reg.keyed ++ [(rid, r)] }
      else none
    | _, _, _, _ => none
  | .arr items =>
    match (items[1]? : Option Value) with
    | some (.str k) =>
      if !listClasses.contains k then none
      else if k == "WITHDRAWAL" &&
          !(items.length == 14 && V.isStr (items[3]?.getD .null) &&
            (items[5]? == some (.str "REFUTED") || items[5]? == some (.str "WITHDRAWN")) &&
            pairsOk (items[10]?.getD .null)) then none
      else if k == "PROMOTION" &&
          !(items.length == 5 && (match (items[3]? : Option Value) with
            | some (.arr ts) => ts.all (fun | .arr [.str _, _, _] => true | _ => false)
            | _ => false)) then none
      else some { reg with lists := reg.lists ++ [items] }
    | _ => none
  | _ => none

/-- v1's `_register(register, argument)`: the register, or REC-50. -/
def readRegister (register : Value) (argument : String := "register") : M (Except Value Register) := do
  let bad ← badArg argument register "a register"
  match register with
  | .arr rs =>
    match rs.foldlM readMember { keyed := [], lists := [] } with
    | some reg => return .ok reg
    | none => return .error bad
  | _ => return .error bad

/-- v1's `_grade_now`: the record's GRADE, then the highest grade a WITHDRAWAL or a
PROMOTION gives it (REFUTED > WITHDRAWN > ESTABLISHED > the start); NOT GRADED stays. -/
def Register.gradeNow (reg : Register) (rid : String) : String :=
  let g0 := ((reg.get? rid).bind fun r => V.getStr? r "GRADE").getD ""
  if g0 == "NOT GRADED" then g0
  else
    reg.lists.foldl (fun (best : String) (r : List Value) =>
      let given : List String :=
        match (r[1]? : Option Value) with
        | some (.str "WITHDRAWAL") =>
          (if r[3]? == some (.str rid) then
            (match (r[5]? : Option Value) with | some (.str g) => [g] | _ => []) else []) ++
          (if (pairsOf (r[10]?.getD .null)).any (·.1 == rid) then ["WITHDRAWN"] else [])
        | some (.str "PROMOTION") =>
          match (r[3]? : Option Value) with
          | some (.arr ts) =>
            if ts.any (fun | .arr (.str i :: _) => i == rid | _ => false) then ["ESTABLISHED"] else []
          | _ => []
        | _ => []
      given.foldl (fun b g => if rankOf g > rankOf b then g else b) best) g0

/-- v1's status word of a keyed record: its STATUS when HELD or REFUTED, else its grade
now. -/
def Register.word (reg : Register) (rid : String) : String :=
  match (reg.get? rid).bind fun r => V.getStr? r "STATUS" with
  | some "HELD" => "HELD"
  | some "REFUTED" => "REFUTED"
  | _ => reg.gradeNow rid

/-- v1's `_words`: every keyed record's status word. -/
def Register.words (reg : Register) : List (String × String) :=
  reg.keyed.map fun (rid, _) => (rid, reg.word rid)

/-- v1's `_standing`. -/
def standing (w : String) : Bool := w == "PROVISIONAL" || w == "ESTABLISHED"

/-- v1's `_class_arg`: REC-51 unless a class of the table. -/
def classArg (c : Value) : M (Option Value) := do
  match c with
  | .str s =>
    if classes.contains s then return none
    else return some (one "REC-51" "-" s!"class {← showJson c} is not a record class")
  | _ => return some (one "REC-51" "-" s!"class {← showJson c} is not a record class")

/-- REC-38 unless a grade of GRADE_VALUES. -/
def gradeArg (g : Value) : M (Option String) := do
  match g with
  | .str s =>
    if gradeValues.contains s then return none
    else return some s!"grade {← showJson g} is not a grade"
  | _ => return some s!"grade {← showJson g} is not a grade"

/-- The string a value holds, or the empty string. -/
def strOf : Value → String
  | .str s => s
  | _ => ""

/-! ## 4 Grade and status -/

/-- v1's `grade_values(class)`: the class's GRADES line. -/
def gradeValuesOf (cls : Value) : M Value := do
  if let some r ← classArg cls then return r
  return okWith [V.strs (gradesOf (strOf cls))]

/-- v1's `status_values(class)`: the class's STATUSES line, `[]` without STATUS. -/
def statusValuesOf (cls : Value) : M Value := do
  if let some r ← classArg cls then return r
  return okWith [V.strs (statusesOf (strOf cls))]

/-- v1's `grade_now(register, id)`. -/
def gradeNow (register rid : Value) : M Value := do
  match ← readRegister register with
  | .error b => return b
  | .ok reg =>
    match rid with
    | .str s =>
      if (reg.get? s).isSome then return okWith [.str (reg.gradeNow s)]
      else return one "REC-52" "-" s!"record {← showArg rid} is not in the register"
    | _ => return one "REC-52" "-" s!"record {← showArg rid} is not in the register"

/-- v1's `status_words(register)`: `{id: word}`. -/
def statusWords (register : Value) : M Value := do
  match ← readRegister register with
  | .error b => return b
  | .ok reg => return okWith [.obj (reg.words.map fun (i, w) => (i, .str w))]

/-- v1's `is_standing(word)`. -/
def isStanding (word : Value) : M Value := do
  match word with
  | .str w =>
    if statusWordList.contains w then return okWith [.bool (standing w)]
    else return one "REC-53" "-" s!"word {← showArg word} is not a status word"
  | _ => return one "REC-53" "-" s!"word {← showArg word} is not a status word"

/-- v1's `status_word(grade, status)`: the status when HELD or REFUTED, else the grade. -/
def statusWord (grade status : Value) : M Value := do
  if let some m ← gradeArg grade then return one "REC-38" "-" m
  unless status == .null || (match status with | .str s => statusValueList.contains s | _ => false) do
    return one "REC-53" "-" s!"word {← showArg status} is not a status word"
  match status with
  | .str "HELD" | .str "REFUTED" => return okWith [status]
  | _ => return okWith [grade]

/-- v1's `_art` (F-GV2-11): "an" before ASSUMPTION and ENTRY_STATUS. -/
def article (cls : String) : String :=
  if cls == "ASSUMPTION" || cls == "ENTRY_STATUS" then "an" else "a"

/-- The grade an event gives a class of a grade, when it applies (functions 4.6). -/
def gradeNextOf (cls grade event : String) : Option String :=
  if event == "PROMOTE" && cls == "RESULT" && grade == "PROVISIONAL" then some "ESTABLISHED"
  else if event == "STRIKE" && (cls == "RESULT" || cls == "CORROBORATION") &&
      (grade == "PROVISIONAL" || grade == "ESTABLISHED") && (gradesOf cls).contains grade then
    some "REFUTED"
  else if event == "WITHDRAW" && gradesOf cls != ["NOT GRADED"] &&
      (grade == "PROVISIONAL" || grade == "ESTABLISHED") && (gradesOf cls).contains grade then
    some "WITHDRAWN"
  else none

/-- v1's `grade_next(class, grade, event)`. -/
def gradeNext (cls grade event : Value) : M Value := do
  if let some r ← classArg cls then return r
  if let some m ← gradeArg grade then return one "REC-38" "-" m
  let ev := strOf event
  unless V.isStr event && (ev == "PROMOTE" || ev == "STRIKE" || ev == "WITHDRAW") do
    return one "REC-55" "-" s!"event {← showArg event} is not PROMOTE, STRIKE or WITHDRAW"
  let c := strOf cls
  let g := strOf grade
  match gradeNextOf c g ev with
  | some out => return okWith [.str out]
  | none => return one "REC-54" "-" s!"{ev} does not apply to {article c} {c} of grade {g}"

/-- The STATUS an event gives a class of a STATUS, when it applies (functions 4.7). -/
def statusNextOf (cls status event : String) : Option String :=
  if !(statusesOf cls).contains status then none
  else if event == "HOLD" then some (if status == "REFUTED" then "REFUTED" else "HELD")
  else if event == "STRIKE" then
    if (cls == "RESULT" || cls == "CORROBORATION") && (status == "UNMARKED" || status == "HELD")
    then some "REFUTED" else none
  else releaseOf (statusesOf cls) (String.ofList (event.toList.drop "RELEASE:".length))
where
  /-- RELEASE:<word>: HELD and REFUTED restored, a grade word to UNMARKED, when the class
  carries it. -/
  releaseOf (statuses : List String) (w : String) : Option String :=
    let out := if w == "HELD" || w == "REFUTED" then w else "UNMARKED"
    if statuses.contains out then some out else none

/-- v1's `status_next(class, status, event)`. -/
def statusNext (cls status event : Value) : M Value := do
  if let some r ← classArg cls then return r
  let c := strOf cls
  if (statusesOf c).isEmpty then return one "REC-56" "-" s!"{c} carries no STATUS"
  let ev := strOf event
  let okEvent := V.isStr event && (ev == "HOLD" || ev == "STRIKE" ||
    ("RELEASE:".isPrefixOf ev && statusWordList.contains (String.ofList (ev.toList.drop "RELEASE:".length))))
  unless okEvent do
    return one "REC-55" "-" s!"event {← showArg event} is not HOLD, STRIKE or RELEASE:<word>"
  let out := match status with
    | .str s => statusNextOf c s ev
    | _ => none
  match out with
  | some o => return okWith [.str o]
  | none => return one "REC-54" "-" s!"{ev} does not apply to {article c} {c} of STATUS {← showArg status}"

/-- The grade an inherited record holds once the copy is written (functions 4.8). -/
def inheritGradeOf (cls grade : String) : String :=
  if gradesOf cls == ["NOT GRADED"] then "NOT GRADED"
  else if grade == "REFUTED" || grade == "WITHDRAWN" then grade else "PROVISIONAL"

/-- v1's `inherit_grade(class, grade)`. -/
def inheritGrade (cls grade : Value) : M Value := do
  if let some r ← classArg cls then return r
  if let some m ← gradeArg grade then return one "REC-38" "-" m
  return okWith [.str (inheritGradeOf (strOf cls) (strOf grade))]

/-! ## 5 Citations -/

/-- A member of an object, or null (v1's `.get`). -/
def getOr (v : Value) (k : String) : Value := (V.get? v k).getD .null

/-- v1's `citation_check(record, register, entries, supersede_decided)`. -/
def citationCheck (record register entries supersedeDecided : Value) : M Value := do
  let reg ← match ← readRegister register with
    | .error b => return b
    | .ok reg => pure reg
  unless (match entries with | .arr es => es.all (fun | .str s => isBib s | _ => false) | _ => false) do
    return ← badArg "entries" entries "a list of BIB IDs"
  let decided ← match supersedeDecided with
    | .bool b => pure b
    | _ => return ← badArg "supersede_decided" supersedeDecided "a boolean"
  unless V.isObj record do return one "REC-01" "-" "the record is not an object"
  let entryIds := V.members (some entries)
  let mut p : List Problem := []
  if let some (.str rid) := V.get? record "ID" then
    if (reg.get? rid).isSome then
      p := p ++ [("REC-57", "ID", s!"ID {← showSlot rid} is already in the register")]
  for (field, want, art) in [("CITES", "RESULT", "a RESULT"), ("ASSUMPTIONS", "ASSUMPTION", "an ASSUMPTION")] do
    for x in V.members (V.get? record field) do
      if reg.cls x != some want then
        p := p ++ [("REC-58", field, s!"{field} member {← showSlot x} is not {art} of the register")]
        break
      if !standing (reg.word x) then
        p := p ++ [("REC-59", field, s!"{field} member {← showSlot x} does not stand ({reg.word x})")]
        break
  let cls := getOr record "CLASS"
  if cls == .str "CORROBORATION" || cls == .str "VERIFICATION" then
    if let some (.str t) := V.get? record "TARGET" then
      if reg.cls t != some "RESULT" then
        p := p ++ [("REC-58", "TARGET", s!"TARGET {← showSlot t} is not a RESULT of the register")]
      else if !(["PROVISIONAL", "ESTABLISHED", "HELD"].contains (reg.word t)) then
        p := p ++ [("REC-59", "TARGET", s!"TARGET {← showSlot t} does not stand ({reg.word t})")]
  if let some (.str s) := V.get? record "SUPERSEDES" then
    if (reg.get? s).map (getOr · "CLASS") != some cls then
      p := p ++ [("REC-58", "SUPERSEDES", s!"SUPERSEDES {← showSlot s} is not a {← showArg cls} of the register")]
    else if !standing (reg.word s) then
      p := p ++ [("REC-59", "SUPERSEDES", s!"SUPERSEDES {← showSlot s} does not stand ({reg.word s})")]
    else
      let a := ((reg.get? s).map (getOr · "AUTHOR")).getD .null
      let b := getOr record "AUTHOR"
      if !decided && a != b then
        p := p ++ [("REC-60", "SUPERSEDES",
          s!"SUPERSEDES {← showSlot s} was authored by {← showArg a}, not {← showArg b}")]
  for b in V.members (V.get? record "LITERATURE") do
    if !entryIds.contains b then
      p := p ++ [("REC-61", "LITERATURE", s!"LITERATURE member {← showSlot b} is not a landed entry of the UWC")]
      break
  return if p.isEmpty then okV else refused p

/-! ## 6 The withdrawal -/

/-- v1's `_rid_list`: a list of distinct record identifiers. -/
def ridList? : Value → Option (List String)
  | .arr xs => do
    let ids ← xs.mapM (fun | .str s => if isRid s then some s else none | _ => none)
    if ids.eraseDups.length == ids.length then some ids else none
  | _ => none

/-- The records a withdrawal reaches from `root` (functions 6.1): a keyed record is
reached when a member of its CITES or ASSUMPTIONS is root or a reached record; a member of
`ss` is reached but not walked past. -/
def reachFrom (reg : Register) (root : String) (ss : List String) : List String :=
  go (reg.keyed.length + 1) [root] []
where
  go : Nat → List String → List String → List String
    | 0, _, reached => reached
    | _, [], reached => reached
    | n + 1, cur :: frontier, reached =>
      let new := reg.keyed.filterMap fun (rid, r) =>
        if reached.contains rid || rid == root then none
        else if (V.members (V.get? r "CITES")).contains cur ||
            (V.members (V.get? r "ASSUMPTIONS")).contains cur then some rid
        else none
      let new := new.eraseDups
      go n ((new.filter fun r => !ss.contains r) ++ frontier) (reached ++ new)

/-- v1's `withdrawal_scope(register, root, still_stands)`: the cascade, `[[id, word],
...]` sorted by id. -/
def withdrawalScope (register root stillStands : Value) : M Value := do
  let reg ← match ← readRegister register with
    | .error b => return b
    | .ok reg => pure reg
  let r ← match root with
    | .str s =>
      if (reg.get? s).isSome then pure s
      else return one "REC-52" "-" s!"record {← showArg root} is not in the register"
    | _ => return one "REC-52" "-" s!"record {← showArg root} is not in the register"
  let some ss := ridList? stillStands
    | return ← badArg "still_stands" stillStands "a list of record identifiers"
  let reached := reachFrom reg r ss
  let probs : List Problem := (ss.filter fun x => !reached.contains x).map fun x =>
    ("REC-62", "-", s!"STILL STANDS member {x} is not reached by the withdrawal")
  unless probs.isEmpty do return refused probs
  let casc := (sortStrings (reached.filter fun x => !ss.contains x)).filter fun rid =>
    let g := reg.gradeNow rid
    g == "PROVISIONAL" || g == "ESTABLISHED"
  return okWith [.arr (casc.map fun rid => .arr [.str rid, .str (reg.word rid)])]

/-- v1's `ACT_KEYS`. -/
def actKeys : List String :=
  ["cause", "withdrawn", "withdrawn_by", "status_set", "prior_status", "superseded_by",
   "locus_gap", "still_stands", "cascade", "tps_version", "d_tms"]

/-- v1's `CAUSES`. -/
def causes : List String := ["SR1", "SR5", "AUDIT", "AUTHOR", "SUPERSEDED", "INHERITED"]

/-- v1's `CAUSE_SETS`. -/
def causeSets : String → List String
  | "SR1" | "SR5" => ["REFUTED"]
  | "AUTHOR" | "SUPERSEDED" => ["WITHDRAWN"]
  | _ => ["REFUTED", "WITHDRAWN"]

/-- v1's `_pair_list_ok`: `[id, word]` pairs, the ids distinct record identifiers in code
point order, each word a status word. -/
def pairListOk (v : Value) : Bool :=
  pairsOk v &&
    let ps := pairsOf v
    let ids := ps.map Prod.fst
    ids.all isRid && ids.eraseDups.length == ids.length && ids == sortStrings ids &&
      ps.all fun p => statusWordList.contains p.2

/-- A string value that is a record identifier (v1's `_m(_RID, v)`). -/
def ridValue : Value → Bool
  | .str s => isRid s
  | _ => false

/-- v1's `_act`: the act's problems (REC-63 alone, or REC-64 per key and REC-65). -/
def actProblems (act : Value) : M (List Problem) := do
  let keysOk := V.isObj act && sortStrings (V.keys act) == sortStrings actKeys
  unless keysOk do return [("REC-63", "-", "act is not a withdrawal act")]
  let a (k : String) : Value := getOr act k
  let mut p : List Problem := []
  let bad (key form : String) : M Problem := do
    return ("REC-64", key, s!"{key} {← showArg (a key)} is not {form}")
  let cause := a "cause"
  let causeOk := match cause with | .str c => causes.contains c | _ => false
  if !causeOk then p := p ++ [← bad "cause" "one of SR1, SR5, AUDIT, AUTHOR, SUPERSEDED or INHERITED"]
  if !ridValue (a "withdrawn") then p := p ++ [← bad "withdrawn" "a record identifier"]
  let wbOk ← match a "withdrawn_by" with
    | .str s => isText s
    | _ => pure false
  if !wbOk then p := p ++ [← bad "withdrawn_by" "a text"]
  let c := strOf cause
  if causeOk && !((causeSets c).any fun s => a "status_set" == .str s) then
    p := p ++ [← bad "status_set" s!"the grade cause {c} sets"]
  if c == "INHERITED" && causeOk then
    if a "prior_status" != .str "PROVISIONAL" then p := p ++ [← bad "prior_status" "PROVISIONAL"]
  else if !(["PROVISIONAL", "ESTABLISHED", "HELD"].any fun s => a "prior_status" == .str s) then
    p := p ++ [← bad "prior_status" "a status word of a record that stands or is held"]
  if cause == .str "SUPERSEDED" then
    if !ridValue (a "superseded_by") then p := p ++ [← bad "superseded_by" "a record identifier"]
  else if a "superseded_by" != .str "" then p := p ++ [← bad "superseded_by" "empty"]
  if cause == .str "SR5" then
    if a "locus_gap" != .str "" && !ridValue (a "locus_gap") then
      p := p ++ [← bad "locus_gap" "a record identifier"]
  else if a "locus_gap" != .str "" then p := p ++ [← bad "locus_gap" "empty"]
  if cause == .str "AUDIT" then
    if !pairListOk (a "still_stands") then
      p := p ++ [← bad "still_stands" "a sorted list of [id, word] pairs"]
  else if a "still_stands" != .arr [] then p := p ++ [← bad "still_stands" "empty"]
  if cause == .str "INHERITED" then
    if a "cascade" != .arr [] then p := p ++ [← bad "cascade" "empty"]
  else if !pairListOk (a "cascade") then p := p ++ [← bad "cascade" "a sorted list of [id, word] pairs"]
  if !(match a "tps_version" with | .str s => isVersion s | _ => false) then
    p := p ++ [← bad "tps_version" "a version n.n.n"]
  if !(match a "d_tms" with | .str s => isHex64 s | _ => false) then
    p := p ++ [← bad "d_tms" "64 lowercase hexadecimal characters"]
  if p.isEmpty then
    let names := strOf (a "withdrawn") :: (pairsOf (a "still_stands")).map Prod.fst ++
      (pairsOf (a "cascade")).map Prod.fst
    for i in sortStrings names.eraseDups do
      if names.count i > 1 then p := p ++ [("REC-65", "-", s!"{i} is named twice")]
  return p

/-- v1's `_act_fields`: the `TPC-WITHDRAW` form 1 field list. -/
def actFields (act : Value) : List Value :=
  let a (k : String) : Value := getOr act k
  let pairs (k : String) : List Value :=
    let ps := pairsOf (a k)
    .int ps.length :: ps.flatMap fun (i, w) => [.str i, .str w]
  [.str "TPC-WITHDRAW", .str "1", a "cause", a "withdrawn", a "withdrawn_by", a "status_set",
   a "prior_status", a "superseded_by", a "locus_gap"] ++ pairs "still_stands" ++ pairs "cascade" ++
   [a "tps_version", a "d_tms"]

/-- v1's `withdrawal_preimage(act)`. -/
def withdrawalPreimage (act : Value) : M Value := do
  let p ← actProblems act
  unless p.isEmpty do return refused p
  return okWith [.arr (actFields act)]

/-- v1's `withdrawal_record(withdrawal_id, act)`: the positional WITHDRAWAL, its digest
over the act's field list. -/
def withdrawalRecord (withdrawalId act : Value) : M Value := do
  let mut p ← actProblems act
  if p.head?.map (·.1) == some "REC-63" then return refused p
  if !ridValue withdrawalId then
    p := p ++ [("REC-64", "withdrawal_id", s!"withdrawal_id {← showArg withdrawalId} is not a record identifier")]
  unless p.isEmpty do return refused p
  let a (k : String) : Value := getOr act k
  let d := Digest.digestFields (digestFields (actFields act))
  return okWith [.arr [withdrawalId, .str "WITHDRAWAL", a "cause", a "withdrawn", a "withdrawn_by",
    a "status_set", a "prior_status", a "superseded_by", a "locus_gap", a "still_stands",
    a "cascade", a "tps_version", a "d_tms", .str d]]

/-! ## 13 Named gaps -/

/-- v1's `GAP_TEMPLATES`. -/
def gapTemplate : String → Option String
  | "IC2" => some "The DOF {d} is tied by no TrM entry (IC2)."
  | "UNDER" => some "The unknown DOF {d} is determined by no form (UNDER)."
  | "SR5_LOCUS" => some "The ASSUMPTIONS {ids} lie outside the closer record's closure in the withdrawal {t} (SR5)."
  | "SR7_ASSUMPTIONS" => some "The ASSUMPTIONS {ids} of an L record are contradicted by {t} (SR7)."
  | "SR7_DOMAIN" => some "{t} contradicts an L record whose a(r) is 0: a finding against the TFK DOMAIN (SR7)."
  | _ => none

/-- v1's `_gap`: the NAMED_GAP record, checked at landing, then digested. -/
def gap (rid source against trigger landed tps : Value) : M Value := do
  let strsOnly := V.strList? against
  let ag : Value := match strsOnly with
    | some xs => V.strs (sortStrings xs)
    | none => against
  let mut r : Value := .obj [("ID", rid), ("CLASS", .str "NAMED_GAP"), ("GRADE", .str "NOT GRADED"),
    ("LANDED_BY", .str "TPX"), ("LANDED", landed), ("TPS", tps), ("SOURCE", source), ("AGAINST", ag),
    ("TRIGGER", trigger), ("STATE", .str "OPEN")]
  match source, trigger, strsOnly with
  | .str s, .str t, some xs =>
    if let some tmpl := gapTemplate s then
      let ids := ", ".intercalate (sortStrings xs)
      r := V.set r "STATEMENT" (.str (((tmpl.replace "{d}" ids).replace "{ids}" ids).replace "{t}" t))
  | _, _, _ => pure ()
  let c ← recordCheckM r .null .null (.str "LANDED")
  unless c.problems.isEmpty do return c.result
  match ← recordDigestM r with
  | .arr [.str "OK", d] => return okWith [V.set r "DIGEST" d]
  | other => return other

/-- v1's `_ident_list`. -/
def identList? : Value → Option (List String)
  | .arr xs => xs.mapM (fun | .str s => if Zone.isIdent s then some s else none | _ => none)
  | _ => none

/-- v1's `gap_records(prefix, ic2, under, trigger, landed, tps)`: one NAMED_GAP per IC2
DOF, then per UNDER DOF, each in code point order, numbered from 2. -/
def gapRecords (pre ic2 under trigger landed tps : Value) : M Value := do
  let some l2 := identList? ic2 | return ← badArg "ic2" ic2 "a list of identifiers"
  let some lu := identList? under | return ← badArg "under" under "a list of identifiers"
  unless (match landed with | .str s => utcOk s | _ => false) do
    return ← badArg "landed" landed "a UTC time"
  unless (match tps with | .str s => isVersion s | _ => false) do
    return ← badArg "tps" tps "a version n.n.n"
  let mut p : List Problem := []
  for (name, l) in [("ic2", l2), ("under", lu)] do
    for d in sortStrings l.eraseDups do
      if l.count d > 1 then p := p ++ [("REC-89", "-", s!"{name} repeats {d}")]
  unless p.isEmpty do return refused p
  let px := strOf pre
  let mut out : List Value := []
  let mut n := 2
  for (src, l) in [("IC2", l2), ("UNDER", lu)] do
    for d in sortStrings l do
      match ← gap (.str s!"{px}-{n}") (.str src) (V.strs [d]) trigger landed tps with
      | .arr [.str "OK", g] =>
        out := out ++ [g]
        n := n + 1
      | other => return other
  return okWith [.arr out]

/-- v1's `gap_record(id, source, against, trigger, landed, tps)`. -/
def gapRecord (rid source against trigger landed tps : Value) : M Value :=
  gap rid source against trigger landed tps

/-- v1's `_closure`: the ASSUMPTIONS of `rid` and of every record it CITES, transitively,
through keyed records. Each step pops one ID; an ID is pushed only by the visit of a
keyed record, once per record, so the steps are at most one more than the CITES of the
register. -/
def assumptionsClosure (reg : Register) (rid : String) : List String :=
  go (reg.keyed.length + 1 + (reg.keyed.map fun (_, r) => (V.members (V.get? r "CITES")).length).sum)
    [rid] [] []
where
  go : Nat → List String → List String → List String → List String
    | 0, _, _, acc => acc
    | _, [], _, acc => acc
    | n + 1, cur :: stack, seen, acc =>
      if seen.contains cur then go n stack seen acc
      else
        match reg.get? cur with
        | none => go n stack seen acc
        | some r =>
          go n (V.members (V.get? r "CITES") ++ stack) (cur :: seen) (acc ++ V.members (V.get? r "ASSUMPTIONS"))

/-- The TrM's entries by NAME (v1's `_trm_entries`, the last of a NAME kept). -/
def trmEntries (tfk : Value) : List (String × Value) :=
  (((listOr ((V.get? tfk "TrM").getD .null) "ENTRIES").getD []).filterMap fun e =>
    (V.getStr? e "NAME").map fun n => (n, e)).reverse

/-- v1's `gap_view(gap, records, tfk)`: the standing records a gap bears on. -/
def gapView (g records tfk : Value) : M Value := do
  let reg ← match ← readRegister records "records" with
    | .error b => return b
    | .ok reg => pure reg
  unless V.get? g "CLASS" == some (.str "NAMED_GAP") && V.isArr (getOr g "AGAINST") do
    return ← badArg "gap" g "a NAMED_GAP record"
  unless tfk != .null && assemblyOk tfk do return one "REC-39" "-" "the TFK is not readable"
  let against := V.members (V.get? g "AGAINST")
  let ents := trmEntries tfk
  let src := getOr g "SOURCE"
  let out := reg.sortedIds.filter fun rid =>
    standing (reg.word rid) &&
      let r := (reg.get? rid).getD .null
      if src == .str "IC2" || src == .str "UNDER" then
        let refs := V.members (V.get? r "REFS")
        let named := V.members (V.get? r "ENTRIES") ++ (match V.get? r "QUANTITY" with
          | some (.str q) => [q] | _ => [])
        against.any refs.contains ||
          named.any fun n => match ents.lookup n with
            | some e => match V.get? e "DOF" with
              | some (.str d) => against.contains d
              | _ => false
            | none => false
      else if src == .str "SR5_LOCUS" || src == .str "SR7_ASSUMPTIONS" then
        (assumptionsClosure reg rid).any against.contains
      else false
  return okWith [V.strs out]

/-- v1's `gap_state(state, date, what)`: the STATE line. -/
def gapState (state date what : Value) : M Value := do
  let st := strOf state
  unless V.isStr state && (st == "OPEN" || st == "SETTLED" || st == "STANDING") do
    return one "REC-90" "-" s!"state {← showArg state} is not OPEN, SETTLED or STANDING"
  if st == "OPEN" then return okWith [.str "OPEN"]
  let mut p : List Problem := []
  unless (match date with | .str s => dayOk s | _ => false) do
    p := p ++ [("REC-50", "-", s!"date {← showJson date} is not a date YYYY-MM-DD")]
  if st == "SETTLED" then
    unless (match ridList? what with | some (_ :: _) => true | _ => false) do
      p := p ++ [("REC-50", "-", s!"what {← showJson what} is not a list of record identifiers")]
  else
    let ok ← match what with
      | .str s => isText s
      | _ => pure false
    unless ok do p := p ++ [("REC-50", "-", s!"what {← showJson what} is not a text")]
  unless p.isEmpty do return refused p
  if st == "SETTLED" then
    return okWith [.str s!"SETTLED {strOf date} BY {", ".intercalate (sortStrings (V.members (some what)))}"]
  return okWith [.str s!"STANDING {strOf date} BY {strOf what}"]

/-- v1's `eom0_open(records)`: an UNDER gap is OPEN. -/
def eom0Open (records : Value) : M Value := do
  match ← readRegister records "records" with
  | .error b => return b
  | .ok reg =>
    return okWith [.bool (reg.keyed.any fun (_, r) =>
      V.get? r "CLASS" == some (.str "NAMED_GAP") && V.get? r "SOURCE" == some (.str "UNDER") &&
        V.get? r "STATE" == some (.str "OPEN"))]

/-! ## 14 Verification -/

/-- v1's `verification_order(target_push, verification_push, source_push)`. -/
def verificationOrder (t v s : Value) : M Value := do
  let nat? : Value → Option Int
    | .int n => if 0 ≤ n then some n else none
    | _ => none
  match nat? t, nat? v, (s == .null || (nat? s).isSome) with
  | some tp, some vp, true =>
    if vp ≤ tp then return one "REC-91" "-" "the VERIFICATION lands in its TARGET's push or before it"
    match nat? s with
    | some sp =>
      if sp < tp then return worded "INSPECT" "the SOURCE entry landed before the TARGET"
      else return okV
    | none => return okV
  | _, _, _ => badArg "pushes" (.arr [t, v, s]) "integers from 0"

/-! ## 15 Promotion, the entry view, successors -/

/-- v1's `FCLASS`. -/
def fclasses : List String := ["F1", "F2", "F3"]

/-- v1's `_floor`: the TMS's PROMOTION_FLOOR, F2 when absent or not a falsifier class. -/
def promotionFloor (tfk : Value) : String :=
  match V.get? tfk "TMS" with
  | some tms@(.obj _) =>
    match V.get? tms "PARAMETERS" with
    | some pm@(.obj _) =>
      match V.get? pm "PROMOTION_FLOOR" with
      | none => "F2"
      | some (.str f) => if fclasses.contains f then f else "F2"
      | some _ => "F2"
    | _ => "F2"
  | _ => "F2"

/-- v1's `_words_arg`: a map of status words. -/
def wordsArg? : Value → Option (List (String × String))
  | .obj ms => ms.mapM (fun | (k, .str w) => some (k, w) | _ => none)
  | _ => none

/-- The IDs a record's CITES and ASSUMPTIONS reach, transitively through keyed records, the
record itself included (v1's closure in `_eligible`). -/
def citeClosure (reg : Register) (rid : String) : List String :=
  go (reg.keyed.length + 1 + (reg.keyed.map fun (_, r) =>
      (V.members (V.get? r "CITES")).length + (V.members (V.get? r "ASSUMPTIONS")).length).sum)
    [rid] [] [rid]
where
  go : Nat → List String → List String → List String → List String
    | 0, _, _, acc => acc
    | _, [], _, acc => acc
    | n + 1, cur :: stack, seen, acc =>
      if seen.contains cur then go n stack seen acc
      else
        match reg.get? cur with
        | none => go n stack seen acc
        | some r =>
          let nxt := V.members (V.get? r "CITES") ++ V.members (V.get? r "ASSUMPTIONS")
          go n (nxt ++ stack) (cur :: seen) (acc ++ nxt)

/-- v1's `_eligible`: `["ELIGIBLE", class_read, floor]` or `["NOT", reasons]`. -/
def eligible (reg : Register) (words : List (String × String)) (ents : List (String × Value))
    (floor : String) (audits : List String) (rid : String) : M Value := do
  let r := (reg.get? rid).getD .null
  if V.get? r "CLASS" != some (.str "RESULT") then return .arr [.str "NOT", V.strs ["not a RESULT"]]
  let mut reasons : List String := []
  let w := (words.lookup rid).getD "NOT GRADED"
  if w != "PROVISIONAL" then reasons := reasons ++ [s!"does not stand as PROVISIONAL ({← showSlot w})"]
  if !V.has r "DOMAIN" then reasons := reasons ++ ["DOMAIN is absent"]
  if !V.has r "DOMAIN_CONDITION" then reasons := reasons ++ ["DOMAIN_CONDITION is absent"]
  let entries := V.members (V.get? r "ENTRIES")
  if entries.isEmpty then reasons := reasons ++ ["ENTRIES is absent or empty"]
  let cs := (getOr r "FALSIFIER_CLASS") :: entries.filterMap fun e =>
    (ents.lookup e).map fun x => getOr x "FALSIFIER_CLASS"
  let cs := cs.filterMap (fun | .str c => if fclasses.contains c then some c else none | _ => none)
  let classRead := (sortStrings cs).headD "F1"
  if decide (classRead < floor) then
    reasons := reasons ++ [s!"FALSIFIER_CLASS {classRead} is below PROMOTION_FLOOR {floor}"]
  for c in sortStrings (V.members (V.get? r "CITES")) do
    if (words.lookup c).getD "NOT GRADED" != "ESTABLISHED" then
      reasons := reasons ++ [s!"cites {c}, which is not ESTABLISHED"]
  let cl := citeClosure reg rid
  for a in sortStrings (audits.filter cl.contains).eraseDups do
    reasons := reasons ++ [s!"an audit block is open on {a}"]
  if !reasons.isEmpty then return .arr [.str "NOT", V.strs reasons]
  return .arr [.str "ELIGIBLE", .str classRead, .str floor]

/-- v1's `_promotion_args`: the register, the words map, the Research Assembly and the open
audits, or the refusal. -/
def promotionArgs (records words tfk openAudits : Value) :
    M (Except Value (Register × List (String × String) × List String)) := do
  let reg ← match ← readRegister records "records" with
    | .error b => return .error b
    | .ok reg => pure reg
  let some ws := wordsArg? words | return .error (← badArg "words" words "a map of status words")
  unless tfk != .null && assemblyOk tfk do return .error (one "REC-39" "-" "the TFK is not readable")
  let some audits := ridList? openAudits
    | return .error (← badArg "open_audits" openAudits "a list of record identifiers")
  return .ok (reg, ws, audits)

/-- v1's `promotion_eligible(records, words, tfk, open_audits, id)`. -/
def promotionEligible (records words tfk openAudits rid : Value) : M Value := do
  match ← promotionArgs records words tfk openAudits with
  | .error b => return b
  | .ok (reg, ws, audits) =>
    match rid with
    | .str s =>
      if (reg.get? s).isSome then eligible reg ws (trmEntries tfk) (promotionFloor tfk) audits s
      else return one "REC-52" "-" s!"record {← showArg rid} is not in the register"
    | _ => return one "REC-52" "-" s!"record {← showArg rid} is not in the register"

/-- Set a word in a words map (v1's `words[k] = w`). -/
def setWord (ws : List (String × String)) (k w : String) : List (String × String) :=
  if ws.any (·.1 == k) then ws.map fun p => if p.1 == k then (k, w) else p else ws ++ [(k, w)]

/-- v1's `_fixed_point`: rounds of promotion, each round's eligible candidates ESTABLISHED
for the next, until a round promotes none; the promoted `[id, class_read, floor]` sorted. -/
def fixedPoint (reg : Register) (words : List (String × String)) (tfk : Value)
    (audits candidates : List String) : M (List Value) :=
  go (candidates.length + 1) words []
where
  go : Nat → List (String × String) → List (String × String × String) → M (List Value)
    | 0, _, promoted => pure (done promoted)
    | n + 1, ws, promoted => do
      let mut rnd : List (String × String × String) := []
      for rid in sortStrings candidates do
        if promoted.any (·.1 == rid) then continue
        match ← eligible reg ws (trmEntries tfk) (promotionFloor tfk) audits rid with
        | .arr [.str "ELIGIBLE", .str c, .str f] => rnd := rnd ++ [(rid, c, f)]
        | _ => pure ()
      if rnd.isEmpty then return done promoted
      go n (rnd.foldl (fun w t => setWord w t.1 "ESTABLISHED") ws) (promoted ++ rnd)
  done (promoted : List (String × String × String)) : List Value :=
    (promoted.mergeSort fun a b => decide (a.1 ≤ b.1)).map fun (i, c, f) => V.strs [i, c, f]

/-- v1's `promotion_pass(records, words, tfk, open_audits)`. -/
def promotionPass (records words tfk openAudits : Value) : M Value := do
  match ← promotionArgs records words tfk openAudits with
  | .error b => return b
  | .ok (reg, ws, audits) =>
    let cands := (reg.keyed.filter fun (_, r) => V.get? r "CLASS" == some (.str "RESULT")).map Prod.fst
    return okWith [.arr (← fixedPoint reg ws tfk audits cands)]

/-- A promoted triple `[id, class_read, floor]`. -/
def triple? : Value → Option (String × String × String)
  | .arr [.str i, .str c, .str f] =>
    if isRid i && fclasses.contains c && fclasses.contains f then some (i, c, f) else none
  | _ => none

/-- v1's `promotion_record(promotion_id, landing_block, promoted)`: the positional
PROMOTION, its digest over the `TPC-PROMOTE` form 1 field list. -/
def promotionRecord (promotionId landingBlock promoted : Value) : M Value := do
  unless ridValue promotionId do return ← badArg "promotion_id" promotionId "a record identifier"
  let lbOk ← match landingBlock with
    | .str s => isText s
    | _ => pure false
  unless lbOk do return ← badArg "landing_block" landingBlock "a text"
  let ts? := match promoted with
    | .arr xs => xs.mapM triple?
    | _ => none
  let some ts := ts?.bind fun ts =>
      if (ts.map (·.1)).eraseDups.length == ts.length then some ts else none
    | return ← badArg "promoted" promoted "a list of [id, class_read, floor] triples"
  if ts.isEmpty then return one "REC-97" "-" "a PROMOTION with nothing promoted is never written"
  let pr := ts.mergeSort fun a b => decide (a.1 ≤ b.1)
  let fields : List Digest.Field :=
    [.text "TPC-PROMOTE", .text "1", .text (strOf landingBlock), .int pr.length] ++
      pr.flatMap fun (i, c, f) => [.text i, .text c, .text f]
  let d := Digest.digestFields fields
  return okWith [.arr [promotionId, .str "PROMOTION", landingBlock,
    .arr (pr.map fun (i, c, f) => V.strs [i, c, f]), .str d]]

/-- v1's `entry_view(records, words, tfk, entry)`. -/
def entryView (records words tfk entry : Value) : M Value := do
  let reg ← match ← readRegister records "records" with
    | .error b => return b
    | .ok reg => pure reg
  let some ws := wordsArg? words | return ← badArg "words" words "a map of status words"
  unless tfk != .null && assemblyOk tfk do return one "REC-39" "-" "the TFK is not readable"
  let ents := trmEntries tfk
  let e ← match entry with
    | .str s =>
      if (ents.lookup s).isSome then pure s
      else return one "REC-74" "-" s!"quantity {← showArg entry} is not an entry of the TrM"
    | _ => return one "REC-74" "-" s!"quantity {← showArg entry} is not an entry of the TrM"
  let dof := ((ents.lookup e).map (getOr · "DOF")).getD .null
  let mut recs : List Value := []
  let mut gaps : List Value := []
  let mut vers : List Value := []
  let mut es : Option (String × String) := none
  for rid in reg.sortedIds do
    let r := (reg.get? rid).getD .null
    let c := getOr r "CLASS"
    if c == .str "RESULT" && ((V.members (V.get? r "ENTRIES")).contains e || V.get? r "QUANTITY" == some (.str e)) then
      recs := recs ++ [V.strs [rid, (ws.lookup rid).getD "NOT GRADED"]]
    else if c == .str "NAMED_GAP" && (V.get? r "SOURCE" == some (.str "IC2") || V.get? r "SOURCE" == some (.str "UNDER")) &&
        V.get? r "STATE" == some (.str "OPEN") &&
        (match dof with | .str d => (V.members (V.get? r "AGAINST")).contains d | _ => false) then
      gaps := gaps ++ [.str rid]
    else if c == .str "VERIFICATION" && (match V.get? r "EXTERNAL" with
        | some x@(.obj _) => V.get? x "QUANTITY" == some (.str e)
        | _ => false) then
      vers := vers ++ [.str rid]
    else if c == .str "ENTRY_STATUS" && V.get? r "ENTRY" == some (.str e) then
      let key := ((V.getStr? r "LANDED").getD "", rid)
      match es with
      | none => es := some key
      | some k => if decide (k.1 < key.1) || (k.1 == key.1 && decide (k.2 < key.2)) then es := some key
  return okWith [.obj [("ENTRY", .str e), ("RECORDS", .arr recs), ("GAPS", .arr gaps),
    ("VERIFICATIONS", .arr vers), ("ENTRY_STATUS", (es.map fun k => Value.str k.2).getD .null)]]

/-- v1's `TMSC_FIELDS` and `YARD_FIELDS`, with `LIM_FIELDS`. -/
def constantFields : List String := ["NAME", "VALUE"]
/-- A yardstick's fields. -/
def yardstickFields : List String := ["NAME", "KEY", "LIMITING"]
/-- A limiting case's fields. -/
def limitingFields : List String := ["DOMAIN", "KEY"]

/-- v1's `_entry_list` for the Criteria Set's CONSTANTS and YARDSTICKS, as the tree `_node`
encodes (every string as its canonical text): each present field's name and canonical
value. -/
def entryTree (e : Value) (fields : List String) : M Value := do
  let mut out : List Value := []
  for f in fields do
    match V.get? e f with
    | none => pure ()
    | some v =>
      let cv ← if f == "KEY" then
          .arr <$> (V.members (some v)).mapM fun x => do return .str (Criteria.canonicalTerm (← text x))
        else if f == "LIMITING" then do
          let os := match v with | .arr os => os | _ => []
          let keyed ← os.mapM fun o => do return (← text (strOf (getOr o "DOMAIN")), o)
          let sorted := keyed.mergeSort fun a b => decide (a.1 ≤ b.1)
          .arr <$> sorted.mapM fun (_, o) => limitingTree o
        else if f == "VALUE" then
          pure (match v with
            | .str s => ((Decimal.canon s).map fun c => Value.str c).getD .null
            | _ => .null)
        else match v with
          | .str s => Value.str <$> text s
          | _ => pure v
      out := out ++ [.str f, cv]
  return .arr out
where
  /-- A limiting case's `_entry_list`. -/
  limitingTree (o : Value) : M Value := do
    let mut out : List Value := []
    for f in limitingFields do
      match V.get? o f with
      | none => pure ()
      | some v =>
        let cv ← if f == "KEY" then
            .arr <$> (V.members (some v)).mapM fun x => do return .str (Criteria.canonicalTerm (← text x))
          else match v with
            | .str s => Value.str <$> text s
            | _ => pure v
        out := out ++ [.str f, cv]
    return .arr out

/-- v1's `_zone_sub`: a part of the Criteria Set as its preimage's tree. -/
def zoneSub (tms : Value) (part : String) (fields : List String) : M Value := do
  let es := (listOr tms part).getD []
  let keyed ← es.mapM fun e => do return (← text (strOf (getOr e "NAME")), e)
  let sorted := keyed.mergeSort fun a b => decide (a.1 ≤ b.1)
  return .arr [.str part, .arr (← sorted.mapM fun (_, e) => entryTree e fields)]

/-- v1's `reaudit_scope(src, dst)`: the checks a successor's re-audit runs. -/
def reauditScope (src dst : Value) : M Value := do
  for (name, v) in [("src", src), ("dst", dst)] do
    let good ← (do
      unless V.isObj v && V.has v "D_TPK" && V.has v "D_TRM" && V.has v "TMS" do return false
      let tms := getOr v "TMS"
      unless V.isObj tms && V.isObj (getOr tms "PARAMETERS") do return false
      match Criteria.wellFormed Zone.UnitHook.calculator (toZone tms) with
      | .checked ps => return ps.isEmpty
      | .owed _ => throw (.number "the Criteria Set's check owes its verdict") : M Bool)
    unless good do return ← badArg name v "an object with D_TPK, D_TRM and TMS"
  if getOr src "D_TPK" != getOr dst "D_TPK" || getOr src "D_TRM" != getOr dst "D_TRM" then
    return okWith [V.strs ["ALL"]]
  let a := getOr src "TMS"
  let b := getOr dst "TMS"
  let pa := getOr a "PARAMETERS"
  let pb := getOr b "PARAMETERS"
  let canonParam (pm : Value) (name : String) : M (Option String) := do
    let v := getOr pm name
    if name == "K" then
      match v with
      | .str s => return Decimal.canon s
      | _ => return some (cj v)
    if name == "STEP_CONVENTION" then
      match v with
      | .str s => return some (← text s)
      | _ => return some (cj v)
    let dflt : Option String := match name with
      | "IC2_POLICY" => some "GAP"
      | "PROMOTION_FLOOR" => some "F2"
      | "STRUCTURE_CHECK" => some "ON"
      | _ => none
    match dflt, V.get? pm name with
    | some d, none => return some (cj (.str d))
    | _, _ => return some (cj v)
  let mut checks : List String := []
  for (name, adds) in [("K", ["SR3", "SR8"]), ("N_X", ["SR6"]), ("STEP_CONVENTION", ["SR4", "SR5"]),
      ("PROMOTION_FLOOR", ["PROMOTION"]), ("STRUCTURE_CHECK", ["STRUCTURE", "EOM-0"]),
      ("S_MAX", ["T3"]), ("IC2_POLICY", ["IC2"])] do
    if (← canonParam pa name) != (← canonParam pb name) then checks := checks ++ adds
  let cz := (← zoneSub a "CONSTANTS" constantFields) != (← zoneSub b "CONSTANTS" constantFields)
  let yz := (← zoneSub a "YARDSTICKS" yardstickFields) != (← zoneSub b "YARDSTICKS" yardstickFields)
  if cz || yz then checks := checks ++ ["SR4", "SR5"]
  return okWith [V.strs (sortStrings checks.eraseDups)]

/-- v1's `repromote_batch(src_records, src_words, dst_records, dst_words, tfk,
open_audits)`: the successor's RESULTs inheriting an ESTABLISHED record,
promoted by the fixed point. -/
def repromoteBatch (srcRecords srcWords dstRecords dstWords tfk openAudits : Value) : M Value := do
  match ← readRegister srcRecords "src_records" with
  | .error b => return b
  | .ok _ =>
    let some sws := wordsArg? srcWords | return ← badArg "src_words" srcWords "a map of status words"
    match ← promotionArgs dstRecords dstWords tfk openAudits with
    | .error b => return b
    | .ok (reg, ws, audits) =>
      let cands := (reg.keyed.filter fun (_, r) =>
        V.get? r "CLASS" == some (.str "RESULT") &&
          match V.get? r "INHERITS" with
          | some (.str i) => sws.lookup i == some "ESTABLISHED"
          | _ => false).map Prod.fst
      return okWith [.arr (← fixedPoint reg ws tfk audits cands)]

/-! ## What version 1's text states, proved

tpm_record_functions 0.3.0, sections 4 and 6: a grade event applies only to a standing
grade and moves it away from standing (4.6); an inherited record never lands ESTABLISHED,
and keeps a predecessor's REFUTED or WITHDRAWN (4.8); a hold never clears a strike,
and a strike only marks REFUTED (4.7); the current grade is the highest given, never below
the record's own, and a NOT GRADED record stays so (4.2, RD-RS-28); a withdrawal's reach
never names its root (6.1), so neither does its cascade. -/

/-- A grade event applies only to PROVISIONAL or ESTABLISHED, and gives ESTABLISHED,
REFUTED or WITHDRAWN: never PROVISIONAL, never NOT GRADED. -/
theorem gradeNextOf_out {c g e o : String} (h : gradeNextOf c g e = some o) :
    (g = "PROVISIONAL" ∨ g = "ESTABLISHED") ∧
      (o = "ESTABLISHED" ∨ o = "REFUTED" ∨ o = "WITHDRAWN") := by
  unfold gradeNextOf at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    simp at h; subst h; exact ⟨.inl hc.2, .inl rfl⟩
  · split at h
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
      simp at h; subst h; exact ⟨hc.1.2, .inr (.inl rfl)⟩
    · split at h
      · rename_i _ _ hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
        simp at h; subst h; exact ⟨hc.1.2, .inr (.inr rfl)⟩
      · simp at h

/-- PROMOTE applies to a PROVISIONAL RESULT alone, and makes it ESTABLISHED. -/
theorem gradeNextOf_promote {c g o : String} (h : gradeNextOf c g "PROMOTE" = some o) :
    c = "RESULT" ∧ g = "PROVISIONAL" ∧ o = "ESTABLISHED" := by
  unfold gradeNextOf at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    simp at h; exact ⟨hc.1.2, hc.2, h.symm⟩
  · split at h
    · rename_i _ hc; simp at hc
    · split at h
      · rename_i _ _ hc; simp at hc
      · simp at h

/-- An inherited record never holds ESTABLISHED: a successor re-promotes it. -/
theorem inheritGradeOf_ne_established (c g : String) : inheritGradeOf c g ≠ "ESTABLISHED" := by
  unfold inheritGradeOf
  split
  · decide
  · split
    · rename_i _ hg
      simp only [Bool.or_eq_true, beq_iff_eq] at hg
      rcases hg with h | h <;> subst h <;> decide
    · decide

/-- A HOLD on a struck record leaves it REFUTED. -/
theorem statusNextOf_hold_refuted (c : String) {o : String}
    (h : statusNextOf c "REFUTED" "HOLD" = some o) : o = "REFUTED" := by
  unfold statusNextOf at h
  split at h
  · simp at h
  · simp at h; exact h.symm

/-- A STRIKE marks REFUTED, or does not apply. -/
theorem statusNextOf_strike {c s o : String} (h : statusNextOf c s "STRIKE" = some o) :
    o = "REFUTED" := by
  unfold statusNextOf at h
  split at h
  · simp at h
  · split at h
    · rename_i _ hc; simp at hc
    · split at h
      · split at h
        · simp at h; exact h.symm
        · simp at h
      · rename_i _ _ hc; simp at hc

/-- Choosing the higher-ranked grade never lowers the rank. -/
theorem rankOf_foldl (gs : List String) (b : String) :
    rankOf b ≤ rankOf (gs.foldl (fun b g => if rankOf g > rankOf b then g else b) b) := by
  induction gs generalizing b with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl]
    split
    · rename_i hgt
      exact Nat.le_trans (Nat.le_of_lt hgt) (ih g)
    · exact ih b

/-- A fold whose every step keeps or raises the rank keeps or raises it. -/
theorem rankOf_foldl_lists {f : String → List Value → String}
    (hf : ∀ b r, rankOf b ≤ rankOf (f b r)) :
    ∀ (l : List (List Value)) (b : String), rankOf b ≤ rankOf (l.foldl f b)
  | [], _ => Nat.le_refl _
  | r :: rs, b => Nat.le_trans (hf b r) (rankOf_foldl_lists hf rs (f b r))

/-- The current grade ranks at least as high as the record's own GRADE (RD-RS-28: grades
only move away from standing). -/
theorem Register.rank_le_gradeNow (reg : Register) (rid : String) :
    rankOf (((reg.get? rid).bind fun r => V.getStr? r "GRADE").getD "") ≤
      rankOf (reg.gradeNow rid) := by
  unfold Register.gradeNow
  dsimp only
  split
  · exact Nat.le_refl _
  · exact rankOf_foldl_lists (fun b _ => rankOf_foldl _ b) _ _

/-- A NOT GRADED record is NOT GRADED whatever names it. -/
theorem Register.gradeNow_notGraded (reg : Register) (rid : String)
    (h : ((reg.get? rid).bind fun r => V.getStr? r "GRADE").getD "" = "NOT GRADED") :
    reg.gradeNow rid = "NOT GRADED" := by
  unfold Register.gradeNow
  simp [h]

/-- The walk never reaches its root. -/
theorem reachFrom_go_root (reg : Register) (root : String) (ss : List String) :
    ∀ (n : Nat) (fr reached : List String), root ∉ reached →
      root ∉ reachFrom.go reg root ss n fr reached := by
  intro n
  induction n with
  | zero => intro fr reached h; simpa [reachFrom.go] using h
  | succ n ih =>
    intro fr reached h
    cases fr with
    | nil => simpa [reachFrom.go] using h
    | cons cur frontier =>
      simp only [reachFrom.go]
      apply ih
      simp only [List.mem_append, not_or]
      refine ⟨h, ?_⟩
      intro hm
      have := List.mem_eraseDups.mp hm
      simp [List.mem_filterMap] at this
      obtain ⟨_, _, _, ⟨_, hne⟩, _, heq⟩ := this
      exact hne heq

/-- A WITHDRAWAL the Calculator writes ends with SHA-256 of its act's field list; anything
else it answers is a refusal. -/
theorem withdrawalRecord_digest {i a v : Value} (h : withdrawalRecord i a = .ok v) :
    (∃ ps, v = refused ps) ∨
      ∃ xs, v = okWith [.arr xs] ∧
        xs.getLast? = some (.str (Digest.digestFields (digestFields (actFields a)))) := by
  unfold withdrawalRecord at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact Or.inl ⟨_, (Except.ok.inj h).symm⟩
    | exact Or.inr ⟨_, (Except.ok.inj h).symm, rfl⟩
    | simp at h

/-- A PROMOTION the Calculator writes ends with SHA-256 of its `TPC-PROMOTE` field list;
anything else it answers is a refusal. -/
theorem promotionRecord_digest {i b p v : Value} (h : promotionRecord i b p = .ok v) :
    (∃ ps, v = refused ps) ∨
      ∃ xs fs, v = okWith [.arr xs] ∧ xs.getLast? = some (.str (Digest.digestFields fs)) := by
  unfold promotionRecord at h
  simp only [bind, Except.bind, pure, Except.pure, badArg, one] at h
  repeat' split at h
  all_goals first
    | exact Or.inl ⟨_, (Except.ok.inj h).symm⟩
    | exact Or.inr ⟨_, _, (Except.ok.inj h).symm, rfl⟩
    | simp at h

/-- A withdrawal's reach never names its root, so its cascade never does (6.1). -/
theorem root_not_mem_reachFrom (reg : Register) (root : String) (ss : List String) :
    root ∉ reachFrom reg root ss :=
  reachFrom_go_root reg root ss _ _ _ (by simp)

end Principia.Record
