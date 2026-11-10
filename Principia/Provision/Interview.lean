import Principia.Provision.Expand
import Principia.Provision.Catalogue

/-!
# The interview and the NOT INCLUDED lines

v1's `interview_check` and `not_included_lines` (tpm_module_spec 0.2.0 5.4-5.5a, 6.6, 6.7;
TPS 5.22.4-5.22.6). Every draft answers one question, "Which of these interactions act on the
system you are modelling?", over the OFFERED Provisions, or answers NONE. The answer is bound to
the catalogue it was given over: each round records the number of lines then in force (AT) and
the OFFER it covered; a later round covers only the Provisions added since, or those it
re-selects. A claim is admitted PINNED when its version was OFFERED in the round that chose it,
or CARRIED when copied forward from a source certificate; a new claim of a version not OFFERED
is refused, as are a claim the answer did not choose, a choice no claim takes, and a pair that
excludes each other. The Provisions the answer has not yet covered are asked about (ASK).

The NOT INCLUDED lines of the check page: each covered Provision not chosen gives its
NOT_CHOSEN line, each chosen one its NOT_INCLUDED lines, each one the author edited by hand
its "Modified from" line, each question raised the line its answer selects, and last the
closing line of the closed world.
-/

namespace Principia.Provision

open Principia.Zone (Value Entry get? has getStr?)

/-- v1's `_declared_texts`: every text given is of a declared version, and its digest is the
declared one. -/
def declaredTexts (D : DigestHook) (texts : List Provision) (S : State) : Run Unit := do
  let sorted := texts.mergeSort fun a b => pairLe (a.id, a.version) (b.id, b.version)
  for M in sorted do
    let some r := S.versions.find? (M.id, M.version) | refuse ("MODULES: " ++ M.cv ++ " is not declared")
    if (← M.digest D) != r.digest then
      refuse ("MODULES: " ++ M.cv ++ ": the text's digest does not match the declaration")

/-- A list of `[ID, VERSION, DIGEST]` triples of strings, or `none`. -/
def triples? (v : Value) : Option (List (String × String × String)) := do
  let .arr xs := v | none
  xs.mapM fun
    | .arr [.str i, .str ver, .str d] => some (i, ver, d)
    | _ => none

/-- v1's `_carried`: the claims COPY-FORWARD brought, each declared with its digest. -/
def readCarried (carried : Value) (S : State) : Run (List (String × String × String)) := do
  let some ts := triples? carried | refuse "CARRIED: not a list of [ID, VERSION, DIGEST]"
  for (i, v, d) in ts do
    let some r := S.versions.find? (i, v) | refuse ("CARRIED " ++ i ++ " " ++ v ++ ": not declared")
    if r.digest != d then refuse ("CARRIED " ++ i ++ " " ++ v ++ ": DIGEST does not match the declaration")
  pure ts

/-- v1's `_modified`: the IDs the author edited by hand, each declared and none claimed. -/
def readModified (modified : Value) (S : State) (cls : List Claim) : Run (List (String × String)) := do
  let pairs? : Option (List (String × String)) := match modified with
    | .arr xs => xs.mapM fun (x : Value) => match x with
      | .arr [.str i, .str v] => some (i, v)
      | _ => none
    | _ => none
  let some ps := pairs? | refuse "MODIFIED: not a list of [ID, VERSION]"
  if let some d := leastDup (ps.map (·.1)) then refuse ("MODIFIED: duplicate module " ++ d)
  let out := ps.mergeSort pairLe
  for (i, v) in out do
    if (S.versions.find? (i, v)).isNone then refuse ("MODIFIED " ++ i ++ " " ++ v ++ ": not declared")
    if cls.any (·.id == i) then refuse ("MODIFIED " ++ i ++ " " ++ v ++ ": the ID is also claimed")
  pure out

/-- A round of the answer, read: the OFFER it covered and the IDs it chose. -/
structure Round where
  covered : List (String × String × String)
  chosen : List String
  deriving Repr, Inhabited

/-- v1's `_answer` (5.4): the rounds, each checked against the OFFER at its AT; for each ID the
latest round's entry and whether it chose it. -/
def readAnswer (answer : Value) (S : State) : Run (List (String × (String × String × String) × Bool)) := do
  let .arr rs := answer | refuse "ANSWER: not a list"
  if rs.isEmpty then refuse "INTERACTIONS: not answered"
  let n := S.lines
  let mut rounds : List Round := []
  let mut coveredIds : List String := []
  let mut prevAt : Option Nat := none
  let mut k := 0
  for rv in rs do
    k := k + 1
    let tag := s!"ANSWER ROUND {k}"
    let .obj r := rv | refuse (tag ++ ": not an object")
    fields tag r ["AT", "COVERED", "CHOSEN"] ["RESELECT"]
    let at_ ← match field r "AT" with
      | .int a => if 0 ≤ a && a ≤ n then pure a.toNat else refuse (tag ++ s!": AT is not a line count from 0 to {n}")
      | _ => refuse (tag ++ s!": AT is not a line count from 0 to {n}")
    if let some p := prevAt then
      if at_ ≤ p then refuse (tag ++ ": AT is not after the previous round's")
    let offer := S.offerAt at_
    let mut resel : List String := []
    if let some rsv := get? r "RESELECT" then
      let some xs := strList? rsv | refuse (tag ++ ": field RESELECT has the wrong type")
      unless strictlySorted xs do refuse (tag ++ ": RESELECT is not in code point order without repeats")
      for x in xs do
        unless coveredIds.contains x do refuse (tag ++ ": RESELECT " ++ x ++ " was not covered before")
        unless offer.any (·.1 == x) do refuse (tag ++ ": RESELECT " ++ x ++ " is not offered at AT")
      resel := xs
    let some cov := triples? (field r "COVERED") | refuse (tag ++ ": field COVERED has the wrong type")
    let want := if k == 1 then offer else offer.filter fun e => !coveredIds.contains e.1 || resel.contains e.1
    if k != 1 && want.isEmpty then refuse (tag ++ ": no module was added since the previous round")
    if cov != want then refuse (tag ++ ": COVERED is not the offer the round was given over")
    let chosen ← match field r "CHOSEN" with
      | .str "NONE" => pure []
      | ch =>
        match strList? ch with
        | none => refuse (tag ++ ": field CHOSEN has the wrong type")
        | some xs =>
          if xs.isEmpty then refuse (tag ++ ": CHOSEN is empty; the exclusive answer is NONE")
          unless strictlySorted xs do refuse (tag ++ ": CHOSEN is not in code point order without repeats")
          for x in xs do
            unless want.any (·.1 == x) do refuse (tag ++ ": CHOSEN " ++ x ++ " is not in COVERED")
          pure xs
    rounds := rounds ++ [⟨want, chosen⟩]
    coveredIds := coveredIds ++ want.map (·.1)
    prevAt := some at_
  let mut latest : List (String × (String × String × String) × Bool) := []
  for r in rounds do
    for e in r.covered do
      latest := (latest.filter (·.1 != e.1)) ++ [(e.1, e, r.chosen.contains e.1)]
  pure latest

/-- v1's `_questions` with `skip_fixed` (I7): each claim's answers are YES or NO to a
question, every question raised is answered and every answer answers one raised; a FIXED
answer is the expansion's to judge. -/
def checkQuestions (cls : List Claim) (find : Texts) : Run Unit := do
  let ids := cls.map (·.id)
  for c in cls do
    let some M := find c.id c.version | refuse ("CLAIM " ++ c.cv ++ ": no module text")
    checkAnswerWords c.cv c.answers
    let raised := (raisedQuestions M c ids).map (·.qid)
    for q in raised do
      unless has c.answers q do refuse ("CLAIM " ++ c.cv ++ ": question " ++ q ++ " is not answered")
    for k in keysOf c.answers do
      unless raised.contains k || k.startsWith "FIXED:" do
        refuse ("CLAIM " ++ c.cv ++ ": answer " ++ k ++ " answers no question raised")

/-- How a claim is admitted. -/
inductive Admitted where
  | pinned | carried
  deriving DecidableEq, Repr

/-- The word of an admission. -/
def Admitted.word : Admitted → String
  | .pinned => "PINNED"
  | .carried => "CARRIED"

/-- The interview, read and checked (v1's `_interview`). -/
structure Interview where
  ask : List (String × String × String)
  rows : List (String × String × Admitted)
  latest : List (String × (String × String × String) × Bool)
  texts : List Provision
  claims : List Claim
  modified : List (String × String)
  deriving Repr, Inhabited

/-- v1's `_interview`. -/
def interviewRun (D : DigestHook) (answer claims lines textsV carried modified : Value) : Run Interview := do
  let S ← readCatalogue lines
  let texts ← readTexts textsV
  declaredTexts D texts S
  let cls ← readClaims claims
  let car ← readCarried carried S
  let mods ← readModified modified S cls
  let latest ← readAnswer answer S
  let mut rows : List (String × String × Admitted) := []
  for c in cls do
    let cv := c.cv
    let some r := S.versions.find? (c.id, c.version) | refuse ("CLAIM " ++ cv ++ ": not declared")
    if c.digest != r.digest then refuse ("CLAIM " ++ cv ++ ": DIGEST does not match the declaration")
    if (textOf? texts c.id c.version).isNone then refuse ("CLAIM " ++ cv ++ ": no module text")
    let trip := (c.id, c.version, c.digest)
    match latest.lookup c.id with
    | some (entry, chosen) =>
      unless chosen do refuse ("CLAIM " ++ cv ++ ": the answer did not choose " ++ c.id)
      if entry == trip then rows := rows ++ [(c.id, c.version, .pinned)]
      else if car.contains trip then rows := rows ++ [(c.id, c.version, .carried)]
      else refuse ("CLAIM " ++ cv ++ ": not OFFERED when chosen (a new claim names the OFFERED version)")
    | none =>
      if car.contains trip then rows := rows ++ [(c.id, c.version, .carried)]
      else refuse ("CLAIM " ++ cv ++ ": " ++ c.id ++ " is not in the answer")
  let claimed := cls.map (·.id) ++ mods.map (·.1)
  for i in sortStrs (latest.map (·.1)) do
    if ((latest.lookup i).map (·.2)) == some true && !claimed.contains i then
      refuse ("ANSWER: " ++ i ++ " is chosen but not claimed")
  checkExcludes cls (textOf? texts)
  checkQuestions cls (textOf? texts)
  let ask := S.versions.offer.filter fun e => (latest.lookup e.1).isNone
  pure ⟨ask, rows, latest, texts, cls, mods⟩

/-- What `interview_check` answers: the Provisions still to ask about, and each claim's
admission. -/
structure InterviewAnswer where
  ask : List (String × String × String)
  claims : List (String × String × Admitted)
  deriving DecidableEq, Repr

/-- v1's `interview_check`. -/
def interviewCheck (D : DigestHook) (answer claims lines textsV carried modified : Value) :
    Answer InterviewAnswer :=
  finish do
    let R ← interviewRun D answer claims lines textsV carried modified
    pure ⟨R.ask, R.rows⟩

/-- The closing line of the check page (TPS 2.2.19). -/
def catchLine : String := "Any interaction not listed under INCLUDED is absent from this kernel."

/-- The NOT INCLUDED lines before the closing one, each with the Provision it is from. -/
def notIncludedBody (D : DigestHook) (answer claims lines textsV carried modified : Value) :
    Run (List (String × String)) := do
  let R ← interviewRun D answer claims lines textsV carried modified
  let mut out : List (String × String) := []
  for i in sortStrs (R.latest.map (·.1)) do
    let some ((ei, ev, _), chosen) := R.latest.lookup i | continue
    if chosen then continue
    let some M := textOf? R.texts ei ev
      | refuse ("MODULES: no text of " ++ ei ++ " " ++ ev ++ ", covered by the answer")
    out := out ++ [(M.cv, M.notChosen)]
  for c in R.claims do
    if let some M := textOf? R.texts c.id c.version then
      out := out ++ M.notIncluded.map (c.cv, ·)
  for (i, v) in R.modified do
    out := out ++ [(i ++ " " ++ v, "Modified from " ++ i ++ " " ++ v ++ ": its entries are the author's own.")]
  let ids := R.claims.map (·.id)
  for c in R.claims do
    if let some M := textOf? R.texts c.id c.version then
      for qd in raisedQuestions M c ids do
        out := out ++ [(c.cv, if getStr? c.answers qd.qid == some "YES" then qd.yesLine else qd.noLine)]
  pure out

/-- v1's `not_included_lines`: each line with the Provision it is from, `-` for the closing
one. -/
def notIncludedLines (D : DigestHook) (answer claims lines textsV carried modified : Value) :
    Answer (List (String × String)) :=
  finish ((notIncludedBody D answer claims lines textsV carried modified).map (· ++ [("-", catchLine)]))

/-- The check page's NOT INCLUDED lines always end with the closing line of the closed world
(TPS 5.22.6): "Any interaction not listed under INCLUDED is absent from this kernel." -/
theorem notIncludedLines_last {D : DigestHook} {answer claims lines textsV carried modified : Value}
    {xs : List (String × String)}
    (h : notIncludedLines D answer claims lines textsV carried modified = .ok xs) :
    xs.getLast? = some ("-", catchLine) := by
  unfold notIncludedLines at h
  cases hb : notIncludedBody D answer claims lines textsV carried modified with
  | error e =>
    rw [hb] at h
    cases e with
    | refused m =>
      simp [Except.map, finish] at h
    | owed w => simp [Except.map, finish] at h
  | ok out =>
    rw [hb] at h
    simp only [Except.map, finish, Answer.ok.injEq] at h
    subst h
    simp

end Principia.Provision
