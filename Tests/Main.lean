import Lean.Data.Json
import Principia
import Tests.Beta
import Tests.Biblio
import Tests.Calculator
import Tests.Canonical
import Tests.Cluster
import Tests.Eom
import Tests.Falcon
import Tests.Form
import Tests.FundamentalTests
import Tests.Governor
import Tests.Hold
import Tests.Identity
import Tests.Lint
import Tests.Permissions
import Tests.Probe
import Tests.Provision
import Tests.Record
import Tests.Score
import Tests.Sha256
import Tests.Sponsor
import Tests.Strike
import Tests.StructuredCheck
import Tests.Unicode
import Tests.Units
import Tests.Volunteer
import Tests.Yardstick
import Tests.Zone

/-!
The vector runner. Every executable function has vectors under `vectors/`
and a case here. `Lean.Json` is used to read inputs only (collision register
R5): PMA's canonical serializer is hand-written, elsewhere.
-/

open Lean
open Principia
open Principia.Record

/-! ## The harness -/

/-- A corpus's count of passing and failing checks. -/
structure Tally where
  pass : Nat := 0
  fail : Nat := 0

/-- Count one check; a failure is reported on stderr with what was checked. -/
def Tally.check (t : Tally) (ok : Bool) (what : String) : IO Tally := do
  if ok then
    return { t with pass := t.pass + 1 }
  else
    IO.eprintln s!"FAIL {what}"
    return { t with fail := t.fail + 1 }

/-- A corpus: a JSON list of cases. -/
def loadCases (path : System.FilePath) : IO (Array Json) := do
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text)
  IO.ofExcept json.getArr?

def jStr (j : Json) (k : String) : IO String := IO.ofExcept (j.getObjValAs? String k)
def jBool (j : Json) (k : String) : IO Bool := IO.ofExcept (j.getObjValAs? Bool k)
def jStrs (j : Json) (k : String) : IO (List String) := do
  let arr ← IO.ofExcept (j.getObjValAs? (Array String) k)
  return arr.toList

/-- Read a wire word into its enumeration; a word that does not read is a
defect of the corpus. -/
def word (α : Type) [WireWord α] (s : String) : IO α :=
  match (WireWord.ofWire? s : Option α) with
  | some a => pure a
  | none => throw (IO.userError s!"not a wire word: {repr s}")

def wire {α : Type} [WireWord α] (a : α) : String := WireWord.toWire a

/-! ## netstring.json: `Principia.Digest.preimage` -/

def runNetstring : IO Tally := do
  let mut t : Tally := {}
  for c in ← loadCases "vectors/netstring.json" do
    let fields ← jStrs c "fields"
    let expected ← jStr c "expected"
    let got := Principia.Digest.preimage fields
    t ← t.check (got == expected)
      s!"netstring {repr fields}: expected {repr expected}, got {repr got}"
  return t

/-! ## wire_words.json: `WireWord.toWire` and `WireWord.ofWire?` -/

/-- An enumeration's wire map, read through the class. -/
structure WireOps where
  members : List String
  read : String → Option String

def wireOps (α : Type) [WireWord α] : WireOps where
  members := (WireWord.members : List α).map WireWord.toWire
  read s := (WireWord.ofWire? s : Option α).map WireWord.toWire

def wireOpsFor : String → Option WireOps
  | "RecordClass" => some (wireOps RecordClass)
  | "Grade" => some (wireOps Grade)
  | "RecordStatus" => some (wireOps RecordStatus)
  | "RecordLayout" => some (wireOps RecordLayout)
  | "DerivationForm" => some (wireOps DerivationForm)
  | "DerivationClass" => some (wireOps DerivationClass)
  | "ValueType" => some (wireOps ValueType)
  | "Cardinality" => some (wireOps Cardinality)
  | "FieldWriter" => some (wireOps FieldWriter)
  | "EnvelopeField" => some (wireOps EnvelopeField)
  | "GovernedRequest" => some (wireOps Principia.Parameters.GovernedRequest)
  | "Lane" => some (wireOps Principia.Parameters.Lane)
  | "Switch" => some (wireOps Principia.Governor.Switch)
  | "Payer" => some (wireOps Principia.Governor.Payer)
  | "SlotCap" => some (wireOps Principia.Governor.SlotCap)
  | "DecisionWord" => some (wireOps Principia.Governor.DecisionWord)
  | "RefusalWord" => some (wireOps Principia.Governor.RefusalWord)
  | "PressureLevel" => some (wireOps Principia.Parameters.PressureLevel)
  | "Descent" => some (wireOps Principia.Governor.Descent)
  | "PressureRetry" => some (wireOps Principia.Governor.PressureRetry)
  | "ThresholdRule" => some (wireOps Principia.Governor.ThresholdRule)
  | "ExternalOrder" => some (wireOps Principia.Governor.ExternalOrder)
  | "AnonymousFull" => some (wireOps Principia.Governor.AnonymousFull)
  | "TrafficEvent" => some (wireOps Principia.Governor.TrafficEvent)
  | "TrafficStage" => some (wireOps Principia.Governor.TrafficStage)
  | "Ending" => some (wireOps Principia.Governor.Ending)
  | "PenalizedPayer" => some (wireOps Principia.Governor.PenalizedPayer)
  | "Doubling" => some (wireOps Principia.Governor.Doubling)
  | "TrialSuccess" => some (wireOps Principia.Governor.TrialSuccess)
  | "Te2Causes" => some (wireOps Principia.Governor.Te2Causes)
  | _ => none

/-- R1's spelling for a wire word: not empty; capitals, digits, `_` and single
inner spaces only (`NOT GRADED`, `NAMED_GAP`, `D_IS`). -/
def r1Spelling (s : String) : Bool :=
  !s.isEmpty &&
    s.all (fun ch => ch.isUpper || ch.isDigit || ch == '_' || ch == ' ') &&
    !s.startsWith " " && !s.endsWith " " && (s.splitOn "  ").length == 1

def runWireWords : IO Tally := do
  let mut t : Tally := {}
  for c in ← loadCases "vectors/wire_words.json" do
    let e ← jStr c "enum"
    let some ops := wireOpsFor e | throw (IO.userError s!"unknown enumeration {e}")
    match c.getObjValAs? (Array String) "members" with
    | .ok ms =>
      let ms := ms.toList
      t ← t.check (ops.members == ms)
        s!"{e} members: expected {repr ms}, got {repr ops.members}"
      t ← t.check (ops.members.eraseDups.length == ops.members.length)
        s!"{e} members repeat a wire word"
      for w in ops.members do
        t ← t.check (r1Spelling w) s!"{e} {repr w} is not spelled as R1 asks"
      for w in ms do
        t ← t.check (ops.read w == some w) s!"{e} {repr w} does not read back"
    | .error _ =>
      let w ← jStr c "word"
      let reads ← jBool c "reads"
      let got := ops.read w
      t ← t.check (got.isSome == reads && got.all (· == w))
        s!"{e} {repr w}: expected reads {reads}, got {repr got}"
  return t

/-! ## record_class.json: the class table -/

def runRecordClass : IO Tally := do
  let mut t : Tally := {}
  for c in ← loadCases "vectors/record_class.json" do
    let k ← word RecordClass (← jStr c "class")
    let n := wire k
    t ← t.check (wire k.layout == (← jStr c "layout")) s!"{n} layout"
    t ← t.check (k.pushed == (← jBool c "pushed")) s!"{n} pushed"
    t ← t.check (wire k.landingGrade == (← jStr c "landing_grade")) s!"{n} landing grade"
    t ← t.check (k.grades.map wire == (← jStrs c "grades")) s!"{n} grades"
    t ← t.check (k.statuses.map wire == (← jStrs c "statuses")) s!"{n} statuses"
  return t

/-! ## record_envelope.json: the envelope's rows -/

def runRecordEnvelope : IO Tally := do
  let mut t : Tally := {}
  for c in ← loadCases "vectors/record_envelope.json" do
    let k ← word RecordClass (← jStr c "class")
    let n := wire k
    let rows ← IO.ofExcept (c.getObjValAs? (Array Json) "fields")
    let names ← rows.toList.mapM (jStr · "field")
    t ← t.check (k.envelopeFields.map wire == names)
      s!"{n} envelope: expected {repr names}, got {repr (k.envelopeFields.map wire)}"
    for f in (WireWord.members : List EnvelopeField) do
      t ← t.check (k.carries f == names.contains (wire f)) s!"{n} carries {wire f}"
    for r in rows do
      let f ← word EnvelopeField (← jStr r "field")
      let at_ := s!"{n}.{wire f}"
      t ← t.check (wire f.valueType == (← jStr r "type")) s!"{at_} type"
      t ← t.check (wire f.cardinality == (← jStr r "card")) s!"{at_} cardinality"
      t ← t.check (f.required == (← jBool r "required")) s!"{at_} required"
      t ← t.check (wire (k.writer f) == (← jStr r "writer")) s!"{at_} writer"
      t ← t.check (f.inDigest == (← jBool r "digest")) s!"{at_} digest"
  return t


/-! ## derivation_class.json: forms, classes, the orders and the credit -/

/-- The runner's input shape for STRUCTURED steps (not the wire form, which
comes with the canonical serializer). -/
def readSteps (s : Json) : IO (List StructuredStep) := do
  let arr ← IO.ofExcept s.getArr?
  arr.toList.mapM fun st => do
    let eq ← jStr st "equation"
    match st.getObjValAs? String "law", st.getObjValAs? String "assumption" with
    | .ok l, _ => pure { equation := eq, cites := .law l }
    | _, .ok a => pure { equation := eq, cites := .assumption a }
    | _, _ => throw (IO.userError "a step cites neither a law nor an assumption")

/-- The runner's input shape for an attachment: `{"structured": [...]}` or
`{"kernelProof": "..."}`. -/
def readAttachment (j : Json) : IO Attachment := do
  match j.getObjVal? "structured", j.getObjVal? "kernelProof" with
  | .ok s, _ => return .structured (← readSteps s) .lhs
  | _, .ok (.str e) => return .kernelProof e
  | _, _ => throw (IO.userError s!"not an attachment: {j.compress}")

/-- The runner's input shape for a derivation: `{"prose": {"steps", "text",
"attachment"?}}`, or a STRUCTURED or KERNEL payload as for an attachment. -/
def readDerivation (j : Json) : IO Derivation := do
  match j.getObjVal? "prose" with
  | .ok p =>
    let steps ← IO.ofExcept (p.getObjValAs? Nat "steps")
    let text ← jStr p "text"
    let att ← match p.getObjVal? "attachment" with
      | .ok a => some <$> readAttachment a
      | .error _ => pure none
    return .prose steps text att
  | .error _ =>
    match ← readAttachment j with
    | .structured s st => return .structured s st
    | .kernelProof e => return .kernelProof e

def runDerivationClass : IO Tally := do
  let mut t : Tally := {}
  for c in ← loadCases "vectors/derivation_class.json" do
    match ← jStr c "function" with
    | "checkClass" =>
      let f ← word DerivationForm (← jStr c "form")
      let e ← jStr c "expected"
      t ← t.check (wire f.checkClass == e) s!"checkClass {wire f}"
    | "formCredit" =>
      let f ← word DerivationForm (← jStr c "form")
      let v ← jBool c "verified"
      t ← t.check (wire (f.credit v) == (← jStr c "expected")) s!"credit {wire f} {v}"
    | "credit" =>
      -- The checker accepts exactly the derivations listed under "accepted".
      let d ← readDerivation (← IO.ofExcept (c.getObjVal? "derivation"))
      let accepted ← (← IO.ofExcept (c.getObjValAs? (Array Json) "accepted")).mapM
        readDerivation
      let check := fun x => accepted.contains x
      t ← t.check (wire (d.creditedForm check) == (← jStr c "form_credited"))
        s!"creditedForm of {repr d}"
      t ← t.check (wire (d.creditedClass check) == (← jStr c "class_credited"))
        s!"creditedClass of {repr d}"
    | "classOrder" =>
      let a ← word DerivationClass (← jStr c "a")
      let b ← word DerivationClass (← jStr c "b")
      t ← t.check (decide (a ≤ b) == (← jBool c "le")) s!"{wire a} <= {wire b}"
      t ← t.check (decide (a < b) == (← jBool c "lt")) s!"{wire a} < {wire b}"
    | "formOrder" =>
      let a ← word DerivationForm (← jStr c "a")
      let b ← word DerivationForm (← jStr c "b")
      t ← t.check (decide (a ≤ b) == (← jBool c "le")) s!"{wire a} <= {wire b}"
      t ← t.check (decide (a < b) == (← jBool c "lt")) s!"{wire a} < {wire b}"
    | "derivationForm" =>
      let d ← readDerivation (← IO.ofExcept (c.getObjVal? "derivation"))
      t ← t.check (wire d.form == (← jStr c "expected")) s!"form of {repr d}"
    | "attachmentForm" =>
      let a ← readAttachment (← IO.ofExcept (c.getObjVal? "attachment"))
      t ← t.check (wire a.form == (← jStr c "expected")) s!"form of {repr a}"
    | other => throw (IO.userError s!"unknown function {other}")
  return t

/-! ## The run -/

def main : IO UInt32 := do
  -- One runner per line, in code point order of its name, each line ending with a comma, so
  -- that two runners added at once touch different lines; `main` refuses another order.
  let corpora : List (String × IO Tally) := [
    ("beta", Tests.Beta.runBeta >>= fun (p, f) => pure { pass := p, fail := f }),
    ("biblio", Tests.Biblio.runBiblio >>= fun (p, f) => pure { pass := p, fail := f }),
    ("biblio_recheck_urls", Tests.Biblio.runRecheckUrls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("biblio_table", Tests.Biblio.runTable >>= fun (p, f) => pure { pass := p, fail := f }),
    ("canon_corpus", Tests.Canonical.runCanonCorpus >>= fun (p, f) => pure { pass := p, fail := f }),
    ("canonical_json", Tests.Canonical.runCanonicalJson >>= fun (p, f) => pure { pass := p, fail := f }),
    ("cluster", Tests.Cluster.runCluster >>= fun (p, f) => pure { pass := p, fail := f }),
    ("cluster_rows", Tests.Cluster.runRows >>= fun (p, f) => pure { pass := p, fail := f }),
    ("cluster_schedule", Tests.Cluster.runSchedule >>= fun (p, f) => pure { pass := p, fail := f }),
    ("cluster_screen", Tests.Cluster.runScreen >>= fun (p, f) => pure { pass := p, fail := f }),
    ("conditions", Tests.Strike.runConditions >>= fun (p, f) => pure { pass := p, fail := f }),
    ("derivation_class", runDerivationClass),
    ("digest_corpus", Tests.Canonical.runDigestCorpus >>= fun (p, f) => pure { pass := p, fail := f }),
    ("digest_preimage", Tests.Canonical.runDigestPreimage >>= fun (p, f) => pure { pass := p, fail := f }),
    ("dis_corpus", Tests.Canonical.runDisCorpus >>= fun (p, f) => pure { pass := p, fail := f }),
    ("eom", Tests.Eom.runEom >>= fun (p, f) => pure { pass := p, fail := f }),
    ("falcon", Tests.Falcon.runFalcon >>= fun (p, f) => pure { pass := p, fail := f }),
    ("falcon_hand", Tests.Falcon.runHand >>= fun (p, f) => pure { pass := p, fail := f }),
    ("falcon_table", Tests.Falcon.runTable >>= fun (p, f) => pure { pass := p, fail := f }),
    ("form", Tests.Form.runForm >>= fun (p, f) => pure { pass := p, fail := f }),
    ("form_numbers", Tests.Form.runFormNumbers >>= fun (p, f) => pure { pass := p, fail := f }),
    ("governor", Tests.Governor.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("hold", Tests.Hold.runHold >>= fun (p, f) => pure { pass := p, fail := f }),
    ("identity", Tests.Identity.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("json_text", Tests.Calculator.runJsonText >>= fun (p, f) => pure { pass := p, fail := f }),
    ("lint", Tests.Lint.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("lint_tables", Tests.Lint.runTables >>= fun (p, f) => pure { pass := p, fail := f }),
    ("netstring", runNetstring),
    ("pcalc", Tests.Calculator.runPcalc >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc biblio (biblio_corpus)", Tests.Calculator.runBiblioCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc biblio bounds", Tests.Calculator.runBiblioBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc cluster (cluster_corpus)", Tests.Calculator.runClusterCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc coverage (pcalc.json)", Tests.Calculator.runPcalcCoverage >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc derivation (structured_credit, structured_wire)", Tests.Calculator.runDerivationCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc derivation bounds", Tests.Calculator.runDerivationBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc digest (digest_corpus)", Tests.Calculator.runDigestCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc digest (dis_corpus)", Tests.Calculator.runDisCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc eom (eom, settlement)", Tests.Calculator.runEomCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc falcon (falcon_corpus, falcon_hand)", Tests.Calculator.runFalconCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc falcon bounds", Tests.Calculator.runFalconBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc family bounds", Tests.Calculator.runFamilyBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc form (form_corpus, form_numbers)", Tests.Calculator.runFormCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc form bounds", Tests.Calculator.runFormBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc fundamental (tests_corpus)", Tests.Calculator.runFundamentalCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc fundamental bounds", Tests.Calculator.runFundamentalBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc governor (governor)", Tests.Calculator.runGovernorCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc hold (hold_corpus)", Tests.Calculator.runHoldCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc hold bounds", Tests.Calculator.runHoldBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc identity (identity_corpus)", Tests.Calculator.runIdentityCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc landing (landing_screen)", Tests.Calculator.runLandingCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc lint (lint_corpus)", Tests.Calculator.runLintCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc permissions (permissions)", Tests.Calculator.runPermissionsCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc probe (probe_corpus)", Tests.Calculator.runProbeCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc provision (module_corpus)", Tests.Calculator.runProvisionCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc provision bounds", Tests.Calculator.runProvisionBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc record (record, record_view, record_forms)", Tests.Calculator.runRecordCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc record bounds", Tests.Calculator.runRecordBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc request bounds (governor, permissions, sha256, unicode)", Tests.Calculator.runRequestBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc score (score, beta)", Tests.Calculator.runScoreCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc score bounds", Tests.Calculator.runScoreBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc sha256 (sha256, SHA256ShortMsg, SHA256LongMsg)", Tests.Calculator.runSha256Calls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc sponsor (sponsor_corpus)", Tests.Calculator.runSponsorCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc sr9 (sr9_corpus)", Tests.Calculator.runSr9Calls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc strike (conditions_corpus)", Tests.Calculator.runConditionsCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc strike (sr3_scope_corpus)", Tests.Calculator.runSr3ScopeCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc strike (strike, sr8_order)", Tests.Calculator.runStrikeCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc unicode (NormalizationTest, UnicodeData)", Tests.Calculator.runUnicodeCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc units (units_corpus, units_range, units_pi)", Tests.Calculator.runUnitsCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc volunteer (volunteer_corpus)", Tests.Volunteer.runVolunteer >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc yardstick (yardstick_corpus)", Tests.Calculator.runYardstickCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc zone (zone_corpus)", Tests.Calculator.runZoneCalls >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pcalc zone bounds", Tests.Calculator.runZoneBounds >>= fun (p, f) => pure { pass := p, fail := f }),
    ("permissions", Tests.Permissions.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("pi_scale", Tests.Units.runPiScale >>= fun (p, f) => pure { pass := p, fail := f }),
    ("probe", Tests.Probe.runProbe >>= fun (p, f) => pure { pass := p, fail := f }),
    ("provision", Tests.Provision.runProvision >>= fun (p, f) => pure { pass := p, fail := f }),
    ("reaudit", Tests.Record.runReaudit >>= fun (p, f) => pure { pass := p, fail := f }),
    ("record", Tests.Record.runRecord >>= fun (p, f) => pure { pass := p, fail := f }),
    ("record_class", runRecordClass),
    ("record_envelope", runRecordEnvelope),
    ("record_forms", Tests.Record.runRecordForms >>= fun (p, f) => pure { pass := p, fail := f }),
    ("record_table", Tests.Record.runRecordTable >>= fun (p, f) => pure { pass := p, fail := f }),
    ("record_view", Tests.Record.runRecordView >>= fun (p, f) => pure { pass := p, fail := f }),
    ("score", Tests.Score.runScore >>= fun (p, f) => pure { pass := p, fail := f }),
    ("settlement", Tests.Eom.runSettlement >>= fun (p, f) => pure { pass := p, fail := f }),
    ("sha256", Tests.Sha256.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("sponsor", Tests.Sponsor.runSponsor >>= fun (p, f) => pure { pass := p, fail := f }),
    ("sr3_scope", Tests.Strike.runSr3Scope >>= fun (p, f) => pure { pass := p, fail := f }),
    ("sr8_order", Tests.Strike.runSr8Order >>= fun (p, f) => pure { pass := p, fail := f }),
    ("sr9", Tests.Strike.runSr9 >>= fun (p, f) => pure { pass := p, fail := f }),
    ("strike", Tests.Strike.runStrike >>= fun (p, f) => pure { pass := p, fail := f }),
    ("structured_check", Tests.StructuredCheck.runStructuredCheck >>= fun (p, f) => pure { pass := p, fail := f }),
    ("structured_credit", Tests.StructuredCheck.runStructuredCredit >>= fun (p, f) => pure { pass := p, fail := f }),
    ("structured_wire", Tests.StructuredCheck.runStructuredWire >>= fun (p, f) => pure { pass := p, fail := f }),
    ("tests", Tests.FundamentalTests.runTests >>= fun (p, f) => pure { pass := p, fail := f }),
    ("unicode", Tests.Unicode.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("units", Tests.Units.run >>= fun (p, f) => pure { pass := p, fail := f }),
    ("wire_words", runWireWords),
    ("yardstick", Tests.Yardstick.runYardstick >>= fun (p, f) => pure { pass := p, fail := f }),
    ("yardstick_bound", Tests.Yardstick.runBound >>= fun (p, f) => pure { pass := p, fail := f }),
    ("zone", Tests.Zone.runZone >>= fun (p, f) => pure { pass := p, fail := f }),
    ("zone_text", Tests.Zone.runZoneText >>= fun (p, f) => pure { pass := p, fail := f }),
  ]
  let mut failed := 0
  -- The list is the place a new runner goes: it is kept sorted and without a name twice.
  let names := corpora.map Prod.fst
  unless names.Pairwise (· < ·) do
    IO.eprintln s!"FAIL the runner list: names out of code point order, or one twice: {names}"
    failed := failed + 1
  for (name, run) in corpora do
    let t ← run
    IO.println s!"{name}: {t.pass} pass, {t.fail} fail"
    failed := failed + t.fail
    -- A corpus that checks nothing is a failure: an emptied file must not pass.
    if t.pass + t.fail == 0 then
      IO.eprintln s!"FAIL {name}: the corpus checked nothing"
      failed := failed + 1
  return (if failed == 0 then 0 else 1)
