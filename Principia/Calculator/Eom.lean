import Principia.Calculator.Interface
import Principia.Eom

/-!
# Family `eom`: the structure check of the equations of motion

v1 `tpc_eom`'s five functions (`Principia.Eom`), their arguments named as v1's corpora
name them:
* `eom_map {"tfk"}`: `["OK", report]`, the report's map of each DOF to the law that
  determines it, the parts UNDER, SQUARE and OVER, the index and the initial values.
* `eom_findings {"tfk"}`: `["OK", findings]`, each finding with its question for the
  Declarer.
* `eom_class {"tfk"}`: `["STRUCTURE", "structurally regular"]` or `["STRUCTURE",
  "Structure not Validated at Inception", reasons]`.
* `eom_register_test {"tfk", "records"}`: `["OK", report, findings, ["USED", ids],
  ["SETTLED", unknowns], ["OPEN", unknowns]]`, the register's standing records with a
  form entering as laws.
* `settlement_check {"tfk", "records", "words", "naming"}`: `["OK", {"BY_TEST",
  "BY_NAMING", "OPEN", "USED"}]`, what the structure test and the lead's naming settle of
  the register's open gaps.

The answers are v1's values, written as canonical JSON; v1's `canon` text of each is v1's
expectation. v1's own refusals are values too, `["REFUSED", reason]` (for
`settlement_check`, `["REFUSED", problems]`), exit code 0, the reason escaped as v1
escaped it. Each EQUATION is read by the declared forms after NFC, as v1 read it: a form
is at most 4096 code points and 64 nested parentheses once read, the declared forms' own
bounds, so a form's tree is no deeper than its text is long. An answer the Calculator does
not compute is refused `OWED`, its detail saying what it waits on; with the declared
forms' parser none is.

Bounds, measured on the Calculator's command line: at most `maxEntries` entries in each
of the Starting Set's DOF, CONSTANT, LAW and CONSTRAINT kinds; at most `maxRecords`
records, status words and namings; and an EQUATION's text, in a law or a record, at most
`maxEquation` code points before it is read. The matching, the parts and the signature
method run over lists, so their cost grows with a power of the laws and the unknowns.
The slowest requests found at the bounds: a register test of 64 laws and 64 records, each
holding a form of about 4096 code points naming every unknown at varied orders, 0.8 s;
the 64 laws alone, 0.26 s; a settlement check of 64 records and 64 namings over such
laws, 0.41 s. At 200 entries the same kinds of request took up to 14 s.
-/

namespace Principia.Calculator.Eom

open Principia.Canonical

/-! ## The family's bounds, measured -/

/-- The most entries each of the Starting Set's DOF, CONSTANT, LAW and CONSTRAINT kinds
holds. v1's own cases hold at most 7. -/
def maxEntries : Nat := 64

/-- The most records a register test or a settlement check is given, and the most status
words and namings a settlement check is given: every record that enters is a law of the
analysis, which a register test runs twice. -/
def maxRecords : Nat := 64

/-- The most code points an EQUATION's text holds before it is read: four times the
declared forms' bound on a form, which is checked after NFC. Normalizing an EQUATION of a
mebibyte, combining marks to be reordered, took 1.7 s; one of this length takes 0.08 s, and
the longer one is now refused in 0.05 s. -/
def maxEquation : Nat := 16384

/-- The member `k` of an object, `null` for anything else or when absent. -/
def memberOf (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => (ms.lookup k).getD .null
  | _ => .null

/-- A list's or an object's entries within a bound; anything else is left to the function,
which refuses it as v1 refused it. -/
def within (what : String) (n : Nat) : Value → Except Refusal Unit
  | .arr xs => atMost what n xs
  | .obj ms => atMost what n ms
  | _ => pure ()

/-- Each EQUATION text of a list of laws or records within `maxEquation` code points. -/
def equationsWithin (what : String) : Value → Except Refusal Unit
  | .arr xs => xs.forM fun x =>
    match memberOf x "EQUATION" with
    | .str s =>
      if maxEquation < s.length then
        badArgument s!"{what} holds an EQUATION of more than {maxEquation} code points (the Calculator's bound)"
      else pure ()
    | _ => pure ()
  | _ => pure ()

/-- The Starting Set's kinds within `maxEntries`, and its laws' EQUATIONs within
`maxEquation`. -/
def tfkWithin (tfk : Value) : Except Refusal Unit := do
  let tpk := memberOf tfk "TPK"
  for kind in ["DOF", "CONSTANT", "LAW", "CONSTRAINT"] do
    within s!"the Starting Set's {kind}" maxEntries (memberOf tpk kind)
  equationsWithin "a LAW" (memberOf tpk "LAW")

/-- Records within `maxRecords`, and their EQUATIONs within `maxEquation`. -/
def recordsWithin (records : Value) : Except Refusal Unit := do
  within "records" maxRecords records
  equationsWithin "a record" records

/-- An owed answer's detail, in plain words: what it waits on. -/
def owedDetail (why : String) : String :=
  if why == Zone.Owed.forms.message then
    "the structure check waits on the declared forms to read a law's equation"
  else if why.startsWith "exact: " then
    "the structure check waits on an exact value beyond the Calculator's bounds in a law's equation: " ++
      String.ofList (why.toList.drop 7)
  else "the structure check does not compute this answer yet: " ++ why

/-- An answer as `pcalc` gives it: v1's value, or the refusal `OWED`. -/
def answer : Principia.Eom.Result → Except Refusal Value
  | .ok v => .ok v
  | .error why => .error ⟨.owed, owedDetail why⟩

/-- The declared forms' parser the check reads with. -/
def forms : Principia.Eom.FormHook := Principia.Eom.FormHook.calculator

/-- A request's `tfk` within the bounds, as the zones read it. -/
def readTfk (tfk : Value) : Except Refusal Zone.Value := do
  tfkWithin tfk
  pure (Principia.Strike.toZoneValue tfk)

/-- The family's functions. -/
def calls : Family := [
  ("eom_class", fun v => do
    let tfk ← readTfk (← argument1 "tfk" v)
    answer (Principia.Eom.eomClass forms tfk)),
  ("eom_findings", fun v => do
    let tfk ← readTfk (← argument1 "tfk" v)
    answer (Principia.Eom.eomFindings forms tfk)),
  ("eom_map", fun v => do
    let tfk ← readTfk (← argument1 "tfk" v)
    answer (Principia.Eom.eomMap forms tfk)),
  ("eom_register_test", fun v => do
    let (t, r) ← argument2 "tfk" "records" v
    let tfk ← readTfk t
    recordsWithin r
    answer (Principia.Eom.eomRegisterTest forms tfk (Principia.Strike.toZoneValue r))),
  ("settlement_check", fun v => do
    let ms ← membersOf ["tfk", "records", "words", "naming"] v
    let t ← needed ms "tfk"
    let r ← needed ms "records"
    let w ← needed ms "words"
    let n ← needed ms "naming"
    tfkWithin t
    recordsWithin r
    within "words" maxRecords w
    within "naming" maxRecords n
    answer (Principia.Eom.settlementCheck forms t r w n)),
]

end Principia.Calculator.Eom
