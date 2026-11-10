/-!
# The record table, as v1 wrote it

v1's `tpc_record` 0.1.0 carried the closed table of tpm_record_schema 0.4.0 (section 7.5) as
its text and read it by the table's own line grammar (7.1, v1's `_parse_table`). The table
is carried here the same way: `tableText` is v1's `TABLE_TEXT`, byte for byte (the vector
runner checks it against version 1's table module), and `parseTable` is v1's reader.
Every function of the register reads the table through `table`, as v1's read `T`.

The table's class part is also Phase 1's typed table (`Principia.Record.RecordClass` and
its grades, statuses and envelope, `Principia.Record.Classes` and `Principia.Record.Envelope`); the
vector runner checks that the two agree, class by class and field by field.

The line grammar (7.1): a line that begins with two spaces continues the line before it,
joined by one space; blank lines are skipped; every other line is `ENUM`, `CLASS`,
`LANDGRADE`, `GRADES`, `STATUSES`, `SUB`, `FIELD` (ten words) or `RULE` (four parts
joined by ` | `).
-/

namespace Principia.Record.Table

/-- v1's `TABLE_TEXT`: tpm_record_schema 0.4.0, section 7.5, from `BEGIN RECORD TABLE` to
`END RECORD TABLE`, each line ending with a line feed. -/
def tableText : String := "BEGIN RECORD TABLE
ENUM CLASS = RESULT | ASSUMPTION | CORROBORATION | VERIFICATION
  | WITHDRAWAL | NAMED_GAP | ENTRY_STATUS | PROMOTION | MASTER | HOLD
  | RELEASE
ENUM GRADE_VALUES = PROVISIONAL | ESTABLISHED | REFUTED | WITHDRAWN
  | NOT GRADED
ENUM REGIME = L | M
ENUM REGIME_M = M
ENUM FALSIFIER_CLASS = F1 | F2 | F3
ENUM SITUATION = INITIAL | BOUNDARY
ENUM OUTCOME = MATCH | MATCH WITH DIFFERENCE NOTED
ENUM TARGET_STATUS = PROVISIONAL | ESTABLISHED | HELD
ENUM EVALUATION = A | B
ENUM ORIGIN = SAME BLOCK | REPRODUCTION BLOCK
ENUM GAP_SOURCE = IC2 | UNDER | SR5_LOCUS | SR7_ASSUMPTIONS | SR7_DOMAIN
ENUM ROLE_WORDS = CONSTRAINT | CONSTITUTIVE | INVARIANT | DEFINITION

CLASS RESULT KEYED PUSH
CLASS ASSUMPTION KEYED PUSH
CLASS CORROBORATION KEYED PUSH
CLASS VERIFICATION KEYED PUSH
CLASS WITHDRAWAL LIST TPX
CLASS NAMED_GAP KEYED TPX
CLASS ENTRY_STATUS KEYED PUSH
CLASS PROMOTION LIST TPX
CLASS MASTER KEYED TPX
CLASS HOLD LIST TPX
CLASS RELEASE LIST TPX

LANDGRADE RESULT = PROVISIONAL
LANDGRADE ASSUMPTION = PROVISIONAL
LANDGRADE CORROBORATION = PROVISIONAL
LANDGRADE VERIFICATION = PROVISIONAL
LANDGRADE WITHDRAWAL = NOT GRADED
LANDGRADE NAMED_GAP = NOT GRADED
LANDGRADE ENTRY_STATUS = NOT GRADED
LANDGRADE PROMOTION = NOT GRADED
LANDGRADE MASTER = NOT GRADED
LANDGRADE HOLD = NOT GRADED
LANDGRADE RELEASE = NOT GRADED

GRADES RESULT = PROVISIONAL | ESTABLISHED | REFUTED | WITHDRAWN
GRADES ASSUMPTION = PROVISIONAL | WITHDRAWN
GRADES CORROBORATION = PROVISIONAL | REFUTED | WITHDRAWN
GRADES VERIFICATION = PROVISIONAL | WITHDRAWN
GRADES WITHDRAWAL = NOT GRADED
GRADES NAMED_GAP = NOT GRADED
GRADES ENTRY_STATUS = NOT GRADED
GRADES PROMOTION = NOT GRADED
GRADES MASTER = NOT GRADED
GRADES HOLD = NOT GRADED
GRADES RELEASE = NOT GRADED

STATUSES RESULT = UNMARKED | HELD | REFUTED
STATUSES ASSUMPTION = UNMARKED | HELD
STATUSES CORROBORATION = UNMARKED | HELD | REFUTED
STATUSES VERIFICATION = UNMARKED | HELD
STATUSES ENTRY_STATUS = UNMARKED | HELD

SUB DERIVATION KEY -
SUB COMPONENT KEY NAME
SUB POINT KEY DOF
SUB INDEPENDENCE KEY -
SUB EXTERNAL KEY -
SUB DIFFERENCE KEY -

FIELD RESULT ID RID ONE R LEAD D - -
FIELD RESULT CLASS ENUM ONE R AUTHOR D - ENUM=CLASS
FIELD RESULT GRADE ENUM ONE R TPX D - GRADE
FIELD RESULT STATUS ENUM ONE R TPX X - STATUS
FIELD RESULT BLOCK TEXT ONE R TPX D - NOTBLANK
FIELD RESULT AUTHOR TEXT ONE R TPX D - NOTBLANK
FIELD RESULT LANDED_BY TEXT ONE R TPX D - NOTBLANK
FIELD RESULT LANDED TEXT ONE R TPX D - UTC
FIELD RESULT VETTED_IN TEXT ONE O TPX D - NOTBLANK
FIELD RESULT CITES IDSET SET R AUTHOR D - RID
FIELD RESULT ASSUMPTIONS IDSET SET R AUTHOR D - RID
FIELD RESULT LITERATURE IDSET SET O AUTHOR D - BIBID,SETTING
FIELD RESULT SUPERSEDES RID ONE O AUTHOR D - -
FIELD RESULT INHERITS RID ONE O TPX D - -
FIELD RESULT TPS TEXT ONE R TPX D - VERSION
FIELD RESULT D_IS TEXT ONE R TPX D - HEX64
FIELD RESULT STATEMENT TEXT ONE R AUTHOR D - NOTBLANK
FIELD RESULT REGIME ENUM ONE R AUTHOR D - ENUM=REGIME
FIELD RESULT DERIVATION OBJECT ONE R AUTHOR D - SUB=DERIVATION
FIELD RESULT FALSIFIER TEXT ONE R AUTHOR D - NOTBLANK
FIELD RESULT FALSIFIER_CLASS ENUM ONE R AUTHOR D - ENUM=FALSIFIER_CLASS
FIELD RESULT DOMAIN TEXT ONE O AUTHOR D - NOTBLANK
FIELD RESULT DOMAIN_CONDITION PREDICATE ONE O AUTHOR D - -
FIELD RESULT REFS IDENT SET C AUTHOR D - TPKNAME
FIELD RESULT EQUATION FORM ONE C AUTHOR D - -
FIELD RESULT ROLE ENUM ONE C AUTHOR D - ROLE
FIELD RESULT ENTRIES IDENT SET O AUTHOR D - TRMENTRY
FIELD RESULT QUANTITY IDENT ONE C AUTHOR D - TRMENTRY
FIELD RESULT VALUE DECIMAL ONE C AUTHOR D - -
FIELD RESULT UNIT UNIT ONE C AUTHOR D - DIM=QUANTITY
FIELD RESULT U_C DECIMAL ONE C AUTHOR D - POSITIVE,PREC
FIELD RESULT BUDGET OBJECT LIST C AUTHOR D - SUB=COMPONENT,NONEMPTY
FIELD RESULT CORRELATED BOOL ONE C AUTHOR D FALSE -
FIELD RESULT AT OBJECT LIST C AUTHOR D EMPTY SUB=POINT
FIELD RESULT DIGEST TEXT ONE O TPX X - HEX64,DIGEST
RULE RESULT | IF REGIME = M | REQUIRE | QUANTITY, VALUE, UNIT, U_C, BUDGET
RULE RESULT | IF REGIME = M | FORBID | EQUATION, ROLE
RULE RESULT | IF REGIME = L | FORBID | U_C, BUDGET
RULE RESULT | IF REGIME = L | ALL OR NONE | QUANTITY, VALUE, UNIT
RULE RESULT | IF BUDGET ABSENT | FORBID | CORRELATED
RULE RESULT | IF VALUE ABSENT | FORBID | AT
RULE RESULT | IF ROLE PRESENT | REQUIRE | EQUATION
RULE RESULT | IF EQUATION PRESENT | REQUIRE | REFS
RULE RESULT | IF DOMAIN_CONDITION PRESENT | REQUIRE | REFS

FIELD ASSUMPTION ID RID ONE R LEAD D - -
FIELD ASSUMPTION CLASS ENUM ONE R AUTHOR D - ENUM=CLASS
FIELD ASSUMPTION GRADE ENUM ONE R TPX D - GRADE
FIELD ASSUMPTION STATUS ENUM ONE R TPX X - STATUS
FIELD ASSUMPTION BLOCK TEXT ONE R TPX D - NOTBLANK
FIELD ASSUMPTION AUTHOR TEXT ONE R TPX D - NOTBLANK
FIELD ASSUMPTION LANDED_BY TEXT ONE R TPX D - NOTBLANK
FIELD ASSUMPTION LANDED TEXT ONE R TPX D - UTC
FIELD ASSUMPTION VETTED_IN TEXT ONE O TPX D - NOTBLANK
FIELD ASSUMPTION CITES IDSET SET R AUTHOR D - RID
FIELD ASSUMPTION ASSUMPTIONS IDSET SET R AUTHOR D - RID
FIELD ASSUMPTION LITERATURE IDSET SET O AUTHOR D - BIBID,SETTING
FIELD ASSUMPTION SUPERSEDES RID ONE O AUTHOR D - -
FIELD ASSUMPTION INHERITS RID ONE O TPX D - -
FIELD ASSUMPTION TPS TEXT ONE R TPX D - VERSION
FIELD ASSUMPTION D_IS TEXT ONE R TPX D - HEX64
FIELD ASSUMPTION PROPOSITION TEXT ONE R AUTHOR D - NOTBLANK,T2
FIELD ASSUMPTION REFS IDENT SET R AUTHOR D - TPKNAME
FIELD ASSUMPTION SITUATION ENUM ONE O AUTHOR D - ENUM=SITUATION
FIELD ASSUMPTION DOF IDENT ONE C AUTHOR D - TPKDOF
FIELD ASSUMPTION VALUE DECIMAL ONE C AUTHOR D - -
FIELD ASSUMPTION UNIT UNIT ONE C AUTHOR D - DIM=DOF
FIELD ASSUMPTION AT OBJECT LIST C AUTHOR D EMPTY SUB=POINT
FIELD ASSUMPTION EQUATION FORM ONE C AUTHOR D - -
FIELD ASSUMPTION ROLE ENUM ONE C AUTHOR D - ROLE
FIELD ASSUMPTION DIGEST TEXT ONE O TPX X - HEX64,DIGEST
RULE ASSUMPTION | IF SITUATION PRESENT | REQUIRE | DOF, VALUE, UNIT
RULE ASSUMPTION | IF SITUATION ABSENT | FORBID | DOF, VALUE, UNIT, AT
RULE ASSUMPTION | IF SITUATION PRESENT | FORBID | EQUATION, ROLE
RULE ASSUMPTION | IF ROLE PRESENT | REQUIRE | EQUATION

FIELD CORROBORATION ID RID ONE R LEAD D - -
FIELD CORROBORATION CLASS ENUM ONE R AUTHOR D - ENUM=CLASS
FIELD CORROBORATION GRADE ENUM ONE R TPX D - GRADE
FIELD CORROBORATION STATUS ENUM ONE R TPX X - STATUS
FIELD CORROBORATION BLOCK TEXT ONE R TPX D - NOTBLANK
FIELD CORROBORATION AUTHOR TEXT ONE R TPX D - NOTBLANK
FIELD CORROBORATION LANDED_BY TEXT ONE R TPX D - NOTBLANK
FIELD CORROBORATION LANDED TEXT ONE R TPX D - UTC
FIELD CORROBORATION VETTED_IN TEXT ONE O TPX D - NOTBLANK
FIELD CORROBORATION CITES IDSET SET R AUTHOR D - RID
FIELD CORROBORATION ASSUMPTIONS IDSET SET R AUTHOR D - RID
FIELD CORROBORATION LITERATURE IDSET SET O AUTHOR D - BIBID,SETTING
FIELD CORROBORATION SUPERSEDES RID ONE O AUTHOR D - -
FIELD CORROBORATION INHERITS RID ONE O TPX D - -
FIELD CORROBORATION TPS TEXT ONE R TPX D - VERSION
FIELD CORROBORATION D_IS TEXT ONE R TPX D - HEX64
FIELD CORROBORATION TARGET RID ONE R AUTHOR D - -
FIELD CORROBORATION OUTCOME ENUM ONE R TPX D - ENUM=OUTCOME
FIELD CORROBORATION DIFFERENCE TEXT ONE C TPX D - NOTBLANK
FIELD CORROBORATION INDEPENDENCE OBJECT ONE R TPX D - SUB=INDEPENDENCE
FIELD CORROBORATION TARGET_STATUS ENUM ONE R TPX D - ENUM=TARGET_STATUS
FIELD CORROBORATION SELF_REPORTED TEXT ONE O AUTHOR D - NOTBLANK
FIELD CORROBORATION DIGEST TEXT ONE O TPX X - HEX64,DIGEST
RULE CORROBORATION | IF OUTCOME = MATCH WITH DIFFERENCE NOTED
  | REQUIRE | DIFFERENCE
RULE CORROBORATION | IF OUTCOME = MATCH | FORBID | DIFFERENCE

FIELD VERIFICATION ID RID ONE R LEAD D - -
FIELD VERIFICATION CLASS ENUM ONE R AUTHOR D - ENUM=CLASS
FIELD VERIFICATION GRADE ENUM ONE R TPX D - GRADE
FIELD VERIFICATION STATUS ENUM ONE R TPX X - STATUS
FIELD VERIFICATION BLOCK TEXT ONE R TPX D - NOTBLANK
FIELD VERIFICATION AUTHOR TEXT ONE R TPX D - NOTBLANK
FIELD VERIFICATION LANDED_BY TEXT ONE R TPX D - NOTBLANK
FIELD VERIFICATION LANDED TEXT ONE R TPX D - UTC
FIELD VERIFICATION VETTED_IN TEXT ONE O TPX D - NOTBLANK
FIELD VERIFICATION CITES IDSET SET R AUTHOR D - RID
FIELD VERIFICATION ASSUMPTIONS IDSET SET R AUTHOR D - RID
FIELD VERIFICATION LITERATURE IDSET SET O AUTHOR D - BIBID,SETTING
FIELD VERIFICATION SUPERSEDES RID ONE O AUTHOR D - -
FIELD VERIFICATION INHERITS RID ONE O TPX D - -
FIELD VERIFICATION TPS TEXT ONE R TPX D - VERSION
FIELD VERIFICATION D_IS TEXT ONE R TPX D - HEX64
FIELD VERIFICATION REGIME ENUM ONE R AUTHOR D - ENUM=REGIME_M
FIELD VERIFICATION TARGET RID ONE R AUTHOR D - -
FIELD VERIFICATION EXTERNAL OBJECT ONE R AUTHOR D - SUB=EXTERNAL
FIELD VERIFICATION SOURCE TEXT ONE R AUTHOR D - NOTBLANK,BIBSOURCE
FIELD VERIFICATION AT OBJECT LIST O AUTHOR D EMPTY SUB=POINT
FIELD VERIFICATION DIFFERENCE OBJECT ONE R AUTHOR D - SUB=DIFFERENCE
FIELD VERIFICATION DIGEST TEXT ONE O TPX X - HEX64,DIGEST

FIELD NAMED_GAP ID RID ONE R TPX D - -
FIELD NAMED_GAP CLASS ENUM ONE R TPX D - ENUM=CLASS
FIELD NAMED_GAP GRADE ENUM ONE R TPX D - GRADE
FIELD NAMED_GAP LANDED_BY TEXT ONE R TPX D - TPXONLY
FIELD NAMED_GAP LANDED TEXT ONE R TPX D - UTC
FIELD NAMED_GAP TPS TEXT ONE R TPX D - VERSION
FIELD NAMED_GAP INHERITS RID ONE O TPX D - -
FIELD NAMED_GAP SOURCE ENUM ONE R TPX D - ENUM=GAP_SOURCE
FIELD NAMED_GAP AGAINST TEXT SET R TPX D - AGAINST
FIELD NAMED_GAP TRIGGER TEXT ONE R TPX D - NOTBLANK,TRIGGER
FIELD NAMED_GAP STATEMENT TEXT ONE R TPX D - NOTBLANK
FIELD NAMED_GAP STATE TEXT ONE R TPX X - STATELINE
FIELD NAMED_GAP DIGEST TEXT ONE O TPX X - HEX64,DIGEST

FIELD ENTRY_STATUS ID RID ONE R LEAD D - -
FIELD ENTRY_STATUS CLASS ENUM ONE R AUTHOR D - ENUM=CLASS
FIELD ENTRY_STATUS GRADE ENUM ONE R TPX D - GRADE
FIELD ENTRY_STATUS STATUS ENUM ONE R TPX X - STATUS
FIELD ENTRY_STATUS BLOCK TEXT ONE R TPX D - NOTBLANK
FIELD ENTRY_STATUS AUTHOR TEXT ONE R TPX D - NOTBLANK
FIELD ENTRY_STATUS LANDED_BY TEXT ONE R TPX D - NOTBLANK
FIELD ENTRY_STATUS LANDED TEXT ONE R TPX D - UTC
FIELD ENTRY_STATUS VETTED_IN TEXT ONE O TPX D - NOTBLANK
FIELD ENTRY_STATUS CITES IDSET SET R AUTHOR D - RID
FIELD ENTRY_STATUS ASSUMPTIONS IDSET SET R AUTHOR D - RID
FIELD ENTRY_STATUS LITERATURE IDSET SET O AUTHOR D - BIBID,SETTING
FIELD ENTRY_STATUS INHERITS RID ONE O TPX D - -
FIELD ENTRY_STATUS TPS TEXT ONE R TPX D - VERSION
FIELD ENTRY_STATUS D_IS TEXT ONE R TPX D - HEX64
FIELD ENTRY_STATUS ENTRY IDENT ONE R AUTHOR D - TRMENTRY
FIELD ENTRY_STATUS RIDER TEXT ONE O AUTHOR D - NOTBLANK
FIELD ENTRY_STATUS NOTE TEXT ONE O AUTHOR D - NOTBLANK
FIELD ENTRY_STATUS SCRUTINY TEXT ONE O AUTHOR D - NOTBLANK
FIELD ENTRY_STATUS CHECKS_OWED TEXT ONE O AUTHOR D - NOTBLANK
FIELD ENTRY_STATUS DIGEST TEXT ONE O TPX X - HEX64,DIGEST
RULE ENTRY_STATUS | ALWAYS | AT LEAST ONE | RIDER, NOTE, SCRUTINY, CHECKS_OWED

FIELD MASTER ID RID ONE R TPX D - MASTERID
FIELD MASTER CLASS ENUM ONE R TPX D - ENUM=CLASS
FIELD MASTER GRADE ENUM ONE R TPX D - GRADE
FIELD MASTER LANDED_BY TEXT ONE R TPX D - TPXONLY
FIELD MASTER LANDED TEXT ONE R TPX D - UTC
FIELD MASTER TPS TEXT ONE R TPX D - VERSION
FIELD MASTER UUID TEXT ONE R TPX D - UUID4
FIELD MASTER PREFIX IDENT ONE R TPX D - -
FIELD MASTER D_TPK TEXT ONE R TPX D - HEX64,ZONE=TPK
FIELD MASTER D_TRM TEXT ONE R TPX D - HEX64,ZONE=TrM
FIELD MASTER D_TMS TEXT ONE R TPX D - HEX64,ZONE=TMS
FIELD MASTER D_TFK TEXT ONE R TPX D - HEX64,DTFK
FIELD MASTER CERTIFICATE TEXT ONE R TPX D - NOTBLANK
FIELD MASTER STRUCTURE_LINE TEXT ONE R TPX D - NOTBLANK
FIELD MASTER MODULES_USED TEXT ONE R TPX D - NOTBLANK
FIELD MASTER DIGEST TEXT ONE O TPX X - HEX64,DIGEST

FIELD SUB:DERIVATION STEPS INT ONE R AUTHOR D - STEPS
FIELD SUB:DERIVATION TEXT TEXT ONE R AUTHOR D - NOTBLANK
FIELD SUB:COMPONENT NAME IDENT ONE R AUTHOR D - KEY
FIELD SUB:COMPONENT U DECIMAL ONE R AUTHOR D - NONNEG
FIELD SUB:COMPONENT UNIT UNIT ONE R AUTHOR D - -
FIELD SUB:COMPONENT EVALUATION ENUM ONE R AUTHOR D - ENUM=EVALUATION
FIELD SUB:COMPONENT BASIS TEXT ONE R AUTHOR D - NOTBLANK
FIELD SUB:POINT DOF IDENT ONE R AUTHOR D - KEY,TPKDOF
FIELD SUB:POINT VALUE DECIMAL ONE R AUTHOR D - -
FIELD SUB:POINT UNIT UNIT ONE R AUTHOR D - DIM=DOF
FIELD SUB:INDEPENDENCE ACCOUNT TEXT ONE R TPX D - NOTBLANK
FIELD SUB:INDEPENDENCE SNAPSHOT TEXT ONE R TPX D - NOTBLANK
FIELD SUB:INDEPENDENCE VENDOR TEXT ONE R TPX D - NOTBLANK
FIELD SUB:INDEPENDENCE IMPLEMENTATION TEXT ONE R TPX D - NOTBLANK
FIELD SUB:INDEPENDENCE ORIGIN ENUM ONE R TPX D - ENUM=ORIGIN
FIELD SUB:INDEPENDENCE NOT_SERVED_BEFORE BOOL ONE R TPX D - -
FIELD SUB:INDEPENDENCE SAME_SPONSOR BOOL ONE R TPX D - -
FIELD SUB:INDEPENDENCE SAME_MODEL BOOL ONE R TPX D - -
FIELD SUB:EXTERNAL VALUE DECIMAL ONE R AUTHOR D - -
FIELD SUB:EXTERNAL U_C DECIMAL ONE R AUTHOR D - NONNEG
FIELD SUB:EXTERNAL UNIT UNIT ONE R AUTHOR D - DIM=QUANTITY
FIELD SUB:EXTERNAL QUANTITY IDENT ONE R AUTHOR D - TRMENTRY
FIELD SUB:DIFFERENCE VALUE DECIMAL ONE R AUTHOR D - -
FIELD SUB:DIFFERENCE U DECIMAL ONE R AUTHOR D - POSITIVE
FIELD SUB:DIFFERENCE ZETA DECIMAL ONE R AUTHOR D - -
END RECORD TABLE
"

/-! ## Reading text -/

/-- `s` cut at every occurrence of `sep` (not empty), as Python's `str.split(sep)`. The
count bounds the steps: each consumes at least one character. -/
def splitChars (sep : List Char) (s : List Char) : List (List Char) :=
  go (s.length + 1) s [] []
where
  go : Nat → List Char → List Char → List (List Char) → List (List Char)
    | 0, _, cur, acc => acc ++ [cur.reverse]
    | _, [], cur, acc => acc ++ [cur.reverse]
    | n + 1, c :: cs, cur, acc =>
      if !sep.isEmpty && sep.isPrefixOf (c :: cs) then
        go n ((c :: cs).drop sep.length) [] (acc ++ [cur.reverse])
      else go n cs (c :: cur) acc

/-- `s.split(sep)`. -/
def split (s sep : String) : List String :=
  (splitChars sep.toList s.toList).map String.ofList

/-- `s.split(sep, 1)` when `sep` occurs: the text before its first occurrence and after. -/
def splitOnce (s sep : String) : Option (String × String) :=
  match splitChars sep.toList s.toList with
  | a :: b :: rest => some (String.ofList a, sep.intercalate (String.ofList b :: rest.map String.ofList))
  | _ => none

/-- ASCII white space, which `str.strip()` removes from a line of the table. -/
def spaceChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- `s.strip()` over ASCII white space (the table is ASCII). -/
def strip (s : String) : String :=
  String.ofList ((s.toList.dropWhile spaceChar).reverse.dropWhile spaceChar).reverse

/-! ## The table -/

/-- A `FIELD` line: the field's name, TYPE, CARD, REQ, WRITER, DIG, DEFAULT and
constraints (the last column, `-` for none, else comma-separated). -/
structure FieldRow where
  name : String
  type : String
  card : String
  req : String
  writer : String
  dig : String
  default : String
  cons : List String
  deriving Repr, Inhabited, DecidableEq

/-- A `RULE`'s condition: `IF <field> PRESENT`, `IF <field> ABSENT` or `IF <field> =
<value>` (`op` is `PRESENT`, `ABSENT` or `=`); `ALWAYS` is no condition. -/
structure Cond where
  field : String
  op : String
  value : String := ""
  deriving Repr, Inhabited, DecidableEq

/-- A `RULE` line: its condition, its action (`REQUIRE`, `FORBID`, `ALL OR NONE`, `AT
LEAST ONE`) and the fields it names. -/
structure Rule where
  cond : Option Cond
  action : String
  fields : List String
  deriving Repr, Inhabited, DecidableEq

/-- The table as v1's `_parse_table` reads it: each part keyed as v1 keys it, a `SUB`'s
fields under `SUB:<name>`. -/
structure Table where
  enums : List (String × List String) := []
  classes : List String := []
  form : List (String × String) := []
  writer : List (String × String) := []
  landgrade : List (String × String) := []
  grades : List (String × List String) := []
  statuses : List (String × List String) := []
  subs : List String := []
  subkey : List (String × Option String) := []
  fields : List (String × List FieldRow) := []
  rules : List (String × List Rule) := []
  deriving Repr, Inhabited

/-- Append `x` to the list under `k` (v1's `setdefault(k, []).append(x)`). -/
def appendAt {α : Type} : List (String × List α) → String → α → List (String × List α)
  | [], k, x => [(k, [x])]
  | (k', xs) :: rest, k, x =>
    if k' == k then (k', xs ++ [x]) :: rest else (k', xs) :: appendAt rest k x

/-- A `RULE`'s condition read (v1: `ALWAYS`, a condition ending ` PRESENT` or ` ABSENT`,
else `IF <field> = <value>`). -/
def readCond (c : String) : Option (Option Cond) :=
  if c == "ALWAYS" then some none
  else if c.endsWith " PRESENT" || c.endsWith " ABSENT" then
    match split c " " with
    | _ :: f :: op :: _ => some (some { field := f, op })
    | _ => none
  else
    match splitOnce (String.ofList (c.toList.drop "IF ".length)) " = " with
    | some (f, v) => some (some { field := f, op := "=", value := v })
    | none => none

/-- One joined line read into the table, or `none` for a line v1 refuses. -/
def readLine (t : Table) (ln : String) : Option Table :=
  let kw := (split ln " ").headD ""
  let after (n : Nat) := String.ofList (ln.toList.drop n)
  match kw with
  | "ENUM" => do
    let (name, vals) ← splitOnce (after "ENUM ".length) " = "
    pure { t with enums := t.enums ++ [(name, split vals " | ")] }
  | "CLASS" =>
    match split ln " " with
    | [_, name, form, writer] =>
      some { t with classes := t.classes ++ [name], form := t.form ++ [(name, form)],
                    writer := t.writer ++ [(name, writer)] }
    | _ => none
  | "LANDGRADE" => do
    let (name, vals) ← splitOnce (after (kw.length + 1)) " = "
    pure { t with landgrade := t.landgrade ++ [(name, vals)] }
  | "GRADES" => do
    let (name, vals) ← splitOnce (after (kw.length + 1)) " = "
    pure { t with grades := t.grades ++ [(name, split vals " | ")] }
  | "STATUSES" => do
    let (name, vals) ← splitOnce (after (kw.length + 1)) " = "
    pure { t with statuses := t.statuses ++ [(name, split vals " | ")] }
  | "SUB" =>
    match split ln " " with
    | [_, name, _, key] =>
      some { t with subs := t.subs ++ [name],
                    subkey := t.subkey ++ [(name, if key == "-" then none else some key)] }
    | _ => none
  | "FIELD" =>
    match split ln " " with
    | [_, owner, name, type, card, req, writer, dig, default, cons] =>
      let row : FieldRow := { name, type, card, req, writer, dig, default,
                              cons := if cons == "-" then [] else split cons "," }
      some { t with fields := appendAt t.fields owner row }
    | _ => none
  | "RULE" =>
    match split ln " | " with
    | [head, cond, action, fields] => do
      let cls ← (split head " ")[1]?
      let c ← readCond cond
      pure { t with rules := appendAt t.rules cls { cond := c, action, fields := split fields ", " } }
    | _ => none
  | _ => none

/-- The lines between `BEGIN RECORD TABLE` and `END RECORD TABLE`, each continuation
line joined to the line before it by one space, blank lines dropped. -/
def joinedLines (text : String) : Option (List String) := do
  let lines := split text "\n"
  let i0 ← lines.idxOf? "BEGIN RECORD TABLE"
  let i1 ← lines.idxOf? "END RECORD TABLE"
  let body := (lines.take i1).drop (i0 + 1)
  pure (body.foldl (fun acc ln =>
    if ln.startsWith "  " then
      match acc.getLast? with
      | some last => acc.dropLast ++ [last ++ " " ++ strip ln]
      | none => acc
    else if strip ln != "" then acc ++ [ln] else acc) [])

/-- v1's `_parse_table`, or `none` where v1 raises. -/
def parseTable (text : String) : Option Table := do
  let lines ← joinedLines text
  lines.foldlM readLine {}

/-- The table, read once. `parseTable tableText` reads (the vector runner checks it). -/
def table : Table := (parseTable tableText).getD {}

/-! ## Reading the table, as v1's functions read `T` -/

/-- v1's `T["classes"]`: the eleven classes in the table's order. -/
def classes : List String := table.classes

/-- v1's `KEYED`: the classes of the keyed form. -/
def keyed : List String := classes.filter fun c => table.form.lookup c == some "KEYED"

/-- v1's `T["enums"][name]`. -/
def enumValues (name : String) : List String := (table.enums.lookup name).getD []

/-- v1's `GRADE_VALUES`. -/
def gradeValues : List String := enumValues "GRADE_VALUES"

/-- v1's `T["form"][cls]`. -/
def formOf (cls : String) : String := (table.form.lookup cls).getD ""

/-- v1's `T["writer"][cls]`. -/
def writerOf (cls : String) : String := (table.writer.lookup cls).getD ""

/-- v1's `T["landgrade"][cls]`. -/
def landgradeOf (cls : String) : String := (table.landgrade.lookup cls).getD ""

/-- v1's `T["grades"][cls]`. -/
def gradesOf (cls : String) : List String := (table.grades.lookup cls).getD []

/-- v1's `T["statuses"].get(cls, [])`. -/
def statusesOf (cls : String) : List String := (table.statuses.lookup cls).getD []

/-- v1's `T["fields"][key]`: a class's fields, or a sub-object's under `SUB:<name>`. -/
def fieldsOf (key : String) : List FieldRow := (table.fields.lookup key).getD []

/-- v1's `T["rules"].get(cls, [])`. -/
def rulesOf (cls : String) : List Rule := (table.rules.lookup cls).getD []

/-- v1's `T["subkey"][sub]`. -/
def subkeyOf (sub : String) : Option String := ((table.subkey.lookup sub).getD none)

/-- v1's `_cons_value`: the rest of the first constraint with the prefix. -/
def FieldRow.consValue (f : FieldRow) (pre : String) : Option String :=
  (f.cons.find? (·.startsWith pre)).map fun c => String.ofList (c.toList.drop pre.length)

/-- v1's `_field`: the field of the name. -/
def fieldNamed (fields : List FieldRow) (name : String) : Option FieldRow :=
  fields.find? (·.name == name)

end Principia.Record.Table
