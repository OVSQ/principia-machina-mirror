import Tests.Calculator.Common

/-!
The Calculator's runners across families: the JSON reader and the bounds of every family and of a request.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## json_text.json: the reader -/

def runJsonText : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← arr (← readJson "vectors/json_text.json") do
    let what := c.compress
    let got := readText (← input c "text" "bytes")
    match c.getObjValAs? String "refused" with
    | .ok code =>
      let pos : Option Nat ← match c.getObjVal? "position" with
        | .ok .null => pure none
        | .ok (.num ⟨p, 0⟩) => pure (some p.toNat)
        | _ => throw (IO.userError s!"{what}: no position")
      let ok := match got with
        | .error f => WireWord.toWire f.error == code && f.position == pos
        | .ok _ => false
      t ← t.check ok s!"{what}: got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error f => some f | _ => none)}"
    | .error _ =>
      match got with
      | .error f => t ← t.check false s!"{what}: refused {repr f}"
      | .ok v =>
        match c.getObjValAs? String "canonical" with
        | .ok text =>
          t ← t.check (v.canonicalJson == some text) s!"{what}: got {repr v.canonicalJson}"
        | .error _ =>
          let expected ← value (← field c "value")
          t ← t.check (v == expected) s!"{what}: got {repr v}"
        t ← t.check (rereads v) s!"{what}: its canonical JSON does not read back alike"
  -- Built here, too long for a corpus line: the size bound, and numbers in a text.
  let spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
  let atLimit := (spaces (maxTextBytes - 1) ++ "1").toUTF8
  t ← t.check ((readText atLimit).toOption.isSome) s!"a text of exactly {maxTextBytes} bytes is read"
  let overLimit := (spaces maxTextBytes ++ "1").toUTF8
  t ← t.check (refusedWith (readText overLimit) ⟨.tooLarge, none⟩)
    s!"a text of {maxTextBytes + 1} bytes is refused TOO_LARGE"
  let digits (n : Nat) : String := String.ofList (List.replicate n '7')
  t ← t.check ((readString ("[" ++ digits maxNumberDigits ++ "]")).toOption.isSome)
    s!"a number of {maxNumberDigits} digits in a text is read"
  t ← t.check (refusedWith (readString ("[" ++ digits (maxNumberDigits + 1) ++ "]"))
      ⟨.numberTooLong, some 1⟩)
    s!"a number of {maxNumberDigits + 1} digits in a text is refused NUMBER_TOO_LONG"
  return t.pair

/-- A `user_evidence` request of `events` events FOR, each of weight 1, and `ages` ages of 0. -/
def evidenceRequest (events ages : Nat) : Value :=
  .obj [("events", .arr ((List.range events).map fun _ =>
      .obj [("kind", .str "AGENT"), ("resolution", .str "FOR"), ("weight", .int 1)])),
    ("ages", .arr ((List.range ages).map fun _ => .int 0)),
    ("g", .obj [("CE-F1", .int 1), ("CE-F2", .int 1)]),
    ("h", .obj [("CE-A1", .int 2), ("CE-A2", .int 3), ("CE-A3", .int 3), ("CE-A4", .int 2),
      ("CE-A5", .int 3)]),
    ("a0", .int 1), ("b0", .int 1), ("half_life", .int 500)]

/-- A `whitewash_count` request of `adm` admissions, `ret` retirements and `st` states, none
of an agent then troubled. -/
def whitewashRequest (adm ret st : Nat) : Value :=
  .obj [("admissions", .arr ((List.range adm).map fun i =>
      .obj [("agent", .str s!"A{i}"), ("time", .int 1000)])),
    ("retirements", .arr ((List.range ret).map fun i =>
      .obj [("agent", .str s!"R{i}"), ("time", .int 1000)])),
    ("states", .obj ((List.range st).map fun i =>
      (s!"R{i}", .obj [("state", .str "GREEN"), ("pending", .int 0)]))),
    ("window", .int 10)]

/-- A `lint` request of a zone of `n` zero-width spaces, one finding each. -/
def hiddenZone (n : Nat) : Value :=
  .obj [("zone_parts", .arr [.arr [.str "\u200b", .int n]]), ("tools", .str "[]"),
    ("cap", .int 1048576)]
/-- `n` letters `m`: one token, no unit symbol. -/
def letters (n : Nat) : String := String.ofList (List.replicate n 'm')

/-- The unit `m` written `n` times, one token each. -/
def metres (n : Nat) : String := " ".intercalate (List.replicate n "m")

/-- A decimal of `n` digits. -/
def digitText (n : Nat) : String := "1" ++ String.ofList (List.replicate (n - 1) '0')

/-- `n` measurements in metres whose values carry `d` digits. -/
def unitMeasurements (n d : Nat) : Value :=
  .arr ((List.range n).map fun i =>
    .obj [("x", .str ("1." ++ String.ofList (List.replicate (d - 2) '0') ++ toString (i % 10))),
      ("u", .str "1"), ("unit", .str "m")])
/-- A Starting Set of the DOF `t` and `d - 1` unknowns, `c` CONSTANTs, `l` laws (law `i`:
`D(x_i, t) = x_(i+1)`, of ROLE EOM(x_i)) and `k` FIXes; `d` at least 2. -/
def eomTfk (d c l k : Nat) : Value :=
  let x (i : Nat) : String := s!"x{i % (d - 1)}"
  .obj [("TPK", .obj [
      ("DOF", .arr (.obj [("NAME", .str "t")] ::
        (List.range (d - 1)).map fun i => .obj [("NAME", .str s!"x{i}")])),
      ("CONSTANT", .arr ((List.range c).map fun i => .obj [("NAME", .str s!"c{i}")])),
      ("LAW", .arr ((List.range l).map fun i => .obj [("NAME", .str s!"L{i}"),
        ("ROLE", .str s!"EOM({x i})"), ("EQUATION", .str s!"D({x i}, t) = {x (i + 1)}")])),
      ("CONSTRAINT", .arr ((List.range k).map fun i => .obj [("NAME", .str s!"C{i}"),
        ("TARGET", .str (x i)), ("ACTION", .str "FIX"), ("VALUE", .str "0")]))]),
    ("TMS", .obj [("PARAMETERS", .obj [])])]

/-- `n` standing records, record `i` of ROLE EOM(x_i) and the form `D(x_i, t) = x_i`, over
`d - 1` unknowns. -/
def eomRecords (n d : Nat) : Value :=
  .arr ((List.range n).map fun i => .obj [("ID", .str s!"R-{i + 1}"),
    ("STATUS", .str "PROVISIONAL"), ("ROLE", .str s!"EOM(x{i % (d - 1)})"),
    ("EQUATION", .str s!"D(x{i % (d - 1)}, t) = x{i % (d - 1)}")])

/-- A Starting Set of the DOFs `t` and `x0` and one law whose EQUATION's text is `n` code
points, at least 13: `D(x0, t) = x0` and spaces. -/
def eomLongLaw (n : Nat) : Value :=
  .obj [("TPK", .obj [("DOF", .arr [.obj [("NAME", .str "t")], .obj [("NAME", .str "x0")]]),
      ("LAW", .arr [.obj [("NAME", .str "L0"), ("ROLE", .str "EOM(x0)"),
        ("EQUATION", .str ("D(x0, t) = " ++ String.ofList (List.replicate (n - 13) ' ') ++ "x0"))]])]),
    ("TMS", .obj [("PARAMETERS", .obj [])])]

/-- A settlement check over `n` OPEN UNDER gaps, `w` status words and `k` namings. -/
def eomSettlement (n w k : Nat) : Value :=
  .obj [("tfk", eomTfk 3 1 1 0),
    ("records", .arr ((List.range n).map fun i => .obj [("ID", .str s!"G-{i + 1}"),
      ("CLASS", .str "NAMED_GAP"), ("SOURCE", .str "UNDER"), ("STATE", .str "OPEN"),
      ("AGAINST", strs [s!"u{1000 + i}"])])),
    ("words", .obj ((List.range w).map fun i => (s!"G-{i + 1}", .str "NOT GRADED"))),
    ("naming", .arr ((List.range k).map fun i => strs [s!"u{1000 + i}", s!"G-{i + 1}"]))]
/-- A register of one RESULT record `R0` with `n` AT points, each of `value` in `unit`. -/
def pointsRegister (n : Nat) (value unit : String) : Value :=
  .arr [.obj [("ID", .str "R0"), ("CLASS", .str "RESULT"), ("AT", .arr ((List.range n).map
    fun i => .obj [("DOF", .str s!"t{i}"), ("VALUE", .str value), ("UNIT", .str unit)]))]]

/-- A `conditions_of` request for `R0`. -/
def conditionsRequest (records : Value) : Value := .obj [("records", records), ("id", .str "R0")]

/-- A `comparison_set` or `sr8_groups` request over `E_x`, an entry of the Research
Assembly's Correspondence Table, with no status word given. -/
def scopeRequest (records : Value) : Value :=
  .obj [("records", records), ("words", .obj []), ("quantity", .str "E_x"),
    ("tfk", .obj [("TrM", .obj [("ENTRIES", .arr [.obj [("NAME", .str "E_x"),
      ("DOF", .str "x")]])]), ("TPK", .obj [])])]

/-- A `landing strike_screen` request over `records`, the batch `R0`. -/
def screenRequest (records : Value) : Value :=
  .obj [("records", records), ("incoming", strs ["R0"]),
    ("tfk", .obj [("TrM", .obj [("ENTRIES", .arr [.obj [("NAME", .str "E_x"),
      ("DOF", .str "x")]])]), ("TPK", .obj [])])]

/-- A unit of `n` metres and a square second: `2n + 2` characters. -/
def longUnit (n : Nat) : String := " ".intercalate (List.replicate n "m") ++ " s2"

def runFamilyBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × String × Value × Bool) := [
    ("DOF at 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 1 0)], false),
    ("DOF past 64", "eom", "eom_map", .obj [("tfk", eomTfk 65 1 1 0)], true),
    ("CONSTANT at 64", "eom", "eom_findings", .obj [("tfk", eomTfk 3 64 1 0)], false),
    ("CONSTANT past 64", "eom", "eom_findings", .obj [("tfk", eomTfk 3 65 1 0)], true),
    ("LAW at 64", "eom", "eom_class", .obj [("tfk", eomTfk 64 1 64 0)], false),
    ("LAW past 64", "eom", "eom_class", .obj [("tfk", eomTfk 64 1 65 0)], true),
    ("CONSTRAINT at 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 2 64)], false),
    ("CONSTRAINT past 64", "eom", "eom_map", .obj [("tfk", eomTfk 64 1 2 65)], true),
    ("a LAW's EQUATION at 16384 code points", "eom", "eom_map",
      .obj [("tfk", eomLongLaw 16384)], false),
    ("a LAW's EQUATION past 16384 code points", "eom", "eom_map",
      .obj [("tfk", eomLongLaw 16385)], true),
    ("register records at 64", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 64 1 64 0), ("records", eomRecords 64 64)], false),
    ("register records past 64", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 64 1 64 0), ("records", eomRecords 65 64)], true),
    ("a record's EQUATION past 16384 code points", "eom", "eom_register_test",
      .obj [("tfk", eomTfk 3 1 1 0), ("records", .arr [.obj [("ID", .str "R-1"),
        ("STATUS", .str "PROVISIONAL"), ("ROLE", .str "EOM(x0)"),
        ("EQUATION", .str (String.ofList (List.replicate 16385 ' ')))]])], true),
    ("settlement records, words and namings at 64", "eom", "settlement_check",
      eomSettlement 64 64 64, false),
    ("settlement records past 64", "eom", "settlement_check", eomSettlement 65 1 1, true),
    ("settlement words past 64", "eom", "settlement_check", eomSettlement 1 65 1, true),
    ("settlement namings past 64", "eom", "settlement_check", eomSettlement 1 1 65, true),
    ("probe records at 400", "probe", "load", .obj [("records", probeRecords 400), ("r", .str "P1")], false),
    ("probe records past 400", "probe", "load", .obj [("records", probeRecords 401), ("r", .str "P1")], true),
    ("probe revisions at 4000", "probe", "historical_view",
      .obj [("revisions", revisions 4000 1), ("target", .str "a0_0")], false),
    ("probe revisions past 4000", "probe", "historical_view",
      .obj [("revisions", revisions 4001 0), ("target", .str "a0_0")], true),
    ("probe allocated at 4000", "probe", "historical_view",
      .obj [("revisions", revisions 2 2000), ("target", .str "a0_0")], false),
    ("probe allocated past 4000", "probe", "historical_view",
      .obj [("revisions", revisions 2 2001), ("target", .str "a0_0")], true),
    ("probe standing at 100", "probe", "compare", standingCompare 100 30, false),
    ("probe standing past 100", "probe", "compare", standingCompare 101 1, true),
    ("probe standing digits past 30", "probe", "compare", standingCompare 1 31, true),
    ("rows at 1000", "cluster", "cluster", .obj [("rows", clusterRows 1000)], false),
    ("rows past 1000", "cluster", "cluster", .obj [("rows", clusterRows 1001)], true),
    ("paired at 5000", "cluster", "cluster",
      .obj [("rows", clusterRows 3), ("paired", .arr ((List.range 5000).map fun _ => .null))], false),
    ("paired past 5000", "cluster", "cluster",
      .obj [("rows", clusterRows 3), ("paired", .arr ((List.range 5001).map fun _ => .null))], true),
    ("ses at 1000", "cluster", "resolving_step",
      .obj [("spacing", .int 1), ("ses", .arr ((List.range 1000).map fun _ => .int 1))], false),
    ("ses past 1000", "cluster", "resolving_step",
      .obj [("spacing", .int 1), ("ses", .arr ((List.range 1001).map fun _ => .int 1))], true),
    ("records at 2000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 2000 1)], false),
    ("records past 2000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 2001 1)], true),
    ("record entries at 20000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 1000 19)], false),
    ("record entries past 20000", "strike", "a_of_r",
      .obj [("rid", .str "R0"), ("records", strikeRecords 1000 20)], true),
    ("register records at 2000", "strike", "conditions_of", conditionsRequest (register 2000 1), false),
    ("register records past 2000", "strike", "conditions_of", conditionsRequest (register 2001 1), true),
    ("register entries at 5000", "strike", "conditions_of", conditionsRequest (register 2 5000), false),
    ("register entries past 5000", "strike", "conditions_of", conditionsRequest (register 2 5001), true),
    ("scope records at 200", "strike", "comparison_set", scopeRequest (register 200 1), false),
    ("scope records past 200", "strike", "comparison_set", scopeRequest (register 201 1), true),
    ("scope records past 200, the groups", "strike", "sr8_groups", scopeRequest (register 201 1), true),
    ("scope entries at 500", "strike", "sr8_groups", scopeRequest (register 2 500), false),
    ("scope entries past 500", "strike", "sr8_groups", scopeRequest (register 2 501), true),
    ("scope entries past 500, the pairs", "strike", "comparison_set", scopeRequest (register 2 501), true),
    ("screen records at 225", "landing", "strike_screen", screenRequest (register 225 1), false),
    ("screen records past 225", "landing", "strike_screen", screenRequest (register 226 1), true),
    ("screen entries at 1500", "landing", "strike_screen", screenRequest (register 2 1500), false),
    ("screen entries past 1500", "landing", "strike_screen", screenRequest (register 2 1501), true),
    ("screen AT points past 1000", "landing", "strike_screen", screenRequest (.arr [.obj [("ID", .str "R0"), ("CLASS", .str "RESULT"),
      ("QUANTITY", .str "E_x"), ("AT", .arr ((List.range 1001).map fun i =>
        .obj [("DOF", .str s!"t{i}"), ("VALUE", .str "1.5"), ("UNIT", .str "m")]))]]), true),
    ("screen records past 225, no QUANTITY reached", "landing", "strike_screen",
      .obj [("records", .arr ((List.range 226).map fun i => .obj [("ID", .str s!"R{i}")])),
        ("incoming", strs ["R0"]), ("tfk", .obj [])], false),
    ("AT points at 1000", "strike", "conditions_of", conditionsRequest (pointsRegister 1000 "1.5" "m"), false),
    ("AT points past 1000", "strike", "conditions_of", conditionsRequest (pointsRegister 1001 "1.5" "m"), true),
    ("AT points past 1000, the pairs", "strike", "comparison_set", scopeRequest (pointsRegister 1001 "1.5" "m"), true),
    ("AT VALUE at 64 characters", "strike", "conditions_of",
      conditionsRequest (pointsRegister 1 ("1." ++ String.ofList (List.replicate 62 '2')) "m"), false),
    ("AT VALUE past 64 characters", "strike", "conditions_of",
      conditionsRequest (pointsRegister 1 ("1." ++ String.ofList (List.replicate 63 '2')) "m"), true),
    ("AT UNIT at 64 characters", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1" (longUnit 31)), false),
    ("AT UNIT past 64 characters", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1" (longUnit 31 ++ "0")), true),
    ("AT value at 2048 bits", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1e-616" "m"), false),
    ("AT value past 2048 bits", "strike", "conditions_of", conditionsRequest (pointsRegister 1 "1e-617" "m"), true),
    ("AT value past 2048 bits, the groups", "strike", "sr8_groups", scopeRequest (pointsRegister 1 "1e-617" "m"), true),
    ("SR6 identifiers at 128", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 16).map fun i =>
        strs ((List.range 8).map fun j => s!"p{i}_{j}")))], false),
    ("SR6 identifiers past 128", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 16).map (fun i =>
        strs ((List.range 8).map fun j => s!"p{i}_{j}")) ++ [strs ["q"]]))], true),
    ("SR6 sets at 1000", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 1000).map fun _ => strs [])),
            ("same_model", .arr ((List.range 1000).map fun _ => .bool true))], false),
    ("SR6 sets past 1000", "strike", "sr6_independence_count",
      .obj [("sets", .arr ((List.range 1001).map fun _ => strs [])),
            ("same_model", .arr ((List.range 1001).map fun _ => .bool true))], true),
    ("SR8 measurements at 100", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 100 3)], false),
    ("SR8 measurements past 100", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 101 3)], true),
    ("SR8 digits at 30", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 2 30)], false),
    ("SR8 digits past 30", "strike", "sr8_scale_factor",
      .obj [("measurements", measurements 2 31)], true),
    ("suite records at 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 1 0)], false),
    ("suite records past 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 51 1 0)], true),
    ("suite contradictions past 50", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 10 1 51)], true),
    ("suite entries at 500", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 9 0)], false),
    ("suite entries past 500", "sr9", "sr9_harness",
      .obj [("entry", .str "skeleton"), ("suite", suite 50 10 0)], true),
    ("pages at 1000", "digest", "digest_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1000)], false),
    ("pages past 1000", "digest", "digest_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1001)], true),
    ("pages past 1000, the list", "digest", "specification_pages",
      .obj [("pages", specPages 1001)], true),
    ("pages past 1000, the preimage", "digest", "preimage_specification",
      .obj [("version", .str "1.0.0"), ("pages", specPages 1001)], true),
    ("members at 1000", "digest", "digest_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1000)],
      false),
    ("members past 1000", "digest", "digest_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1001)],
      true),
    ("members past 1000, the preimage", "digest", "preimage_instruction_set",
      .obj [("version", .str "1.0.0"), ("specification", .str hex64a), ("members", members 1001)],
      true),
    ("findings' text at 1048576 characters", "lint", "lint", hiddenZone 19993, false),
    ("findings' text past 1048576 characters", "lint", "lint", hiddenZone 19994, true),
    ("the counts of findings past it", "lint", "counts", hiddenZone 19994, false),
    ("events at 50", "sponsor", "user_evidence", evidenceRequest 50 50, false),
    ("events past 50", "sponsor", "user_evidence", evidenceRequest 51 51, true),
    ("ages past 50", "sponsor", "user_evidence", evidenceRequest 50 51, true),
    ("agents at 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4000 4000, false),
    ("admissions past 4000", "sponsor", "whitewash_count", whitewashRequest 4001 4000 4000, true),
    ("retirements past 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4001 4000, true),
    ("states past 4000", "sponsor", "whitewash_count", whitewashRequest 4000 4000 4001, true),
    ("a unit of 1024 characters", "units", "unit_parse", .obj [("u", .str (letters 1024))], false),
    ("a unit past 1024 characters", "units", "unit_parse", .obj [("u", .str (letters 1025))], true),
    ("a unit of 128 tokens", "units", "unit_scale", .obj [("u", .str (metres 128))], false),
    ("a unit past 128 tokens", "units", "unit_scale", .obj [("u", .str (metres 129))], true),
    ("a dimension past 1024 characters", "units", "unit_matches",
      .obj [("u", .str "m"), ("dimension", .str (letters 1025))], true),
    ("a value of 4096 characters", "units", "normalize_measurement",
      .obj [("value", .str (digitText 4096)), ("uncertainty", .str "0"), ("u", .str "m")], false),
    ("a value past 4096 characters", "units", "normalize_measurement",
      .obj [("value", .str (digitText 4097)), ("uncertainty", .str "0"), ("u", .str "m")], true),
    ("x_m past 4096 characters", "units", "lm_contradicts_units",
      .obj [("x_l", .str "1"), ("unit_l", .str "m"), ("x_m", .str (digitText 4097)),
        ("u_m", .str "1"), ("unit_m", .str "m"), ("k", .int 2)], true),
    ("SR8 units, measurements at 100", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 100 30)], false),
    ("SR8 units, measurements past 100", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 101 1)], true),
    ("SR8 units, digits past 30", "units", "sr8_scale_factor_units",
      .obj [("measurements", unitMeasurements 2 31)], true)]
  for (what, family, fn, request, refused) in cases do
    let got := respondTo family fn request
    t ← t.check (boundRefusal got == refused)
      s!"{family} {fn}, {what}: refused by the bound {boundRefusal got}, expected {refused}"
  -- The bound on an exact value, where a unit's scale meets it: held in lowest terms, the
  -- scale is refused exactly when its numerator or denominator passes 65,536 bits.
  let tooLarge : List (String × String × Value × Bool) := [
    ("a scale whose denominator has 65,536 bits", "unit_scale",
      .obj [("u", .str "arcsec9286 Qrad1635 hrad")], false),
    ("a scale whose denominator has 65,537 bits", "unit_scale",
      .obj [("u", .str "arcsec9286 Qrad1635 darad")], true),
    ("a value in a unit whose scale has 65,537 bits", "normalize_measurement",
      .obj [("value", .str "1"), ("uncertainty", .str "0"), ("u", .str "arcsec9286 Qrad1635 darad")],
      true),
    ("SR3 over a scale of 32,748 bits, squared", "mm_contradicts_units",
      .obj [("x1", .str "1"), ("u1", .str "1"), ("unit1", .str "arcsec4662 Qrad826"),
        ("x2", .str "2"), ("u2", .str "1"), ("unit2", .str "arcsec4662 Qrad826"), ("k", .int 2)],
      false),
    ("SR3 over a scale of 32,780 bits, squared", "mm_contradicts_units",
      .obj [("x1", .str "1"), ("u1", .str "1"), ("unit1", .str "arcsec4667 Qrad827"),
        ("x2", .str "2"), ("u2", .str "1"), ("unit2", .str "arcsec4667 Qrad827"), ("k", .int 2)],
      true)]
  for (what, fn, request, refused) in tooLarge do
    let got := respondTo "units" fn request
    let isTooLarge := match got with
      | .error r => r.code == .badArgument && r.detail == Principia.ValueBound.tooLarge
      | .ok _ => false
    t ← t.check (isTooLarge == refused && (refused || got.toOption.isSome))
      s!"units {fn}, {what}: refused as too large {isTooLarge}, expected {refused}"
  return t.pair

/-- `n` combining marks of falling class, 230, 220, 202 and 1, over and over: each run is
sorted by canonical ordering. -/
def fallingMarks (n : Nat) : String :=
  String.ofList ((List.range n).map fun i => match i % 4 with
    | 0 => '́' | 1 => '̖' | 2 => '̧' | _ => '̴')

/-- A request's text of exactly `size` bytes: `{"<name>":"` and `"}` around `fill` repeated. -/
def requestOfSize (name : String) (fill : Char) (size : Nat) : ByteArray :=
  let head := "{\"" ++ name ++ "\":\""
  (head ++ String.ofList (List.replicate (size - head.utf8ByteSize - 2) fill) ++ "\"}").toUTF8

/-- A number of 308 digits, near the reader's bound below 2^1024. -/
def nearBound : Value := .int (10 ^ 307 + 7)

/-- The new families' bounds, each at and past it, through `Calculator.answer` (the reader
included); the slowest accepted request of each family is timed and printed. -/
def runRequestBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let text (s : String) : ByteArray :=
    ((Value.obj [("text", .str s)]).canonicalJson.getD "").toUTF8
  let at_ := String.singleton 'a' ++ fallingMarks (Principia.Calculator.Unicode.maxText - 1)
  let past := at_ ++ "́"
  let big := Value.obj [("state", .obj [("now", nearBound), ("agent_stop", .bool false),
      ("suspended", .bool false), ("governor_off", .bool false),
      ("agent_seats", .arr [nearBound, .int 0]), ("sponsor_seats", .arr [nearBound, .int 0]),
      ("agent_in_flight", .int 0), ("sponsor_in_flight", .int 0), ("finishing_in_flight", .int 0),
      ("starting_in_flight", .int 0), ("tuning", .obj [("agent_seat_rate", nearBound),
        ("sponsor_seat_rate", .int 1), ("sponsor_seat_burst", nearBound),
        ("agent_seat_burst", .int 1), ("retry_after_jitter", .arr [nearBound, nearBound])])]),
    ("request", .obj [("kind", .str "PUSH"), ("seats", nearBound), ("draw", .arr [nearBound, nearBound])])]
  let words := Value.arr ((List.replicate 100000 "LISTED").map .str)
  let bigUse := Value.obj [("hour", nearBound), ("day", nearBound), ("thirty_days", nearBound)]
  let bigLevel := Value.obj [("use", bigUse), ("prev", .str "OVERLOADED"),
    ("external_until", nearBound), ("now", nearBound),
    ("tuning", .obj [("kappa_m", .arr [nearBound, nearBound]), ("descent", .str "BANDS")])]
  let bigPressure := match big with
    | .obj ms => Value.obj (ms.map fun ((k : String), (v : Value)) => match k, v with
      | "state", Value.obj st => (k, Value.obj (st ++ [("use", bigUse), ("pressure", .str "OVERLOADED"),
          ("external_until", nearBound), ("anonymous_in_flight", nearBound)]))
      | _, _ => (k, v))
    | v => v
  let bigRecord := Value.obj [("stage", .str "PENALIZED"), ("breaker_until", nearBound),
    ("trial_pending", .bool true), ("retry_after", nearBound), ("backoff_until", nearBound),
    ("streak", nearBound), ("te3_times", .arr (List.replicate 10 nearBound)),
    ("throttled_times", .arr [nearBound, nearBound]), ("penalized_times", .arr [nearBound, nearBound]),
    ("last_event", nearBound), ("flood_inquire", nearBound), ("flood_release", nearBound)]
  let bigTuning := Value.obj [("retry_after_cap", nearBound), ("penalty_hour", nearBound),
    ("flood_interval", nearBound), ("error_streak", nearBound), ("doubling", .str "PER EVENT")]
  let bigTraffic := Value.obj [("traffic", bigRecord), ("now", nearBound),
    ("end", .obj [("kind", .str "PETITION"), ("ending", .str "RATE"), ("retry_after", nearBound)]),
    ("tuning", bigTuning)]
  let bigStage := Value.obj [("traffic", bigRecord), ("now", nearBound), ("kind", .str "INQUIRE"),
    ("tuning", bigTuning)]
  let cases : List (String × String × String × ByteArray × Bool) := [
    ("governor", "admit", "admit with every number near 2^1024",
      ((big.canonicalJson.getD "").toUTF8), true),
    ("governor", "pressure_level", "pressure_level with every number near 2^1024",
      ((bigLevel.canonicalJson.getD "").toUTF8), true),
    ("governor", "admit", "admit from the uses, every number near 2^1024",
      ((bigPressure.canonicalJson.getD "").toUTF8), true),
    ("governor", "traffic_step", "traffic_step with every number near 2^1024",
      ((bigTraffic.canonicalJson.getD "").toUTF8), true),
    ("governor", "traffic_stage", "traffic_stage with every number near 2^1024",
      ((bigStage.canonicalJson.getD "").toUTF8), true),
    ("permissions", "permits", "permits with 100,000 context words",
      (((Value.obj [("asker", .str "HOLDER"), ("class", .str "REGISTER OPEN"),
        ("op", .str "WRITE"), ("context", words)]).canonicalJson.getD "").toUTF8), true),
    ("sha256", "digest_text", "digest_text of a request of 1 MiB",
      requestOfSize "text" 'a' Principia.Canonical.maxTextBytes, true),
    ("sha256", "digest_text", "digest_text of a request of 1 MiB and a byte",
      requestOfSize "text" 'a' (Principia.Canonical.maxTextBytes + 1), false),
    ("sha256", "digest", "digest of a request of 1 MiB",
      requestOfSize "hex" 'a' Principia.Canonical.maxTextBytes, true),
    ("sha256", "digest", "digest of a request of 1 MiB and a byte",
      requestOfSize "hex" 'a' (Principia.Canonical.maxTextBytes + 1), false),
    ("unicode", "nfc", "nfc at 131,072 code points, a run of falling marks", text at_, true),
    ("unicode", "nfc", "nfc past 131,072 code points", text past, false),
    ("unicode", "nfd", "nfd at 131,072 code points, a run of falling marks", text at_, true),
    ("unicode", "nfd", "nfd past 131,072 code points", text past, false),
    ("unicode", "general_category", "general_category at 131,072 code points", text at_, true),
    ("unicode", "general_category", "general_category past 131,072 code points", text past, false)]
  let mut slowest : List (String × Nat) := []
  for (family, fn, what, bytes, accepted) in cases do
    let start ← IO.monoMsNow
    let (out, code) := answer family fn bytes
    t ← t.check ((code == 0) == accepted && (accepted || out.startsWith "{\"detail\":"))
      s!"{family} {fn}, {what}: exit {code}, {(out.take 200).toString}"
    let ms := (← IO.monoMsNow) - start
    if accepted then
      slowest := match slowest.lookup family with
        | some m => if m < ms then (family, ms) :: slowest.filter (·.1 != family) else slowest
        | none => (family, ms) :: slowest
  -- The answers at the bounds agree with the library, and a digest reads upper case alike.
  let lower := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str "616263")]))
  let upper := canonOf (respondTo "sha256" "digest" (.obj [("hex", .str "616263".toUpper)]))
  t ← t.check (lower == upper && lower == (Value.str (Principia.Sha256.digestText "abc")).canonicalJson)
    s!"sha256 digest of 616263: {repr lower}, upper case {repr upper}"
  t ← t.check (refusalOf (respondTo "sha256" "digest" (.obj [("hex", .str "abc")])) == some .badArgument)
    "sha256 digest of an odd count of digits is not refused BAD_ARGUMENT"
  t ← t.check (canonOf (respondTo "unicode" "nfc" (.obj [("text", .str at_)])) ==
      (Value.str (Principia.Unicode.nfc at_)).canonicalJson) "unicode nfc at the bound"
  let shown := ", ".intercalate ((slowest.reverse).map fun (f, m) => s!"{f} {m} ms")
  IO.println s!"pcalc request bounds: the slowest accepted request of each family, reading included: {shown}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Interface

open Tests.Calculator

/-- The cross-family runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("json_text", runJsonText),
  ("pcalc family bounds", runFamilyBounds),
  ("pcalc request bounds (governor, permissions, sha256, unicode)", runRequestBounds),
]

end Tests.Calculator.Interface
