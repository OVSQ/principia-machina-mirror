import Principia.Record.Bounded
import Principia.Record.Register
import Principia.Record.Verification

/-!
# A record's measured fields, its declared form, and the verification's checks

v1's `tpc_record` 0.1.0, the functions of tpm_record_functions 0.3.0 that read a record's
numbers, units and forms:

* exact decimal arithmetic and the result's measured fields (sections 2 and 7):
  `precDecimal`, `budgetCheck`, `fieldValues`;
* the parrot comparison's pair (8): `lFindingPair`;
* the declared form on a record (11): `recordFormCheck`, `domainCheck`;
* verification (14): `verificationDifference`.

**Numbers.** `budget_check` is v1's exact digit-string arithmetic (functions 2), here on
natural numbers, which it computes exactly the same. Where v1 normalized a measurement in
IEEE doubles and wrote it to twelve significant digits (`field_values`, `l_finding_pair`,
the points of `verification_difference`), the Calculator normalizes exactly
(`Principia.Units.normalizeMeasurementArg`) and rounds the exact value once to twelve
digits (`Principia.Form.twelve`); a value whose twelve digits the bounds on π do not settle
is owed (the Calculator's numbers are exact). `verification_difference` then took a square root and a quotient of
doubles: the Calculator computes the difference, its uncertainty and its zeta exactly, each
correctly rounded once to twelve digits (`Principia.Record.Verification`). Every number these
functions form from their arguments, the normalized measurements, `budget_check`'s sums and
the verification's numbers, is checked against the bound on an exact value's size before it
is formed (`Principia.Record.Bounded`, `Principia.Record.Verification`), and refused past it
(`Owed.tooLarge`, "exact value too large").

**Units' reasons.** `Principia.Units` escapes a reason's code points as v1 did, by Unicode
15.1.0's general category.
-/

namespace Principia.Record

open Principia.Canonical (Value)
open Principia.Record.Table

/-! ## 2, 7 The measured fields -/

/-- v1's `prec_decimal(s)` (functions 7.3). -/
def precDecimal (s : Value) : M Value := do
  match s with
  | .str t =>
    match precForm t with
    | some p => return okWith [.str p]
    | none => badArg "s" s "a decimal string"
  | _ => badArg "s" s "a decimal string"

/-- A canonical decimal's `(m, e)` (v1's `_mexp`): the digits as a natural, the exponent;
the sign dropped. -/
def mexp (c : String) : Nat × Int :=
  let cs := match c.toList with
    | '-' :: r => r
    | r => r
  match cs.idxOf? 'e' with
  | some i =>
    let e := String.ofList (cs.drop (i + 1))
    (digitsNat (cs.take i), (e.toInt?).getD 0)
  | none => (digitsNat cs, 0)

/-- A UNIT that reads: its tokens. -/
def unitTokens? : Option Value → Option (List (Units.Reading × Int))
  | some (.str u) => (Units.tokens u).toOption
  | _ => none

/-- A canonical decimal of a string member. -/
def canonOf? : Option Value → Option String
  | some (.str s) => Decimal.canon s
  | _ => none

/-- v1's `_m_result`: an M RESULT whose measured fields `budget_check` reads. -/
def mResult (r : Value) : Bool :=
  V.get? r "CLASS" == some (.str "RESULT") && V.get? r "REGIME" == some (.str "M") &&
    (match canonOf? (V.get? r "U_C") with
      | some u => u != "0" && !u.startsWith "-"
      | none => false) &&
    (unitTokens? (V.get? r "UNIT")).isSome &&
    (match V.get? r "BUDGET" with
      | some (.arr (b :: bs)) => (b :: bs).all fun c =>
          V.isObj c && (unitTokens? (V.get? c "UNIT")).isSome &&
            (match canonOf? (V.get? c "U") with
              | some u => !u.startsWith "-"
              | none => false)
      | _ => false)

/-- The dimension and the kind of merged tokens (v1's `unit_parse` items 2 and 3). -/
def dimKind (items : List (Units.Reading × Int)) : String × String :=
  (Dimension.canon (Units.dimExps items), Units.kind items)

/-- v1's `budget_check(record)` (functions 7.1): U_C, at its last written digit, is
the root sum of squares of the BUDGET's U, each brought to UNIT by a power of ten. -/
def budgetCheck (record : Value) : M Value := do
  unless mResult record do return one "REC-66" "-" "budget_check reads an M RESULT"
  if V.get? record "CORRELATED" == some (.bool true) then
    return worded "INSPECT" "BUDGET is correlated: its consistency is INSPECTION"
  let unit := (V.getStr? record "UNIT").getD ""
  let rtok := (unitTokens? (V.get? record "UNIT")).getD []
  let (rdim, rkind) := dimKind rtok
  let budget := match V.get? record "BUDGET" with | some (.arr b) => b | _ => []
  let mut firstDim : Option Value := none
  let mut firstConv : Option Value := none
  let mut firstInsp : Option Value := none
  let mut shifts : List (Option Int) := []
  for (c, i) in budget.zipIdx 1 do
    let cu := (V.getStr? c "UNIT").getD ""
    let ctok := (unitTokens? (V.get? c "UNIT")).getD []
    let (cdim, ckind) := dimKind ctok
    if cdim != rdim then
      if firstDim.isNone then
        firstDim := some (one "REC-67" s!"BUDGET[{i}].UNIT"
          s!"BUDGET[{i}].UNIT {← showSlot cu} has dimension {cdim}, not {rdim}")
      shifts := shifts ++ [none]
      continue
    if ckind != rkind then
      if firstConv.isNone then
        firstConv := some (worded "CONVENTION" s!"units of different kind: {ckind} and {rkind}")
      shifts := shifts ++ [none]
      continue
    if ctok.length != rtok.length ||
        (ctok.zip rtok).any (fun (a, b) => a.1.sym != b.1.sym || a.2 != b.2) then
      if firstInsp.isNone then
        firstInsp := some (worded "INSPECT"
          s!"BUDGET[{i}].UNIT {← showSlot cu} is not a power of ten of UNIT {← showSlot unit}")
      shifts := shifts ++ [none]
      continue
    shifts := shifts ++ [some ((ctok.zip rtok).map fun (a, b) => (a.1.power - b.1.power) * a.2).sum]
  for outcome in [firstDim, firstConv, firstInsp] do
    if let some o := outcome then return o
  let uc := (V.getStr? record "U_C").getD ""
  let pc := (precForm uc).getD "0"
  let us := (budget.zip shifts).map fun (c, s) => ((canonOf? (V.get? c "U")).getD "0", s)
  -- each digit string is read as a whole number only within the bound on an exact value
  unless Bounded.digitsFit pc && us.all (fun u => Bounded.digitsFit u.1) do throw .tooLarge
  let (mc, ec) := mexp pc
  let eb := 2 * ec - 2
  let terms : List (Nat × Int) := us.filterMap fun (u, s) =>
    let (m, e) := mexp u
    if m == 0 then none else some (m, 2 * (e + s.getD 0))
  let exps := eb :: terms.map (·.2)
  let b := exps.foldl min eb
  let top := exps.foldl max eb
  if top - b > 20000 then return worded "INSPECT" "BUDGET spans more than 20000 decimal digits"
  match Bounded.budgetWithin mc eb b terms with
  | .ok true => return okV
  | .ok false =>
    return one "REC-68" "U_C" s!"U_C {← showSlot uc} is not the root sum of squares of BUDGET at its last digit"
  | .error _ => throw .tooLarge

/-- A measurement normalized (v1's `normalize_measurement`), or its reason; refused when a
value it forms could cross the bound on an exact value's size
(`Bounded.normalizeWithin`, which answers what `normalize_measurement` does when it answers). -/
def normalize (v u unit : Option Value) : M (Except String Units.Measurement) := do
  let arg : Option Value → Units.Arg := fun | some (.str s) => some s | _ => none
  match Bounded.normalizeWithin (arg v) (arg u) (arg unit) with
  | .ok r => return r
  | .error _ => throw .tooLarge

/-- v1's `_cd(x)`: a value's twelve-digit form, as a canonical decimal; owed when the
bounds on π do not settle the twelve digits. -/
def twelveDecimal (x : Exact) : M String := do
  match Form.twelve x with
  | some t => return (Decimal.canon t).getD t
  | none => throw (.number "twelve digits")

/-- v1's `field_values(record)`: a RESULT's U_C in coherent SI (0 for an L RESULT). -/
def fieldValues (record : Value) : M Value := do
  unless V.get? record "CLASS" == some (.str "RESULT") do
    return one "REC-69" "-" "field_values reads a RESULT"
  if V.get? record "REGIME" != some (.str "M") then return okWith [.obj [("U_C", .str "0")]]
  match ← normalize (V.get? record "VALUE") (V.get? record "U_C") (V.get? record "UNIT") with
  | .error r => return one "REC-70" "U_C" s!"U_C: {r}"
  | .ok m => return okWith [.obj [("U_C", .str (← twelveDecimal m.u))]]

/-! ## 8 The parrot comparison's pair -/

/-- v1's `_l_result`. -/
def lResult (r : Value) : Bool :=
  V.get? r "CLASS" == some (.str "RESULT") && V.get? r "REGIME" == some (.str "L")

/-- A finding `{"finding": {"type": t, "value": v}}`. -/
def finding (t : String) (v : String) : Value :=
  .obj [("finding", .obj [("type", .str t), ("value", .str v)])]

/-- v1's `l_finding_pair(original, reproduction)`: the two L RESULTs' findings, each in
its canonical form. -/
def lFindingPair (original reproduction : Value) : M Value := do
  let notL := one "REC-71" "-" "l_finding_pair reads two L RESULTs"
  unless lResult original && lResult reproduction do return notL
  let pair := [original, reproduction]
  if pair.all fun x => (V.getStr? x "EQUATION").isSome then
    let mut out : List Value := []
    for x in pair do
      match Form.parseForm ((V.getStr? x "EQUATION").getD "") .equation with
      | .ok t => out := out ++ [finding "EQUATION" t]
      | .refused _ => return notL
      | .owed (.exact w) => throw (.number w)
    return okWith out
  if pair.all fun x => V.has x "VALUE" && V.has x "UNIT" then
    let a ← normalize (V.get? original "VALUE") (some (.str "0")) (V.get? original "UNIT")
    let b ← normalize (V.get? reproduction "VALUE") (some (.str "0")) (V.get? reproduction "UNIT")
    match a, b with
    | .ok a, .ok b =>
      if a.dimension != b.dimension then
        return one "REC-72" "-" s!"units of different dimension: {a.dimension} and {b.dimension}"
      if a.kind != b.kind then
        return worded "CONVENTION" s!"units of different kind: {a.kind} and {b.kind}"
      return okWith [finding "DECIMAL" (← twelveDecimal a.x), finding "DECIMAL" (← twelveDecimal b.x)]
    | _, _ => return notL
  unless pair.all fun x => (V.getStr? x "STATEMENT").isSome do return notL
  let fs ← pair.mapM fun x => do return finding "TEXT" (← text ((V.getStr? x "STATEMENT").getD ""))
  return okWith fs

/-! ## 11 The declared form on a record -/

/-- The names a form uses (v1's `_names`): `[]` for a text that is not a string or does not
parse. -/
def formNamesOf (text : Option Value) (mode : Form.Mode) : M (List String) := do
  match text with
  | some (.str t) =>
    match Form.formNames t mode with
    | .ok ns => return ns
    | .refused _ => return []
    | .owed (.exact w) => throw (.number w)
  | _ => return []

/-- v1's `_tpk_dims`: every DOF's and CONSTANT's DIMENSION by NAME, the last of a NAME
kept. -/
def tpkDims (tfk : Value) : Form.DimTable :=
  let tpk := getOr tfk "TPK"
  let kvs := (["DOF", "CONSTANT"].flatMap fun k => namedDims tpk k).map fun (n, d) =>
    (n, match d with | some (.str s) => some s | _ => none)
  Form.DimTable.ofStrings kvs.reverse

/-- A form answer's refusal or owed reason, for v1's `r[1]`. -/
def formFailure {α : Type} : Form.Answer α → M (Option String)
  | .ok _ => pure none
  | .refused r => pure (some r)
  | .owed (.exact w) => throw (.number w)

/-- v1's `record_form_check(record, tfk)`. -/
def recordFormCheck (record tfk : Value) : M Value := do
  unless V.get? record "CLASS" == some (.str "RESULT") || V.get? record "CLASS" == some (.str "ASSUMPTION") do
    return one "REC-75" "-" "record_form_check reads a RESULT or an ASSUMPTION"
  unless tfk != .null && assemblyOk tfk do return one "REC-39" "-" "the TFK is not readable"
  let some eqv := V.get? record "EQUATION" | return okV
  let refs := V.members (V.get? record "REFS")
  let en ← formNamesOf (some eqv) .equation
  let dn ← if V.has record "DOMAIN_CONDITION" then formNamesOf (V.get? record "DOMAIN_CONDITION") .predicate
    else pure []
  let mut p : List Problem := []
  for n in en do
    if !refs.contains n then p := p ++ [("REC-76", "EQUATION", s!"EQUATION names {n}, which is not in REFS")]
  for n in refs do
    if !en.contains n && !dn.contains n then
      p := p ++ [("REC-77", "REFS", s!"REFS {← showSlot n} is named in neither EQUATION nor DOMAIN_CONDITION")]
  unless p.isEmpty do return refused p
  let eq := match eqv with | .str s => some s | _ => none
  let dimFail ← match eq with
    | some e => formFailure (Form.formDimension e .equation (tpkDims tfk))
    | none => pure (some "the form is not a string")
  if let some r := dimFail then return one "REC-78" "EQUATION" s!"EQUATION {r} (T4)"
  let dv := match eq with
    | some e => match Form.formTree e .equation with
      | .ok t => sortStrings t.dVariables.eraseDups
      | _ => []
    | none => []
  let tpk := getOr tfk "TPK"
  let dofs := (namedDims tpk "DOF").map Prod.fst
  let cons := match V.get? tpk "CONSTRAINT" with | some (.arr cs) => cs | _ => []
  for s in dv do
    if !dofs.contains s then p := p ++ [("REC-79", "EQUATION", s!"EQUATION's D variable {s} is not a DOF")]
    let targets := sortStrings (cons.filterMap fun c =>
      if V.isObj c && V.get? c "TARGET" == some (.str s) then V.getStr? c "NAME" else none)
    for c in targets do
      p := p ++ [("REC-79", "EQUATION", s!"EQUATION's D variable {s} is the TARGET of CONSTRAINT:{c}")]
  let params := getOr tpk "PARAMETERS"
  let oneVar := !(V.isObj params && V.get? params "D_VARIABLES" == some (.str "SEVERAL"))
  let tdv ← match Form.dVariables (toZone tpk) with
    | .ok ds => pure ds
    | .error (.exact w) => throw (.number w)
  if oneVar && (tdv ++ dv).eraseDups.length > 1 then
    let a := if dv.isEmpty then "none" else ", ".intercalate dv
    let b := if tdv.isEmpty then "none" else ", ".intercalate tdv
    p := p ++ [("REC-80", "EQUATION", s!"EQUATION's D variables {a} and the TPK's {b} are more than one under D_VARIABLES ONE")]
  unless p.isEmpty do return refused p
  if let some (.str role) := V.get? record "ROLE" then
    if let some x := eomName? role then
      if !dofs.contains x then return one "REC-81" "ROLE" s!"ROLE EOM({x}): {x} is not a DOF of the TPK"
  return okV

/-- v1's `domain_check(record, tfk)` (T6 on DOMAIN_CONDITION). -/
def domainCheck (record tfk : Value) : M Value := do
  unless V.isObj record do return one "REC-01" "-" "the record is not an object"
  unless tfk != .null && assemblyOk tfk do return one "REC-39" "-" "the TFK is not readable"
  let some dcv := V.get? record "DOMAIN_CONDITION" | return okV
  let refs := V.members (V.get? record "REFS")
  let dn ← formNamesOf (some dcv) .predicate
  let mut p : List Problem := []
  for n in dn do
    if !refs.contains n then
      p := p ++ [("REC-82", "DOMAIN_CONDITION", s!"DOMAIN_CONDITION names {n}, which is not in REFS")]
  if !V.has record "EQUATION" then
    for n in refs do
      if !dn.contains n then
        p := p ++ [("REC-77", "REFS", s!"REFS {← showSlot n} is named in neither EQUATION nor DOMAIN_CONDITION")]
  unless p.isEmpty do return refused p
  match dcv with
  | .str dc =>
    match Form.formTotality dc (tpkDims tfk) with
    | .ok qs =>
      let ps := qs.map fun q => ("REC-83", "DOMAIN_CONDITION", s!"DOMAIN_CONDITION {q} (T6)")
      return if ps.isEmpty then okV else refused ps
    | .refused r => return one "REC-83" "DOMAIN_CONDITION" s!"DOMAIN_CONDITION {r} (T6)"
    | .owed (.exact w) => throw (.number w)
  | _ => return one "REC-83" "DOMAIN_CONDITION" "DOMAIN_CONDITION the form is not a string (T6)"

/-! ## 14 Verification -/

/-- v1's `_at_list`: each point as `[DOF, value, kind]`, the value in its twelve-digit
form, sorted; `none` when a point does not normalize. -/
def atList (at? : Option Value) : M (Option (List (String × String × String))) := do
  let pts := match at? with | some (.arr ps) => ps | _ => []
  let mut out : List (String × String × String) := []
  for q in pts do
    unless V.isObj q do return none
    match ← normalize (V.get? q "VALUE") (some (.str "0")) (V.get? q "UNIT"), V.getStr? q "DOF" with
    | .ok m, some d => out := out ++ [(d, ← twelveDecimal m.x, m.kind)]
    | _, _ => return none
  return some (out.mergeSort fun a b =>
    decide (a.1 < b.1) || (a.1 == b.1 && (decide (a.2.1 < b.2.1) || (a.2.1 == b.2.1 && decide (a.2.2 ≤ b.2.2)))))

/-- A number of the declared forms in canon's twelve-digit form, as a canonical decimal;
owed when the bounds on π do not settle the twelve digits. -/
def numTwelve (n : Form.Num) : M String := do
  match n.twelve? with
  | some t => return Verification.canonText t
  | none => throw (.number "twelve digits")

/-- A value formed within the bound on an exact value, or refused, "exact value too large". -/
def within {α : Type} : ValueBound.Bounded α → M α
  | .ok a => pure a
  | .error _ => throw .tooLarge

/-- The verification's VALUE, U and ZETA as texts, and the contradiction test, from the two
normalized measurements of one DIMENSION and KIND; `none` when U is 0 (REC-95). One power of
π: the rationals of `Verification.sameParts`, within the bound; different powers: the
declared forms' numbers (`Verification.numParts`), owed where 4096 bits of π do not settle
a text or the test. -/
def verificationFigures (a b : Units.Measurement) (k : Rat) :
    M (Option (String × String × String × Bool)) := do
  let figures ← if a.piPower = b.piPower then do
      let p := a.piPower
      match ← within (Verification.sameParts a.x.coef a.u.coef b.x.coef b.u.coef) with
      | none => pure none
      | some (d, s, z) =>
        let v ← twelveDecimal (Exact.of d p)
        let u ← if p = 0 then pure (Verification.uText s)
          else numTwelve (Form.Num.sqrt (.exact (Exact.of s (2 * p))))
        pure (some (v, u, Verification.zetaText d z))
    else do
      within (Verification.numWithin a.x.coef a.u.coef b.x.coef b.u.coef)
      match Verification.numParts a.x a.u b.x b.u with
      | none => throw (.number "twelve digits")
      | some r => pure r
  match figures with
  | none => return none
  | some (v, u, z) =>
    match Verification.contradicts a b k with
    | some c => return some (v, u, z, c)
    | none => throw (.number "twelve digits")

/-- v1's `verification_difference(target, verification, k)` (functions 14.2): the arguments, the
quantity, the points, the units; then VALUE = x_t - x_e, U = √(u_t² + u_e²) (REC-95 when it
is 0) and ZETA = VALUE / U, each exact and written to twelve digits as a canonical decimal,
and the M-M contradiction test with `S = 1`; REC-96 for each member of the presented
DIFFERENCE that is not the recomputed text as a canonical decimal. -/
def verificationDifference (target verification k : Value) : M Value := do
  let notPair := one "REC-92" "-" "verification_difference reads a RESULT and a VERIFICATION of it"
  unless V.get? target "CLASS" == some (.str "RESULT") &&
      ["ID", "QUANTITY", "VALUE", "UNIT"].all (fun f => (V.getStr? target f).isSome) &&
      V.get? verification "CLASS" == some (.str "VERIFICATION") &&
      V.get? verification "TARGET" == V.get? target "ID" && V.isObj (getOr verification "EXTERNAL") do
    return notPair
  unless (match k with
      | .str s => Decimal.canon s == some s && Decimal.isPosFinite s
      | _ => false) do
    return ← badArg "k" k "a positive canonical decimal"
  let ext := getOr verification "EXTERNAL"
  let mut p : List Problem := []
  if getOr ext "QUANTITY" != getOr target "QUANTITY" then
    p := p ++ [("REC-93", "EXTERNAL.QUANTITY",
      s!"EXTERNAL.QUANTITY {← showArg (getOr ext "QUANTITY")} is not the TARGET's QUANTITY {← showSlot (strOf (getOr target "QUANTITY"))}")]
  let at1 ← atList (V.get? target "AT")
  let at2 ← atList (V.get? verification "AT")
  match at1, at2 with
  | some a, some b =>
    if a.map (fun q => (q.1, q.2.1)) != b.map (fun q => (q.1, q.2.1)) then
      p := p ++ [("REC-94", "AT", "AT is not the TARGET's AT")]
  | _, _ => p := p ++ [("REC-94", "AT", "AT is not the TARGET's AT")]
  unless p.isEmpty do return refused p
  let tu : Option Value := if V.get? target "REGIME" == some (.str "M") then
      some ((V.get? target "U_C").getD (.str "0")) else some (.str "0")
  let nt ← normalize (V.get? target "VALUE") tu (V.get? target "UNIT")
  let ne ← normalize (V.get? ext "VALUE") (V.get? ext "U_C") (V.get? ext "UNIT")
  match nt, ne with
  | .ok a, .ok b =>
    if a.dimension != b.dimension then
      return one "REC-72" "-" s!"units of different dimension: {a.dimension} and {b.dimension}"
    if a.kind != b.kind then
      return worded "CONVENTION" s!"units of different kind: {a.kind} and {b.kind}"
    let kq := (match k with | .str s => Decimal.value s | _ => none).getD 0
    match ← verificationFigures a b kq with
    | none => return one "REC-95" "-" "U is 0: both uncertainties are 0"
    | some (v, u, z, contra) =>
      let pres := match V.get? verification "DIFFERENCE" with
        | some (.obj ms) => Value.obj ms
        | _ => Value.obj []
      for (f, g) in [("VALUE", v), ("U", u), ("ZETA", z)] do
        if canonOf? (V.get? pres f) != some g then
          p := p ++ [("REC-96", "DIFFERENCE." ++ f,
            s!"DIFFERENCE.{f} {← showArg (getOr pres f)} is not the recomputed {g}")]
      unless p.isEmpty do return refused p
      return okWith [.obj [("U", .str u), ("VALUE", .str v), ("ZETA", .str z)], .bool contra]
  | _, _ => return notPair

end Principia.Record
