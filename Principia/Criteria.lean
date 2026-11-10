import Principia.Zone.Fields

/-!
# The Criteria Set's well-formedness and the yardstick terms

v1's `tms_well_formed`, `canonical_term`, `_parse_term`, `_parse_base`,
`_parse_atom`, `_a_sign` and `_check_key` (`tpc_zone` 0.5.1, schema 0.5.0).

The yardstick term grammar, closed:

    term := SR1 | A | S | FIELD:<ident> | NEG:<term> | WSUM:<wt>(;<wt>)*
    wt   := <constant>*<atom>        atom := A | S | FIELD:<ident>

A KEY is a list of terms compared lexicographically, lower is closer, and must
begin with SR1. A WSUM names each atom at most once; its weights are Criteria Set
CONSTANTS by name, never literal numbers (SR9 C5). With `c2` (a main KEY, not a
limiting case) the first term whose value moves with A must move up with it, so
adding an assumption never lowers the key (SR9 C2, decided statically).

The duplicate check of a yardstick's limiting DOMAINs compares them after v1's `_text`,
line endings as LF and NFC at Unicode 15.1.0 (`Principia.Zone.text`), and names a duplicate by that text.
-/

namespace Principia.Criteria

open Principia.Zone

/-! ## Terms -/

/-- v1's `_parse_atom`. -/
def parseAtom (a : String) : Bool :=
  a == "A" || a == "S" || (a.startsWith "FIELD:" && isIdent (a.drop 6).toString)

/-- What a term reads as. -/
structure TermParse where
  /-- Well formed. -/
  ok : Bool
  /-- The term is SR1. -/
  sr1 : Bool := false
  /-- The constants it names as weights. -/
  consts : List String := []
  /-- Its canonical spelling (the term unchanged when it is malformed). -/
  canon : String
  /-- Where A enters it: a sign and its weight constant (none for a bare A). -/
  contrib : List (Int × Option String) := []

/-- Weighted atoms `(atom, constant)` sorted by atom, then constant. -/
def insertWt (x : String × String) : List (String × String) → List (String × String)
  | [] => [x]
  | y :: ys => if x.1 < y.1 || (x.1 == y.1 && x.2 < y.2) then x :: y :: ys else y :: insertWt x ys

/-- One weighted atom `<constant>*<atom>`, split at the first `*`. -/
def splitWt (wt : String) : Option (String × String) :=
  match wt.splitOn "*" with
  | c :: rest@(_ :: _) => if c.isEmpty then none else some (c, "*".intercalate rest)
  | _ => none

/-- The weighted atoms of a WSUM, refused at the first malformed or repeated one. -/
def readWts : List String → List String → Option (List (String × String))
  | [], _ => some []
  | wt :: wts, seen =>
    match splitWt wt with
    | some (c, a) =>
      if !isIdent c || !parseAtom a || seen.contains a then none
      else (readWts wts (a :: seen)).map ((a, c) :: ·)
    | none => none

/-- v1's `_parse_base`: a term that does not begin with `NEG:`. -/
def parseBase (t : String) : TermParse :=
  if t == "SR1" then { ok := true, sr1 := true, canon := t }
  else if t == "S" then { ok := true, canon := t }
  else if t == "A" then { ok := true, canon := t, contrib := [(1, none)] }
  else if t.startsWith "FIELD:" then { ok := isIdent (t.drop 6).toString, canon := t }
  else if t.startsWith "WSUM:" then
    match readWts ((t.drop 5).toString.splitOn ";") [] with
    | some wts =>
      { ok := true, consts := wts.map (·.2),
        canon := "WSUM:" ++ ";".intercalate ((wts.foldl (fun acc w => insertWt w acc) []).map fun (a, c) => c ++ "*" ++ a),
        contrib := wts.filterMap fun (a, c) => if a == "A" then some (1, some c) else none }
    | none => { ok := false, canon := t }
  else { ok := false, canon := t }

/-- The `NEG:` prefixes of a term: how many, and what follows them. Counted, not
recursed into, as v1 does, so no depth exhausts the stack. -/
def stripNeg : List Char → Nat × List Char
  | 'N' :: 'E' :: 'G' :: ':' :: cs => let (n, b) := stripNeg cs; (n + 1, b)
  | cs => (0, cs)

/-- v1's `_parse_term`: an even count of `NEG:` cancels. -/
def parseTerm (t : String) : TermParse :=
  let (n, b) := stripNeg t.toList
  let p := parseBase (String.ofList b)
  if !p.ok then { ok := false, canon := t }
  else if n % 2 = 1 then { p with canon := "NEG:" ++ p.canon, contrib := p.contrib.map fun (s, k) => (-s, k) }
  else p

/-- v1's `canonical_term`: WSUM weights sorted by atom, double negation removed; a
malformed term unchanged. -/
def canonicalTerm (t : String) : String := (parseTerm t).canon

/-- v1's `_a_sign`: the sign of A's coefficient in a term, each weight's sign read
from its constant's VALUE. -/
def aSign (contrib : List (Int × Option String)) (consts : List (String × String)) : Int :=
  let total := contrib.foldl (fun acc (s, k) =>
    acc + s * match k with
      | none => 1
      | some k => Decimal.sign ((consts.lookup k).getD "0")) 0
  if 0 < total then 1 else if total < 0 then -1 else 0

/-- v1's `_check_key`: non-empty; SR1 first and nowhere else; every term well formed;
every weight a constant; with `c2`, SR9 C2. -/
def checkKey (tag : String) (key : List String) (consts : List (String × String)) (c2 : Bool) :
    List String :=
  match key with
  | [] => [tag ++ ": KEY is empty"]
  | first :: _ =>
    let head := if first != "SR1" then [tag ++ ": KEY must begin with SR1"] else []
    let rec go : Nat → Bool → List String → List String
      | _, _, [] => []
      | i, decided, t :: ts =>
        let p := parseTerm t
        if !p.ok then (tag ++ ": term " ++ t ++ " is not well-formed") :: go (i + 1) decided ts
        else
          let sr1 := if p.sr1 && i > 0 then [tag ++ ": SR1 may appear only as the first term"] else []
          let missing := p.consts.filter fun c => (consts.lookup c).isNone
          let miss := missing.map fun c => tag ++ ": constant " ++ c ++ " is not a TMS constant"
          if c2 && !decided && missing.isEmpty then
            let s := aSign p.contrib consts
            if s != 0 then
              sr1 ++ miss ++
                (if s < 0 then [tag ++ ": KEY ranks a record higher when an assumption is added (SR9 C2)"] else []) ++
                go (i + 1) true ts
            else sr1 ++ miss ++ go (i + 1) decided ts
          else sr1 ++ miss ++ go (i + 1) decided ts
    head ++ go 0 false key

/-! ## The Criteria Set -/

/-- The parts of the Criteria Set. -/
def partsOf : List String := ["PARAMETERS", "CONSTANTS", "YARDSTICKS"]
/-- The PARAMETERS' required and optional fields. -/
def paramFields : List String × List String :=
  (["STEP_CONVENTION", "K", "N_X", "S_MAX"], ["IC2_POLICY", "PROMOTION_FLOOR", "STRUCTURE_CHECK"])
/-- v1's `INT_MAX`: N_X and S_MAX are held natively in both residences. -/
def intMax : Int := 1000000

/-- The problems of the PARAMETERS part. -/
def paramProblems (units : UnitHook) (pm : Entry) : List String :=
  checkFields units "PARAMETERS" pm paramFields.1 paramFields.2 ++
  (match getStr? pm "STEP_CONVENTION" with
    | some s => if blank s then ["PARAMETERS: STEP_CONVENTION is empty"] else []
    | none => []) ++
  (match getStr? pm "K" with
    | some k => if (Decimal.canon k).isSome && !Decimal.isPosFinite k then
        ["PARAMETERS: K " ++ k ++ " is not a positive decimal in double range"] else []
    | none => []) ++
  (match get? pm "N_X" with
    | some (.int n) => (if n < 2 then ["PARAMETERS: N_X must be at least 2"] else []) ++
        (if n > intMax then ["PARAMETERS: N_X must be at most " ++ toString intMax] else [])
    | _ => []) ++
  (match get? pm "S_MAX" with
    | some (.int n) => (if n < 1 then ["PARAMETERS: S_MAX must be at least 1"] else []) ++
        (if n > intMax then ["PARAMETERS: S_MAX must be at most " ++ toString intMax] else [])
    | _ => []) ++
  (match getStr? pm "PROMOTION_FLOOR" with
    | some f => if ["F1", "F2", "F3"].contains f then [] else ["PARAMETERS: PROMOTION_FLOOR " ++ f ++ " is not F1, F2 or F3"]
    | none => []) ++
  (match getStr? pm "IC2_POLICY" with
    | some p => if p == "GAP" || p == "REJECT" then [] else ["PARAMETERS: IC2_POLICY " ++ p ++ " is not GAP or REJECT"]
    | none => []) ++
  (match getStr? pm "STRUCTURE_CHECK" with
    | some s => if s == "ON" || s == "OFF" then [] else ["PARAMETERS: STRUCTURE_CHECK " ++ s ++ " is not ON or OFF"]
    | none => [])

/-- The objects of a LIMITING list v1 checks (a list of objects), if it is one. -/
def limitingOf (e : Entry) : Option (List Entry) :=
  match get? e "LIMITING" with
  | some (.arr xs) => xs.mapM fun | .obj o => some o | _ => none
  | _ => none

/-- The problems of one yardstick. -/
def yardstickProblems (units : UnitHook) (consts : List (String × String)) (e : Entry) : List String :=
  let tag := "YARDSTICK:" ++ nameOf e
  let key := match get? e "KEY" with
    | some v => if typeOk "KEY" v then checkKey tag (strItems v) consts true else []
    | none => []
  let limiting := match limitingOf e with
    | some lim =>
      (lim.flatMap fun le =>
        let ltag := tag ++ " LIMITING " ++ nameOf le "DOMAIN"
        checkFields units ltag le ["DOMAIN", "KEY"] [] ++
        (match getStr? le "DOMAIN" with
          | some d => if blank d then [ltag ++ ": DOMAIN is empty"] else []
          | none => []) ++
        (match get? le "KEY" with
          | some v => if typeOk "KEY" v then checkKey ltag (strItems v) consts false else []
          | none => [])) ++
      (dupes ((names lim "DOMAIN").map text)).map fun n => tag ++ ": duplicate limiting DOMAIN " ++ n
    | none => []
  checkFields units tag e ["NAME", "KEY", "LIMITING"] [] ++ key ++ limiting

/-- The problems of a Criteria Set that `owedOf` passed, before `done`. -/
def problems (units : UnitHook) : Value → List String
  | .obj z =>
    let unknown := z.filterMap fun (p, _) => if partsOf.contains p then none else some ("TMS: unknown part " ++ p)
    let missing := if has z "PARAMETERS" then [] else ["TMS: missing part PARAMETERS"]
    let params := match get? z "PARAMETERS" with
      | some (.obj pm) => paramProblems units pm
      | some _ => ["TMS: PARAMETERS is not an object"]
      | none => []
    let (cons, consShape) := entries "TMS CONSTANTS" ((get? z "CONSTANTS").getD (.arr []))
    let consProbs := cons.flatMap fun e => checkFields units ("CONSTANT:" ++ nameOf e) e ["NAME", "VALUE"] []
    let consDup := (dupes (names cons)).map ("TMS: duplicate constant name " ++ ·)
    -- The first constant of each NAME gives its VALUE.
    let consts := cons.filterMap fun e =>
      match getStr? e "NAME", getStr? e "VALUE" with
      | some n, some v => some (n, v)
      | _, _ => none
    let (yards, yardShape) := entries "TMS YARDSTICKS" ((get? z "YARDSTICKS").getD (.arr []))
    let yardProbs := yards.flatMap (yardstickProblems units consts)
    let yardDup := (dupes (names yards)).map ("TMS: duplicate yardstick name " ++ ·)
    unknown ++ missing ++ params ++ consShape ++ consProbs ++ consDup ++ yardShape ++ yardProbs ++ yardDup
  | _ => ["TMS: zone is not an object"]

/-- The Criteria Set's well-formedness: v1's verdict, or owed. -/
def wellFormed (units : UnitHook) (tms : Value) : Verdict :=
  match owedOf tms with
  | some o => .owed o
  | none => .checked (done (problems units tms))

/-! ## Theorems -/

theorem stripNeg_neg (cs : List Char) :
    stripNeg ('N' :: 'E' :: 'G' :: ':' :: cs) = ((stripNeg cs).1 + 1, (stripNeg cs).2) := by
  simp [stripNeg]

/-- Double negation cancels: a well-formed term under `NEG:NEG:` has its own
canonical spelling. -/
theorem canonicalTerm_negneg {t : String} (h : (parseTerm t).ok = true) :
    canonicalTerm ("NEG:NEG:" ++ t) = canonicalTerm t := by
  have hl : ("NEG:NEG:" ++ t).toList =
      'N' :: 'E' :: 'G' :: ':' :: 'N' :: 'E' :: 'G' :: ':' :: t.toList := by
    simp [String.toList_append]
  unfold canonicalTerm parseTerm at *
  rw [hl, stripNeg_neg, stripNeg_neg]
  rcases hs : stripNeg t.toList with ⟨n, b⟩
  simp only [hs] at h ⊢
  by_cases hb : (parseBase (String.ofList b)).ok = true
  · have hn : (n + 1 + 1) % 2 = n % 2 := by omega
    simp [hb, hn]
  · simp [hb] at h

/-- A malformed term is returned unchanged, never altered into a well-formed one. -/
theorem canonicalTerm_malformed {t : String} (h : (parseTerm t).ok = false) :
    canonicalTerm t = t := by
  unfold canonicalTerm parseTerm at *
  rcases hs : stripNeg t.toList with ⟨n, b⟩
  simp only [hs] at h ⊢
  by_cases hb : (parseBase (String.ofList b)).ok = true
  · by_cases hn : n % 2 = 1 <;> simp_all
  · simp [hb]

/-- SR9 C1: an empty KEY is refused. -/
theorem checkKey_empty (tag : String) (consts : List (String × String)) (c2 : Bool) :
    checkKey tag [] consts c2 = [tag ++ ": KEY is empty"] := rfl

/-- SR9 C1: a KEY that does not begin with SR1 is refused. -/
theorem checkKey_not_sr1 {tag first : String} {rest : List String} {consts : List (String × String)}
    {c2 : Bool} (h : first ≠ "SR1") :
    (tag ++ ": KEY must begin with SR1") ∈ checkKey tag (first :: rest) consts c2 := by
  simp [checkKey, h]

end Principia.Criteria
