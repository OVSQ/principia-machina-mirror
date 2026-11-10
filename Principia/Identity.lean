import Principia.Wire
import Principia.Digest
import Principia.Zone.Fields

/-!
# Identity: the PROMPT's canonical tools, the MODEL MAP, the change class and the comparison

v1's `tpc_identity` 0.1.1, the unit of identity's pure functions:

* `canonicalTools`: the tool definitions in TPM's canonical JSON (CJ1-CJ5): v1's own
  JSON parser, strings in NFC, numbers in the canonical DECIMAL form, members sorted by
  code point, no whitespace;
* `promptDigest`: SHA-256 over the netstring of `["TPM-PROMPT", "1", family, salt,
  template, tools]` (PD1-PD5);
* `familyOf`: the MODEL MAP lookup and the VENDOR FAMILY KEY (FO1, FO2);
* `changeClass`: a reported model's change class (CC1-CC4);
* `identityCompare`: the four vendor-level values compared pairwise (IC1, IC2).

Arguments are v1's, as parsed JSON (`Principia.Zone.Value`): v1 checks their types
and refuses with a fixed word (`Refusal`), in its own order, and so does the port.

**Text.** v1 puts every text in NFC where it takes it in, as here, with Unicode 15.1.0's
tables, v1's (`Principia.Unicode.nfc`):
each string the tools' JSON decodes, the family and the template of a PROMPT, the model
string and the MODEL MAP's names, families, servers and quantizations, the change class's
four texts and the four vendor-level values; equalities and duplicates are found between
the NFC texts.

**Digests.** `promptDigest` is SHA-256 over `promptPreimage`, the netstring of the six
fields, in lowercase hexadecimal (`Principia.Digest.ofPreimage`, `Principia.Sha256`). Nothing of identity is owed.
-/

namespace Principia.Identity

open Principia.Zone (Value)

/-! ## Refusals -/

/-- v1's `ValueError` words: the argument refused. -/
inductive Refusal where
  /-- `tools`: the tools' JSON text (CJ1-CJ4). -/
  | tools
  /-- `salt` -/
  | salt
  /-- `family` -/
  | family
  /-- `template` -/
  | template
  /-- `model` -/
  | model
  /-- `model_map` -/
  | modelMap
  /-- `certified_family` -/
  | certifiedFamily
  /-- `last_model` -/
  | lastModel
  /-- `reported_model` -/
  | reportedModel
  /-- `lookup` -/
  | lookup
  /-- `declared` -/
  | declared
  /-- `stated` -/
  | stated
  /-- `relayed` -/
  | relayed
  /-- `inferred` -/
  | inferred
  deriving DecidableEq, Repr

/-- v1's message for a refusal. -/
def Refusal.message : Refusal → String
  | .tools => "tools"
  | .salt => "salt"
  | .family => "family"
  | .template => "template"
  | .model => "model"
  | .modelMap => "model_map"
  | .certifiedFamily => "certified_family"
  | .lastModel => "last_model"
  | .reportedModel => "reported_model"
  | .lookup => "lookup"
  | .declared => "declared"
  | .stated => "stated"
  | .relayed => "relayed"
  | .inferred => "inferred"

/-- Every refusal, for reading v1's word back. -/
def Refusal.all : List Refusal :=
  [.tools, .salt, .family, .template, .model, .modelMap, .certifiedFamily, .lastModel,
    .reportedModel, .lookup, .declared, .stated, .relayed, .inferred]

/-- v1's word read back into the refusal. -/
def Refusal.ofMessage? (w : String) : Option Refusal := Refusal.all.find? (·.message == w)

/-- Why a function stops without a value: v1's refusal. -/
inductive Stop where
  /-- v1 refuses with this word. -/
  | refused (r : Refusal)
  deriving DecidableEq, Repr

/-- A function's outcome: its value, or why it stops. -/
abbrev Outcome := Except Stop

/-- Refuse with v1's word. -/
def refuse {α : Type} (r : Refusal) : Outcome α := throw (.refused r)

/-! ## NFC -/

/-- v1's `NFC(a) == NFC(b)`. -/
def eqNfc (a b : String) : Bool := Unicode.nfc a == Unicode.nfc b

/-- `eqNfc` answers `true` exactly for texts with one NFC. -/
theorem eqNfc_true {a b : String} : eqNfc a b = true ↔ Unicode.nfc a = Unicode.nfc b := by
  simp [eqNfc]

/-- `eqNfc` answers `false` only for different texts. -/
theorem eqNfc_false {a b : String} (h : eqNfc a b = false) : a ≠ b := by
  intro e
  subst e
  simp [eqNfc] at h

/-- `eqNfc` is symmetric: which of two texts comes first never changes the answer. -/
theorem eqNfc_comm (a b : String) : eqNfc a b = eqNfc b a := by
  unfold eqNfc
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

/-! ## Canonical JSON (CJ1-CJ5)

v1's own parser, on the code points of the text. It refuses with `tools`. Each string it
decodes, a member's key or a value, is put in NFC as it is decoded, as v1's `string()`
does: members are sorted, and a duplicate key found, among the NFC keys. -/

/-- The four whitespace characters around tokens (CJ1). -/
def wsChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Skip whitespace. -/
def skipWs : List Char → List Char
  | c :: cs => if wsChar c then skipWs cs else c :: cs
  | [] => []

/-- A decimal digit. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The value of a hexadecimal digit, either case. -/
def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits (v1's `hex4`). -/
def hex4 (a b c d : Char) : Option Nat := do
  pure ((((← hexVal a) * 16 + (← hexVal b)) * 16 + (← hexVal c)) * 16 + (← hexVal d))

/-- The leading digits and the rest. -/
def takeDigits : List Char → List Char × List Char
  | c :: cs => if isDigit c then let (ds, r) := takeDigits cs; (c :: ds, r) else ([], c :: cs)
  | [] => ([], [])

/-- A string's body after its opening quote (CJ2): the decoded code points, in
reverse, and the text after the closing quote. -/
def decodeString : List Char → List Char → Except Unit (List Char × List Char)
  | acc, '"' :: rest => pure (acc, rest)
  | acc, '\\' :: '"' :: rest => decodeString ('"' :: acc) rest
  | acc, '\\' :: '\\' :: rest => decodeString ('\\' :: acc) rest
  | acc, '\\' :: '/' :: rest => decodeString ('/' :: acc) rest
  | acc, '\\' :: 'b' :: rest => decodeString ('\x08' :: acc) rest
  | acc, '\\' :: 'f' :: rest => decodeString ('\x0c' :: acc) rest
  | acc, '\\' :: 'n' :: rest => decodeString ('\n' :: acc) rest
  | acc, '\\' :: 'r' :: rest => decodeString ('\r' :: acc) rest
  | acc, '\\' :: 't' :: rest => decodeString ('\t' :: acc) rest
  | acc, '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    match hex4 a b c d with
    | none => throw ()
    | some cp =>
      if 0xD800 ≤ cp && cp ≤ 0xDBFF then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: rest' =>
          match hex4 e f g h with
          | some lo =>
            if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
              decodeString (Char.ofNat (0x10000 + (cp - 0xD800) * 1024 + (lo - 0xDC00)) :: acc) rest'
            else throw ()
          | none => throw ()
        | _ => throw ()
      else if 0xDC00 ≤ cp && cp ≤ 0xDFFF then throw ()
      else decodeString (Char.ofNat cp :: acc) rest
  | _, '\\' :: _ => throw ()
  | acc, c :: rest => if c.toNat < 0x20 then throw () else decodeString (c :: acc) rest
  | _, [] => throw ()

/-- v1's `_quote` (CJ5): `"` and `\` escaped, the controls as `\b \f \n \r \t` or
`\u00xx` lowercase, every other code point raw. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\x08' then "\\b" else if c == '\x0c' then "\\f"
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      "\\u00" ++ String.ofList [(Nat.toDigits 16 (c.toNat / 16)).getD 0 '0',
        (Nat.toDigits 16 (c.toNat % 16)).getD 0 '0']
    else c.toString) ++ "\""

/-- The canonical DECIMAL of a JSON number's parts (CJ3): `0` for zero, else
`[-]M` and `eE` when `E` is not 0, `M` without leading or trailing zeros. -/
def canonicalNumber (negative : Bool) (intPart frac : List Char) (exp : Int) : String :=
  let digits := (intPart ++ frac).dropWhile (· == '0')
  if digits.isEmpty then "0"
  else
    let trimmed := (digits.reverse.dropWhile (· == '0')).reverse
    let e := exp - frac.length + (digits.length - trimmed.length)
    (if negative then "-" else "") ++ String.ofList trimmed ++ (if e != 0 then "e" ++ toString e else "")

/-- A JSON number (CJ3): its canonical text and the rest. An exponent of more than
four digits is refused. -/
def parseNumber (cs : List Char) : Except Unit (String × List Char) := do
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let (intPart, cs) ← match cs with
    | '0' :: r => pure (['0'], r)
    | c :: r => if '1' ≤ c && c ≤ '9' then pure (takeDigits (c :: r)) else throw ()
    | [] => throw ()
  let (frac, cs) ← match cs with
    | '.' :: r =>
      let (fd, r') := takeDigits r
      if fd.isEmpty then throw () else pure (fd, r')
    | r => pure ([], r)
  let (exp, cs) ← match cs with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (sign, r') : Int × List Char := match r with
          | '+' :: x => (1, x)
          | '-' :: x => (-1, x)
          | x => (1, x)
        let (ed, r'') := takeDigits r'
        if ed.isEmpty || ed.length > 4 then throw ()
        else pure (sign * (String.ofList ed).toNat!, r'')
      else pure (0, e :: r)
    | [] => pure (0, [])
  pure (canonicalNumber neg intPart frac exp, cs)

/-- Code-point order on texts (Python's `sorted`): Lean's order on strings, which compares
their characters one by one, each by its code point. -/
def textLt (a b : String) : Bool := decide (a < b)

/-- An object's members in code-point order of their keys, sorted once all are read (a
sort by merging, so an object of many members costs about their number times its
logarithm). -/
def sortMembers (ms : List (String × String)) : List (String × String) :=
  ms.mergeSort fun a b => !textLt b.1 a.1

/-- Two members side by side with one key: in sorted members, a key held twice. -/
def adjacentDuplicate : List (String × String) → Bool
  | a :: b :: rest => a.1 == b.1 || adjacentDuplicate (b :: rest)
  | _ => false

/-- The nesting bound (CJ4, PD-OC-6). -/
def maxDepth : Nat := 64

mutual
/-- v1's `value(depth)`: the canonical text of the value at the head and the rest.
`fuel` bounds the recursion; every two calls consume a character, so twice the
text's length is never exhausted. -/
def parseValue : Nat → Nat → List Char → Except Unit (String × List Char)
  | 0, _, _ => throw ()
  | fuel + 1, depth, cs =>
    if depth > maxDepth then throw ()
    else match skipWs cs with
      | '{' :: r =>
        match skipWs r with
        | '}' :: r' => pure ("{}", r')
        | _ => do
          let (members, rest) ← parseMembers fuel depth r []
          -- v1 keeps the members in a dictionary, refusing a key it already holds, and
          -- sorts the keys at the end; any refusal is the one word `tools`, so the
          -- duplicate is found here among the sorted keys, with the same answer.
          let sorted := sortMembers members
          if adjacentDuplicate sorted then throw ()
          pure ("{" ++ ",".intercalate (sorted.map fun (k, v) => quote k ++ ":" ++ v) ++ "}", rest)
      | '[' :: r =>
        match skipWs r with
        | ']' :: r' => pure ("[]", r')
        | _ => do
          let (items, rest) ← parseItems fuel depth r []
          pure ("[" ++ ",".intercalate items.reverse ++ "]", rest)
      | '"' :: r => do
        let (s, rest) ← decodeString [] r
        pure (quote (Unicode.nfc (String.ofList s.reverse)), rest)
      | 't' :: 'r' :: 'u' :: 'e' :: rest => pure ("true", rest)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => pure ("false", rest)
      | 'n' :: 'u' :: 'l' :: 'l' :: rest => pure ("null", rest)
      | c :: r => if c == '-' || isDigit c then parseNumber (c :: r) else throw ()
      | [] => throw ()

/-- v1's `obj`'s loop: members so far, the last read first, and the rest after `}`. -/
def parseMembers : Nat → Nat → List Char → List (String × String) →
    Except Unit (List (String × String) × List Char)
  | 0, _, _, _ => throw ()
  | fuel + 1, depth, cs, acc =>
    match skipWs cs with
    | '"' :: r => do
      let (k, r) ← decodeString [] r
      let key := Unicode.nfc (String.ofList k.reverse)
      match skipWs r with
      | ':' :: r => do
        let (v, r) ← parseValue fuel (depth + 1) r
        let acc := (key, v) :: acc
        match skipWs r with
        | ',' :: r => parseMembers fuel depth r acc
        | '}' :: r => pure (acc, r)
        | _ => throw ()
      | _ => throw ()
    | _ => throw ()

/-- v1's `arr`'s loop: items so far, in reverse, and the rest after `]`. -/
def parseItems : Nat → Nat → List Char → List String → Except Unit (List String × List Char)
  | 0, _, _, _ => throw ()
  | fuel + 1, depth, cs, acc => do
    let (v, r) ← parseValue fuel (depth + 1) cs
    match skipWs r with
    | ',' :: r => parseItems fuel depth r (v :: acc)
    | ']' :: r => pure (v :: acc, r)
    | _ => throw ()
end

/-- v1's `canonical_tools` on a text: one JSON value with whitespace around it and
nothing after it, in canonical form, each string in NFC, or `none` when v1 refuses it. -/
def canonicalJson (text : String) : Option String :=
  match parseValue (2 * text.length + 4) 0 text.toList with
  | .ok (v, rest) => if (skipWs rest).isEmpty then some v else none
  | .error _ => none

/-- `canonical_tools(json_text)`: the canonical text; refused `tools`. -/
def canonicalTools : Value → Outcome String
  | .str text =>
    match canonicalJson text with
    | none => refuse .tools
    | some out => pure out
  | _ => refuse .tools

/-! ## The PROMPT digest (PD1-PD5) -/

/-- PD2: exactly 32 characters of `0-9a-f`. -/
def isSalt (s : String) : Bool :=
  s.length == 32 && s.toList.all fun c => isDigit c || ('a' ≤ c && c ≤ 'f')

/-- The six fields v1 digests, in order, after its checks: PD1 family (NFC, not
empty), PD2 salt, PD3 template (NFC), PD4 tools (canonical). -/
def promptFields (family salt template tools : Value) : Outcome (List String) := do
  let fam ← match family with
    | .str s => if s.isEmpty then refuse .family else pure s
    | _ => refuse .family
  let saltText ← match salt with
    | .str s => if isSalt s then pure s else refuse .salt
    | _ => refuse .salt
  let tmpl ← match template with
    | .str s => pure s
    | _ => refuse .template
  let canon ← canonicalTools tools
  -- NFC goes into the preimage, as v1's `_nfc` puts it.
  pure ["TPM-PROMPT", "1", Unicode.nfc fam, saltText, Unicode.nfc tmpl, canon]

/-- The netstring v1 digests: what `prompt_digest` takes the SHA-256 of. -/
def promptPreimage (family salt template tools : Value) : Outcome String :=
  Principia.Digest.preimage <$> promptFields family salt template tools

/-- `prompt_digest(family, salt, template, tools)`: every check is
made, then SHA-256 over `promptPreimage`, in lowercase hexadecimal. -/
def promptDigest (family salt template tools : Value) : Outcome String :=
  Principia.Digest.ofPreimage <$> promptPreimage family salt template tools

/-! ## The MODEL MAP (FO1, FO2) -/

/-- An object with exactly these keys (v1's `_keys_are`, no optional key). -/
def keysAre (kvs : List (String × Value)) (required : List String) : Bool :=
  required.all (fun k => kvs.any (·.1 == k)) && kvs.all (fun kv => required.contains kv.1)

/-- A field of an object. -/
def field (kvs : List (String × Value)) (k : String) : Value := (kvs.lookup k).getD .null

/-- A non-empty text. -/
def nonEmptyText : Value → Option String
  | .str s => if s.isEmpty then none else some s
  | _ => none

/-- One MODEL MAP row, checked. -/
structure MapRow where
  /-- The model string as PRB relays it. -/
  name : String
  /-- The maker's family or lineage. -/
  family : String
  /-- Open weights. -/
  openWeights : Bool
  /-- The pinned serving provider, for open weights. -/
  server : Option String
  /-- The pinned quantization, for open weights. -/
  quantization : Option String
  deriving DecidableEq, Repr

/-- One row as v1's `_check_map` reads it, in its order. -/
def readRow : Value → Outcome MapRow
  | .obj kvs => do
    unless keysAre kvs ["name", "family", "open", "server", "quantization"] do refuse .modelMap
    let some name := nonEmptyText (field kvs "name") | refuse .modelMap
    let some fam := nonEmptyText (field kvs "family") | refuse .modelMap
    let .bool o := field kvs "open" | refuse .modelMap
    if o then
      let some s := nonEmptyText (field kvs "server") | refuse .modelMap
      let some q := nonEmptyText (field kvs "quantization") | refuse .modelMap
      pure ⟨name, fam, true, some s, some q⟩
    else
      match field kvs "server", field kvs "quantization" with
      | .null, .null => pure ⟨name, fam, false, none, none⟩
      | _, _ => refuse .modelMap
  | _ => refuse .modelMap

/-- Two texts side by side that are one: in sorted texts, a text held twice. -/
def adjacentEqual : List String → Bool
  | a :: b :: rest => a == b || adjacentEqual (b :: rest)
  | _ => false

/-- Some text held twice, found among the texts sorted by merging. -/
def hasDuplicate (xs : List String) : Bool :=
  adjacentEqual (xs.mergeSort fun a b => !textLt b a)

/-- `_check_map`: every row read, each beside its name in NFC, and no two names one after
NFC. v1 checks each name against those before it as it reads the rows; every refusal is the
one word `model_map`, so the names are put in NFC once each and compared once sorted, with
the same answer. -/
def checkMap : Value → Outcome (List (String × MapRow))
  | .arr rows => do
    let read ← rows.mapM readRow
    let named := read.map fun r => (Unicode.nfc r.name, r)
    if hasDuplicate (named.map (·.1)) then refuse .modelMap
    pure named
  | _ => refuse .modelMap

/-- The VENDOR FAMILY KEY (FO2): the netstring of `["CLOSED", family]`, or of
`["OPEN", family, server, quantization]`. -/
def familyKey (family : String) (openWeights : Bool) (server quantization : Option String) :
    String :=
  if openWeights then
    Principia.Digest.preimage ["OPEN", family, server.getD "", quantization.getD ""]
  else Principia.Digest.preimage ["CLOSED", family]

/-- `family_of`'s answer. -/
inductive FamilyResult where
  /-- `UNMAPPED`: no row. -/
  | unmapped
  /-- `MAPPED`, with the row's family, open flag, server, quantization and key. -/
  | mapped (family : String) (openWeights : Bool) (server quantization : Option String)
      (key : String)
  deriving DecidableEq, Repr

/-- FO1: the first row whose name in NFC is the model string in NFC, `ms`. -/
def findRow (ms : String) (rows : List (String × MapRow)) : Option MapRow :=
  (rows.find? (·.1 == ms)).map (·.2)

/-- `family_of(model_string, model_map)`. -/
def familyOf (model map : Value) : Outcome FamilyResult := do
  let ms ← match model with
    | .str s => if s.isEmpty then refuse .model else pure s
    | _ => refuse .model
  let rows ← checkMap map
  match findRow (Unicode.nfc ms) rows with
  | none => pure .unmapped
  | some r =>
    let fam := Unicode.nfc r.family
    let server := r.server.map Unicode.nfc
    let quant := r.quantization.map Unicode.nfc
    pure (.mapped fam r.openWeights server quant (familyKey fam r.openWeights server quant))

/-! ## The change class (CC1-CC4) -/

/-- The CLUSTER LOOKUP's answer after substitution and succession. -/
inductive LookupAnswer where
  /-- `IN` -/
  | inside
  /-- `CUSP` -/
  | cusp
  /-- `OUT` -/
  | outside
  /-- `FADING` -/
  | fading
  /-- `UNLISTED` -/
  | unlisted
  /-- `EXCLUDED` -/
  | excluded
  deriving DecidableEq, Repr

instance : WireWord LookupAnswer where
  members := [.inside, .cusp, .outside, .fading, .unlisted, .excluded]
  toWire
    | .inside => "IN"
    | .cusp => "CUSP"
    | .outside => "OUT"
    | .fading => "FADING"
    | .unlisted => "UNLISTED"
    | .excluded => "EXCLUDED"
  read_toWire a := by cases a <;> decide

/-- A change class. -/
inductive ChangeClass where
  /-- `SAME` -/
  | same
  /-- `RECORDED CHANGE` -/
  | recordedChange
  /-- `CUSP PATH` -/
  | cuspPath
  /-- `REFUSED MODEL` -/
  | refusedModel
  /-- `REFUSED FAMILY` -/
  | refusedFamily
  deriving DecidableEq, Repr

instance : WireWord ChangeClass where
  members := [.same, .recordedChange, .cuspPath, .refusedModel, .refusedFamily]
  toWire
    | .same => "SAME"
    | .recordedChange => "RECORDED CHANGE"
    | .cuspPath => "CUSP PATH"
    | .refusedModel => "REFUSED MODEL"
    | .refusedFamily => "REFUSED FAMILY"
  read_toWire a := by cases a <;> decide

/-- A change class's detail (v1 prints `-` for none). -/
inductive ChangeDetail where
  /-- `UNMAPPED` -/
  | unmapped
  /-- `FAMILY` -/
  | family
  /-- The cluster lookup's answer. -/
  | cluster (a : LookupAnswer)
  deriving DecidableEq, Repr

instance : WireWord ChangeDetail where
  members := [.unmapped, .family, .cluster .inside, .cluster .cusp, .cluster .outside,
    .cluster .fading, .cluster .unlisted, .cluster .excluded]
  toWire
    | .unmapped => "UNMAPPED"
    | .family => "FAMILY"
    | .cluster a => WireWord.toWire a
  read_toWire a := by
    rcases a with _ | _ | a
    · decide
    · decide
    · cases a <;> decide

/-- `change_class`'s answer: the class and its detail. -/
structure ChangeResult where
  /-- The class. -/
  cls : ChangeClass
  /-- Its detail; `none` for SAME. -/
  detail : Option ChangeDetail
  deriving DecidableEq, Repr

/-- CC1-CC4 on checked values, each in NFC: the certified key, the last and the reported
model, the lookup's family and its cluster answer. -/
def classify (cert last rep fam : String) (cl : Option LookupAnswer) : Outcome ChangeResult := do
  if fam == "UNMAPPED" then return ⟨.refusedModel, some .unmapped⟩
  unless fam == cert do return ⟨.refusedFamily, some .family⟩
  if rep == last then return ⟨.same, none⟩
  match cl with
  | none => refuse .lookup
  | some .inside => pure ⟨.recordedChange, some (.cluster .inside)⟩
  | some .cusp => pure ⟨.cuspPath, some (.cluster .cusp)⟩
  | some a => pure ⟨.refusedModel, some (.cluster a)⟩

/-- A non-empty text, else the refusal. -/
def textArg (v : Value) (r : Refusal) : Outcome String :=
  match nonEmptyText v with
  | some s => pure s
  | none => refuse r

/-- `change_class(certified_family, last_model, reported_model, lookup)`. -/
def changeClass (certified last reported lookup : Value) : Outcome ChangeResult := do
  let cert ← textArg certified .certifiedFamily
  let lastM ← textArg last .lastModel
  let rep ← textArg reported .reportedModel
  let .obj kvs := lookup | refuse .lookup
  unless keysAre kvs ["family", "cluster"] do refuse .lookup
  let some fam := nonEmptyText (field kvs "family") | refuse .lookup
  let cl ← match field kvs "cluster" with
    | .null => pure none
    | .str s =>
      match (WireWord.ofWire? s : Option LookupAnswer) with
      | some a => pure (some a)
      | none => refuse .lookup
    | _ => refuse .lookup
  classify (Unicode.nfc cert) (Unicode.nfc lastM) (Unicode.nfc rep) (Unicode.nfc fam) cl

/-! ## The identity comparison (IC1, IC2) -/

/-- The four vendor-level values. -/
inductive Party where
  | declared
  | stated
  | relayed
  | inferred
  deriving DecidableEq, Repr

/-- v1's lower-case name of a value. -/
def Party.name : Party → String
  | .declared => "declared"
  | .stated => "stated"
  | .relayed => "relayed"
  | .inferred => "inferred"

/-- The six pairs, in v1's fixed order (IC1). -/
def pairs : List (Party × Party) :=
  [(.declared, .stated), (.declared, .relayed), (.declared, .inferred),
    (.stated, .relayed), (.stated, .inferred), (.relayed, .inferred)]

/-- A pair's or the overall answer. -/
inductive Agreement where
  /-- `AGREE` -/
  | agree
  /-- `DIFFER` -/
  | differ
  /-- `ABSENT` -/
  | absent
  deriving DecidableEq, Repr

instance : WireWord Agreement where
  members := [.agree, .differ, .absent]
  toWire
    | .agree => "AGREE"
    | .differ => "DIFFER"
    | .absent => "ABSENT"
  read_toWire a := by cases a <;> decide

/-- `identity_compare`'s answer. -/
structure Comparison where
  /-- IC2. -/
  overall : Agreement
  /-- The six pairs with their answers, in order. -/
  pairs : List (Party × Party × Agreement)
  /-- How many pairs differ. -/
  differ : Nat
  deriving DecidableEq, Repr

/-- A value: absent (`null`) or a non-empty text, in NFC, else refused with its name. -/
def partyValue (v : Value) (r : Refusal) : Outcome (Option String) :=
  match v with
  | .null => pure none
  | .str s => if s.isEmpty then refuse r else pure (some (Unicode.nfc s))
  | _ => refuse r

/-- One pair's answer. -/
def comparePair (a b : Option String) : Outcome Agreement :=
  match a, b with
  | some x, some y => if x == y then pure .agree else pure .differ
  | _, _ => pure .absent

/-- IC2 from the six answers. -/
def overallOf (answers : List Agreement) : Agreement :=
  if answers.any (· == .differ) then .differ
  else if answers.any (· == .agree) then .agree else .absent

/-- `identity_compare(declared, stated, relayed, inferred)`. -/
def identityCompare (declared stated relayed inferred : Value) : Outcome Comparison := do
  let d ← partyValue declared .declared
  let s ← partyValue stated .stated
  let r ← partyValue relayed .relayed
  let i ← partyValue inferred .inferred
  let val : Party → Option String
    | .declared => d
    | .stated => s
    | .relayed => r
    | .inferred => i
  let answers ← pairs.mapM fun (a, b) => comparePair (val a) (val b)
  pure { overall := overallOf answers, pairs := (pairs.zip answers).map fun ((a, b), x) => (a, b, x),
         differ := (answers.filter (· == .differ)).length }

/-! ## Theorems -/

/-- `prompt_digest` answers exactly when its fields are read, with SHA-256 of their
netstring; otherwise it refuses with their refusal. -/
theorem promptDigest_eq (f s t u : Value) :
    promptDigest f s t u =
      (fun fs => Principia.Digest.ofPreimage (Principia.Digest.preimage fs)) <$>
        promptFields f s t u := by
  unfold promptDigest promptPreimage
  cases promptFields f s t u <;> rfl

/-- A PROMPT digest is 64 characters. -/
theorem promptDigest_length {f s t u : Value} {d : String} (h : promptDigest f s t u = .ok d) :
    d.length = 64 := by
  rw [promptDigest_eq] at h
  cases hp : promptFields f s t u with
  | error e => simp [hp, Functor.map, Except.map] at h
  | ok fs =>
    simp only [hp, Functor.map, Except.map, Except.ok.injEq] at h
    rw [← h]
    exact Principia.Digest.ofPreimage_length _

/-- A two-field preimage is its fields' netstrings, in order. -/
theorem preimage_two (a b : String) :
    Principia.Digest.preimage [a, b] = Principia.Digest.netstring a ++ Principia.Digest.netstring b := by
  simp [Principia.Digest.preimage, String.join]

/-- A four-field preimage is its fields' netstrings, in order. -/
theorem preimage_four (a b c d : String) :
    Principia.Digest.preimage [a, b, c, d] =
      Principia.Digest.netstring a ++ (Principia.Digest.netstring b ++
        (Principia.Digest.netstring c ++ Principia.Digest.netstring d)) := by
  simp [Principia.Digest.preimage, String.join, String.append_assoc]

/-- A closed key starts `6:CLOSED`, so with `6`. -/
theorem familyKey_closed_head (f : String) :
    (familyKey f false none none).toList.head? = some '6' := by
  have h : Principia.Digest.netstring "CLOSED" = "6:CLOSED" := by decide
  simp only [familyKey, Bool.false_eq_true, ↓reduceIte, preimage_two, h]
  simp [String.toList_append]

/-- An open key starts `4:OPEN`, so with `4`. -/
theorem familyKey_open_head (g : String) (s q : Option String) :
    (familyKey g true s q).toList.head? = some '4' := by
  have h : Principia.Digest.netstring "OPEN" = "4:OPEN" := by decide
  simp only [familyKey, ↓reduceIte, preimage_four, h]
  simp [String.toList_append]

/-- The closed and the open key of any family differ (FO2: a change between the two is a
change of family). -/
theorem familyKey_closed_ne_open (f g : String) (s q : Option String) :
    familyKey f false none none ≠ familyKey g true s q := by
  intro h
  have := familyKey_closed_head f
  rw [h, familyKey_open_head] at this
  simp at this

/-- "A change of family is never a MODEL CHANGE" (CC2): a RECORDED CHANGE or a CUSP
PATH is found only when the lookup's family is the certified one. -/
theorem classify_change_same_family {cert last rep fam : String} {cl : Option LookupAnswer}
    {r : ChangeResult} (h : classify cert last rep fam cl = .ok r)
    (hc : r.cls = .recordedChange ∨ r.cls = .cuspPath) : fam = cert := by
  unfold classify at h
  by_cases h1 : fam = "UNMAPPED"
  · simp [h1, pure, Except.pure] at h
    subst h
    simp at hc
  · by_cases h2 : fam = cert
    · exact h2
    · simp [h1, h2, pure, Except.pure] at h
      subst h
      simp at hc

/-- IC2: the comparison differs exactly when some pair differs, and counts them. -/
theorem overallOf_differ (xs : List Agreement) :
    overallOf xs = .differ ↔ (xs.filter (· == .differ)).length > 0 := by
  unfold overallOf
  constructor
  · intro h
    split at h
    · rename_i hd
      simpa [List.length_pos_iff_exists_mem, List.mem_filter] using List.any_eq_true.mp hd
    · split at h <;> simp at h
  · intro h
    have : xs.any (· == .differ) = true := by
      obtain ⟨x, hx⟩ := List.length_pos_iff_exists_mem.mp h
      exact List.any_eq_true.mpr ⟨x, (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩
    simp [this]

end Principia.Identity
