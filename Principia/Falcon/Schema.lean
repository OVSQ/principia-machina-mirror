import Principia.Digest
import Principia.Falcon.Reconcile

/-!
# The output schema's canonical text and digest

v1's `tpc_falcon` 0.2.0 (TPS 5.20.2; S79; FS1 to FS5 in v1's text):
`falcon_schema_canon(schema)`, the canonical text of the output schema a FALCON KIND
DECLARATION states, and `falcon_schema_digest(schema)`, its SHA-256.

* FS1: a schema `checkSchema` accepts, every string of which, keys included, is already
  its own canonical text: no CR, and in NFC, at Unicode 15.1.0
  (`Principia.Unicode.isNfc`).
* FS2: `narrow` removed at the top; every `quote` and `confidential` that is `false`
  removed.
* FS3: JSON with no white space; members in ascending code point order of their keys;
  arrays in their order; each string quoted, `"` and `\` backslashed, each code point
  below U+0020 as `\u00xx` (lower-case hexadecimal), every other as itself.
* FS4: the digest, SHA-256 over the netstring of `TPC-FALCON-SCHEMA`, `1` and the text
  (`Principia.Digest.digestFields`, v1's `_digest_fields`; SHA-256 is `Principia.Sha256`): 64 lower-case hexadecimal characters.
-/

namespace Principia.Falcon.Schema

open Principia.Canonical (Value)
open Principia.Falcon

/-- FS2: `narrow` dropped at the top; `quote` and `confidential` dropped where `false`. -/
def norm (top : Bool) : Value → Value
  | .obj ms => .obj (normMembers top ms)
  | .arr vs => .arr (normList vs)
  | v => v
where
  normMembers (top : Bool) : List (String × Value) → List (String × Value)
    | [] => []
    | (k, v) :: rest =>
      if (top && k == "narrow") ||
          ((k == "quote" || k == "confidential") && (match v with | .bool false => true | _ => false))
      then normMembers top rest
      else (k, norm false v) :: normMembers top rest
  normList : List Value → List Value
    | [] => []
    | v :: rest => norm false v :: normList rest

/-- Every string of a value, keys included. -/
def strs : Value → List String
  | .obj ms => strsMembers ms
  | .arr vs => strsList vs
  | .str s => [s]
  | _ => []
where
  strsMembers : List (String × Value) → List String
    | [] => []
    | (k, v) :: rest => k :: strs v ++ strsMembers rest
  strsList : List Value → List String
    | [] => []
    | v :: rest => strs v ++ strsList rest

/-- One code point as FS3 writes it inside quotes. -/
def escChar (c : Char) : List Char :=
  if c == '"' || c == '\\' then ['\\', c]
  else if c.toNat < 0x20 then
    ['\\', 'u', '0', '0', Canonical.hexDigit (c.toNat / 16), Canonical.hexDigit (c.toNat % 16)]
  else [c]

/-- FS3's string. -/
def strText (s : String) : String := "\"" ++ String.ofList (s.toList.flatMap escChar) ++ "\""

/-- Members' texts in ascending code point order of their keys. -/
def sortMembers (ms : List (String × String)) : List String :=
  (ms.mergeSort fun a b => a.1 ≤ b.1).map (·.2)

/-- FS3's text of a value (v1's `_schema_text`); a number or null, which a checked
schema never holds, writes as nothing. -/
def text : Value → String
  | .bool true => "true"
  | .bool false => "false"
  | .str s => strText s
  | .arr vs => "[" ++ ",".intercalate (textList vs) ++ "]"
  | .obj ms => "{" ++ ",".intercalate (sortMembers (textMembers ms)) ++ "}"
  | _ => ""
where
  textList : List Value → List String
    | [] => []
    | v :: rest => text v :: textList rest
  textMembers : List (String × Value) → List (String × String)
    | [] => []
    | (k, v) :: rest => (k, strText k ++ ":" ++ text v) :: textMembers rest

/-- v1's `falcon_schema_canon(schema)`: the canonical text, or the refusal `schema`. -/
def schemaCanon (schema : Value) : Result String :=
  if !Reconcile.checkSchema schema then refuse "schema"
  else
    let n := norm true schema
    let ss := strs n
    if ss.any (fun s => s.toList.contains '\r' || !Unicode.isNfc s) then refuse "schema"
    else .ok (text n)

/-- FS4's tag and form (v1's `SCHEMA_TAG`, `SCHEMA_FORM`). -/
def schemaTag : String := "TPC-FALCON-SCHEMA"

def schemaForm : String := "1"

/-- FS4's digest of a canonical text: SHA-256 over the netstring of the tag, the form and
the text. -/
def digestOfText (t : String) : String :=
  Digest.digestFields [.text schemaTag, .text schemaForm, .text t]

/-- v1's `falcon_schema_digest(schema)`: the digest of the canonical text, or the refusal
`schema`. -/
def schemaDigest (schema : Value) : Result String :=
  (schemaCanon schema).map digestOfText

/-- The digest is refused exactly where the canonical text is, with the same word. -/
theorem schemaDigest_refused (schema : Value) (w : String) :
    schemaDigest schema = .error (.refused w) ↔ schemaCanon schema = .error (.refused w) := by
  unfold schemaDigest
  cases schemaCanon schema <;> simp [Except.map]

/-- An accepted schema's digest is the digest of its canonical text. -/
theorem schemaDigest_ok {schema : Value} {t : String} (h : schemaCanon schema = .ok t) :
    schemaDigest schema = .ok (digestOfText t) := by
  simp [schemaDigest, h, Except.map]

/-- Every digest answered is 64 characters. -/
theorem schemaDigest_length {schema : Value} {d : String} (h : schemaDigest schema = .ok d) :
    d.length = 64 := by
  unfold schemaDigest at h
  cases hc : schemaCanon schema with
  | error e => rw [hc] at h; simp [Except.map] at h
  | ok t =>
    rw [hc] at h
    simp only [Except.map, Except.ok.injEq] at h
    rw [← h]
    exact Digest.ofPreimage_length _

/-- v1's `render_schema` of a canonical text. -/
def renderCanonText (t : String) : String := "canon|" ++ t

/-- v1's `render_schema` of a digest. -/
def renderDigest (d : String) : String := "digest|" ++ d

end Principia.Falcon.Schema
