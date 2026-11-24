import Tests.Calculator.Common

/-!
The Calculator's runners of the family `biblio`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-! ## The bibliography through `pcalc` -/

/-- v1's `_esc`: `|` and `\` behind a backslash; a C0 control or DEL as `\xHH`. -/
def biblioEsc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '|' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 0x20 || c.toNat == 0x7F then
      let h := Nat.toDigits 16 c.toNat
      "\\x" ++ (if h.length < 2 then "0" else "") ++ String.ofList h
    else c.toString)

/-- A member of an answer object as a string, "" when absent or not a string. -/
def sOf (v : Value) (k : String) : String :=
  match member v k with
  | some (.str s) => s
  | _ => ""

/-- A text or `null` as v1 rendered None in `render_compare`: `-`. -/
def orDash : Option Value → String
  | some (.str s) => s
  | _ => "-"

/-- v1's render (`render_*` in tpc_biblio.py) of the family's JSON answer. -/
def biblioRender (fn : String) (v : Value) : Option String :=
  match fn, v with
  | "doi", _ => some s!"doi|{sOf v "kind"}|{biblioEsc (sOf v "doi")}|{biblioEsc (sOf v "id")}"
  | "shape", .bool b => some ("shape|" ++ toString b)
  | "withdrawn", .bool b => some ("withdrawn|" ++ toString b)
  | "arxiv", _ => match member v "version" with
    | some (.int n) => some s!"arxiv|{sOf v "id"}|{n}|{sOf v "key"}|{sOf v "scheme"}"
    | _ => none
  | "isbn", _ => some s!"isbn|{sOf v "isbn13"}|{sOf v "given"}"
  | "issn", .str s => some ("issn|" ++ s)
  | "pmid", .str s => some ("pmid|" ++ s)
  | "pmcid", .str s => some ("pmcid|" ++ s)
  | "key", .str s => some ("key|" ++ biblioEsc s)
  | "url", .str s => some ("url|" ++ biblioEsc s)
  | "preimage", .str s => some ("preimage|" ++ biblioEsc s)
  | "dupe", _ => some s!"dupe|{sOf v "kind"}|{biblioEsc (sOf v "key")}"
  | "canon", _ => some ("canon|" ++ sOf v "digest" ++ "\n" ++ biblioEsc (sOf v "text"))
  | "check", _ => do
    let d ← member v "dupe"
    let .obj ids ← member v "identifiers" | none
    -- v1's order of kinds (the answer's keys are sorted once written as canonical JSON).
    let idLines := ["DOI", "ARXIV", "ISBN", "ISSN", "PMID", "PMCID"].filterMap fun k =>
      match ids.lookup k with
      | some (.str s) => some s!"id|{k}|{biblioEsc s}"
      | _ => none
    some ("\n".intercalate (s!"check|OK|{sOf d "kind"}|{biblioEsc (sOf d "key")}" :: idLines))
  | "compare", _ => do
    let .arr rs ← member v "results" | none
    let .arr ns ← member v "notices" | none
    let rLines ← rs.mapM fun r => match r with
      | .arr [.str k, .str i, .str res, .arr fs] =>
        some s!"{k}|{biblioEsc i}|{res}|{",".intercalate (fs.filterMap fun | .str f => some f | _ => none)}"
      | _ => none
    let nLines := ns.map fun n =>
      s!"notice|{biblioEsc (sOf n "source")}|{biblioEsc (orDash (member n "identifier"))}|{orDash (member n "date")}|{biblioEsc (sOf n "type")}"
    let nl := sOf v "notices_line"
    some ("\n".intercalate ((("compare|" ++ sOf v "check") :: rLines) ++ nLines ++
      ["line|" ++ biblioEsc (sOf v "check_line"), "line|" ++ (if nl.isEmpty then "-" else biblioEsc nl)]))
  | "view", _ => do
    let .arr rs ← member v "records" | none
    let .arr hs ← member v "for_hdecl" | none
    let rLines ← rs.mapM fun r => match r with
      | .arr [.str rid, .arr fl] => do
        let parts ← fl.mapM fun p => match p with
          | .arr [.str b, .str reason] => some (biblioEsc b ++ ":" ++ reason)
          | _ => none
        some ("record|" ++ biblioEsc rid ++ "|" ++ "|".intercalate parts)
      | _ => none
    let hd := ",".intercalate (hs.filterMap fun | .str b => some (biblioEsc b) | _ => none)
    some ("\n".intercalate ((s!"view|{rs.length}" :: rLines) ++ ["hdecl|" ++ hd]))
  | "holdlist", .arr ps => do
    let ls ← ps.mapM fun p => match p with
      | .arr [.str b, .str c] => some (biblioEsc b ++ "|" ++ c)
      | _ => none
    some ("\n".intercalate (s!"holdlist|{ps.length}" :: ls))
  | _, _ => none

/-- `biblio_corpus.json`: all 405 cases through `biblio <fn>`, each case's `args` the request;
the answer rendered as v1 rendered it (`biblioRender`) and compared with `expected` byte for
byte; `ERROR:<m>` expects the refusal `BAD_ARGUMENT` with detail `m`. -/
def runBiblioCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/biblio_corpus.json" do
    let name ← memberStr c "name"
    let fn ← memberStr c "fn"
    let expected ← memberStr c "expected"
    let some args := member c "args" | throw (IO.userError s!"{name}: no args")
    let got := respondTo "biblio" fn args
    let ok := match got with
      | .ok v => biblioRender fn v == some expected
      | .error r => r.code == .badArgument && "ERROR:" ++ r.detail == expected
    t ← t.check ok s!"biblio {fn} {name}: expected {repr expected}, got {repr (got.toOption.bind (biblioRender fn))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

/-- The biblio family's bounds (`Calculator.Biblio`), each at its value and one past it. -/
def runBiblioBounds : IO (Nat × Nat) := do
  let mut t : Counts := {}
  let cases : List (String × String × Value × Bool) := [
    ("a text at 16384 code points", "pmid", .obj [("text", .str (codePoints 16384))], false),
    ("a text past 16384 code points", "pmid", .obj [("text", .str (codePoints 16385))], true),
    ("identifiers at 64", "dupe",
      .obj [("identifiers", .obj ((List.range 64).map fun i => (s!"K{i}", .str "x")))], false),
    ("identifiers past 64", "dupe",
      .obj [("identifiers", .obj ((List.range 65).map fun i => (s!"K{i}", .str "x")))], true),
    ("existing at 1024", "check",
      .obj [("entry", .obj []), ("existing", .arr ((List.range 1024).map fun _ => .arr [])), ("caps", .obj [])], false),
    ("existing past 1024", "check",
      .obj [("entry", .obj []), ("existing", .arr ((List.range 1025).map fun _ => .arr [])), ("caps", .obj [])], true),
    -- "comment" holds 7 code points.
    ("text at 131072 code points in all", "withdrawn",
      .obj [("comment", .arr (textsOf (131072 - 7)))], false),
    ("text past 131072 code points in all", "withdrawn",
      .obj [("comment", .arr (textsOf (131073 - 7)))], true)]
  for (what, fn, request, refused) in cases do
    let got := respondTo "biblio" fn request
    t ← t.check (boundRefusal got == refused)
      s!"biblio {fn}, {what}: expected refused {refused}, got {repr (got.toOption.map (·.canonicalJson))} or {repr (match got with | .error r => some r.detail | _ => none)}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Biblio

open Tests.Calculator

/-- The family `biblio`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc biblio (biblio_corpus)", runBiblioCalls),
  ("pcalc biblio bounds", runBiblioBounds),
]

end Tests.Calculator.Biblio
