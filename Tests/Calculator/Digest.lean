import Tests.Calculator.Common

/-!
The Calculator's runners of the family `digest`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- `digest_corpus.json`: every case's request through the digest family, v1's names
mapped to the Calculator's (`d_tfk` is `digest_research_assembly`, its zones' digests named
by their zones; `hex_digests` is `digests`); the answer is v1's digest. -/
def runDigestCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/digest_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let arg (k : String) : IO Value := match member input k with
      | some v => pure v
      | none => throw (IO.userError s!"{id}: no {k}")
    let (fn, request) ← match ← memberStr c "fn" with
      | "digest_fields" => pure ("digest_fields", Value.obj [("fields", ← arg "fields")])
      | "combine_digests" => pure ("combine_digests", Value.obj [("digests", ← arg "hex_digests")])
      | "d_tfk" => pure ("digest_research_assembly", Value.obj [("starting_set", ← arg "d_tpk"),
          ("correspondence", ← arg "d_trm"), ("criteria", ← arg "d_tms")])
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    let got := respondTo "digest" fn request
    let ok := match got with
      | .ok (.str d) => d == expect
      | _ => false
    t ← t.check ok s!"digest {fn} {id}: expected {expect}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

/-- `dis_corpus.json`: every case's request through the digest family, v1's names mapped to
the Calculator's (`d_tps` is `digest_specification`, `d_is` is `digest_instruction_set` with
its `d_tps` named `specification`, `tps_pages` is `specification_pages`); the answer's v1
`canon` text is `expect`, no string of it holding `,`, `[` or `]`
(`Tests.Canonical.bracketFree`); a digest case's preimage is compared too, through
`preimage_specification` and `preimage_instruction_set`. -/
def runDisCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/dis_corpus.json" do
    let id ← memberStr c "id"
    let expect ← memberStr c "expect"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let arg (k : String) : IO Value := match member input k with
      | some v => pure v
      | none => throw (IO.userError s!"{id}: no {k}")
    let (fn, pre, request) ← match ← memberStr c "fn" with
      | "pre_texts" => pure ("pre_texts", none, Value.obj [("wikitext", ← arg "wikitext")])
      | "tps_pages" => pure ("specification_pages", none, Value.obj [("pages", ← arg "pages")])
      | "d_tps" => pure ("digest_specification", some "preimage_specification",
          Value.obj [("version", ← arg "version"), ("pages", ← arg "pages")])
      | "d_is" => pure ("digest_instruction_set", some "preimage_instruction_set",
          Value.obj [("version", ← arg "version"), ("specification", ← arg "d_tps"),
            ("members", ← arg "members")])
      | other => throw (IO.userError s!"{id}: unknown function {other}")
    let got := respondTo "digest" fn request
    let ok := match got with
      | .ok v => v.canon == some expect && Tests.Canonical.bracketFree v
      | .error _ => false
    t ← t.check ok
      s!"digest {fn} {id}: expected {repr expect}, got {repr (got.toOption.map (·.canonicalJson))}"
    match member c "preimage", pre with
    | some (.str p), some preFn =>
      let ok := match respondTo "digest" preFn request with
        | .ok (.arr [.str "OK", .str q]) => q == p
        | _ => false
      t ← t.check ok s!"digest {preFn} {id}: expected {repr p}"
    | _, _ => pure ()
  return t.pair

/-- `dis_members.json`: each case's `input`, the request as written (an argument it lacks
stays absent), through `instruction_set_members`; the answer's canonical JSON is `expect`'s,
or, for a case with `refused` in its place, the Calculator's own refusal has `refused`'s word
and `detail`. A case with `specification_pages` and `page` also checks that its one member's
`h` is the `h` `specification_pages` answers for `page` over those pages. -/
def runDisMembers : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/dis_members.json" do
    let id ← memberStr c "id"
    let some input := member c "input" | throw (IO.userError s!"{id}: no input")
    let got := respondTo "digest" "instruction_set_members" input
    match member c "expect", member c "refused" with
    | some expect, none =>
      let ok := match got with
        | .ok v => v.canonicalJson.isSome && v.canonicalJson == expect.canonicalJson
        | .error _ => false
      t ← t.check ok
        s!"digest instruction_set_members {id}: expected {repr expect.canonicalJson}, got {repr (got.toOption.map (·.canonicalJson))}"
    | none, some refused =>
      let word ← match member refused "refused" with
        | some (.str w) => pure w
        | _ => throw (IO.userError s!"{id}: refused has no word")
      let detail ← match member refused "detail" with
        | some (.str d) => pure d
        | _ => throw (IO.userError s!"{id}: refused has no detail")
      let ok := match got with
        | .error r => r.code.word == word && r.detail == detail
        | .ok _ => false
      t ← t.check ok
        s!"digest instruction_set_members {id}: expected the refusal {word} {repr detail}, got {repr (got.toOption.map (·.canonicalJson))}"
    | _, _ => throw (IO.userError s!"{id}: expect or refused, one of them")
    match member c "specification_pages", member c "page" with
    | some pages, some (.str title) =>
      let kept := respondTo "digest" "specification_pages" (Value.obj [("pages", pages)])
      let ok := match got, kept with
        | .ok (.arr [.str "OK", .arr [.arr [_, .str h]]]), .ok (.arr [.str "OK", .arr rows]) =>
          rows.any fun r => r == .arr [.str title, .str h]
        | _, _ => false
      t ← t.check ok s!"digest instruction_set_members {id}: h is not specification_pages' h of {title}"
    | _, _ => pure ()
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Digest

open Tests.Calculator

/-- The family `digest`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc digest (digest_corpus)", runDigestCalls),
  ("pcalc digest (dis_corpus)", runDisCalls),
  ("pcalc digest (dis_members)", runDisMembers),
]

end Tests.Calculator.Digest
