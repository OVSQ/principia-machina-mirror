import Principia.Calculator.Interface
import Principia.Digest
import Principia.Digest.Specification

/-!
# Family `digest`: the digests and their preimages

A digest is SHA-256 (`Principia.Sha256`) over its preimage, written as 64
lowercase hexadecimal characters.

* `digest_fields {"fields": [f, ...]}`: each field a string or an integer (v1
  `digest_fields`); `preimage_fields` takes the same request and answers its preimage.
* `combine_digests {"digests": [d, ...]}`: each a digest, 64 lowercase hexadecimal
  characters (v1 `combine_digests`); `preimage_digests` answers its preimage.
* `digest_research_assembly {"starting_set": d, "correspondence": d, "criteria": d}`:
  D(RAS) (v1 `d_tfk`); `preimage_research_assembly` answers its preimage.
* `tree_preimage {"tree": t}`: a zone tree, written as JSON: a string, an integer, or a
  list of trees (v1 tpc_zone `_node`).
* `pre_texts {"wikitext": w}`: a page's blocks (v1 `pre_texts`).
* `specification_pages {"pages": [[title, wikitext], ...]}`: the kept pages' list of
  `[title, h]` (v1 `tps_pages`).
* `digest_specification {"version": v, "pages": [[title, wikitext], ...]}`: D(PFS) (v1
  `d_tps`); `preimage_specification` answers its preimage.
* `digest_instruction_set {"version": v, "specification": d, "members": [[title, h], ...]}`:
  D(IS) (v1 `d_is`, its `d_tps` named by what it digests); `preimage_instruction_set` answers
  its preimage.

The last six answer as v1 answered, `["OK", answer]` or `["REFUSED", reason]`, and take any
JSON value where v1 took one, refusing as v1 refused for its type
(`Principia.Digest.Specification`). Their family bound: at most 1000 pages and 1000 members,
each a list v1 checks for repeats pair by pair.
-/

namespace Principia.Calculator.Digest

open Principia.Canonical Principia.Digest

/-- A digest field: a string or an integer. -/
def fieldOf : Value → Except Refusal Field
  | .str s => .ok (.text s)
  | .int n => .ok (.int n)
  | _ => badArgument "a field is a string or an integer"

mutual
/-- A zone tree: a string, an integer, or a list of trees. -/
def treeOf : Value → Except Refusal Tree
  | .str s => .ok (.text s)
  | .int n => .ok (.int n)
  | .arr xs => (treesOf xs).map .list
  | _ => badArgument "a tree is a string, an integer or a list of trees"

/-- The trees of a list. -/
def treesOf : List Value → Except Refusal (List Tree)
  | [] => .ok []
  | x :: xs => do
    let t ← treeOf x
    let ts ← treesOf xs
    pure (t :: ts)
end

/-- A list of digests' preimage or digest, or the refusal of one that is not a digest. -/
def digestsText : Option String → Except Refusal Value
  | some p => .ok (.str p)
  | none => badArgument "a digest is not 64 lowercase hexadecimal characters"

/-- The most pages or members a request may hold (the Calculator's bound): their titles are
compared pair by pair for a repeat. -/
def maxEntries : Nat := 1000

/-- A value that is a list of more than `maxEntries` entries is refused by the bound; any
other value goes to the function, which refuses what v1 refused. -/
def bounded (what : String) (v : Value) : Except Refusal Value :=
  match v with
  | .arr xs => do atMost what maxEntries xs; pure v
  | _ => pure v

open Principia.Digest.Specification in
/-- v1's answer of a digest or a preimage. -/
def textAnswer (r : Except Reason String) : Value := answer Value.str r

/-- The family's functions. -/
def calls : Family := [
  ("combine_digests", fun v => do
    let ds ← asList "digests" (← argument1 "digests" v)
    digestsText (combineDigests (← ds.mapM (asString "a digest")))),
  ("digest_fields", fun v => do
    let fs ← asList "fields" (← argument1 "fields" v)
    pure (.str (digestFields (← fs.mapM fieldOf)))),
  ("digest_instruction_set", fun v => do
    let (version, d, ms) ← argument3 "version" "specification" "members" v
    pure (textAnswer (Specification.digestInstructionSetOf version d (← bounded "members" ms)))),
  ("digest_research_assembly", fun v => do
    let (a, b, c) ← argument3 "starting_set" "correspondence" "criteria" v
    digestsText (digestResearchAssembly (← asString "starting_set" a)
      (← asString "correspondence" b) (← asString "criteria" c))),
  ("digest_specification", fun v => do
    let (version, pages) ← argument2 "version" "pages" v
    pure (textAnswer (Specification.digestSpecificationOf version (← bounded "pages" pages)))),
  ("pre_texts", fun v => do
    let w ← argument1 "wikitext" v
    pure (Specification.answer (fun bs => .arr (bs.map .str)) (Specification.preTextsOf w))),
  ("preimage_fields", fun v => do
    let fs ← asList "fields" (← argument1 "fields" v)
    pure (.str (preimageFields (← fs.mapM fieldOf)))),
  ("preimage_instruction_set", fun v => do
    let (version, d, ms) ← argument3 "version" "specification" "members" v
    pure (textAnswer
      (Specification.preimageInstructionSetOf version d (← bounded "members" ms)))),
  ("preimage_digests", fun v => do
    let ds ← asList "digests" (← argument1 "digests" v)
    digestsText (preimageDigests (← ds.mapM (asString "a digest")))),
  ("preimage_research_assembly", fun v => do
    let (a, b, c) ← argument3 "starting_set" "correspondence" "criteria" v
    digestsText (preimageResearchAssembly (← asString "starting_set" a)
      (← asString "correspondence" b) (← asString "criteria" c))),
  ("preimage_specification", fun v => do
    let (version, pages) ← argument2 "version" "pages" v
    pure (textAnswer
      (Specification.preimageSpecificationOf version (← bounded "pages" pages)))),
  ("specification_pages", fun v => do
    let pages ← argument1 "pages" v
    pure (Specification.answer Specification.pairsValue
      (Specification.specificationPagesOf (← bounded "pages" pages)))),
  ("tree_preimage", fun v => do
    pure (.str (← treeOf (← argument1 "tree" v)).preimage))]

end Principia.Calculator.Digest
