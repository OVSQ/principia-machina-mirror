import Tests.Calculator.Common

/-!
The Calculator's runners of the family `cluster`.
-/

open Lean
open Principia Principia.Canonical Principia.Calculator
open Tests.Canonical (Counts readJson field str arr value)

namespace Tests.Calculator

/-- `cluster_corpus.json`: every case's request through `cluster cluster` or
`cluster resolving_step`; v1's text, or v1's word as a refusal's detail. -/
def runClusterCalls : IO (Nat × Nat) := do
  let mut t : Counts := {}
  for c in ← v1Cases "vectors/cluster_corpus.json" do
    let name ← memberStr c "name"
    let expected ← memberStr c "expected"
    let fn := match member c "fn" with
      | some (.str "resolving") => "resolving_step"
      | _ => "cluster"
    let params := match member c "params" with
      | some (.obj ps) => ps
      | _ => []
    let keys := if fn == "cluster" then ["rows", "paired"] else ["spacing", "ses", "paired"]
    let request : Value := .obj (params ++ keys.filterMap fun k => (member c k).map (k, ·))
    let got := respondTo "cluster" fn request
    let ok := match got, expected.startsWith "ERROR:" with
      | .ok (.str text), false => text == expected
      | .error r, true => r.code == .badArgument && "ERROR:" ++ r.detail == expected
      | _, _ => false
    t ← t.check ok s!"cluster {fn} {name}: expected {repr expected}, got {repr (got.toOption.map (·.canonicalJson))}"
  return t.pair

end Tests.Calculator

namespace Tests.Calculator.Cluster

open Tests.Calculator

/-- The family `cluster`'s runners: each name as `lake test` prints it, in code point order. -/
def runners : List (String × IO (Nat × Nat)) := [
  ("pcalc cluster (cluster_corpus)", runClusterCalls),
]

end Tests.Calculator.Cluster
