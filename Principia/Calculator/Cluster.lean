import Principia.Calculator.Interface
import Principia.Cluster
import Principia.Cluster.Bounded
import Principia.Cluster.Rows
import Principia.Cluster.Schedule
import Principia.Cluster.Screen
import Principia.Calculator.Identity

/-!
# Family `cluster`: the top-performer cluster

* `cluster {"rows": [[model, config, score, se], ...], "in_max"?, "cusp_max"?, "z"?,
  "spacing_floor"?, "paired"?: [[model, config, model, config, se], ...]}`: the cluster
  rule (TPS 5.19.8; v1 `tpc_cluster.cluster`).
* `resolving_step {"spacing": u, "ses": [se, ...], "in_max"?, "cusp_max"?, "z"?,
  "paired"?: [se, ...]}`: the resolving step (TPS 5.19.9).
* `cluster_rows {"scores": [[model, config, benchmark, score, se], ...], "core": [benchmark,
  ...], "se_definition": "ITEM-SAMPLING" | "FIXED-SET", "se_max": x, "released"?: [[model,
  date], ...], "updated"?: [[benchmark, date], ...]}`: each ROW's COMPOSITE SCORE, its SE and
  its state (TPS 5.19.6, `Principia.Cluster.Rows`). The answer is `{"rows": [...]}`, one
  member per ROW in the order of its first component: `model`, `config`, `composite` and
  `se2` (exact, `n/d`, or `null` when a core score is missing), `composite_text` and `se`
  (six decimals, or `null`), `state` (`LISTED` or `UNLISTED`) and `reasons`. FIXED-SET, and
  an SE given as an item count `{"items": n}`, are refused OWED. Its refusal words:
  `scores`, `score or se`, `score twice`, `core`, `se_definition`, `se_max`, `dates`.
* `cluster_screen {"rows": [{member: text or number, ...}, ...], "exclusion": [pattern, ...],
  "map": [MODEL MAP row, ...]}`: the EXCLUSION LIST applied to the raw rows at ingestion, the
  MODEL MAP, and the EXCLUSION LIST again on the canonical identifiers (TPS 5.19.5,
  `Principia.Cluster.Screen`). Each raw row holds the texts `model` and `config`; the map is
  the form `identity family_of` reads. The answer is `{"kept": [{"model", "config", "family",
  "row"}, ...], "excluded_at_ingestion": n, "excluded_after_map": n, "unmapped": n}`. Its
  refusal words: `rows`, `exclusion`, `model_map` (v1's word for the map).
* `cluster_text_check {"text": t, "exclusion": [pattern, ...]}`: whether the page's text
  names an excluded token: `{"clean": true, "position": null}`, or `{"clean": false,
  "position": i}`, `i` the first match's code point index; the token is never answered. Its
  refusal words: `text`, `exclusion`.
* `cluster_schedule {"clock": t, "state": block or null, "outcomes"?: {source: "SERVED" |
  "FAILED", ...}}`: the cluster month's due rule and the page's next state (TPS 5.19.3,
  5.19.4, `Principia.Cluster.Schedule`), so that no date arithmetic is the wiki's. `clock` is
  the count of UTC seconds since 1970-01-01T00:00:00Z, at most 9999-12-31T23:59:59Z; `state`
  the prior page's state block (`null` when there is no page yet), in the form that module's
  header gives: `{"failing": [{"lost": n, "since": t, "source": s}, ...], "month": "YYYY-MM"
  or null, "state": "PUBLISHED" | "SOURCE FAILING" | "SOURCE LOST"}`, the failing sources in
  code point order of their names. Without `outcomes` (the run has not fetched) the answer is
  `{"due": d, "month": "YYYY-MM"}`, the clock's month; `due` is false while the month last
  published is the clock's month. With `outcomes` (each declared source and whether its fetch
  was served, given only for a due run) the answer adds `publish` (whether the run publishes
  the clock's month), `state` (the page's next state block, to be written back) and `named`
  (the sources the state word names: those within SOURCE RETRY of their failure while the
  state is SOURCE FAILING, else every source published without). A failing source of the
  prior block that `outcomes` does not name is refused OWED: the sources do not say what
  becomes of a source no longer declared. Its refusal words: `clock`, `state` (the block, or a
  state word its sources and month do not bear out), `failing`, `month` (a month after the
  clock's, or not a month), `outcomes` (not an object of at most `maxSources` sources, each
  `SERVED` or `FAILED`, or given for a run not due).

At most `maxRows` rows (or SEs) and `maxPaired` paired SEs. An absent threshold is its declared value (`Principia.Parameters`), an absent
`spacing_floor` 0, an absent or `null` `paired` ITEM-SAMPLING. The answer is v1's text of
the result (`render`, `render_resolving`): its spacings are square roots, written to six
decimals as v1 wrote them, which no exact JSON number holds. A request v1 refused is
refused here with v1's word as the detail (`ids`, `score or se`, `parameters`, `paired`,
`spacing`, `ses`), the checks made in v1's order. Both functions compute within the bound on
an exact value (`Principia.Cluster.Bounded`): a request whose values, or whose answer's
text, would cross it is refused, "exact value too large".
-/

namespace Principia.Calculator.Cluster

open Principia.Canonical

/-- The most rows a `cluster` request holds, and the most SEs a `resolving_step` request
holds: the rows are sorted by insertion (a month has a few dozen), and 1000 take 0.06 s. -/
def maxRows : Nat := 1000

/-- The most paired SEs a request holds: each is checked against those before it, and
5000 take under half a second. -/
def maxPaired : Nat := 5000

/-- v1's refusal: its `ValueError` word. -/
def refuse {α : Type} (e : Principia.Cluster.ClusterError) : Except Refusal α :=
  badArgument e.message

/-- A value v1 checks, refused with v1's word when it is not of its kind. -/
def orWord {α : Type} (e : Principia.Cluster.ClusterError) : Except Refusal α → Except Refusal α
  | .ok a => .ok a
  | .error _ => refuse e

/-- The rows, checked as v1's `_check` checks them, row by row: ids strings, not empty
and not repeated, then the score and the SE numbers and the SE not negative. -/
def readRows : List Value → List Principia.Cluster.RowKey → List Principia.Cluster.Row →
    Except Refusal (List Principia.Cluster.Row)
  | [], _, acc => .ok acc.reverse
  | .arr [.str m, .str c, s, u] :: rest, seen, acc => do
    if m.isEmpty || c.isEmpty || seen.contains (m, c) then refuse .ids
    let score ← orWord .scoreOrSe (asNumber "a score" s)
    let se ← orWord .scoreOrSe (asNumber "an SE" u)
    if se < 0 then refuse .scoreOrSe
    readRows rest ((m, c) :: seen) (⟨m, c, score, se⟩ :: acc)
  | .arr [_, _, _, _] :: _, _, _ => refuse .ids
  | _ :: _, _, _ => badArgument "a row is [model, config, score, se]"

/-- A threshold: absent, its declared value; not a number, v1's `parameters`. -/
def threshold (ms : List (String × Value)) (name : String) (dflt : Rat) : Except Refusal Rat :=
  match optional ms name with
  | none => .ok dflt
  | some x => orWord .parameters (asNumber name x)

/-- IN MAX, CUSP MAX and Z. -/
def thresholds (ms : List (String × Value)) : Except Refusal Principia.Cluster.Thresholds := do
  let d : Principia.Cluster.Thresholds := {}
  pure { inMax := ← threshold ms "in_max" d.inMax, cuspMax := ← threshold ms "cusp_max" d.cuspMax,
         z := ← threshold ms "z" d.z }

/-- A paired entry `[model, config, model, config, se]`; anything else is v1's
`paired`. -/
def pairedEntry : Value → Except Refusal Principia.Cluster.PairedSe
  | .arr [.str ma, .str ca, .str mb, .str cb, s] => do
    pure ⟨(ma, ca), (mb, cb), ← orWord .paired (asNumber "a paired SE" s)⟩
  | _ => refuse .paired

/-- The most component scores a `cluster_rows` request holds: each ROW's components are
found by a scan, and a month has a few dozen ROWs on a few benchmarks. -/
def maxScores : Nat := 5000

/-- The most CORE SET benchmarks a `cluster_rows` request holds. -/
def maxCore : Nat := 100

/-- A component of `cluster_rows`: its SE, or `none` when an item count stands in its place. -/
def readScores : List Value → List (Principia.Cluster.Rows.Component × Bool) →
    Except Refusal (List (Principia.Cluster.Rows.Component × Bool))
  | [], acc => .ok acc.reverse
  | .arr [.str m, .str c, .str b, s, u] :: rest, acc => do
    if m.isEmpty || c.isEmpty || b.isEmpty then badArgument "scores"
    if acc.any (fun (x, _) => x.model == m && x.config == c && x.benchmark == b) then
      badArgument "score twice"
    let score ← orWordText "score or se" (asNumber "a score" s)
    let (se, items) ← match u with
      | .obj ms => do
        match ms.lookup "items", ms.length with
        | some n, 1 => do let _ ← orWordText "score or se" (asCount "an item count" n); pure (0, true)
        | _, _ => badArgument "score or se"
      | _ => do pure (← orWordText "score or se" (asNumber "an SE" u), false)
    if se < 0 then badArgument "score or se"
    readScores rest ((⟨m, c, b, score, se⟩, items) :: acc)
  | _ :: _, _ => badArgument "scores"
where
  orWordText {α : Type} (w : String) : Except Refusal α → Except Refusal α
    | .ok a => .ok a
    | .error _ => badArgument w

/-- A date `YYYY-MM-DD`: ten characters, digits but for the two hyphens. -/
def isDate (s : String) : Bool :=
  let cs := s.toList
  cs.length == 10 && (cs.zipIdx.all fun (ch, i) => if i == 4 || i == 7 then ch == '-' else ch.isDigit)

/-- A list of `[name, date]` pairs, none named twice; anything else is the word `dates`. -/
def readDates (ms : List (String × Value)) (name : String) : Except Refusal (List (String × String)) :=
  match optional ms name with
  | none => .ok []
  | some (.arr xs) => do
    let ps ← xs.mapM fun
      | .arr [.str n, .str d] => if !n.isEmpty && isDate d then .ok (n, d) else badArgument "dates"
      | _ => badArgument "dates"
    if (ps.map (·.1)).eraseDups.length != ps.length then badArgument "dates"
    pure ps
  | some _ => badArgument "dates"

/-- An exact rational's text: `n` or `n/d`. -/
def ratValue : Option Rat → Value
  | none => .null
  | some q => .str (toString q)

/-- A ROW's measure as the answer's member. -/
def measureValue (m : Principia.Cluster.Rows.Measure) : Value :=
  .obj [("model", .str m.model), ("config", .str m.config),
    ("composite", ratValue m.composite),
    ("composite_text", match m.composite with
      | none => .null | some q => .str (Principia.Cluster.Surd.ofRat q).fixed6),
    ("se2", ratValue m.se2),
    ("se", match m.se2 with
      | none => .null | some s => .str (Principia.Cluster.Surd.sqrt s).fixed6),
    ("state", .str (if m.listed then "LISTED" else "UNLISTED")),
    ("reasons", .arr (m.reasons.map fun r => .str r.word))]

/-- `cluster_rows`. -/
def clusterRows (v : Value) : Except Refusal Value := do
  let ms ← membersOf ["scores", "core", "se_definition", "se_max", "released", "updated"] v
  let scoresList ← asList "scores" (← needed ms "scores")
  atMost "scores" maxScores scoresList
  let comps ← readScores scoresList []
  let coreList ← match ← needed ms "core" with
    | .arr xs => pure xs
    | _ => badArgument "core"
  atMost "core" maxCore coreList
  let core ← coreList.mapM fun
    | .str b => if b.isEmpty then badArgument "core" else pure b
    | _ => badArgument "core"
  if core.isEmpty || core.eraseDups.length != core.length then badArgument "core"
  let seDef ← match ← needed ms "se_definition" with
    | .str "ITEM-SAMPLING" => pure false
    | .str "FIXED-SET" => pure true
    | _ => badArgument "se_definition"
  let seMax ← match asNumber "se_max" (← needed ms "se_max") with
    | .ok x => if x < 0 then badArgument "se_max" else pure x
    | .error _ => badArgument "se_max"
  let released ← readDates ms "released"
  let updated ← readDates ms "updated"
  if seDef then
    throw ⟨.owed, "the SE under FIXED-SET (its run-to-run SE on shared items is marked VERIFY by the sources)"⟩
  if comps.any (·.2) then
    throw ⟨.owed, "the binomial SE from an item count (the sources do not fix its scale)"⟩
  let cs := comps.map (·.1)
  let cset : Principia.Cluster.Rows.CoreSet := ⟨core, seMax⟩
  let _ ← bounded (Principia.Cluster.Rows.rowsWithin cs cset)
  pure (.obj [("rows", .arr ((Principia.Cluster.Rows.rows cs cset released updated).map measureValue))])

/-! ## The EXCLUSION LIST and the MODEL MAP -/

/-- The most EXCLUSION LIST patterns a request holds. -/
def maxPatterns : Nat := 256

/-- The most characters an EXCLUSION LIST pattern holds. -/
def maxPatternLength : Nat := 200

/-- The most work a request asks: the characters of the texts scanned times the characters of
the EXCLUSION LIST's patterns. The scan tries every pattern at each character, each try at
most as long as its pattern, so this bounds its steps; a request at the bound built to make
every try run its whole length took under a second when measured (0.77 s: a text of 998,000
characters against one pattern of 100; 0.31 s: 10,000 characters against 50 patterns of
200; 0.27 s: 1000 rows against one pattern of 200). -/
def maxWork : Nat := 100000000

/-- The work bound: `chars` characters of text against the patterns `ps`. -/
def withinWork (chars : Nat) (ps : List (List Char)) : Except Refusal Unit :=
  if maxWork < chars * (ps.map List.length).sum then
    badArgument "the texts and the EXCLUSION LIST exceed the Calculator's bound"
  else .ok ()

/-- The EXCLUSION LIST: a list of texts, each with a character other than Cf and at most
`maxPatternLength` characters; anything else is the word `exclusion`. -/
def readExclusion (ms : List (String × Value)) : Except Refusal (List (List Char)) := do
  let xs ← match ← needed ms "exclusion" with
    | .arr xs => pure xs
    | _ => badArgument "exclusion"
  atMost "exclusion" maxPatterns xs
  xs.mapM fun
    | .str p =>
      let q := Principia.Cluster.Screen.pattern p
      if q.isEmpty || maxPatternLength < p.length then badArgument "exclusion" else pure q
    | _ => badArgument "exclusion"

/-- A raw row: an object, no member named twice, every member a text or a number, the texts
`model` and `config` not empty; anything else is the word `rows`. -/
def readRaw : Value → Except Refusal Principia.Cluster.Screen.Raw
  | .obj ms => do
    unless ms.all (fun (_, v) => match v with | .str _ | .int _ | .num _ => true | _ => false) do
      badArgument "rows"
    if (ms.map (·.1)).eraseDups.length != ms.length then badArgument "rows"
    match ms.lookup "model", ms.lookup "config" with
    | some (.str m), some (.str c) =>
      if m.isEmpty || c.isEmpty then badArgument "rows" else pure ms
    | _, _ => badArgument "rows"
  | _ => badArgument "rows"

/-- A kept row as the answer's member. -/
def keptValue (k : Principia.Cluster.Screen.Kept) : Value :=
  .obj [("model", .str k.model), ("config", .str k.config), ("family", .str k.family),
    ("row", .obj k.row)]

/-- `cluster_screen`: the rows, the EXCLUSION LIST and the MODEL MAP read in that order. -/
def clusterScreen (v : Value) : Except Refusal Value := do
  let ms ← membersOf ["rows", "exclusion", "map"] v
  let rowsList ← match ← needed ms "rows" with
    | .arr xs => pure xs
    | _ => badArgument "rows"
  atMost "rows" maxRows rowsList
  let rows ← rowsList.mapM readRaw
  let ps ← readExclusion ms
  let map ← match Principia.Identity.checkMap
      (Principia.Calculator.Identity.zoneValue (← needed ms "map")) with
    | .ok m => pure m
    | .error _ => badArgument "model_map"
  -- Each row's texts, its model and configuration again in NFC, and the longest map row's
  -- family, server and quantization.
  let idChars := (map.map fun (_, r) => r.family.length +
    (r.server.map String.length).getD 0 + (r.quantization.map String.length).getD 0).foldl max 0
  withinWork (2 * ((rows.flatMap Principia.Cluster.Screen.rawTexts).map String.length).sum +
    rows.length * idChars) ps
  let a := Principia.Cluster.Screen.screen ps map rows
  pure (.obj [("kept", .arr (a.kept.map keptValue)),
    ("excluded_at_ingestion", .int a.ingestion), ("excluded_after_map", .int a.afterMap),
    ("unmapped", .int a.unmapped)])

/-- `cluster_text_check`: the text, then the EXCLUSION LIST. -/
def clusterTextCheck (v : Value) : Except Refusal Value := do
  let ms ← membersOf ["text", "exclusion"] v
  let t ← match ← needed ms "text" with
    | .str t => pure t
    | _ => badArgument "text"
  let ps ← readExclusion ms
  withinWork t.length ps
  pure <| match Principia.Cluster.Screen.textCheck ps t with
    | none => .obj [("clean", .bool true), ("position", .null)]
    | some i => .obj [("clean", .bool false), ("position", .int i)]

/-! ## The cluster month's due rule and the page's state -/

section Schedule

open Principia.Cluster.Schedule

/-- The most sources a `cluster_schedule` request names, in its outcomes or its block. -/
def maxSources : Nat := 100

/-- The clock: an integer count of seconds, 0 to `maxClock`; else the word `clock`. -/
def readClock (ms : List (String × Value)) : Except Refusal Nat := do
  match ← needed ms "clock" with
  | .int n => if 0 ≤ n && n ≤ (maxClock : Int) then pure n.toNat else badArgument "clock"
  | _ => badArgument "clock"

/-- A block whose state word its failing sources and its month bear out: SOURCE FAILING has a
source in its first SOURCE RETRY (none yet published without); PUBLISHED and SOURCE LOST have a
month published and every failing source published without at least once, SOURCE LOST alone
one at SOURCE LOST cycles; before the first publication no source was published without. -/
def consistent (b : Block) : Bool :=
  let lostAll := b.failing.all (fun e => 1 ≤ e.lost)
  let reached := b.failing.any (fun e => lostCycles ≤ e.lost)
  (match b.word with
    | .sourceFailing => b.failing.any (·.lost == 0)
    | .published => b.month.isSome && lostAll && !reached
    | .sourceLost => b.month.isSome && lostAll && reached) &&
  (b.month.isSome || b.failing.all (·.lost == 0))

/-- The prior page's state at clock `c`: `null`, or a block read and borne out, its month not
after the clock's, a SOURCE FAILING page not of the clock's month, no failure begun after the
clock. -/
def readState (ms : List (String × Value)) (c : Nat) : Except Refusal (Option Block) := do
  match ← needed ms "state" with
  | .null => pure none
  | v =>
    match readBlock v with
    | .error w => badArgument w
    | .ok b =>
      atMost "failing" maxSources b.failing
      if !consistent b then badArgument "state"
      if (b.month.map (fun k => decide (monthOf c < k))).getD false then badArgument "month"
      if b.word == .sourceFailing && b.month == some (monthOf c) then badArgument "state"
      if b.failing.any (fun e => c < e.since) then badArgument "failing"
      pure (some b)

/-- The outcomes: an object of at most `maxSources` sources, at least one, each named and
`SERVED` or `FAILED`; answered in code point order of the names. Else the word `outcomes`. -/
def readOutcomes (v : Value) : Except Refusal (List (String × Bool)) := do
  let ms ← match v with
    | .obj ms => pure ms
    | _ => badArgument "outcomes"
  if ms.isEmpty || maxSources < ms.length then badArgument "outcomes"
  let sorted := ms.mergeSort (fun a b => decide (a.1 ≤ b.1))
  let rec distinct : List (String × Value) → Bool
    | a :: b :: rest => a.1 != b.1 && distinct (b :: rest)
    | _ => true
  if !distinct sorted then badArgument "outcomes"
  sorted.mapM fun
    | (s, .str "SERVED") => if s.isEmpty then badArgument "outcomes" else pure (s, true)
    | (s, .str "FAILED") => if s.isEmpty then badArgument "outcomes" else pure (s, false)
    | _ => badArgument "outcomes"

/-- `cluster_schedule`: the clock, the state, then the outcomes. -/
def clusterSchedule (v : Value) : Except Refusal Value := do
  let ms ← membersOf ["clock", "state", "outcomes"] v
  let c ← readClock ms
  let b ← readState ms c
  let d := due b c
  let month := Value.str (monthText (monthOf c))
  match optional ms "outcomes" with
  | none => pure (.obj [("due", .bool d), ("month", month)])
  | some ov =>
    if !d then badArgument "outcomes"
    let outs ← readOutcomes ov
    let prior := (b.map (·.failing)).getD []
    if prior.any (fun e => !outs.any (·.1 == e.source)) then
      throw ⟨.owed, "a failing source no longer declared (the sources do not say what becomes of its state)"⟩
    let n := step b c outs
    let named := if n.block.word == .sourceFailing then (n.block.failing.filter (withinRetry c)).map (·.source)
      else n.block.failing.map (·.source)
    pure (.obj [("due", .bool true), ("month", month), ("named", .arr (named.map .str)),
      ("publish", .bool n.publish), ("state", writeBlock n.block)])

end Schedule

/-- The family's functions. -/
def calls : Family := [
  ("cluster", fun v => do
    let ms ← membersOf ["rows", "in_max", "cusp_max", "z", "spacing_floor", "paired"] v
    let rowsList ← asList "rows" (← needed ms "rows")
    atMost "rows" maxRows rowsList
    let rows ← readRows rowsList [] []
    let t ← thresholds ms
    let floor ← threshold ms "spacing_floor" 0
    -- v1 checks the rows and the thresholds before a paired entry's form.
    match Principia.Cluster.checkInput rows t floor with
    | .error e => refuse e
    | .ok _ =>
      let paired ← match optional ms "paired" with
        | none => pure none
        | some p => do
          let ps ← orWord .paired (asList "paired" p)
          atMost "paired" maxPaired ps
          some <$> ps.mapM pairedEntry
      match ← bounded (Principia.Cluster.Bounded.cluster rows t floor paired) with
      | .ok r => pure (.str (Principia.Cluster.render r))
      | .error e => refuse e),
  ("resolving_step", fun v => do
    let ms ← membersOf ["spacing", "ses", "in_max", "cusp_max", "z", "paired"] v
    let spacing ← orWord .spacing (asNumber "spacing" (← needed ms "spacing"))
    if spacing < 0 then refuse .spacing
    let sesList ← orWord .ses (asList "ses" (← needed ms "ses"))
    atMost "ses" maxRows sesList
    let ses ← orWord .ses (sesList.mapM (asNumber "an SE"))
    let t ← thresholds ms
    -- v1 checks the spacing, the SEs and the thresholds before the paired SEs' form.
    match Principia.Cluster.Bounded.resolvingInput spacing ses t with
    | .error e => refuse e
    | .ok _ =>
      let paired ← match optional ms "paired" with
        | none => pure none
        | some p => do
          let ps ← orWord .paired (asList "paired" p)
          atMost "paired" maxRows ps
          some <$> orWord .paired (ps.mapM (asNumber "a paired SE"))
      match ← bounded (Principia.Cluster.Bounded.resolvingStep spacing ses t paired) with
      | .ok r => pure (.str (Principia.Cluster.renderResolving r))
      | .error e => refuse e),
  ("cluster_rows", clusterRows),
  ("cluster_schedule", clusterSchedule),
  ("cluster_screen", clusterScreen),
  ("cluster_text_check", clusterTextCheck)]

end Principia.Calculator.Cluster
