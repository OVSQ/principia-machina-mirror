import Principia.Canonical
import Principia.Parameters
import Principia.Falcon.Canon

/-!
# The cluster month's due rule and the page's state (TPS 5.19.3, 5.19.4)

The month's run is due from the clock and the prior page's state, so that no date arithmetic
is the wiki's: the month's publication is the first due run on or after day 1 of the month
(UTC, TPS 5.19.3). A source whose fetch fails keeps the prior page, in state SOURCE FAILING
with the source named, and is retried at each run for SOURCE RETRY (7 days); then the page is
published without it, in state PUBLISHED with the lost source named; after SOURCE LOST cycles
(2) the state is SOURCE LOST (TPS 5.19.4, 7.2.24).

**The clock and the month.** The clock is the count of UTC seconds since 1970-01-01T00:00:00Z,
at most `maxClock` (9999-12-31T23:59:59Z). A month is its index `k` from January 1970: year
`1970 + k / 12`, month `k % 12 + 1`. `monthStart k` is the first second of month `k`, built
month by month from the Gregorian month lengths (`Principia.Falcon.monthDays`); `monthOf` is its
inverse on the clock (`monthOf_bracket`, `monthOf_monthStart`): the month whose first second is
at or before the clock and whose successor's is after it. A month is written `YYYY-MM`
(`monthText`), read back by `parseMonth` (`parseMonth_monthText`).

**The state block.** The page's state block, read and written here (`readBlock`, `writeBlock`,
the round trip `readBlock_writeBlock`), is the JSON object
`{"failing": [{"lost": n, "since": t, "source": s}, ...], "month": "YYYY-MM" | null,
"state": "PUBLISHED" | "SOURCE FAILING" | "SOURCE LOST"}`: `month` the month last published
(`null` before the first publication), `state` the page's state word, and `failing` each
source failing now, in code point order of its name, with the clock `since` its failure began
and `lost` the publications made without it since then. No other member is taken.

**The rule.** A run is due when the month last published is not the clock's month
(`due`); a month published is not due again before day 1 of the next month
(`not_due_within_month`). A due run that fetched answers the next state from each declared
source's outcome (`step`): a failed source keeps its failure's start, a new one starts at the
clock, a served one is no longer failing. While any failing source is within SOURCE RETRY of
its failure's start the page is kept (state SOURCE FAILING, the month unchanged): a run inside
SOURCE RETRY of a failure never publishes without the source (`publish_only_past_retry`,
`failed_named`). Otherwise the page is published for the clock's month, each failing source's
`lost` counted up by one, in state SOURCE LOST when one has reached SOURCE LOST cycles and
PUBLISHED otherwise; with every source served the state is PUBLISHED and nothing is failing
(`all_served_publishes`).
-/

namespace Principia.Cluster.Schedule

open Principia.Canonical (Value)

/-! ## The clock and the month -/

/-- The seconds of a day. -/
def daySeconds : Nat := 86400

/-- The latest clock taken: 9999-12-31T23:59:59Z. -/
def maxClock : Nat := 253402300799

/-- The latest month taken: December 9999. -/
def maxMonth : Nat := 12 * (9999 - 1970) + 11

/-- Month `k`'s year. -/
def year (k : Nat) : Nat := 1970 + k / 12

/-- Month `k`'s number in its year, 1 to 12. -/
def monthNo (k : Nat) : Nat := k % 12 + 1

/-- Month `k`'s days. -/
def daysIn (k : Nat) : Nat := Principia.Falcon.monthDays (year k) (monthNo k)

/-- The first second of month `k`. -/
def monthStart : Nat → Nat
  | 0 => 0
  | k + 1 => monthStart k + daysIn k * daySeconds

theorem daysIn_ge (k : Nat) : 28 ≤ daysIn k := by
  unfold daysIn Principia.Falcon.monthDays
  split
  · split <;> omega
  all_goals omega

theorem monthStart_succ (k : Nat) : monthStart (k + 1) = monthStart k + daysIn k * daySeconds := rfl

theorem monthStart_lt_succ (k : Nat) : monthStart k < monthStart (k + 1) := by
  have := daysIn_ge k
  rw [monthStart_succ]
  unfold daySeconds
  omega

theorem monthStart_mono {a b : Nat} (h : a ≤ b) : monthStart a ≤ monthStart b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a = b + 1
    · subst hab; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (monthStart_lt_succ b))

/-- The month of clock `c`, walked month by month from `k` (whose first second is `acc`), at
most `fuel` months. -/
def walk (c : Nat) : Nat → Nat → Nat → Nat
  | 0, k, _ => k
  | f + 1, k, acc =>
    if c < acc + daysIn k * daySeconds then k else walk c f (k + 1) (acc + daysIn k * daySeconds)

/-- The month of clock `c`. Each month has at least 28 days, so `c / (28 days) + 1` months of
walk reach it. -/
def monthOf (c : Nat) : Nat := walk c (c / (28 * daySeconds) + 1) 0 0

theorem walk_bracket (c : Nat) : ∀ (f k acc : Nat), acc = monthStart k → acc ≤ c →
    c < acc + f * (28 * daySeconds) →
    monthStart (walk c f k acc) ≤ c ∧ c < monthStart (walk c f k acc + 1)
  | 0, k, acc, _, h1, h2 => by simp at h2; omega
  | f + 1, k, acc, h0, h1, h2 => by
    unfold walk
    split
    · rename_i h
      subst h0
      exact ⟨h1, by rw [monthStart_succ]; exact h⟩
    · rename_i h
      have hd := daysIn_ge k
      apply walk_bracket c f (k + 1)
      · rw [monthStart_succ, h0]
      · omega
      · unfold daySeconds at *
        rw [Nat.add_mul] at h2
        have : 28 * 86400 ≤ daysIn k * 86400 := Nat.mul_le_mul_right _ hd
        omega

/-- The month of a clock holds it: its first second is at or before the clock, its
successor's after it. -/
theorem monthOf_bracket (c : Nat) : monthStart (monthOf c) ≤ c ∧ c < monthStart (monthOf c + 1) := by
  apply walk_bracket
  · rfl
  · show 0 ≤ c; omega
  · unfold daySeconds; omega

/-- A month that holds a clock is that clock's month. -/
theorem monthOf_unique {m c : Nat} (h1 : monthStart m ≤ c) (h2 : c < monthStart (m + 1)) :
    monthOf c = m := by
  obtain ⟨b1, b2⟩ := monthOf_bracket c
  by_cases hlt : monthOf c < m
  · have := monthStart_mono (show monthOf c + 1 ≤ m by omega)
    omega
  · by_cases hgt : m < monthOf c
    · have := monthStart_mono (show m + 1 ≤ monthOf c by omega)
      omega
    · omega

/-- The month of a month's first second is that month: `monthOf` is proved against its
inverse `monthStart`. -/
theorem monthOf_monthStart (k : Nat) : monthOf (monthStart k) = k :=
  monthOf_unique (Nat.le_refl _) (monthStart_lt_succ k)

/-! ## The month's text, `YYYY-MM` -/

/-- The character of a digit, 0 to 9. -/
def digit (n : Nat) : Char := Char.ofNat (48 + n)

/-- The value of a digit's character. -/
def digitValue (ch : Char) : Nat := ch.toNat - 48

theorem digit_fin : ∀ n : Fin 10, digitValue (digit n) = n ∧ (digit n).isDigit = true := by decide

theorem digitValue_digit {n : Nat} (h : n < 10) : digitValue (digit n) = n := (digit_fin ⟨n, h⟩).1

theorem isDigit_digit {n : Nat} (h : n < 10) : (digit n).isDigit = true := (digit_fin ⟨n, h⟩).2

/-- Month `k`'s characters. -/
def monthChars (k : Nat) : List Char :=
  [digit (year k / 1000 % 10), digit (year k / 100 % 10), digit (year k / 10 % 10), digit (year k % 10),
    '-', digit (monthNo k / 10), digit (monthNo k % 10)]

/-- Month `k` written `YYYY-MM`. -/
def monthText (k : Nat) : String := String.ofList (monthChars k)

/-- A month written `YYYY-MM`, of the year 1970 to 9999. -/
def parseMonth (s : String) : Option Nat :=
  match s.toList with
  | [a, b, c, d, '-', e, f] =>
    if a.isDigit && b.isDigit && c.isDigit && d.isDigit && e.isDigit && f.isDigit then
      let y := 1000 * digitValue a + 100 * digitValue b + 10 * digitValue c + digitValue d
      let m := 10 * digitValue e + digitValue f
      if 1970 ≤ y && 1 ≤ m && m ≤ 12 then some ((y - 1970) * 12 + (m - 1)) else none
    else none
  | _ => none

theorem parseMonth_monthText {k : Nat} (h : k ≤ maxMonth) : parseMonth (monthText k) = some k := by
  have hy : year k < 10000 := by unfold year maxMonth at *; omega
  have hm1 : 1 ≤ monthNo k := by unfold monthNo; omega
  have hm2 : monthNo k ≤ 12 := by unfold monthNo; omega
  unfold parseMonth monthText monthChars
  rw [String.toList_ofList]
  simp only [isDigit_digit (Nat.mod_lt _ (by decide : 10 > 0)),
    isDigit_digit (show monthNo k / 10 < 10 by omega), Bool.and_self,
    digitValue_digit (Nat.mod_lt _ (by decide : 10 > 0)),
    digitValue_digit (show monthNo k / 10 < 10 by omega), ite_true]
  have hy' : 1000 * (year k / 1000 % 10) + 100 * (year k / 100 % 10) + 10 * (year k / 10 % 10) +
      year k % 10 = year k := by omega
  have hm' : 10 * (monthNo k / 10) + monthNo k % 10 = monthNo k := by omega
  rw [hy', hm']
  have h1 : 1970 ≤ year k := by unfold year; omega
  simp only [h1, hm1, hm2, decide_true, Bool.and_self, ite_true, Option.some.injEq]
  unfold year monthNo
  omega

/-! ## The state block -/

/-- The page's state word. -/
inductive Word where
  | published
  | sourceFailing
  | sourceLost
  deriving DecidableEq, Repr

/-- The state word's text. -/
def Word.text : Word → String
  | .published => "PUBLISHED"
  | .sourceFailing => "SOURCE FAILING"
  | .sourceLost => "SOURCE LOST"

/-- A state word read from its text. -/
def Word.ofText? (s : String) : Option Word :=
  if s = "PUBLISHED" then some .published
  else if s = "SOURCE FAILING" then some .sourceFailing
  else if s = "SOURCE LOST" then some .sourceLost
  else none

theorem Word.ofText_text (w : Word) : Word.ofText? w.text = some w := by
  cases w <;> decide

/-- A source failing now: its name, the clock its failure began, and the publications made
without it since then. -/
structure Failing where
  source : String
  since : Nat
  lost : Nat
  deriving DecidableEq, Repr

/-- The page's state: the month last published, the state word, the sources failing. -/
structure Block where
  month : Option Nat
  word : Word
  failing : List Failing
  deriving DecidableEq, Repr

/-- Each failing source after the one before it, in code point order of the names. -/
def sortedSources : List Failing → Bool
  | a :: b :: rest => decide (a.source < b.source) && sortedSources (b :: rest)
  | _ => true

/-- A failing source's member of the block. -/
def writeFailing (e : Failing) : Value :=
  .obj [("lost", .int e.lost), ("since", .int e.since), ("source", .str e.source)]

/-- The month member: `null`, or the month's text. -/
def monthValue : Option Nat → Value
  | none => .null
  | some k => .str (monthText k)

/-- The state block's JSON object. -/
def writeBlock (b : Block) : Value :=
  .obj [("failing", .arr (b.failing.map writeFailing)), ("month", monthValue b.month),
    ("state", .str b.word.text)]

/-- A failing source read: the object of exactly `lost`, `since` and `source`, the name not
empty, the clock at most `maxClock`; else the word `failing`. -/
def readFailing : Value → Except String Failing
  | .obj ms =>
    if ms.length == 3 && ms.all (fun m => ["lost", "since", "source"].contains m.1) then
      match ms.lookup "source", ms.lookup "since", ms.lookup "lost" with
      | some (.str s), some (.int t), some (.int l) =>
        if !s.isEmpty && 0 ≤ t && t ≤ maxClock && 0 ≤ l then .ok ⟨s, t.toNat, l.toNat⟩
        else .error "failing"
      | _, _, _ => .error "failing"
    else .error "failing"
  | _ => .error "failing"

/-- The month member read: `null`, or a month's text; else the word `month`. -/
def readMonth : Value → Except String (Option Nat)
  | .null => .ok none
  | .str t =>
    match parseMonth t with
    | some k => .ok (some k)
    | none => .error "month"
  | _ => .error "month"

/-- The state block read: the object of exactly `failing`, `month` and `state`; else the
word of the member refused (`state` for the object itself). -/
def readBlock : Value → Except String Block
  | .obj ms =>
    if ms.length == 3 && ms.all (fun m => ["failing", "month", "state"].contains m.1) then
      match ms.lookup "failing", ms.lookup "month", ms.lookup "state" with
      | some (.arr xs), some mv, some (.str w) => do
        let fs ← xs.mapM readFailing
        if !sortedSources fs then throw "failing"
        let month ← readMonth mv
        match Word.ofText? w with
        | some word => pure ⟨month, word, fs⟩
        | none => throw "state"
      | some _, some _, some (.str _) => .error "failing"
      | _, _, _ => .error "state"
    else .error "state"
  | _ => .error "state"

/-- A block `writeBlock` writes and `readBlock` reads back: its month at most December 9999,
each failing source named and its clock at most `maxClock`, the sources in code point order. -/
def Block.wellformed (b : Block) : Bool :=
  (match b.month with
    | none => true
    | some k => decide (k ≤ maxMonth)) &&
  b.failing.all (fun e => !e.source.isEmpty && decide (e.since ≤ maxClock)) && sortedSources b.failing

theorem readFailing_writeFailing (e : Failing) (h : (!e.source.isEmpty && decide (e.since ≤ maxClock)) = true) :
    readFailing (writeFailing e) = .ok e := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  have h1 : (0 : Int) ≤ (e.since : Int) := Int.natCast_nonneg _
  have h2 : (e.since : Int) ≤ (maxClock : Int) := Int.ofNat_le.mpr h.2
  have h3 : (0 : Int) ≤ (e.lost : Int) := Int.natCast_nonneg _
  simp [readFailing, writeFailing, h.1, h1, h2, h3, List.lookup]

theorem mapM_readFailing (fs : List Failing)
    (h : fs.all (fun e => !e.source.isEmpty && decide (e.since ≤ maxClock)) = true) :
    (fs.map writeFailing).mapM readFailing = .ok fs := by
  induction fs with
  | nil => rfl
  | cons e rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, List.mapM_cons, readFailing_writeFailing e h.1, ih h.2]
    rfl

/-- The block's round trip: a well-formed block, written, reads back as itself. -/
theorem readBlock_writeBlock (b : Block) (h : b.wellformed = true) : readBlock (writeBlock b) = .ok b := by
  obtain ⟨month, word, fs⟩ := b
  simp only [Block.wellformed, Bool.and_eq_true] at h
  obtain ⟨⟨hm, hf⟩, hs⟩ := h
  have hmonth : readMonth (monthValue month) = .ok month := by
    cases month with
    | none => rfl
    | some k =>
      simp only [decide_eq_true_eq] at hm
      simp [readMonth, monthValue, parseMonth_monthText hm]
  simp only [writeBlock, readBlock]
  simp [List.lookup, mapM_readFailing fs hf]
  simp only [bind, Except.bind, hs, Bool.true_eq_false, ite_false, hmonth, Word.ofText_text]
  rfl

/-! ## The rule -/

/-- SOURCE RETRY, in seconds (`ClusterTuning.sourceRetry`, 7 days). -/
def retry : Nat := ({} : Principia.Parameters.ClusterTuning).sourceRetry.count

/-- SOURCE LOST, in cycles (`ClusterTuning.sourceLost`, 2). -/
def lostCycles : Nat := ({} : Principia.Parameters.ClusterTuning).sourceLost

theorem retry_eq : retry = 7 * 86400 := rfl

theorem lostCycles_eq : lostCycles = 2 := rfl

/-- Whether a run at clock `c` is due: the month last published (none before the first
publication, or no page) is not the clock's month. -/
def due (b : Option Block) (c : Nat) : Bool :=
  match b with
  | none => true
  | some b => b.month != some (monthOf c)

/-- A failure still within SOURCE RETRY of its start at clock `c`. -/
def withinRetry (c : Nat) (e : Failing) : Bool := decide (c - e.since < retry)

/-- The sources failing after a run at clock `c` whose fetch answered `outs` (each source
and whether it was served, in code point order of the names): a failed source keeps the
failure it had, a new one starts at the clock. -/
def nextFailing (prior : List Failing) (c : Nat) (outs : List (String × Bool)) : List Failing :=
  outs.filterMap fun o =>
    if o.2 then none
    else some ((prior.find? (·.source == o.1)).getD ⟨o.1, c, 0⟩)

/-- A run's answer: whether it publishes the clock's month, and the page's next state. -/
structure Next where
  publish : Bool
  block : Block
  deriving DecidableEq, Repr

/-- The next state of a due run at clock `c` whose fetch answered `outs`. -/
def step (b : Option Block) (c : Nat) (outs : List (String × Bool)) : Next :=
  let fs := nextFailing ((b.map (·.failing)).getD []) c outs
  if fs.any (withinRetry c) then
    ⟨false, ⟨b.bind (·.month), .sourceFailing, fs⟩⟩
  else
    let fs' := fs.map fun e => { e with lost := e.lost + 1 }
    ⟨true, ⟨some (monthOf c), if fs'.any (fun e => decide (lostCycles ≤ e.lost)) then .sourceLost else .published,
      fs'⟩⟩

/-- A month published is not due again before day 1 of the next month. -/
theorem not_due_within_month {b : Block} {m c : Nat} (hb : b.month = some m) (h1 : monthStart m ≤ c)
    (h2 : c < monthStart (m + 1)) : due (some b) c = false := by
  simp [due, hb, monthOf_unique h1 h2]

/-- A month published is due again from day 1 of the next month. -/
theorem due_from_next_month {b : Block} {m c : Nat} (hb : b.month = some m) (h : monthStart (m + 1) ≤ c) :
    due (some b) c = true := by
  have hc := (monthOf_bracket c).2
  have : m < monthOf c := by
    by_cases hle : monthOf c ≤ m
    · have := monthStart_mono (show monthOf c + 1 ≤ m + 1 by omega)
      omega
    · omega
  simp [due, hb]
  omega

/-- A run that publishes has every failing source past SOURCE RETRY of its failure's start. -/
theorem publish_only_past_retry {b : Option Block} {c : Nat} {outs : List (String × Bool)}
    (h : (step b c outs).publish = true) : ∀ e ∈ (step b c outs).block.failing, retry ≤ c - e.since := by
  intro e he
  by_cases hn : (nextFailing ((b.map (·.failing)).getD []) c outs).any (withinRetry c) = true
  · simp [step, hn] at h
  · simp only [step, hn] at he
    simp only [Bool.false_eq_true, ite_false, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    have hx' := List.any_eq_false.mp (by simpa using hn) x hx
    simp only [withinRetry, decide_eq_true_eq] at hx'
    show retry ≤ c - x.since
    omega

/-- Every source a run's fetch failed is named among the next state's failing sources. -/
theorem failed_named {b : Option Block} {c : Nat} {outs : List (String × Bool)} {s : String}
    (hs : (s, false) ∈ outs) : ∃ e ∈ (step b c outs).block.failing, e.source = s := by
  have hfind : ∀ (prior : List Failing), ((prior.find? (·.source == s)).getD ⟨s, c, 0⟩).source = s := by
    intro prior
    cases hp : prior.find? (·.source == s) with
    | none => rfl
    | some x =>
      have := List.find?_some hp
      simpa using this
  have hmem : ((((b.map (·.failing)).getD []).find? (·.source == s)).getD ⟨s, c, 0⟩) ∈
      nextFailing ((b.map (·.failing)).getD []) c outs := by
    unfold nextFailing
    exact List.mem_filterMap.mpr ⟨(s, false), hs, by simp⟩
  by_cases hn : (nextFailing ((b.map (·.failing)).getD []) c outs).any (withinRetry c) = true
  · simp only [step, hn, ite_true]
    exact ⟨_, hmem, hfind _⟩
  · simp only [step, hn, Bool.false_eq_true, ite_false]
    exact ⟨_, List.mem_map.mpr ⟨_, hmem, rfl⟩, hfind _⟩

/-- A run with every source served publishes the clock's month in state PUBLISHED, nothing
failing. -/
theorem all_served_publishes {b : Option Block} {c : Nat} {outs : List (String × Bool)}
    (h : ∀ o ∈ outs, o.2 = true) : step b c outs = ⟨true, ⟨some (monthOf c), .published, []⟩⟩ := by
  have hn : nextFailing ((b.map (·.failing)).getD []) c outs = [] := by
    unfold nextFailing
    rw [List.filterMap_eq_nil_iff]
    intro o ho
    simp [h o ho]
  simp [step, hn]

end Principia.Cluster.Schedule
