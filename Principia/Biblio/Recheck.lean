import Principia.Falcon.Canon

/-!
# The bibliography recheck's first call: the due entries and their lookups (TPS 5.21.14, 5.21.18, 5.21.19)

Every entry with an identifier a declared registry takes is looked up again each BIBLIO
RECHECK period, at most BIBLIO RECHECK BATCH identifiers a run, the oldest CHECK date first,
and the fleet's lookups a day held to BIBLIO LOOKUP CAP (TPS 5.21.18, 5.21.21). This module is
the choice of a run's first-round lookups, before any fetch; the Calculator's `recheck_urls`
reads the request into it and builds each URL with `registryUrl`.

* An entry is **due** when it has an identifier a declared registry takes and its CHECK date
  is at least BIBLIO RECHECK days before the run's date, or it has no CHECK line (`isDue`).
* The due entries are taken in order: no CHECK line first, then the oldest CHECK date, ties by
  `bib_id` in code point order (`order`).
* An entry is taken whole or not at all, while its identifiers fit what is left of the batch
  and its fetches what is left of the day's cap; the first entry that does not fit ends the
  run's choice, so the entries taken are a prefix of the due entries in that order
  (`take_prefix`) and the run never exceeds either bound (`take_batch`, `take_cap`).
* An identifier whose URL is refused (the `.` or `..` segment, 5.21.14) is answered LOOKUP
  FAILED and not fetched; it counts against the batch, not the cap.
-/

namespace Principia.Biblio.Recheck

/-! ## Dates -/

/-- The leap years in `[0, y)`, year 0 counted (the proleptic Gregorian calendar). -/
def leapsBefore (y : Nat) : Nat := (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400

/-- The day number of a date, counted from 0000-01-01. -/
def dayNumber (y m d : Nat) : Nat :=
  365 * y + leapsBefore y + ((List.range (m - 1)).map fun i => Principia.Falcon.monthDays y (i + 1)).sum + (d - 1)

/-- A real date written `YYYY-MM-DD`, as its day number. -/
def parseDate (s : String) : Option Nat :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] =>
    let ys := [y1, y2, y3, y4]
    let ms := [m1, m2]
    let ds := [d1, d2]
    if (ys ++ ms ++ ds).all Char.isDigit then
      let y := Principia.Falcon.digitsValue ys
      let m := Principia.Falcon.digitsValue ms
      let d := Principia.Falcon.digitsValue ds
      if 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ Principia.Falcon.monthDays y m then some (dayNumber y m d)
      else none
    else none
  | _ => none

/-- A CHECK LINE's date (5.21.19: `CHECK <date> <value>` then its clauses), as its day number:
`CHECK`, a space, a real date and a space before the rest; `none` otherwise. -/
def checkDate (line : String) : Option Nat :=
  match line.toList with
  | 'C' :: 'H' :: 'E' :: 'C' :: 'K' :: ' ' :: rest =>
    let date := rest.take 10
    if (rest.drop 10).head? == some ' ' then parseDate (String.ofList date)
    else none
  | _ => none

/-! ## The choice -/

/-- One identifier of an entry planned for the first round: its kind, its text, and its
registry and URL, or `none` when the URL is refused (LOOKUP FAILED). -/
structure Planned where
  kind : String
  identifier : String
  target : Option (String × String)
  deriving DecidableEq, Repr

/-- An entry as the recheck reads it: its `bib_id`, its CHECK date's day number (`none`: no
CHECK line), and the identifiers a declared registry takes, in 5.21.19's order of kinds. -/
structure Entry where
  bibId : String
  checkDay : Option Nat
  planned : List Planned
  deriving DecidableEq, Repr

/-- Whether an entry is due on day `today` with the period `period` (days). -/
def isDue (today period : Nat) (e : Entry) : Bool :=
  !e.planned.isEmpty &&
    match e.checkDay with
    | none => true
    | some d => decide (period ≤ today - d)

/-- The order of the due entries: no CHECK line first, then the oldest CHECK date, ties by
`bib_id`. -/
def before (a b : Entry) : Bool :=
  match a.checkDay, b.checkDay with
  | none, none => decide (a.bibId ≤ b.bibId)
  | none, some _ => true
  | some _, none => false
  | some x, some y => decide (x < y) || (decide (x = y) && decide (a.bibId ≤ b.bibId))

/-- The due entries in their order. -/
def order (today period : Nat) (es : List Entry) : List Entry :=
  (es.filter (isDue today period)).mergeSort before

/-- An entry's identifiers, each counted against the batch. -/
def size (e : Entry) : Nat := e.planned.length

/-- An entry's fetches, each counted against the cap. -/
def fetches (e : Entry) : Nat := (e.planned.filter (·.target.isSome)).length

/-- The entries taken, whole, while each fits what is left of the batch `b` and the cap `c`. -/
def take : Nat → Nat → List Entry → List Entry
  | _, _, [] => []
  | b, c, e :: rest => if size e ≤ b && fetches e ≤ c then e :: take (b - size e) (c - fetches e) rest else []

/-- A run's choice: the entries taken and the due entries left (the backlog). -/
structure Choice where
  taken : List Entry
  backlog : Nat
  deriving DecidableEq, Repr

/-- The choice of a run on day `today`: the period, the batch, the cap and the day's lookups so
far. -/
def choose (today period batch cap done : Nat) (es : List Entry) : Choice :=
  let due := order today period es
  let taken := take batch (cap - done) due
  ⟨taken, due.length - taken.length⟩

/-! ## What the choice keeps -/

/-- The entries taken are a prefix of the list they are taken from. -/
theorem take_prefix : ∀ (b c : Nat) (es : List Entry), take b c es <+: es
  | _, _, [] => List.nil_prefix
  | b, c, e :: rest => by
    unfold take
    split
    · exact List.cons_prefix_cons.mpr ⟨rfl, take_prefix _ _ rest⟩
    · exact List.nil_prefix

/-- The entries taken hold at most `b` identifiers. -/
theorem take_batch : ∀ (b c : Nat) (es : List Entry), ((take b c es).map size).sum ≤ b
  | _, _, [] => by simp [take]
  | b, c, e :: rest => by
    unfold take
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := take_batch (b - size e) (c - fetches e) rest
      simp only [List.map_cons, List.sum_cons]
      omega
    · simp

/-- The entries taken make at most `c` fetches. -/
theorem take_cap : ∀ (b c : Nat) (es : List Entry), ((take b c es).map fetches).sum ≤ c
  | _, _, [] => by simp [take]
  | b, c, e :: rest => by
    unfold take
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := take_cap (b - size e) (c - fetches e) rest
      simp only [List.map_cons, List.sum_cons]
      omega
    · simp

/-- The entries a run takes are a prefix of the due entries in their order. -/
theorem choose_prefix (today period batch cap done : Nat) (es : List Entry) :
    (choose today period batch cap done es).taken <+: order today period es :=
  take_prefix _ _ _

/-- Every entry a run takes is one of the entries given, and due. -/
theorem choose_due {today period batch cap done : Nat} {es : List Entry} {e : Entry}
    (h : e ∈ (choose today period batch cap done es).taken) : e ∈ es ∧ isDue today period e = true := by
  have hm : e ∈ order today period es := (choose_prefix today period batch cap done es).subset h
  unfold order at hm
  have := (List.mergeSort_perm (es.filter (isDue today period)) before).mem_iff.mp hm
  exact List.mem_filter.mp this

/-- A run's identifiers, fetched and refused, are at most the batch. -/
theorem choose_batch (today period batch cap done : Nat) (es : List Entry) :
    (((choose today period batch cap done es).taken).map size).sum ≤ batch :=
  take_batch _ _ _

/-- A run's fetches are at most what the day's cap leaves. -/
theorem choose_cap (today period batch cap done : Nat) (es : List Entry) :
    (((choose today period batch cap done es).taken).map fetches).sum ≤ cap - done :=
  take_cap _ _ _

end Principia.Biblio.Recheck
