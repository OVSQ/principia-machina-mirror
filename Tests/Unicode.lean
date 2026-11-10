import Principia

/-!
The runner of Unicode 15.1.0's own data against `Principia.Unicode`, the
normalization version 1 does at version 1's Unicode. Every file it reads is Unicode's, committed unchanged in
`vectors/unicode/`; `scripts/gen_unicode_tables.py --check` checks their SHA-256 (the
Calculator does not carry SHA-256 yet, decision D2).

* **NormalizationTest.txt**, every line of its four parts, by the file's conformance rules:
  NFC, c2 = NFC(c1) = NFC(c2) = NFC(c3) and c4 = NFC(c4) = NFC(c5); NFD, c3 = NFD(c1) =
  NFD(c2) = NFD(c3) and c5 = NFD(c4) = NFD(c5). Then every code point its Part 1 does not
  list is its own NFC and its own NFD, as the file requires of each.
* **UnicodeData.txt**, read here directly and not through the generator: the general
  category of every code point from 0 to U+10FFFF (a surrogate's too, by
  `generalCategoryOf`), and the canonical combining class and the full canonical
  decomposition (each mapping applied again until it no longer applies) of every Unicode
  scalar value. The Hangul syllables, which UnicodeData.txt decomposes by arithmetic and
  not by a mapping, are checked by NormalizationTest.txt's Part 1, which lists all 11,172.
* **The tables**: every item of each table text reads (the count is the generator's), the
  ranges and the keys increase without overlap, and each floor is the least code point its
  table reaches.

The runner prints the counts and the time it took.
-/

namespace Tests.Unicode

open Principia.Unicode
open Principia.Unicode.Tables

/-- The last code point. -/
def lastCode : Nat := 0x10FFFF

/-- A tally of checks, keeping the first failures' descriptions. -/
structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  shown : Array String := #[]

/-- Count one check; its description is built only when it fails. -/
@[inline] def Tally.check (t : Tally) (ok : Bool) (what : Unit → String) : Tally :=
  if ok then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1, shown := if t.shown.size < 20 then t.shown.push (what ()) else t.shown }

/-- `U+XXXX`. -/
def showCode (n : Nat) : String :=
  let ds := (Nat.toDigits 16 n).map Char.toUpper
  "U+" ++ String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

def showChars (l : List Char) : String := " ".intercalate (l.map (showCode ·.toNat))

/-- A Unicode scalar value: a code point that is not a surrogate. -/
def scalar (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n ≤ lastCode)

/-- A field of space-separated hexadecimal code points, each a scalar value. -/
def codes? (s : String) : Option (List Char) :=
  ((s.trimAscii.toString.splitOn " ").filter (· ≠ "")).mapM fun h => do
    let n ← hexValue? h
    if scalar n then some (Char.ofNat n) else none

/-! ## NormalizationTest.txt -/

/-- The NFC and NFD checks of one line, its five columns given. -/
def lineChecks (t : Tally) (line : String) (c : Array String) : Tally :=
  let f (k : Nat) : String := c[k]!
  let nfcOf := fun (k : Nat) => nfc (f k)
  let nfdOf := fun (k : Nat) => nfd (f k)
  let t := [0, 1, 2].foldl (fun t k =>
    t.check (nfcOf k == f 1) fun _ => s!"NFC of column {k + 1} of {line}: {showChars (nfcOf k).toList}") t
  let t := [3, 4].foldl (fun t k =>
    t.check (nfcOf k == f 3) fun _ => s!"NFC of column {k + 1} of {line}: {showChars (nfcOf k).toList}") t
  let t := [0, 1, 2].foldl (fun t k =>
    t.check (nfdOf k == f 2) fun _ => s!"NFD of column {k + 1} of {line}: {showChars (nfdOf k).toList}") t
  [3, 4].foldl (fun t k =>
    t.check (nfdOf k == f 4) fun _ => s!"NFD of column {k + 1} of {line}: {showChars (nfdOf k).toList}") t

/-- What the file gave: the tally, the number of lines, the code points of Part 1, the version
its first line names. -/
structure NormalizationRun where
  tally : Tally
  lines : Nat
  partOne : Array Bool
  header : String

def runNormalizationTest (text : String) : Except String NormalizationRun := do
  let mut t : Tally := {}
  let mut lines := 0
  let mut part := ""
  let mut partOne := Array.replicate (lastCode + 1) false
  let all := text.splitOn "\n"
  for raw in all do
    let line := ((raw.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "@Part" then
      part := (line.splitOn " ").headD ""
      continue
    let cols := line.splitOn ";"
    unless cols.length == 6 && cols.getLast? == some "" do throw s!"not five columns: {line}"
    let some cs := (cols.take 5).mapM codes? | throw s!"a column that does not read: {line}"
    let strs := (cs.map String.ofList).toArray
    t := lineChecks t line strs
    lines := lines + 1
    if part == "@Part1" then
      match cs.head? with
      | some [c] => partOne := partOne.set! c.toNat true
      | _ => throw s!"a Part 1 line whose first column is not one code point: {line}"
  return { tally := t, lines, partOne, header := (all.headD "").trimAscii.toString }

/-- Every scalar value Part 1 does not list is its own NFC and NFD. -/
def runOthers (partOne : Array Bool) : Tally × Nat := Id.run do
  let mut t : Tally := {}
  let mut n := 0
  for i in [0:lastCode + 1] do
    if scalar i && !partOne[i]! then
      let s := String.singleton (Char.ofNat i)
      t := t.check (nfc s == s) fun _ => s!"NFC of {showCode i} is not itself"
      t := t.check (nfd s == s) fun _ => s!"NFD of {showCode i} is not itself"
      n := n + 1
  return (t, n)

/-! ## UnicodeData.txt -/

/-- UnicodeData.txt per code point: general category, combining class, canonical mapping. -/
structure UnicodeData where
  category : Array GeneralCategory
  combining : Array Nat
  mapping : Array (Option (List Nat))

def readUnicodeData (text : String) : Except String UnicodeData := do
  let mut cat := Array.replicate (lastCode + 1) GeneralCategory.cn
  let mut ccc := Array.replicate (lastCode + 1) 0
  let mut map : Array (Option (List Nat)) := Array.replicate (lastCode + 1) none
  let mut first : Option Nat := none
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let f := (line.splitOn ";").toArray
    unless f.size == 15 do throw s!"not 15 fields: {line}"
    let some n := hexValue? f[0]! | throw s!"a code point that does not read: {line}"
    let some g := GeneralCategory.ofCode? f[2]! | throw s!"a category that does not read: {line}"
    let some k := f[3]!.toNat? | throw s!"a class that does not read: {line}"
    if f[1]!.endsWith ", First>" then
      first := some n
      continue
    let lo := if f[1]!.endsWith ", Last>" then first.getD n else n
    for i in [lo:n + 1] do
      cat := cat.set! i g
      ccc := ccc.set! i k
    let d := f[5]!
    unless d.isEmpty || d.startsWith "<" do
      let some ds := (d.splitOn " ").mapM hexValue? | throw s!"a mapping that does not read: {line}"
      map := map.set! n (some ds)
  return { category := cat, combining := ccc, mapping := map }

/-- A full canonical decomposition from the file's mappings; `none` past a depth no mapping
of Unicode's reaches. -/
def fullDecomposition (map : Array (Option (List Nat))) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, n =>
    match map[n]? with
    | some (some ds) => (ds.mapM (fullDecomposition map fuel)).map List.flatten
    | _ => some [n]

def runUnicodeData (u : UnicodeData) : Tally × Nat × Nat := Id.run do
  let mut t : Tally := {}
  let mut scalars := 0
  let mut mapped := 0
  for i in [0:lastCode + 1] do
    let g := generalCategoryOf i
    t := t.check (g == u.category[i]!) fun _ =>
      s!"general category of {showCode i}: {g.code}, UnicodeData.txt {u.category[i]!.code}"
    if scalar i then
      scalars := scalars + 1
      let c := Char.ofNat i
      let k := combiningClass c
      t := t.check (k == u.combining[i]!) fun _ =>
        s!"combining class of {showCode i}: {k}, UnicodeData.txt {u.combining[i]!}"
      unless syllable i do
        let want := fullDecomposition u.mapping 8 i
        if u.mapping[i]!.isSome then mapped := mapped + 1
        let got := (decompose c).map Char.toNat
        t := t.check (want == some got) fun _ =>
          s!"decomposition of {showCode i}: {showChars (decompose c)}"
  return (t, scalars, mapped)

/-! ## The tables -/

/-- Ranges that increase without overlap. -/
def increasing (rs : List (Nat × Nat)) : Bool :=
  rs.all (fun r => r.1 ≤ r.2) && (rs.zip rs.tail).all fun (a, b) => a.2 < b.1

def runTables : Tally := Id.run do
  let mut t : Tally := {}
  t := t.check (unicodeVersion == "15.1.0") fun _ => s!"the tables' version is {unicodeVersion}"
  t := t.check (sources.map (·.1) == ["UnicodeData.txt", "CompositionExclusions.txt",
    "NormalizationTest.txt"]) fun _ => "the tables' sources"
  t := t.check (combiningRuns.size == combiningClassCount) fun _ =>
    s!"combining classes: {combiningRuns.size} items read of {combiningClassCount}"
  t := t.check (categoryRuns.size == generalCategoryCount) fun _ =>
    s!"general categories: {categoryRuns.size} items read of {generalCategoryCount}"
  t := t.check (decompositions.size == decompositionCount) fun _ =>
    s!"decompositions: {decompositions.size} items read of {decompositionCount}"
  t := t.check (compositions.size == compositionCount) fun _ =>
    s!"compositions: {compositions.size} items read of {compositionCount}"
  t := t.check (increasing (combiningRuns.toList.map fun (a, b, _) => (a, b))) fun _ =>
    "combining-class runs do not increase"
  t := t.check (increasing (categoryRuns.toList.map fun (a, b, _) => (a, b))) fun _ =>
    "general-category runs do not increase"
  t := t.check (increasing (decompositions.toList.map fun (a, _) => (a, a))) fun _ =>
    "decompositions do not increase"
  t := t.check (increasing (compositions.toList.map fun (a, _) => (a, a))) fun _ =>
    "compositions do not increase"
  t := t.check (combiningRuns.toList.all (·.2.2 != 0)) fun _ => "a combining-class run of class 0"
  t := t.check ((combiningRuns[0]?.map (·.1)) == some combiningFloor) fun _ =>
    "the combining floor is not the first run's start"
  t := t.check ((decompositions[0]?.map (·.1)) == some decompositionFloor) fun _ =>
    "the decomposition floor is not the first decomposition"
  let seconds := compositions.toList.map (·.1 % 0x110000)
  t := t.check (seconds.all (compositionSecondFloor ≤ ·) && seconds.contains compositionSecondFloor)
    fun _ => "the composition floor is not the least second"
  t := t.check (decompositionFloor ≤ sBase && compositionSecondFloor ≤ vBase &&
    compositionSecondFloor ≤ tBase + 1) fun _ => "a floor above Hangul's"
  return t

/-! ## The run -/

def run : IO (Nat × Nat) := do
  let start ← IO.monoMsNow
  let test ← IO.FS.readFile "vectors/unicode/NormalizationTest.txt"
  let data ← IO.FS.readFile "vectors/unicode/UnicodeData.txt"
  let tables := runTables
  let read ← IO.monoMsNow
  let norm ← IO.ofExcept (runNormalizationTest test |>.mapError IO.userError)
  let (others, otherCount) := runOthers norm.partOne
  let normDone ← IO.monoMsNow
  let u ← IO.ofExcept (readUnicodeData data |>.mapError IO.userError)
  let (ud, scalars, mapped) := runUnicodeData u
  let stop ← IO.monoMsNow
  let header := norm.header == "# NormalizationTest-15.1.0.txt"
  let parts := [("tables", tables), ("NormalizationTest.txt", norm.tally),
    ("code points outside its Part 1", others), ("UnicodeData.txt", ud)]
  for (name, t) in parts do
    for s in t.shown do IO.eprintln s!"FAIL unicode {name}: {s}"
    if t.fail > t.shown.size then IO.eprintln s!"FAIL unicode {name}: {t.fail - t.shown.size} more"
  unless header do IO.eprintln s!"FAIL unicode: NormalizationTest.txt is {norm.header}"
  IO.println s!"unicode: Unicode {unicodeVersion}; NormalizationTest.txt: {norm.lines} lines, {norm.tally.pass} of {norm.tally.pass + norm.tally.fail} NFC and NFD checks pass (5 of each per line); {otherCount} scalar values outside its Part 1: {others.pass} of {others.pass + others.fail} are their own NFC and NFD; UnicodeData.txt: the general category of {lastCode + 1} code points, the combining class of {scalars} scalar values and their decompositions ({mapped} mapped, Hangul syllables aside): {ud.pass} of {ud.pass + ud.fail} agree; tables: {tables.pass} of {tables.pass + tables.fail} checks; {normDone - read} ms for NormalizationTest.txt, {stop - normDone} ms for UnicodeData.txt, {stop - start} ms in all"
  let pass := parts.foldl (· + ·.2.pass) 0 + (if header then 1 else 0)
  let fail := parts.foldl (· + ·.2.fail) 0 + (if header then 0 else 1)
  return (pass, fail)

end Tests.Unicode
