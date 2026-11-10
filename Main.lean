import Principia

/-- All of stdin, but no more than one byte past the reader's bound, so that a text
over the bound is refused without being held whole. -/
def readStdin (limit : Nat) : IO ByteArray := do
  let stdin ← IO.getStdin
  let mut acc := ByteArray.empty
  repeat
    if limit < acc.size then break
    let chunk ← stdin.read 65536
    if chunk.isEmpty then break
    acc := acc ++ chunk
  return acc

/-- Write a line on stdout as its UTF-8 bytes. -/
def writeOut (text : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write text.toUTF8
  stdout.flush

/-- `pcalc`: the Calculator's command line (`Principia.Calculator`).
`pcalc <family> <function>` reads one JSON value on stdin and writes its answer's
canonical JSON and a line feed on stdout, or a refusal and a nonzero exit code;
`pcalc version` writes the version. Deterministic; no network, no file. The arms stay in
the order matching needs; a new family is one line in `Principia.Calculator.families`, not
an arm. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] =>
    IO.println Principia.version
    return 0
  | "permits" :: words =>
    match Principia.Permissions.Request.parse? words with
    | some r =>
      IO.println r.answer
      return 0
    | none =>
      IO.eprintln "usage: pcalc permits <asker> <page class> <operation> [<context word>...]"
      return 2
  | [family, function] =>
    let input ← readStdin Principia.Canonical.maxTextBytes
    let (text, code) := Principia.Calculator.answer family function input
    writeOut text
    return code
  | _ =>
    let (text, code) := Principia.Calculator.usage
    writeOut text
    return code
