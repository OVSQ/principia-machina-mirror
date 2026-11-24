import Lean
/-!
The axiom audit: every constant of a module in scope (`Principia`,
`Principia.*`, `Main`, `Tests.*`) may depend only on Lean's three standard
axioms. `sorryAx` (an unfinished proof, `sorryAx _ false` included, which no
text scan for the word `sorry` finds), any `_native` axiom (from
`native_decide`), `Lean.ofReduceBool` where a toolchain has it, and any
project-declared axiom fail the audit. The roots are chosen by module, never
by name (`AxiomAudit.rootsByModule`): a private constant, an auxiliary one or
one outside the `Principia` namespace is a root as any other. A constant the
walk reaches and the environment does not hold fails the audit (it cannot be
cleared): `AXIOM AUDIT FAIL: <root> reaches <constant>, a constant not in the
environment`. The self-test (`AxiomAudit.selfTest`) runs first: the walk on
constants made in the script, and three probe modules compiled in a
temporary directory (a private theorem, one outside the namespace and a
`native_decide`, each to be found; a clean module; and one out of scope).
Run with `lake env lean scripts/axiom_audit.lean` from the repository's root,
after `lake build`; the proof gate runs `scripts/lake_files_check.py` before
that build.

No code of the library runs in this process. The script imports only `Lean`
in its header (a header's imports run their modules' initializers, so an
initializer of the library would act before the audit read anything); the
library's modules are imported while it runs, with `importModules` and its
extensions not loaded, which runs no initializer. The axioms are collected
from the constants' bodies themselves (`AxiomAudit.findings`: every constant
the library's declarations reach, walked as `collectAxioms` walks them, and
the declarations reaching an axiom off the list), never from data the
modules recorded.

The initializer audit, run by the same command first: no initializer in a
module `Principia`, `Principia.*`, `Main` or `Tests.*`. Lean runs the
initializers of every module it imports (`initialize`, `builtin_initialize`,
`@[init]`, `@[builtin_init]`) in `lake build` of any importer and in a
header's `import`: an initializer could rewrite its own source before the
Float audit's frontend pass read it, or end the process with exit 0. The
audit reads the compiled modules, not their source: every constant of a
module in scope recorded by the `init` or `builtin_init` attribute (in the
module's `.olean` or its `.ir`) fails:
`INIT AUDIT FAIL <module>: <constant>`. On any such failure the `Tests`
modules are not built and the frontend pass does not run (both would run
the initializer). The self-test compiles two probe modules in a temporary
directory, one with an initializer of each kind and one with none, and
must find exactly the first one's. The last line of the command's output
is the initializer audit's (`init audit: <n> modules checked, <k> self-test
cases, 0 failures` on a pass); the proof gate requires it, the axiom
audit's line and the Float audit's line, each with 0 failures, as well as
exit 0.

The Float audit, run by the same command: no `Float` (the Lean rules), over
every `.lean` file under `Principia/` and `Tests/`, and `Main.lean` and
`Principia.lean`. A missing `Principia/`, `Tests/` or `Main.lean` fails.
It judges what Lean elaborated, never what the source text spells.
- The frontend pass: each such file is run through Lean's frontend (its
  header's imports, then command by command) with info trees on, in a child
  process of this script (`lean scripts/axiom_audit.lean` with
  `PMA_FLOAT_FRONT` naming the file), one file a process, since a process
  cannot free the imports of the file before. The child enables the imports'
  initializers first (`enableInitializersExecution`, the call Lean's own
  frontend makes at startup), so each file elaborates with exactly its own
  imports, their extensions loaded, as `lake build` elaborates it.
  - Command kinds, by the syntax node the parser produced, never by
    spelling: only `def`, `theorem`, `abbrev`, `structure`, `inductive`,
    `instance`, `example`, `namespace`, `section`, `end`, `open`,
    `variable`, `set_option` (for an option of `admittedOptions` alone,
    below), `universe`, a module docstring and
    `attribute [...]` are admitted (`admittedCommands`, `admittedDecls`);
    `mutual` and `in` are structural, judged by their children: each member
    of a `mutual` block and both sides of `in` face the same rules.
    Any other kind is refused and not elaborated:
    `FLOAT AUDIT FAIL: <file>:<line>: command kind <kind> not admitted`.
    This refuses `#eval`, `macro`, `macro_rules`, `syntax`, `notation`,
    `infix`, `elab`, `run_cmd`, `initialize` and every other command that
    defines or runs meta code.
  - Attributes, in `@[...]` and `attribute [...]`: only the names of
    `admittedAttrs`; any other (`macro`, `term_elab`, `command_elab`,
    `tactic`, `implemented_by`, ...) is refused:
    `... attribute <name> not admitted`.
  - Inside an admitted command, the syntax kinds that run code written in
    the file while it is elaborated are refused (`refusedInner`: `run_tac`,
    `by_elab`, the term `unsafe`, through which a configuration term
    could reach unsafe code, `native_decide`, which compiles and runs the
    file's `Decidable` instance, and `include_str`, which compiles and runs
    its path term and leaves no axiom the walk would find; `bv_decide`,
    `bv_decide?`, `bv_check` and grind's forms of the three, which evaluate
    the toolchain's checker natively, refused here before the walk meets the
    `_native` axiom they leave): `... syntax kind <kind> not admitted`.
    A `set_option` (the command, its `... in` form, and the term, tactic and
    grind forms inside an admitted command) whose option is off
    `admittedOptions` (the exact names `maxHeartbeats`, `maxRecDepth`,
    `synthInstance.maxHeartbeats`, `autoImplicit`, `relaxedAutoImplicit`, and
    the prefixes `pp.`, `linter.`, `trace.`, save `trace.profiler.serve`,
    which makes Lean's frontend serve the profile over HTTP, start a browser
    and block, and `trace.profiler.output`, which makes it write a file, each
    with the names below it; the same names, prefixes and refused prefixes
    as `admittedOptions` in `scripts/init_scan.lean`, the two changing
    together; the init scan has no `selfTestOptions`) is refused, placed at
    the option's identifier: `... set_option <name> not admitted` (so
    `debug.skipKernelTC`, which adds a definition Lean's checker never checked
    and leaves no axiom, every `debug.*`, `compiler.*` and `Elab.*`); an
    option name the parser's tree does not give is `... set_option <unread>
    not admitted` (fail closed). On the pinned toolchain the option's value
    is the node's fourth argument in all four forms, and the lexer reads a
    dotted name as one identifier, so the optional `.<ident>` part of each of
    the four forms is met only in a tree a parse error left, its identifier
    missing (`optionNameTest` builds each branch by hand).
    The self-test's own sources may also set `Elab.async` (`selfTestOptions`,
    admitted only in a child the self-test starts, `PMA_FLOAT_SELFTEST` set by
    the parent and unset for every scope file's child), to exercise the
    asynchronous proofs below. The pass over the scope carries a canary in
    its own call (`scopeCanary`, a file outside the scope setting
    `Elab.async`): that call started with self-test children admits it, and
    the audit fails `... the scope pass's canary ...`.
    A tactic `decide` whose configuration may turn `native` on (`+native`,
    `(native := ...)`, `(config := ...)`, which may name a structure setting
    it) is refused: `... tactic decide +native not admitted`. Each is placed at
    its syntax, before the axiom walk would meet the axiom it leaves.
  - Every term in the info trees (macro expansions included; a term's
    metavariables instantiated, each outermost tactic block's goal
    instantiated with its final assignment, and each hole an asynchronous
    proof leaves, `set_option Elab.async true in`, filled with that proof's
    tree once its task ends) and its expected type are walked; a constant whose name contains `Float`, or a default instance
    of `OfScientific` (`instOfScientificFloat`), fails:
    `... <constant> elaborated (Float)`.
  - An elaboration error fails, an asynchronous proof's included (read from
    the snapshot tasks the command left): `... elaboration error: <message>`. A child
    that does not end with its done line, or exits non-zero, fails.
- The constant check: the audit builds the module of every such file
  (`lake build +<module> ...`; the `Tests` library is not a default target;
  the `Tests` modules after the others' initializer audit is clean)
  and imports them; a constant defined in a module `Principia`,
  `Principia.*`, `Main` or `Tests.*`, whatever its name, whose type or value
  names a constant whose name contains `Float` (`Float`, `Float32`,
  `Nat.toFloat`, `instOfScientificFloat`, ...) fails:
  `FLOAT AUDIT FAIL: <name> uses <constant> (module <module>)`.
- The self-test runs first: the constant check's cases (`scopeTest`,
  `usesTest`), the file walk (`walkTest`, in a temporary directory), and the
  frontend pass's cases (`frontTest`, each a file in a temporary directory
  run through the same child, giving the failure lines it names and, but for
  lines of a constant with `Float` met, no other), and
  `decideNative` on configurations built by hand (`decideTest`), and the
  rule naming a case's failure lines on lines written by hand
  (`wantNamesTest`); a case that answers wrong fails the audit. The count of
  self-test cases takes in the scope pass's canary only once it has run.
-/

open Lean

namespace FloatAudit

def hasFloat (s : String) : Bool := (s.splitOn "Float").length > 1

/-- The module scopes of the constant check. -/
def inScope (m : Name) : Bool :=
  (`Principia).isPrefixOf m || m == `Main || (`Tests).isPrefixOf m

/-- The constants named in a constant's type or value whose names contain `Float`. -/
def floatUses (ci : ConstantInfo) : Array Name :=
  let used := ci.type.getUsedConstants ++ ((ci.value? true).map (·.getUsedConstants)).getD #[]
  used.foldl (fun acc c => if hasFloat c.toString && !acc.contains c then acc.push c else acc) #[]

def scopeTest : List (Name × Bool) := [
  (`Principia, true), (`Principia.Calculator.Core, true), (`Main, true), (`Tests.Beta, true),
  (`PrincipiaTests, false), (`MainX, false), (`Init.Data.Float, false), (`Lean.Json, false)]

def sciApp (ty inst : Name) : Expr :=
  mkAppN (mkConst ``OfScientific.ofScientific [Level.zero])
    #[mkConst ty, mkConst inst, mkRawNatLit 25, mkConst ``Bool.true, mkRawNatLit 1]

def defn (n : Name) (ty val : Expr) : ConstantInfo :=
  .defnInfo { name := n, levelParams := [], type := ty, value := val,
              hints := .opaque, safety := .safe }

def thm (n : Name) (ty val : Expr) : ConstantInfo :=
  .thmInfo { name := n, levelParams := [], type := ty, value := val }

/-- The constant check's self-test: each constant and the names it must report. -/
def usesTest : List (ConstantInfo × List Name) := [
  (defn `x (mkConst ``Float) (sciApp ``Float ``instOfScientificFloat),
    [``Float, ``instOfScientificFloat]),
  (defn (.str (.num `_private.Tests.Beta 0) "x") (mkConst ``Nat)
    (mkApp (mkConst ``id [Level.one]) (mkApp (mkConst ``Nat.toFloat) (mkRawNatLit 2))),
    [``Nat.toFloat]),
  (defn `r (mkConst ``Rat) (sciApp ``Rat ``Rat.instOfScientific), []),
  (thm `t (mkApp (mkConst ``Nonempty [Level.one]) (mkConst ``Float)) (mkConst ``True.intro),
    [``Float])]

end FloatAudit

namespace AxiomAudit

/-- The axioms a declaration may depend on. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The constants a constant leads to, as `collectAxioms` walks them: its type, its value
(a definition, a theorem, an opaque constant), and an inductive type's constructors. -/
def deps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- Each `(root, constant, known)` where `root` reaches an axiom off `allowed`
(`known` true) or a constant `find` does not have (`known` false: the walk fails closed,
since what it cannot read it cannot clear), in order of the roots: every constant the roots
reach is walked once, from the constants' own bodies; then, from each such constant, the
walk's edges are followed back to the roots. -/
def findings (find : Name → Option ConstantInfo) (roots : Array Name) :
    Array (Name × Name × Bool) := Id.run do
  let mut ids : Std.HashMap Name Nat := {}
  let mut names : Array Name := #[]
  let mut back : Array (Array Nat) := #[]
  for r in roots do
    unless ids.contains r do
      ids := ids.insert r names.size
      names := names.push r
      back := back.push #[]
  let mut stack : Array Nat := (List.range names.size).toArray
  let mut bad : Array (Nat × Bool) := #[]
  repeat
    match stack.back? with
    | none => break
    | some i =>
      stack := stack.pop
      let some ci := find names[i]! | do bad := bad.push (i, false); continue
      if ci matches .axiomInfo _ then
        unless allowed.contains names[i]! do bad := bad.push (i, true)
      for d in deps ci do
        let j := (ids.get? d).getD names.size
        if j == names.size then
          ids := ids.insert d j
          names := names.push d
          back := back.push #[]
          stack := stack.push j
        back := back.modify j (·.push i)
  let mut out : Array (Name × Name × Bool) := #[]
  let mut perRoot : Array (Array (Name × Bool)) := roots.map (fun _ => #[])
  for (ax, known) in bad do
    let mut reach : Array Bool := names.map (fun _ => false)
    reach := reach.set! ax true
    let mut st : Array Nat := #[ax]
    repeat
      match st.back? with
      | none => break
      | some i =>
        st := st.pop
        for p in back[i]! do
          unless reach[p]! do
            reach := reach.set! p true
            st := st.push p
    for k in [0:roots.size] do
      if reach[ids.getD roots[k]! 0]! then perRoot := perRoot.modify k (·.push (names[ax]!, known))
  for k in [0:roots.size] do
    for (ax, known) in perRoot[k]! do out := out.push (roots[k]!, ax, known)
  return out

/-- A failure line of the axiom audit. -/
def failLine (root c : Name) (known : Bool) : String :=
  if known then s!"AXIOM AUDIT FAIL: {root} uses {c}"
  else s!"AXIOM AUDIT FAIL: {root} reaches {c}, a constant not in the environment"

/-- The roots of the audit in `env`: every constant whose module is in scope
(`FloatAudit.inScope`: `Principia`, `Principia.*`, `Main`, `Tests.*`), whatever its name
(a private name, an auxiliary one, one outside the `Principia` namespace), and whose module
`skip` does not name; with those modules (each module of `env` in scope and not skipped,
whether or not it defines a constant). -/
def rootsByModule (env : Environment) (skip : Name → Bool) : Array Name × Array Name := Id.run do
  let names := env.header.moduleNames
  let mods := names.filter (fun m => FloatAudit.inScope m && !skip m)
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if mods.contains names[idx.toNat]! then roots := roots.push n
  return (roots.qsort Name.lt, mods)

/-- The walk's self-test, on constants made here: each root and the `(constant, known)`
pairs it must give. -/
def walkTest : List (Name × List (Name × Bool)) :=
  [(`pa, [(`pnope, false)]), (`pb, [(``sorryAx, true)]), (`pc, []), (`pd, [(`pd, false)]),
   (`pe, [(``sorryAx, true), (`pnope, false)])]

/-- The constants of `walkTest`: `pa` names a constant there is none of, `pb` reaches
`sorryAx` through `pi`, `pc` uses only `propext`, `pd` is not there, `pe` reaches both. -/
def walkEnv : List ConstantInfo :=
  let prop := mkSort Level.zero
  let ax (n : Name) : ConstantInfo :=
    .axiomInfo { name := n, levelParams := [], type := prop, isUnsafe := false }
  [ax ``sorryAx, ax ``propext,
   FloatAudit.thm `pa prop (mkConst `pnope), FloatAudit.defn `pi prop (mkConst ``sorryAx),
   FloatAudit.thm `pb prop (mkConst `pi), FloatAudit.thm `pc prop (mkConst ``propext),
   FloatAudit.thm `pe prop (mkApp (mkConst `pa) (mkConst `pb))]

/-- The probe modules of the rooting self-test: each module's source, and the roots and
the constants the audit must report for it, each by the last component of its name. In
scope by their names, except `PmaAxiomOut`, whose `sorryAx` is outside the audit's scope.
`native_decide` declares an axiom of its own in the module (`w._native.native_decide.ax_1_1`
in Lean 4.35, where `Lean.ofReduceBool` is no more), itself a root. -/
def probes : List (String × String × List (String × String)) := [
  ("Principia.PmaAxiomProbe",
    "namespace Principia\nprivate theorem t : False := sorryAx _ false\nend Principia\n" ++
    "namespace Other\ntheorem u : False := sorryAx _ false\nend Other\n" ++
    "theorem w : 2 + 2 = 4 := by native_decide\n" ++
    "theorem Principia.ok : True := trivial\n",
    [("t", "sorryAx"), ("u", "sorryAx"), ("w", "ax_1_1"), ("ax_1_1", "ax_1_1")]),
  ("Principia.PmaAxiomClean",
    "theorem Principia.cl (p : Prop) (h : p = True) : p := h ▸ trivial\n" ++
    "private def k : Nat := 1\n", []),
  ("PmaAxiomOut", "theorem o : False := sorryAx _ false\n", [])]

/-- The self-test: the walk's cases, then the probe modules compiled in a temporary
directory, imported (no initializer runs) and audited from their roots by module.
Returns the wrong answers. -/
def selfTest : IO (Array String) := do
  let mut wrong := #[]
  let m : Std.HashMap Name ConstantInfo := walkEnv.foldl (fun m ci => m.insert ci.name ci) {}
  let got := findings m.get? (walkTest.map (·.1)).toArray
  for (r, want) in walkTest do
    let mine := (got.filter (·.1 == r)).map (·.2)
    unless mine.size == want.length && want.all mine.contains do
      wrong := wrong.push s!"walk case {r} gave {mine}, wants {want}"
  let t ← IO.FS.createTempDir
  let lean := (← IO.appPath).toString
  let sp ← searchPathRef.get
  try
    IO.FS.createDirAll (t / "Principia")
    let mut compiled := true
    for (mod, src, _) in probes do
      let rel : System.FilePath := mod.replace "." "/"
      IO.FS.writeFile (t / rel.withExtension "lean") src
      let r ← IO.Process.output
        { cmd := lean, args := #[(rel.withExtension "lean").toString, "-o",
            (rel.withExtension "olean").toString], cwd := t }
      if r.exitCode != 0 then
        compiled := false
        wrong := wrong.push s!"probe {mod} did not compile (exit {r.exitCode}): {r.stdout}{r.stderr}"
    if compiled then
      searchPathRef.set (t :: sp)
      let env ← importModules (probes.map (fun (mod, _) => ({ module := mod.toName } : Import))).toArray {}
      let (roots, mods) := rootsByModule env (fun _ => false)
      let found := findings env.find? roots
      for (mod, _, want) in probes do
        let inMod (n : Name) : Bool := match env.getModuleIdxFor? n with
          | some i => env.header.moduleNames[i.toNat]! == mod.toName
          | none => false
        let last (n : Name) : String := (privateToUserName n.eraseMacroScopes).getString!
        let mine := (found.filter (inMod ·.1)).map fun (r, c, _) => (last r, last c)
        let inScope := FloatAudit.inScope mod.toName
        let ok := mods.contains mod.toName == inScope && mine.size == want.length &&
          want.all mine.contains
        unless ok do wrong := wrong.push s!"probe {mod} gave {mine}, wants {want}"
  finally
    searchPathRef.set sp
    IO.FS.removeDirAll t
  return wrong

end AxiomAudit

namespace InitAudit

/-- The constants module `i` of `env` registers as initializers, with the `init` or the
`builtin_init` attribute (`initialize`, `builtin_initialize`, `@[init]`,
`@[builtin_init]`), as its `.olean` and its `.ir` record them. -/
def initializers (env : Environment) (i : Nat) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for attr in [regularInitAttr, builtinInitAttr] do
    for (decl, _) in attr.ext.getModuleEntries env i ++ attr.ext.getModuleIREntries env i do
      unless out.contains decl do out := out.push decl
  return out

/-- The initializer audit of `env`: each `(module, constant)` it fails, and the modules in
scope it read. -/
def findings (env : Environment) : Array (Name × Name) × Array Name := Id.run do
  let mut found : Array (Name × Name) := #[]
  let mut mods : Array Name := #[]
  for m in env.header.moduleNames, i in 0...* do
    if FloatAudit.inScope m then
      mods := mods.push m
      for d in initializers env i do
        found := found.push (m, d)
  return (found, mods)

/-- A failure line of the initializer audit. -/
def failLine (m d : Name) : String := s!"INIT AUDIT FAIL {m}: {d}"

/-- The probe modules of the self-test, in scope by their names: the source of each, and the
constants (by the last component of their names) the audit must report for it. -/
def probes : List (String × String × List String) := [
  ("Tests.PmaInitProbe",
    "initialize pure ()\ninitialize probeRef : IO.Ref Nat ← IO.mkRef 0\n" ++
    "def probeAct : IO Unit := pure ()\n@[init probeAct] opaque probeU : Unit\n" ++
    "builtin_initialize pure ()\n",
    ["initFn", "probeRef", "probeU", "initFn"]),
  ("Tests.PmaInitClean", "def probeClean : Nat := 1\n", [])]

/-- The self-test: compile each probe in a temporary directory, import them (no initializer
runs), and compare the audit's findings. Returns the wrong answers. -/
def selfTest : IO (Array String) := do
  let t ← IO.FS.createTempDir
  let lean := (← IO.appPath).toString
  let mut wrong := #[]
  let sp ← searchPathRef.get
  try
    IO.FS.createDirAll (t / "Tests")
    for (m, src, _) in probes do
      let rel : System.FilePath := m.replace "." "/"
      IO.FS.writeFile (t / rel.withExtension "lean") src
      let r ← IO.Process.output
        { cmd := lean, args := #[(rel.withExtension "lean").toString, "-o",
            (rel.withExtension "olean").toString], cwd := t }
      if r.exitCode != 0 then
        wrong := wrong.push s!"probe {m} did not compile (exit {r.exitCode}): {r.stdout}{r.stderr}"
    if wrong.isEmpty then
      searchPathRef.set (t :: sp)
      let env ← importModules (probes.map (fun (m, _) => ({ module := m.toName } : Import))).toArray {}
      let (found, mods) := findings env
      for (m, _, want) in probes do
        let mine := (found.filter (·.1 == m.toName)).map (·.2)
        let lasts := mine.map (fun d => (privateToUserName d.eraseMacroScopes).getString!)
        let ok := mods.contains m.toName && lasts.size == want.length &&
          want.all (fun w => lasts.contains w)
        unless ok do wrong := wrong.push s!"probe {m} gave {lasts}, wants {want}"
  finally
    searchPathRef.set sp
    IO.FS.removeDirAll t
  return wrong

end InitAudit

namespace FloatFront

open Elab

/-- The command kinds admitted in scope; a `declaration` is admitted by its inner kind. -/
def admittedCommands : List SyntaxNodeKind := [
  ``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
  ``Parser.Command.end, ``Parser.Command.open, ``Parser.Command.variable,
  ``Parser.Command.set_option, ``Parser.Command.universe, ``Parser.Command.moduleDoc,
  ``Parser.Command.attribute, ``Parser.Command.eoi]

/-- The inner kinds of an admitted `declaration` (`class` is a `structure` to the parser). -/
def admittedDecls : List SyntaxNodeKind := [
  ``Parser.Command.definition, ``Parser.Command.theorem, ``Parser.Command.abbrev,
  ``Parser.Command.structure, ``Parser.Command.inductive, ``Parser.Command.instance,
  ``Parser.Command.example]

/-- The attribute names admitted in `@[...]` and `attribute [...]`. -/
def admittedAttrs : List Name := [`simp, `inline, `reducible, `instance, `ext]

/-- Syntax kinds that run code written in the file while it is elaborated
(`native_decide` compiles and runs the file's `Decidable` instance; `include_str` compiles
and runs its path term, and leaves no axiom). -/
def refusedInner : List SyntaxNodeKind := [
  ``Parser.Tactic.runTac, ``Lean.byElab, ``Parser.Term.unsafe, ``Parser.Tactic.nativeDecide,
  ``Lean.includeStr, ``Parser.Tactic.bvDecide, ``Parser.Tactic.bvTrace,
  ``Parser.Tactic.bvCheck, ``Parser.Tactic.Grind.bvDecide, ``Parser.Tactic.Grind.bvTrace,
  ``Parser.Tactic.Grind.bvCheck]

/-- The `set_option` kinds: the command (its `... in` form is `Parser.Command.in` with
the command on its left), the term, the tactic and grind's. -/
def setOptionKinds : List SyntaxNodeKind := [
  ``Parser.Command.set_option, ``Parser.Term.set_option, ``Parser.Tactic.set_option,
  ``Parser.Tactic.Grind.setOption]

/-- The options a `set_option` may set by exact name (the init scan's list). -/
def admittedOptionNames : List Name := [
  `maxHeartbeats, `maxRecDepth, `synthInstance.maxHeartbeats, `autoImplicit,
  `relaxedAutoImplicit]

/-- The first components (`pp.`, `linter.`, `trace.`) of the options a `set_option` may
set by prefix (the init scan's list). -/
def admittedOptionRoots : List Name := [`pp, `linter, `trace]

/-- The options the self-test's own sources may also set, in a child the self-test
starts and in no other: `Elab.async`, for its asynchronous-proof cases. -/
def selfTestOptions : List Name := [`Elab.async]

/-- The options refused under an admitted prefix, each with every name below it (the init
scan's list): the frontend reads `trace.profiler.serve` from a file's final options and then
opens an HTTP server, starts a browser and blocks until interrupted, and
`trace.profiler.output` names a file the profile is written to (`Lean.Elab.runFrontend`;
`trace.profiler.output.pp` is below it). -/
def refusedOptionRoots : List Name := [`trace.profiler.serve, `trace.profiler.output]

/-- Whether an option is admitted: an exact name of `admittedOptionNames` or of `extra`, or
a name of two or more components whose first is in `admittedOptionRoots`; never one equal
to or below a name of `refusedOptionRoots`, whatever `extra` holds. -/
def admittedOptions (extra : List Name) (n : Name) : Bool :=
  !refusedOptionRoots.any (·.isPrefixOf n) &&
    (admittedOptionNames.contains n || extra.contains n ||
      (admittedOptionRoots.contains n.getRoot && n != n.getRoot))

/-- The option a `set_option` node names, with the identifier holding it: its second
argument, an identifier, read whole when the third (the optional `.<ident>` each of the four
forms carries) is empty, and with grind's `.<ident>` appended when that is present; none for
any other shape, the command, term and tactic forms with a `.<ident>` among them (fail
closed). -/
def optionName (stx : Syntax) : Option (Syntax × Name) :=
  let o := stx[1]
  let rest := stx[2]
  if !o.isIdent then none
  else if rest.getNumArgs == 0 then some (o, o.getId.eraseMacroScopes)
  else if stx.getKind == ``Parser.Tactic.Grind.setOption && rest.getNumArgs == 2 &&
      rest[1].isIdent then
    some (o, o.getId.eraseMacroScopes ++ rest[1].getId.eraseMacroScopes)
  else none

/-- An attribute's name as Lean's elaborator reads it: the identifier of a simple
attribute, else the last component of its syntax kind. -/
def attrName (attr : Syntax) : Name :=
  if attr.getKind == ``Parser.Attr.simple then attr[0].getId.eraseMacroScopes
  else match attr.getKind with
    | .str _ s => .mkSimple s
    | k => k

/-- Whether a tactic `decide`'s configuration may turn `native` on: any item but `+<name>`,
`-<name>` and `(<name> := ...)`, `<name>` neither `native` nor `config`, may. A
configuration of a shape not read here may too (fail closed): `(native := false)` and any
`(config := ...)` are refused, since their values are terms not read before elaboration. The
init scan is to refuse by the same rule; the two change together. -/
def decideNative (stx : Syntax) : Bool :=
  let cfg := stx[1]
  if cfg.getKind != ``Parser.Tactic.optConfig then true
  else cfg[0].getArgs.any fun item =>
    let it := item[0]
    let k := it.getKind
    if item.getKind != ``Parser.Tactic.configItem then true
    else if k == ``Parser.Tactic.negConfigItem then false
    else if k == ``Parser.Tactic.posConfigItem then it[1].getId == `native
    else if k == ``Parser.Tactic.valConfigItem then
      it[1].getId == `native || it[1].getId == `config
    else true

/-- The refusals inside a command: attributes off the list, refused inner kinds, a
`set_option` off `admittedOptions` (with `extra`) and a native `decide`, each with the
syntax it was found at. -/
partial def innerRefusals (extra : List Name) (stx : Syntax) (acc : Array (Syntax × String)) :
    Array (Syntax × String) :=
  let k := stx.getKind
  let acc :=
    if k == ``Parser.Term.attrInstance then
      let n := attrName stx[1]
      if admittedAttrs.contains n then acc else acc.push (stx, s!"attribute {n} not admitted")
    else if refusedInner.contains k then acc.push (stx, s!"syntax kind {k} not admitted")
    else if setOptionKinds.contains k then
      match optionName stx with
      | some (o, n) =>
        if admittedOptions extra n then acc else acc.push (o, s!"set_option {n} not admitted")
      | none => acc.push (stx, "set_option <unread> not admitted")
    else if k == ``Parser.Tactic.decide && decideNative stx then
      acc.push (stx, "tactic decide +native not admitted")
    else acc
  stx.getArgs.foldl (fun acc s => innerRefusals extra s acc) acc

/-- Why a command is refused, with the syntax to place it; none when it is admitted.
`mutual` and `in` are structural, judged by their children: each member of a `mutual` block,
and both sides of `in`, face the same rules. `extra`: the options admitted beside
`admittedOptions`'s (`selfTestOptions` in a self-test child, else none). -/
partial def refusals (extra : List Name) (cmd : Syntax) : Array (Syntax × String) :=
  let k := cmd.getKind
  if k == ``Parser.Command.mutual then
    cmd[1].getArgs.foldl (fun acc c => acc ++ refusals extra c) #[]
  else if k == ``Parser.Command.in then refusals extra cmd[0] ++ refusals extra cmd[2]
  else if !admittedCommands.contains k then #[(cmd, s!"command kind {k} not admitted")]
  else if k == ``Parser.Command.declaration && !admittedDecls.contains cmd[1].getKind then
    #[(cmd, s!"command kind {cmd[1].getKind} not admitted")]
  else innerRefusals extra cmd #[]

/-- The constants of `e` that fail: a name containing `Float`, or one of `bad`. -/
def floatConsts (bad : List Name) (e : Expr) : Array Name :=
  e.getUsedConstants.filter (fun c => FloatAudit.hasFloat c.toString || bad.contains c)

/-- Walk an info tree: every term (and its expected type) with its metavariables
instantiated, every field value, and each outermost tactic block's goals instantiated
with the block's final assignment. Returns `(syntax, constant)` pairs. -/
partial def walk (bad : List Name) (ctx? : Option ContextInfo) (inTac : Bool) (t : InfoTree)
    (acc : Array (Syntax × Name)) : Array (Syntax × Name) :=
  match t with
  | .context pci t => walk bad (pci.mergeIntoOuter? ctx?) inTac t acc
  | .hole _ => acc
  | .node i cs =>
    let inst (mctx : MetavarContext) (e : Expr) := (instantiateMVarsCore mctx e).1
    let push (acc : Array (Syntax × Name)) (stx : Syntax) (e : Expr) :=
      (floatConsts bad e).foldl (fun acc c => acc.push (stx, c)) acc
    let mctx := (ctx?.map (·.mctx)).getD {}
    let (acc, inTac') := match i with
      | .ofTermInfo ti =>
        let acc := push acc ti.stx (inst mctx ti.expr)
        let acc := match ti.expectedType? with
          | some ty => push acc ti.stx (inst mctx ty)
          | none => acc
        (acc, inTac)
      | .ofFieldInfo fi => (push acc fi.stx (inst mctx fi.val), inTac)
      | .ofTacticInfo ti =>
        if inTac then (acc, true)
        else (ti.goalsBefore.foldl (fun acc g => push acc ti.stx (inst ti.mctxAfter (.mvar g))) acc,
          true)
      | _ => (acc, inTac)
    cs.foldl (fun acc c => walk bad ctx? inTac' c acc) acc

/-- The module of a relative `.lean` path: `Tests/Beta.lean` is `Tests.Beta`. -/
def moduleOf (rel : System.FilePath) : Name :=
  (rel.withExtension "").components.foldl Name.mkStr .anonymous

/-- The line done by a child that finished. -/
def doneLine (rel : String) : String := s!"float front done: {rel}"

/-- The variable a self-test child is started with, `1`; every scope file's child is
started with it unset. -/
def selfTestVar : String := "PMA_FLOAT_SELFTEST"

/-- The frontend pass over one file (relative to the working directory): its failure
lines. Commands refused are not elaborated. -/
def frontFile (rel : System.FilePath) : IO (Array String) := do
  let extra := if (← IO.getEnv selfTestVar) == some "1" then selfTestOptions else []
  let src ← IO.FS.readFile rel
  let inputCtx := Parser.mkInputContext src rel.toString
  let lineOf (stx : Syntax) (dflt : Nat) : Nat :=
    match stx.getPos? with
    | some p => (inputCtx.fileMap.toPosition p).line
    | none => dflt
  let opts : Options := Elab.async.set {} false
  let (header, pstate, messages) ← Parser.parseHeader inputCtx
  -- the call Lean's own frontend makes at startup: without it the imports' extensions are
  -- not loaded (`importModules (loadExts := true)` refuses inside a running `lean`)
  unsafe enableInitializersExecution
  let (env, messages) ← processHeader header opts messages inputCtx
  let env := env.setMainModule (moduleOf rel)
  let bad := ((Meta.defaultInstanceExtension.getState env).defaultInstances.find?
    ``OfScientific |>.getD []).map (·.1)
  let st0 := Command.mkState env messages opts
  let mut st : Command.State := { st0 with infoState := { st0.infoState with enabled := true } }
  let mut pstate := pstate
  let mut out : Array (Nat × String) := #[]
  -- the header's errors (an import not found leaves an empty environment), then each
  -- command's parse and elaboration errors, collected before the next command resets them
  let errors (ms : MessageLog) : IO (Array (Nat × String)) :=
    ms.toList.toArray.filterMapM fun m => do
      if m.severity != .error then return none
      return some (m.pos.line, s!"elaboration error: {((← m.data.toString).splitOn "\n").headD ""}")
  out := out ++ (← errors messages)
  repeat
    -- every command elaborates synchronously; `set_option Elab.async true in` still
    -- reaches its inner command, whose proof's tree the hole filling below brings in
    st := { st with scopes := st.scopes.map fun sc => { sc with opts := Elab.async.set sc.opts false } }
    let scope := st.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let pos := pstate.pos
    let (cmd, ps, msgs) := Parser.parseCommand inputCtx pmctx pstate st.messages
    pstate := ps
    out := out ++ (← errors msgs)
    st := { st with messages := {} }
    let cmdLine := lineOf cmd (inputCtx.fileMap.toPosition pos).line
    let refused := refusals extra cmd
    if refused.isEmpty then
      let ctx : Command.Context :=
        { fileName := rel.toString, fileMap := inputCtx.fileMap, cmdPos := pos, snap? := none,
          cancelTk? := none }
      match ← EIO.toIO' ((Command.elabCommandTopLevel cmd #[] ctx).run st) with
      | .error e =>
        out := out.push (cmdLine, s!"elaboration error: {← e.toMessageData.toString}")
      | .ok ((), st') => st := st'
      out := out ++ (← errors st.messages)
      -- the trees of the command with their holes filled (an asynchronous proof's tree is a
      -- hole of the command's tree, filled when its task ends: `substituteLazy`, waited on),
      -- and those of any task it left, each waited on
      let mut trees := st.infoState.substituteLazy.get.trees.toArray
      for task in st.snapshotTasks do
        for snap in task.get.getAll do
          if let some tree := snap.infoTree? then trees := trees.push tree
          out := out ++ (← errors snap.diagnostics.msgLog)
      st := { st with messages := {}, snapshotTasks := #[] }
      for t in trees do
        for (stx, c) in walk bad none false t #[] do
          out := out.push (lineOf stx cmdLine, s!"{c} elaborated (Float)")
      st := { st with infoState := { st.infoState with trees := {}, lazyAssignment := {} } }
    else
      for (stx, why) in refused do
        out := out.push (lineOf stx cmdLine, why)
    if Parser.isTerminalCommand cmd then break
  let mut lines : Array String := #[]
  for (l, what) in out do
    let s := s!"FLOAT AUDIT FAIL: {rel}:{l}: {what}"
    unless lines.contains s do lines := lines.push s
  return lines

/-- Run the frontend pass of `rel` in a child process (working directory `cwd`):
its failure lines, and a failure line of its own when the child did not finish. `self?`:
whether the child is the self-test's (`selfTestVar` set to `1`; else unset). -/
def runChild (self : System.FilePath) (cwd : System.FilePath) (self? : Bool) (rel : String) :
    IO (Array String) := do
  let lean := (← IO.appPath).toString
  let r ← IO.Process.output
    { cmd := lean, args := #[self.toString], cwd := cwd,
      env := #[("PMA_FLOAT_FRONT", some rel), (selfTestVar, if self? then some "1" else none)] }
  let lines := (r.stdout.splitOn "\n").filter (· ≠ "")
  let fails := lines.filter (·.startsWith "FLOAT AUDIT FAIL: ")
  if r.exitCode == 0 && lines.getLast? == some (doneLine rel) then return fails.toArray
  let tail := ((r.stdout ++ r.stderr).splitOn "\n").filter (· ≠ "") |>.reverse.take 5 |>.reverse
  return fails.toArray.push
    s!"FLOAT AUDIT FAIL: {rel}: the frontend pass did not finish (exit {r.exitCode}): {tail}"

/-- The frontend pass over `files` (relative to `cwd`), `jobs` children at a time;
`self?` as `runChild`'s. -/
def runChildren (self cwd : System.FilePath) (self? : Bool) (files : Array String) (jobs : Nat) :
    IO (Array String) := do
  let mut out := #[]
  let mut rest := files.toList
  while !rest.isEmpty do
    let batch := rest.take (max jobs 1)
    rest := rest.drop (max jobs 1)
    let tasks ← batch.mapM (fun f => IO.asTask (runChild self cwd self? f))
    for t in tasks do
      match t.get with
      | .ok ls => out := out ++ ls
      | .error e => out := out.push s!"FLOAT AUDIT FAIL: the frontend pass: {e}"
  return out

/-- The canary the audit's pass over the scope carries in its own call, written to a
temporary directory outside the scope: its source, and the end of the one failure line a
scope file's child gives for it. A self-test child admits `Elab.async` (`selfTestOptions`)
and gives none, so that call started with `self? = true` fails the audit. -/
def scopeCanary : String × String :=
  ("set_option Elab.async true in theorem probeCanary : True := trivial\n",
   ":1: set_option Elab.async not admitted")

/-- The frontend pass's self-test: each case's source and the ends of the failure lines it
must give (none: the case must pass, with no failure line). A line it does not name fails the
case unless it is a line of a constant with `Float` met (`... elaborated (Float)`). An end
written with a final `*` names every line that begins with the rest of it after the case's
file name (an error whose words are the toolchain's). -/
def frontTest : List (String × List String) := [
  ("example := OfScientific.ofScientific 25 true 1\n",
    [":1: instOfScientificFloat elaborated (Float)"]),
  ("#eval OfScientific.ofScientific 25 true 1\n",
    [":1: command kind Lean.Parser.Command.eval not admitted"]),
  ("syntax \"foo\" : term\nmacro_rules\n" ++
    "  | `(foo) => pure (Lean.Syntax.mkLit Lean.scientificLitKind \"2.5\")\n#eval foo\n",
    [":1: command kind Lean.Parser.Command.syntax not admitted",
     ":2: command kind Lean.Parser.Command.macro_rules not admitted",
     ":4: command kind Lean.Parser.Command.eval not admitted"]),
  ("syntax \"bar\" : term\nmacro_rules\n" ++
    "  | `(bar) => pure (Lean.Syntax.mkLit (Lean.Name.mkSimple (\"scien\" ++ \"tific\")) \"1.5\")\n" ++
    "#eval bar + bar\n",
    [":1: command kind Lean.Parser.Command.syntax not admitted",
     ":2: command kind Lean.Parser.Command.macro_rules not admitted",
     ":4: command kind Lean.Parser.Command.eval not admitted"]),
  ("@[macro Lean.Parser.Term.app] def m : Lean.Macro := fun _ => Lean.Macro.throwUnsupported\n",
    [":1: attribute macro not admitted"]),
  ("#eval show Lean.Elab.Command.CommandElabM Unit from do\n" ++
    "  let _ := Lean.mkConst (.mkSimple (\"Flo\" ++ \"at\"))\n" ++
    "#eval show Lean.Meta.MetaM Unit from do\n" ++
    "  let _ := Lean.mkConst (.mkSimple (\"Flo\" ++ \"at\"))\n",
    [":1: command kind Lean.Parser.Command.eval not admitted",
     ":3: command kind Lean.Parser.Command.eval not admitted"]),
  ("def x : Float := 1\n", [":1: Float elaborated (Float)"]),
  ("def r : Rat := 2.5\n", []),
  ("def y := 2.5\n", [":1: Float elaborated (Float)"]),
  ("theorem t : True := by\n  run_tac pure ()\n  trivial\n",
    [":2: syntax kind Lean.Parser.Tactic.runTac not admitted"]),
  ("example : Nat := by_elab pure (Lean.mkNatLit 1)\n",
    [":1: syntax kind Lean.byElab not admitted"]),
  ("def u : Nat := unsafe 1\n", [":1: syntax kind Lean.Parser.Term.unsafe not admitted"]),
  ("open Nat in\ndef v := 1\n", []),
  ("open Nat in #eval 1\n", [":1: command kind Lean.Parser.Command.eval not admitted"]),
  ("set_option Elab.async true\ntheorem z : True := by\n" ++
    "  have := OfScientific.ofScientific 25 true 1\n  trivial\n",
    [":3: instOfScientificFloat elaborated (Float)"]),
  ("/-! A module docstring. -/\nnamespace N\n/-- A docstring. -/\n" ++
    "@[simp, inline, reducible] def w (n : Nat) : Nat := n + 1\n" ++
    "structure S where\n  a : Nat\n  deriving Repr\ninstance : Inhabited S := ⟨⟨0⟩⟩\n" ++
    "theorem w0 : w 0 = 1 := by simp [w]\nexample : (0.5 : Rat) = (0.5 : Rat) := rfl\nend N\n",
    []),
  ("mutual\ndef ev : Nat → Bool\n  | 0 => true\n  | n+1 => od n\ndef od : Nat → Bool\n" ++
    "  | 0 => decide ((2.5 : Float) < 3)\n  | n+1 => ev n\nend\n",
    [":6: Float elaborated (Float)"]),
  ("def impl (_ : Nat) : Bool := true\nmutual\n@[implemented_by impl] def ev : Nat → Bool\n" ++
    "  | 0 => true\n  | n+1 => od n\ndef od : Nat → Bool\n  | 0 => false\n  | n+1 => ev n\nend\n",
    [":3: attribute implemented_by not admitted"]),
  ("mutual\ndef ev : Nat → Bool\n  | 0 => true\n  | n+1 => od n\ndef od : Nat → Bool\n" ++
    "  | 0 => false\n  | n+1 => ev n\nend\ntheorem e2 : ev 2 = true := rfl\n",
    []),
  ("set_option Elab.async true in theorem z : True := by\n" ++
    "  have := OfScientific.ofScientific 25 true 1\n  trivial\n",
    [":2: instOfScientificFloat elaborated (Float)"]),
  ("set_option Elab.async true in theorem q : 1 = 2 := by\n  exact rfl\n",
    [":2: elaboration error: Type mismatch"]),
  -- `native_decide` and a native `decide`, refused by their syntax; the kind read from
  -- the parser's own name
  ("theorem a : 2 + 2 = 4 := by native_decide\n",
    [s!":1: syntax kind {``Parser.Tactic.nativeDecide} not admitted"]),
  ("theorem b : 2 + 2 = 4 := by decide +native\n", [":1: tactic decide +native not admitted"]),
  ("theorem c : 2 + 2 = 4 := by decide (config := { native := true })\n",
    [":1: tactic decide +native not admitted"]),
  ("theorem c2 : 2 + 2 = 4 := by decide (native := true)\n",
    [":1: tactic decide +native not admitted"]),
  ("def cfg : Lean.Parser.Tactic.DecideConfig := {}\n" ++
    "theorem c3 : 2 + 2 = 4 := by decide +kernel (config := cfg)\n",
    [":2: tactic decide +native not admitted"]),
  ("theorem d : 2 + 2 = 4 := by decide\n", []),
  ("theorem e : 2 + 2 = 4 := by decide +kernel\n", []),
  ("theorem f : 2 + 2 = 4 := by decide -native\n", []),
  ("theorem g : 2 + 2 = 4 := by\n  decide (kernel := true)\n", []),
  -- `native` in a later item, a value not read and a `config` not read refused (fail
  -- closed); `native_decide` nested in another tactic; a `DecideConfig` definition alone
  -- admitted; two refusals in one file, each at its own line
  ("theorem h : 2 + 2 = 4 := by decide +kernel +native\n",
    [":1: tactic decide +native not admitted"]),
  ("theorem i : 2 + 2 = 4 := by decide (native := false)\n",
    [":1: tactic decide +native not admitted"]),
  ("theorem j : 2 + 2 = 4 := by decide (config := { kernel := true })\n",
    [":1: tactic decide +native not admitted"]),
  ("theorem k : 2 + 2 = 4 := by first | native_decide | decide\n",
    [s!":1: syntax kind {``Parser.Tactic.nativeDecide} not admitted"]),
  ("def cfg : Lean.Parser.Tactic.DecideConfig := {}\n", []),
  ("theorem l : 2 + 2 = 4 := by native_decide\ntheorem m : 2 + 2 = 4 := by decide +native\n",
    [s!":1: syntax kind {``Parser.Tactic.nativeDecide} not admitted",
     ":2: tactic decide +native not admitted"]),
  -- `include_str`, a computed path and a literal one, refused by its syntax
  ("partial def probePick (n : Nat) : String := if n > 2 then \"c.lean\" else probePick (n + 1)\n" ++
    "def probeIs : String := include_str (probePick 0 : System.FilePath)\n",
    [s!":2: syntax kind {``Lean.includeStr} not admitted"]),
  ("def probeIl : String := include_str \"c.lean\"\n",
    [s!":1: syntax kind {``Lean.includeStr} not admitted"]),
  -- `set_option` off `admittedOptions`: the `in` form, the command, the tactic, the term;
  -- `Elab.async` is admitted here only as a self-test child's (`selfTestOptions`)
  ("set_option debug.skipKernelTC true in theorem probeSk : True := trivial\n",
    [":1: set_option debug.skipKernelTC not admitted"]),
  ("set_option debug.skipKernelTC true\n", [":1: set_option debug.skipKernelTC not admitted"]),
  ("theorem probeSt : True := by\n  set_option debug.skipKernelTC true in trivial\n",
    [":2: set_option debug.skipKernelTC not admitted"]),
  ("def probeSm : Nat := set_option debug.skipKernelTC true in 1\n",
    [":1: set_option debug.skipKernelTC not admitted"]),
  ("set_option maxHeartbeats 400000 in theorem probeSh : True := trivial\n" ++
    "set_option pp.all true in\ntheorem probeSp : True := trivial\n" ++
    "theorem probeSq : True := by\n  set_option maxRecDepth 1000 in trivial\n", []),
  ("set_option compiler.extract_closed false\nset_option pp true\n",
    [":1: set_option compiler.extract_closed not admitted", ":2: set_option pp not admitted"]),
  -- `bv_decide`, `bv_decide?`, `bv_check` and grind's forms, refused by their syntax
  ("theorem probeBv (x : BitVec 2) : x &&& x = x := by bv_decide\n" ++
    "theorem probeBt : True := by bv_decide?\ntheorem probeBc : True := by bv_check \"p.lrat\"\n",
    [s!":1: syntax kind {``Parser.Tactic.bvDecide} not admitted",
     s!":2: syntax kind {``Parser.Tactic.bvTrace} not admitted",
     s!":3: syntax kind {``Parser.Tactic.bvCheck} not admitted"]),
  ("theorem probeGd (x : BitVec 2) : x = x := by grind => bv_decide\n" ++
    "theorem probeGt (x : BitVec 2) : x = x := by grind => bv_decide?\n" ++
    "theorem probeGc (x : BitVec 2) : x = x := by grind => bv_check \"p.lrat\"\n" ++
    "theorem probeGs (x : BitVec 2) : x = x := by\n" ++
    "  grind => set_option debug.skipKernelTC true in finish\n",
    [s!":1: syntax kind {``Parser.Tactic.Grind.bvDecide} not admitted",
     s!":2: syntax kind {``Parser.Tactic.Grind.bvTrace} not admitted",
     s!":3: syntax kind {``Parser.Tactic.Grind.bvCheck} not admitted",
     ":5: set_option debug.skipKernelTC not admitted"]),
  -- an admitted option with a numeric value, in grind's form and the term form (the value is
  -- the node's fourth argument; read as the third, a numeral would be refused `<unread>`)
  ("theorem probeGn : True := by\n  grind => set_option maxRecDepth 1000 in done\n" ++
    "def probeTn : Nat := set_option maxRecDepth 1000 in 1\n", []),
  -- a name the parse left without its identifier after the dot: refused `<unread>`, beside
  -- the parser's error on line 1 in whatever words the toolchain gives it
  ("set_option pp. true\n",
    [":1: elaboration error: *", ":1: set_option <unread> not admitted"]),
  -- the same in grind's form (its `.<ident>` part present, the identifier missing: the
  -- branch that reads grind's dotted part) and in the tactic form
  ("theorem probeGd : True := by\n  grind => set_option pp. true in finish\n",
    [":2: elaboration error: *", ":2: set_option <unread> not admitted"]),
  ("theorem probeTd : True := by\n  set_option pp. true in trivial\n",
    [":2: elaboration error: *", ":2: set_option <unread> not admitted"]),
  -- `trace.profiler.serve` and `trace.profiler.output` (and below it), under the admitted
  -- `trace.`: the command, the `in` form, the term and the tactic; the other `trace.`
  -- options stay admitted
  ("set_option trace.profiler.serve true\n" ++
    "set_option trace.profiler.serve true in theorem probePs : True := trivial\n" ++
    "set_option trace.profiler.output \"p.json\"\n" ++
    "set_option trace.profiler.output \"p.json\" in theorem probePo : True := trivial\n" ++
    "set_option trace.profiler.output.pp true\n" ++
    "def probePm : Nat := set_option trace.profiler.serve true in 1\n" ++
    "theorem probePt : True := by\n  set_option trace.profiler.output \"p.json\" in trivial\n",
    [":1: set_option trace.profiler.serve not admitted",
     ":2: set_option trace.profiler.serve not admitted",
     ":3: set_option trace.profiler.output not admitted",
     ":4: set_option trace.profiler.output not admitted",
     ":5: set_option trace.profiler.output.pp not admitted",
     ":6: set_option trace.profiler.serve not admitted",
     ":8: set_option trace.profiler.output not admitted"]),
  ("set_option trace.Meta.synthInstance true in theorem probePa : True := trivial\n" ++
    "set_option trace.profiler true in\nset_option trace.profiler.threshold 5 in\n" ++
    "set_option trace.profiler.useHeartbeats true in theorem probePb : True := trivial\n", [])]

/-- The frontend cases run in a scope file's child, `selfTestVar` unset (as `frontTest`'s
otherwise): `Elab.async`, admitted in a self-test child, is refused here, the `in` form and
the command. The audit's own call over the scope is guarded by `scopeCanary`. -/
def scopeFrontTest : List (String × List String) := [
  ("set_option Elab.async true in theorem probeSa : True := trivial\n",
    [":1: set_option Elab.async not admitted"]),
  ("set_option Elab.async true\ntheorem probeSc : True := trivial\n",
    [":1: set_option Elab.async not admitted"])]

/-- `admittedOptions` on names, with no extra and with `selfTestOptions`: the extras,
`options` and whether it is admitted. -/
def optionTest : List (List Name × Name × Bool) := [
  ([], `Elab.async, false), (selfTestOptions, `Elab.async, true),
  ([], `debug.skipKernelTC, false), (selfTestOptions, `debug.skipKernelTC, false),
  ([], `maxHeartbeats, true), ([], `synthInstance.maxHeartbeats, true), ([], `pp, false),
  ([], `pp.all, true), ([], `linter.unusedVariables, true), ([], `trace.Meta.synthInstance, true),
  ([], `compiler.extract_closed, false), ([], `maxHeartbeatsX, false),
  ([], `trace.profiler.serve, false), (selfTestOptions, `trace.profiler.serve, false),
  ([], `trace.profiler.output, false), ([], `trace.profiler.output.pp, false),
  ([], `trace.profiler, true), ([], `trace.profiler.threshold, true)]

/-- `optionName`, through `innerRefusals` with no extra, on `set_option` nodes built by
hand, one per branch (the `.<ident>` part with an identifier is a layout the parser of the
pinned toolchain does not give from source): the node and the refusals it must give. -/
def optionNameTest : List (Syntax × List String) :=
  let node (k : SyntaxNodeKind) (o rest : Syntax) :=
    mkNode k #[mkAtom "set_option", o, rest, mkAtom "true"]
  let dot (i : Syntax) := mkNullNode #[mkAtom ".", i]
  let grind := ``Parser.Tactic.Grind.setOption
  [(node grind (mkIdent `pp) (dot (mkIdent `all)), []),
   (node grind (mkIdent `debug) (dot (mkIdent `skipKernelTC)),
     ["set_option debug.skipKernelTC not admitted"]),
   (node grind (mkIdent `pp) (dot .missing), ["set_option <unread> not admitted"]),
   (node grind (mkIdent `pp) (mkNullNode #[mkAtom "."]), ["set_option <unread> not admitted"]),
   (node ``Parser.Command.set_option (mkIdent `pp) (dot (mkIdent `all)),
     ["set_option <unread> not admitted"]),
   (node ``Parser.Tactic.set_option (mkIdent `pp) (dot (mkIdent `all)),
     ["set_option <unread> not admitted"]),
   (node ``Parser.Tactic.set_option .missing (mkNullNode), ["set_option <unread> not admitted"]),
   (node ``Parser.Term.set_option (mkIdent `maxRecDepth) (mkNullNode), [])]

/-- `decideNative` on configurations built by hand, one per branch, the three fail-closed
branches among them (a layout the parser of the pinned toolchain does not give): the syntax
and whether it is refused. -/
def decideTest : List (Syntax × Bool) :=
  let dec (cfg : Syntax) := mkNode ``Parser.Tactic.decide #[mkAtom "decide", cfg]
  let opt (items : Array Syntax) := mkNode ``Parser.Tactic.optConfig #[mkNullNode items]
  let item (it : Syntax) := mkNode ``Parser.Tactic.configItem #[it]
  let pos (n : Name) := item (mkNode ``Parser.Tactic.posConfigItem #[mkAtom "+", mkIdent n])
  let neg (n : Name) := item (mkNode ``Parser.Tactic.negConfigItem #[mkAtom "-", mkIdent n])
  [(dec .missing, true),
   (dec (opt #[mkNode `other #[]]), true),
   (dec (opt #[item (mkNode `other #[])]), true),
   (dec (opt #[]), false),
   (dec (opt #[pos `kernel]), false),
   (dec (opt #[neg `native]), false),
   (dec (opt #[pos `kernel, pos `native]), true)]

/-- Whether the end `w` of a `frontTest` case named `n` names the failure line `l`: an end
with a final `*` names every line that begins with `FLOAT AUDIT FAIL: <n><w's rest>` (the
case's own file, line and kind, the words the toolchain's); any other end, the line that ends
with `<n><w>`. -/
def wantNames (n w l : String) : Bool :=
  if w.endsWith "*" then l.startsWith s!"FLOAT AUDIT FAIL: {n}{(w.splitOn "*").headD ""}"
  else l.endsWith s!"{n}{w}"

/-- `wantNames` on lines written by hand: the case's name, the end, the line and whether it
is named. The wildcard names its own file's line of its line number and kind, in any words,
and no other file's, line's or kind's. -/
def wantNamesTest : List (String × String × String × Bool) := [
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case1.lean:1: elaboration error: unexpected token", true),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case1.lean:1: elaboration error: ", true),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case1.lean:12: elaboration error: unexpected token", false),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case1.lean:2: elaboration error: unexpected token", false),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case12.lean:1: elaboration error: unexpected token", false),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: Case1.lean:1: set_option pp not admitted", false),
  ("Case1.lean", ":1: elaboration error: *",
    "FLOAT AUDIT FAIL: x/Case1.lean:1: elaboration error: unexpected token", false),
  ("Case1.lean", ":1: set_option <unread> not admitted",
    "FLOAT AUDIT FAIL: Case1.lean:1: set_option <unread> not admitted", true),
  ("Case1.lean", ":1: set_option <unread> not admitted",
    "FLOAT AUDIT FAIL: Case1.lean:1: set_option <unread> not admitted here", false)]

/-- Run `frontTest` (in self-test children) and `scopeFrontTest` (in children started as a
scope file's, `selfTestVar` unset) in a temporary directory. Returns the wrong answers. -/
def selfTest (self : System.FilePath) (jobs : Nat) : IO (Array String) := do
  let t ← IO.FS.createTempDir
  let mut wrong := #[]
  try
    let names := (List.range frontTest.length).map (fun k => s!"Case{k + 1}.lean")
    let scopeNames := (List.range scopeFrontTest.length).map (fun k => s!"Scope{k + 1}.lean")
    let cases := names.zip frontTest ++ scopeNames.zip scopeFrontTest
    for (n, (src, _)) in cases do
      IO.FS.writeFile (t / n) src
    let got := (← runChildren self t true names.toArray jobs) ++
      (← runChildren self t false scopeNames.toArray jobs)
    for (n, (_, want)) in cases do
      let mine := got.filter (·.startsWith s!"FLOAT AUDIT FAIL: {n}:")
      -- a Float case gives a line per constant met, named in part; every other line, a
      -- refusal or an error, must be named, so a refused case gives exactly its lines
      let names (w l : String) := wantNames n w l
      let named (l : String) := want.any (fun w => names w l)
      let ok := want.all (fun w => mine.any (names w ·)) &&
        mine.all (fun l => named l || l.endsWith " elaborated (Float)") &&
        (!want.isEmpty || mine.isEmpty) && (want.isEmpty || !mine.isEmpty)
      unless ok do wrong := wrong.push s!"{n} gave {mine}, wants {want}"
  finally
    IO.FS.removeDirAll t
  return wrong

end FloatFront

/-- The `.lean` files under `d` (relative to `root`), recursively, relative to `root`. -/
partial def leanFilesUnder (root d : System.FilePath) : IO (Array System.FilePath) := do
  let mut fs := #[]
  for e in ← (root / d).readDir do
    let rel := d / e.fileName
    if ← (root / rel).isDir then fs := fs ++ (← leanFilesUnder root rel)
    else if rel.extension == some "lean" then fs := fs.push rel
  return fs

/-- The `.lean` files the Float audit reads, relative to `root`, sorted. -/
def floatScanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut fs : Array System.FilePath := #["Main.lean", "Principia.lean"]
  for f in fs do
    unless ← (root / f).pathExists do throw <| IO.userError s!"float audit: {f} not found; run from the repository's root"
  for d in (#["Principia", "Tests"] : Array System.FilePath) do
    unless ← (root / d).isDir do throw <| IO.userError s!"float audit: {d}/ not found; run from the repository's root"
    fs := fs ++ (← leanFilesUnder root d)
  return fs.qsort (fun a b => a.toString < b.toString)

/-- The file walk's self-test, in a temporary directory: the files found and their
modules; then a tree with no `Tests/` must fail closed. Returns the wrong answers. -/
def walkTest : IO (Array String) := do
  let t ← IO.FS.createTempDir
  let mut wrong := #[]
  try
    let put (rel : System.FilePath) (s : String) : IO Unit := do
      if let some p := (t / rel).parent then IO.FS.createDirAll p
      IO.FS.writeFile (t / rel) s
    put "Main.lean" "def main : IO Unit := pure ()\n"
    put "Principia.lean" "import Principia.A\n"
    put "Principia/A.lean" "def a := 1\n"
    put "Principia/Sub/B.lean" "def b := 0\n"
    put "Tests/C.lean" "def c := 2\n"
    put "Tests/notes.md" "Float\n"
    let files ← floatScanFiles t
    let wantFiles := #["Main.lean", "Principia.lean", "Principia/A.lean", "Principia/Sub/B.lean",
      "Tests/C.lean"]
    -- by components: the walk joins with the platform's separator, the literals with `/`
    if files.map (·.components) != wantFiles.map (System.FilePath.components ⟨·⟩) then
      wrong := wrong.push s!"files {files}"
    let mods := files.map FloatFront.moduleOf
    if mods != #[`Main, `Principia, `Principia.A, `Principia.Sub.B, `Tests.C] then
      wrong := wrong.push s!"modules {mods}"
    IO.FS.removeDirAll (t / "Tests")
    let closed ← tryCatch (do discard <| floatScanFiles t; pure false) (fun _ => pure true)
    unless closed do wrong := wrong.push "a tree with no Tests/ did not fail"
  finally
    IO.FS.removeDirAll t
  return wrong

/-- Build `mods` (`lake build +<module> ...`). -/
def buildModules (mods : Array Name) : IO Unit := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let r ← IO.Process.output
    { cmd := lake, args := #["build", "-q"] ++ mods.map (fun m => "+" ++ m.toString) }
  if r.exitCode != 0 then
    throw <| IO.userError s!"lake build of the scanned modules failed (exit {r.exitCode})\n{r.stdout}{r.stderr}"

/-- The constant check over `env`, of the constants defined in the modules of `group`: its
failure lines and the number of constants read. -/
def floatConstantFindings (env : Environment) (group : Array Name) : Array String × Nat := Id.run do
  let mut out := #[]
  let mut read := 0
  let names := env.header.moduleNames
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := names[idx.toNat]!
    if FloatAudit.inScope m && group.contains m then
      read := read + 1
      for c in FloatAudit.floatUses ci do
        out := out.push s!"FLOAT AUDIT FAIL: {n} uses {c} (module {m})"
  return (out.qsort (· < ·), read)

#eval show IO Unit from do
  -- a child of the frontend pass: one file, then the done line
  if let some rel ← IO.getEnv "PMA_FLOAT_FRONT" then
    for l in ← FloatFront.frontFile rel do
      IO.println l
    IO.println (FloatFront.doneLine rel)
    return
  let self ← IO.FS.realPath "scripts/axiom_audit.lean"
  let jobs := ((← IO.getEnv "LEAN_NUM_THREADS").bind String.toNat?).getD 2
  -- the self-tests
  let mut fails : Array String := #[]
  let mut initFails : Array String := #[]
  for ((m, want), k) in FloatAudit.scopeTest.zipIdx do
    if FloatAudit.inScope m != want then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test scope case {k + 1} ({m}) wrong"
  for ((ci, want), k) in FloatAudit.usesTest.zipIdx do
    let got := (FloatAudit.floatUses ci).toList
    if got.length != want.length || !want.all got.contains then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test constant case {k + 1} gave {got}, wants {want}"
  for w in ← walkTest do
    fails := fails.push s!"FLOAT AUDIT FAIL: self-test file walk: {w}"
  for w in ← InitAudit.selfTest do
    initFails := initFails.push s!"INIT AUDIT FAIL: self-test: {w}"
  for w in ← FloatFront.selfTest self jobs do
    fails := fails.push s!"FLOAT AUDIT FAIL: self-test frontend case {w}"
  for ((stx, want), k) in FloatFront.decideTest.zipIdx do
    if FloatFront.decideNative stx != want then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test decide case {k + 1} gave {!want}, wants {want}"
  for ((extra, n, want), k) in FloatFront.optionTest.zipIdx do
    if FloatFront.admittedOptions extra n != want then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test option case {k + 1} ({n}) gave {!want}, wants {want}"
  for ((stx, want), k) in FloatFront.optionNameTest.zipIdx do
    let got := (FloatFront.innerRefusals [] stx #[]).toList.map (·.2)
    if got != want then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test option name case {k + 1} gave {got}, wants {want}"
  for ((n, w, l, want), k) in FloatFront.wantNamesTest.zipIdx do
    if FloatFront.wantNames n w l != want then
      fails := fails.push s!"FLOAT AUDIT FAIL: self-test wildcard case {k + 1} gave {!want}, wants {want}"
  -- the cases run so far; the scope pass's canary is counted below, once it has run
  let mut cases := FloatAudit.scopeTest.length + FloatAudit.usesTest.length + 1 +
    FloatFront.frontTest.length + FloatFront.scopeFrontTest.length +
    FloatFront.decideTest.length + FloatFront.optionTest.length +
    FloatFront.optionNameTest.length + FloatFront.wantNamesTest.length
  let mut files : Array System.FilePath := #[]
  try
    files ← floatScanFiles "."
  catch e =>
    fails := fails.push s!"FLOAT AUDIT FAIL: {e}"
  -- two groups, since `Main` and `Tests.Main` each define `main`: the rest (with `Principia`
  -- always, the axiom audit's), then the `Tests` modules, built only once the first group's
  -- initializer audit is clean; each imported with no initializer run
  let mods := files.map FloatFront.moduleOf
  let first := mods.filter (!(`Tests).isPrefixOf ·)
  let first := if first.contains `Principia then first else first.push `Principia
  let mut axiomFails : Array String := #[]
  for w in ← AxiomAudit.selfTest do
    axiomFails := axiomFails.push s!"AXIOM AUDIT FAIL: self-test: {w}"
  let mut axiomMods : Array Name := #[]
  let mut checked := 0
  let mut nConsts := 0
  let mut initMods : Array Name := #[]
  for (group, k) in [first, mods.filter ((`Tests).isPrefixOf ·)].zipIdx do
    if group.isEmpty then continue
    if !initFails.isEmpty then
      fails := fails.push s!"FLOAT AUDIT FAIL: the modules {group} not built: the initializer audit failed"
      continue
    try
      buildModules group
      let env ← importModules (group.map ({ module := · })) {}
      let (found, read) := InitAudit.findings env
      for (m, d) in found do
        let l := InitAudit.failLine m d
        unless initFails.contains l do initFails := initFails.push l
      for m in read do
        unless initMods.contains m do initMods := initMods.push m
      -- the roots by module, never by name: every constant of a module in scope, those of
      -- the first group's modules once (the `Tests` group imports them again)
      let (roots, rooted) := AxiomAudit.rootsByModule env axiomMods.contains
      axiomMods := axiomMods ++ rooted
      checked := checked + roots.size
      for (n, c, known) in AxiomAudit.findings env.find? roots do
        axiomFails := axiomFails.push (AxiomAudit.failLine n c known)
      let (cs, read) := floatConstantFindings env group
      nConsts := nConsts + read
      fails := fails ++ cs
    catch e =>
      fails := fails.push s!"FLOAT AUDIT FAIL: {e}"
      if k == 0 then axiomFails := axiomFails.push s!"AXIOM AUDIT FAIL: the library not imported: {e}"
  unless axiomMods.contains `Principia do
    axiomFails := axiomFails.push "AXIOM AUDIT FAIL: the module Principia not among the roots"
  if checked == 0 && axiomFails.isEmpty then
    axiomFails := axiomFails.push "AXIOM AUDIT FAIL: no declaration checked"
  -- the frontend pass runs each file's imports' initializers: only once none is in scope
  if initFails.isEmpty then
    -- the canary rides in this call, so this call started with self-test children fails here
    let t ← IO.FS.createTempDir
    try
      let canary := (t / "ScopeCanary.lean").toString
      IO.FS.writeFile canary FloatFront.scopeCanary.1
      let got ← FloatFront.runChildren self "." false ((files.map (·.toString)).push canary) jobs
      cases := cases + 1
      let mine := got.filter (·.startsWith s!"FLOAT AUDIT FAIL: {canary}:")
      fails := fails ++ got.filter (!·.startsWith s!"FLOAT AUDIT FAIL: {canary}:")
      unless mine == #[s!"FLOAT AUDIT FAIL: {canary}{FloatFront.scopeCanary.2}"] do
        fails := fails.push s!"FLOAT AUDIT FAIL: the scope pass's canary gave {mine}, wants \
          {FloatFront.scopeCanary.2}: its children did not run as a scope file's"
    finally
      IO.FS.removeDirAll t
  else
    fails := fails.push "FLOAT AUDIT FAIL: the frontend pass not run: the initializer audit failed"
  for f in axiomFails do
    IO.println f
  IO.println s!"axiom audit: {checked} declarations checked, {axiomFails.size} failures"
  for f in fails do
    IO.println f
  IO.println s!"float audit: {files.size} files through the frontend and {nConsts} constants \
    of their modules checked, {cases} self-test cases, {fails.size} failures"
  for f in initFails do
    IO.println f
  IO.println s!"init audit: {initMods.size} modules checked, {InitAudit.probes.length} self-test \
    cases, {initFails.size} failures"
  if axiomFails.size > 0 || fails.size > 0 || initFails.size > 0 then
    -- an error, never `IO.Process.exit`: `#eval` holds the lines printed until it ends
    throw <| IO.userError "proof audit failed"
