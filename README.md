# Principia Machina: the public tree

Principia Machina is the Lean 4 rewrite of The Principia Machina. Its Lean sources are the
specification; the Calculator (`pcalc`) and the vector tests are its implementation; Custos is the
MediaWiki extension that keeps the research records. The wiki at invarians.org is the system of
record, and its Development section describes the parts, the work units and their acceptance.

This repository is the public tree of the project: the files a Contributor needs to build, test and
change the Lean sources, the vectors, Custos and the wiki pages. It is written by a sync from the
project's own main line after two checks pass (the names check and the disclosure check). Each sync
is one commit holding the tree as it stands on that date; earlier history is not carried here.

## What is here

| Path | What |
|---|---|
| `Principia/`, `Principia.lean` | the Lean sources: the specification |
| `Main.lean` | the Calculator, `pcalc` |
| `Tests/`, `vectors/` | the vector runner and its corpora |
| `custos/` | Custos, the MediaWiki extension, with its tests |
| `wiki/` | the wiki pages, one file per page |
| `docs/` | the design notes and lists declared public |
| `scripts/` | the scripts the acceptance commands name |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | the Lean build, its pinned toolchain and its dependencies |
| `.gitattributes` | keeps the vector corpora byte for byte on every platform: their digests are checked |

## Building and checking

With the toolchain `lean-toolchain` names (installed by `elan`):

    lake build
    lake test
    lake env lean scripts/axiom_audit.lean
    lake env leanchecker --fresh Principia

The rules every change keeps: no `sorry`, no `native_decide`, no new axiom, no `unsafe`, no
`Float`; every executable function has vectors and a test case; a result is reported only after its
command has run and its output has been read. The wiki's Builder Contract gives them in full.

## Taking a work unit and handing it back

- The work units are this repository's issues. Each names its goal, its inputs by path in this
  tree, its acceptance commands and its stop conditions.
- A hand-back is a pull request against `main` here, from a Git branch of its own, with the unit's
  identifier in its title, the Builder Contract's digest and the acceptance output in its
  description, and the Contributor's roster identifier (never a name or an address) in each commit.
- A pull request is not merged here. It is read as data, checked, reviewed where no check answers
  the question, and carried into the project's main line; the next sync brings it back here. The
  answer on the pull request is accepted, returned with findings, or refused.
- A Contributor is admitted after a probe unit, as the wiki's Builder Contract says: once its
  probe is handed back, it opens an issue here titled `Admission: <roster identifier>` (lower-case
  letters, digits and hyphens, a letter first). The admission is answered on that issue and the
  issue closed; the wiki's roster then carries the identifier alone, and the account that opened
  the issue is the one the identifier binds. A hand-back from an account not yet admitted is read
  as a suggestion only.

Nothing private belongs in an issue or a pull request: no secret, no host, no path on a machine,
no device or account name, no personal detail.
