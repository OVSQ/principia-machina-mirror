import Principia.Provision.Reader
import Principia.Provision.Kind
import Principia.Provision.Text
import Principia.Provision.Preimage
import Principia.Provision.Catalogue
import Principia.Provision.Expand
import Principia.Provision.Order
import Principia.Provision.Interview
import Principia.Provision.Check
import Principia.Provision.Render

/-!
# Provisions

The Provision functions of the Calculator (Provision expansion and the
interview check), ported from v1's `tpc_module` 0.1.1 (tpm_module_spec 0.2.0; TPS 5.22, where
a Provision is an ENVIRONMENT MODULE). A Provision is a declared, versioned text
from which Custos writes ordinary entries into a draft's Starting Set at its author's choice: a
CONSTANT for each parameter, ASSUMPTION and BOUNDARY entries, and terms composed into laws the
Starting Set already has. It is of one of two kinds (`Kind`, the Declarer's choice of two kinds): an
Interaction (GRAV-UNIFORM, AIR-QUADRATIC, AIR-LINEAR) or a Convention (MATH).

v1's eleven functions, each with its name here:

| v1 | here | defined in |
|---|---|---|
| `module_parse` | `parse` | `Principia.Provision.Text` |
| `module_digest` | `digest` | `Principia.Provision.Text` |
| `module_bind` | `bind` | `Principia.Provision.Expand` |
| `module_expand` | `expand` | `Principia.Provision.Expand` |
| `module_verify` | `verify` | `Principia.Provision.Check` |
| `interview_check` | `interviewCheck` | `Principia.Provision.Interview` |
| `not_included_lines` | `notIncludedLines` | `Principia.Provision.Interview` |
| `catalogue_state` | `catalogueState` | `Principia.Provision.Catalogue` |
| `module_check` | `check` | `Principia.Provision.Check` |
| `draft_module_status` | `draftStatus` | `Principia.Provision.Check` |
| `module_use_view` | `useView` | `Principia.Provision.Check` |

The words on the wire stay v1's: the acts `MODULE ADD` to `MODULE REINSTATE`, the argument
names and every refusal's text, so each answer can be compared with v1's.

**Digests.** Every digest, a Provision's text's, a catalogue state's and a D(TPK), is SHA-256
over its preimage (the Declarer's choice of SHA-256), taken through a `DigestHook`: the Calculator's is
`DigestHook.calculator`, and D(TPK)'s preimage is the zones' (`Principia.Zone.Preimage`), the one
port of v1's canonical serialization. **What is owed.** Numbers the fundamental tests cannot
settle exactly are owed as they owe them. The kind of a Provision declared
after the first catalogue is a rule not yet made. Text is read as v1 read it, in NFC at Unicode
15.1.0 (the Declarer's choice of the Unicode version).

**Proved.** At most one version of an ID is OFFERED after any lines the Calculator accepts, and
a WITHDRAWN version stays WITHDRAWN (`readState_oneOffered`, `stateFrom_withdrawn`); once the
claims are read, their order changes nothing in the expansion (`expandRun_perm`), so the two
orders the checks before a declaring act try always agree (`pair_orders_agree`); EXCLUDES refuses
a pair either way round (`excludesPair_comm`); the NOT INCLUDED lines end with the closing line
(`notIncludedLines_last`); the first catalogue's kinds (`firstCatalogue_interactions`,
`firstCatalogue_conventions`).

Corpus: the Provision corpus (418 cases), run by the Provision vector tests.
-/
