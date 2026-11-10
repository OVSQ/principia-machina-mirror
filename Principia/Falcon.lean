import Principia.Falcon.Canon
import Principia.Falcon.Classes
import Principia.Falcon.Draw
import Principia.Falcon.Quote
import Principia.Falcon.Reconcile
import Principia.Falcon.Schema
import Principia.Falcon.Source
import Principia.Falcon.Stage
import Principia.Falcon.Stop

/-!
# The falcons

v1's `tpc_falcon` 0.2.0, the Falcon round's pure functions, one file each: the
character classes (`Classes`), the canonical forms (`Canon`), the QUOTE CHECK (`Quote`),
the source match and its hops (`Source`), the draw (`Draw`), the reconciliation
(`Reconcile`), the sponsor stage (`Stage`), the per-kind stop (`Stop`) and the output
schema's canonical text and digest (`Schema`). Text is put in NFC with Unicode 15.1.0's
tables, as v1 put it; the draw's order and the schema's digest are SHA-256
(`Principia.Sha256`). Every function answers: nothing is owed.
-/
