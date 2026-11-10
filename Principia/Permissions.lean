import Principia.Wire
import Principia.Parameters

/-!
# Roles and permissions

The two account classes, the six roles, the two lock states and
`permits`, whose definition is version 1's PERMISSIONS table (TPS 0.5.0, 5.13.2)
in PMA's words: H-DECL is the
Declarer, H-OP the Operator, H-OWN the Initiator, H-SPON the Sponsor, ANY the Public;
the Contributor is PMA's own role, with no version 1 term;
AI-LEAD is the Holder and AI-CO the Coworker; TPX is Custos; the TFK pages are the
Research Assembly's; TPS is the Principia Framework Specification; TPC-PY the
Calculator; a MANIFEST page an Index page; a LIBRARY PAGE a Reading page; an
ENVIRONMENT MODULE a Provision.

## The signature

The specification writes `permits : Role → PageClass → Op → Bool`. The table needs more:

* two of its six columns, AI-LEAD and AI-CO, are lock states of an agent account, not
  roles, so the one asking is an `Actor`: a user account in a role, or an agent account
  in its lock state (if any) in the page's UWC;
* three of the theorems below read facts no role carries: the ACCESS POLICY of the
  page's UWC and the asker's ACCESS LIST membership (5.13.4, the CLOSED PREDICATE), and
  whether the page's title names the asker's own account and what DOSSIER READ allows
  (5.18.10); and two cells carry a condition the server check (SC) enforces: a Coworker
  writes the lock page only at the head of the queue, inside its window, and the
  Declarer appends an override, pad or removal declaration only two-factor and
  re-authenticated. Those facts are the `PageContext`, which Custos supplies.

## How the table is read

* A cell's letters: R `read`, W `write`, A `append`, P `protect`, `-` none (5.13.1). A
  cell marked "(TPX)" or "via TPX" is the Holder's write carried out by Custos's API:
  `writeThroughCustos` or `appendThroughCustos`, never a direct edit (5.13.3: "landing
  is TPX's API only"; 5.16.12: the CLOSED PREDICATE conditions such a landing "as it
  does every AI-* write").
* The Public is everyone: every asker holds the Public's cell besides its
  own. Every cell of the Public is R or `-`, so this adds reads only.
* A row that omits the Initiator's cell reads R where the Public reads and `-`
  otherwise (5.13.2, last paragraph).
* A qualifier the table enforces by audit (AU: "own draft", "own petition row",
  "assignments", "clear, with an audit line") is not a condition of the cell:
  version 1's permission hook granted the cell and the audit judged the act.
* One cell departs from version 1's table: the Coworker's "W own page" on STAGING is
  gone, and the Coworker's cell on STAGING is empty. Custos writes a Coworker's return on
  its staging subpage, so no Coworker edits that page directly
  (`coworker_never_writes_staging`).
* Two rows name no page and are not page classes: Custos's secrets, and the
  conformance probe templates. The bibliography row is two classes, OPEN and FROZEN,
  as its AI-LEAD cell reads.

Where the table leaves a slot open or another part of version 1 contradicts it, the
definition refuses and the slot is for the Declarer to choose
(the permissions design note): the Sponsor has no column and holds the Public's
cells only; the Contributor, which version 1 lacks, has no column either and holds the
Public's cells only; an agent reads no restricted page, its own included, whatever DOSSIER
READ says; the Declarer's "declares" on the Research Assembly's pages is no operation
on the page (Custos writes it; the declaration is an append to the DECLARATIONS
volume).

Enforcement is Custos's permission hook, reading this function compiled.
-/

namespace Principia

/-- `USER` and `AGENT` (TPS 5.13.6): the class an account is declared with at
creation, never both. Custos enforces it: its agent API refuses a user account, and an
agent account holds no web-edit right, cannot sponsor and cannot be certified as a
user. -/
inductive AccountClass where
  /-- `USER`: a human's account. Every role is a user account's. -/
  | user
  /-- `AGENT`: an agent's account, group `pma-agent`. Its lock state is per UWC. -/
  | agent
  deriving DecidableEq, Repr, Inhabited

/-- The six roles (TPS 5.13.1 and the Contributor), each a MediaWiki group: the group
is the role. Every role of TPS 5.13.1 is a user account's ("every H-* role is a USER
account"). A Contributor's account keeps its class, USER or AGENT; an agent account asks
the table in its lock state, as every agent account does (`Actor.agent`). -/
inductive Role where
  /-- `DECLARER` (v1 H-DECL), group `pma-declarer`: the one account allowed on the
  DECLARATIONS volumes. -/
  | declarer
  /-- `OPERATOR` (v1 H-OP), group `pma-operator`: host, configuration, tuning options,
  approvals of falcon patches. -/
  | operator
  /-- `INITIATOR` (v1 H-OWN), group `pma-initiator`: a UWC's creator; holds its access
  list; may request its structure test. -/
  | initiator
  /-- `SPONSOR` (v1 H-SPON), group `pma-sponsor`: a user account that answers for its
  agents. -/
  | sponsor
  /-- `PUBLIC` (v1 ANY), `*`: everyone. The `public` of the table is a Lean keyword, so
  the Lean name is `everyone` (R1). -/
  | everyone
  /-- `CONTRIBUTOR` (no v1 term), group `pma-contributor`: an outside builder, an agent
  or a person, admitted by the Declarer after a probe unit; it holds work units on the
  public channel and nothing on the wiki beyond its account. -/
  | contributor
  deriving DecidableEq, Repr, Inhabited

/-- The two lock states (TPS 5.13.1), per UWC, per agent account,
transient. -/
inductive LockState where
  /-- `HOLDER` (v1 AI-LEAD): the lock holder, the sole allocation authority for the
  UWC's identifier mark, requesting writes of Custos. -/
  | holder
  /-- `COWORKER` (v1 AI-CO): petitions, is assigned, returns. -/
  | coworker
  deriving DecidableEq, Repr, Inhabited

instance : WireWord AccountClass where
  members := [.user, .agent]
  toWire
    | .user => "USER"
    | .agent => "AGENT"
  read_toWire a := by cases a <;> decide

instance : WireWord Role where
  members := [.declarer, .operator, .initiator, .sponsor, .everyone, .contributor]
  toWire
    | .declarer => "DECLARER"
    | .operator => "OPERATOR"
    | .initiator => "INITIATOR"
    | .sponsor => "SPONSOR"
    | .everyone => "PUBLIC"
    | .contributor => "CONTRIBUTOR"
  read_toWire a := by cases a <;> decide

/-- The role's MediaWiki group: the group is the role. The Public is every reader, `*`,
not a group an account is put in. -/
def Role.group : Role → String
  | .declarer => "pma-declarer"
  | .operator => "pma-operator"
  | .initiator => "pma-initiator"
  | .sponsor => "pma-sponsor"
  | .everyone => "*"
  | .contributor => "pma-contributor"

instance : WireWord LockState where
  members := [.holder, .coworker]
  toWire
    | .holder => "HOLDER"
    | .coworker => "COWORKER"
  read_toWire a := by cases a <;> decide

end Principia

namespace Principia.Permissions

open Principia.Parameters (DossierRead)

/-! ## The one asking, the operations, the page classes -/

/-- The one asking: a user account in one of its roles, or an agent account in its
lock state in the page's UWC (`none`: neither Holder nor Coworker there). An account
holding several roles is permitted what any one of them is. -/
inductive Actor where
  /-- A user account acting in a role. -/
  | user (role : Role)
  /-- An agent account, in its lock state in the page's UWC, if it has one. -/
  | agent (lock : Option LockState)
  deriving DecidableEq, Repr, Inhabited

namespace Actor

/-- The account class of the one asking. -/
def accountClass : Actor → AccountClass
  | user _ => .user
  | agent _ => .agent

/-- The role, for a user account. -/
def role? : Actor → Option Role
  | user r => some r
  | agent _ => none

/-- The lock state, for an agent account. -/
def lockState? : Actor → Option LockState
  | user _ => none
  | agent l => l

end Actor

instance : WireWord Actor where
  members := [.user .declarer, .user .operator, .user .initiator, .user .sponsor,
    .user .everyone, .user .contributor, .agent (some .holder), .agent (some .coworker), .agent none]
  toWire
    | .user r => WireWord.toWire r
    | .agent (some l) => WireWord.toWire l
    | .agent none => "AGENT"
  read_toWire a := by
    rcases a with r | l
    · cases r <;> decide
    · rcases l with _ | l
      · decide
      · cases l <;> decide

/-- An operation on a page (TPS 5.13.1's cell letters; the "(TPX)" cells apart). -/
inductive Op where
  /-- `READ` (R). -/
  | read
  /-- `WRITE` (W): the account's own edit. -/
  | write
  /-- `APPEND` (A): the account's own edit, adding only. -/
  | append
  /-- `PROTECT` (P). -/
  | protect
  /-- `WRITE THROUGH CUSTOS` (W (TPX), W via TPX): Custos writes, in the Holder's
  lane; the account itself does not edit the page. -/
  | writeThroughCustos
  /-- `APPEND THROUGH CUSTOS` (A (TPX)). -/
  | appendThroughCustos
  deriving DecidableEq, Repr, Inhabited

instance : WireWord Op where
  members := [.read, .write, .append, .protect, .writeThroughCustos, .appendThroughCustos]
  toWire
    | .read => "READ"
    | .write => "WRITE"
    | .append => "APPEND"
    | .protect => "PROTECT"
    | .writeThroughCustos => "WRITE THROUGH CUSTOS"
    | .appendThroughCustos => "APPEND THROUGH CUSTOS"
  read_toWire a := by cases a <;> decide

/-- The operations that change a page's text: every write and append, the account's
own or through Custos. -/
def Op.changesText : Op → Bool
  | .write | .append | .writeThroughCustos | .appendThroughCustos => true
  | .read | .protect => false

/-- The page classes: the rows of TPS 5.13.2 that name a page, in the table's order,
in PMA's words. -/
inductive PageClass where
  /-- `RESEARCH ASSEMBLY`: the Research Assembly's pages (v1: TFK pages: TPK, TrM
  identification fields, TMS). -/
  | researchAssembly
  /-- `DRAFT UWC`: DRAFT UWC pages. -/
  | draftUwc
  /-- `SPECIFICATION`: instruction artifacts, the Principia Framework Specification
  (v1: TPS). -/
  | specification
  /-- `IMPLEMENTATION`: implementations (index class IMPLEMENTATION). -/
  | implementation
  /-- `CALCULATOR SOURCE`: the Calculator's source pages (v1: TPC-PY source pages,
  plain-text content model). -/
  | calculatorSource
  /-- `ACCESS LIST`: a UWC's access list. -/
  | accessList
  /-- `CANARY FAILURE DETAIL`: restricted. -/
  | canaryFailureDetail
  /-- `SCORE OR USER PAGE`: score pages and user pages, restricted. -/
  | scoreOrUserPage
  /-- `OVERRIDE DETAIL`: override, pad and removal detail pages, restricted. -/
  | overrideDetail
  /-- `PROMPT MANIFEST`: prompt manifests and session-log heads, restricted (v1's
  term, carried unchanged). -/
  | promptManifest
  /-- `CONFIGURATION STRATA`: the configuration strata page, public. -/
  | configurationStrata
  /-- `COMMUNITY LEDGER`: community ledger volumes and community views. -/
  | communityLedger
  /-- `DOSSIER`: dossier pages, public. -/
  | dossier
  /-- `OVERRIDE DECLARATION`: override, pad and removal declarations. -/
  | overrideDeclaration
  /-- `SCORECARD`: the scorecard, the published aggregate. -/
  | scorecard
  /-- `DECLARATIONS VOLUME`: the DECLARATIONS volumes (TPS 5.6.10). -/
  | declarationsVolume
  /-- `BUILD CHAIN VOLUME`: the BUILD CHAIN volumes (TPS 5.6.10). -/
  | buildChainVolume
  /-- `CHAIN HEAD`: the DECLARATIONS and BUILD CHAIN heads; they carry no declaration. -/
  | chainHead
  /-- `DECLARATION OUTSIDE D_IS`: declarations outside D(IS) on the DECLARATIONS page:
  CLUSTER, FALCON KIND, the FALCON SOURCE LIST, REGISTRY and PROVISION (v1: MODULE)
  DECLARATIONS. -/
  | declarationOutsideIs
  /-- `TOP PERFORMER`: top performer pages and their monthly snapshots. -/
  | topPerformer
  /-- `FALCON PAGE`: FALCON PAGES. -/
  | falconPage
  /-- `FALCON LOG`: FALCON LOG volumes. -/
  | falconLog
  /-- `FALCON RESTRICTED`: falcon alias, PRIVATE REPORT and stratum pages,
  restricted. -/
  | falconRestricted
  /-- `PROVISION`: Provision pages, one per declared version (v1: ENVIRONMENT MODULE
  pages). -/
  | provision
  /-- `PROPOSAL`: proposal pages, marked UNTRUSTED PROPOSAL. -/
  | proposal
  /-- `CANDIDATE CERTIFICATE`: the candidate certificate (staging). -/
  | candidateCertificate
  /-- `INDEX AND BADGE`: Index pages and the badge (v1: manifests, badge). -/
  | indexAndBadge
  /-- `SPINE`: spines, structural diagram pages, the references page, Reading pages
  and the hub index. -/
  | spine
  /-- `HUB FRAME`: hub frame text, the general and operator help sets, conceptual
  diagram pages. -/
  | hubFrame
  /-- `AGENT HELP`: the agent-facing help set. -/
  | agentHelp
  /-- `REGISTER OPEN`: register volumes, OPEN. -/
  | registerOpen
  /-- `REGISTER FROZEN`: register volumes, FROZEN. -/
  | registerFrozen
  /-- `BIBLIOGRAPHY OPEN`: bibliography volumes, OPEN. -/
  | bibliographyOpen
  /-- `BIBLIOGRAPHY FROZEN`: bibliography volumes, FROZEN. -/
  | bibliographyFrozen
  /-- `STAGING`: staging subpages. -/
  | staging
  /-- `COLLABORATION`: the collaboration page. -/
  | collaboration
  /-- `LOCK PAGE`: the lock page. -/
  | lockPage
  /-- `CONTROL PANEL`: the control panel, the schedule log and the work-block log. -/
  | controlPanel
  /-- `SYNTHETIC CONTAINER`: the synthetic certification container, suite pages. -/
  | syntheticContainer
  /-- `RETIRED CONTAINER`: a retired container, all pages. -/
  | retiredContainer
  deriving DecidableEq, Repr, Inhabited

instance : WireWord PageClass where
  members := [.researchAssembly, .draftUwc, .specification, .implementation,
    .calculatorSource, .accessList, .canaryFailureDetail, .scoreOrUserPage,
    .overrideDetail, .promptManifest, .configurationStrata, .communityLedger, .dossier,
    .overrideDeclaration, .scorecard, .declarationsVolume, .buildChainVolume, .chainHead,
    .declarationOutsideIs, .topPerformer, .falconPage, .falconLog, .falconRestricted,
    .provision, .proposal, .candidateCertificate, .indexAndBadge, .spine, .hubFrame,
    .agentHelp, .registerOpen, .registerFrozen, .bibliographyOpen, .bibliographyFrozen,
    .staging, .collaboration, .lockPage, .controlPanel, .syntheticContainer,
    .retiredContainer]
  toWire
    | .researchAssembly => "RESEARCH ASSEMBLY"
    | .draftUwc => "DRAFT UWC"
    | .specification => "SPECIFICATION"
    | .implementation => "IMPLEMENTATION"
    | .calculatorSource => "CALCULATOR SOURCE"
    | .accessList => "ACCESS LIST"
    | .canaryFailureDetail => "CANARY FAILURE DETAIL"
    | .scoreOrUserPage => "SCORE OR USER PAGE"
    | .overrideDetail => "OVERRIDE DETAIL"
    | .promptManifest => "PROMPT MANIFEST"
    | .configurationStrata => "CONFIGURATION STRATA"
    | .communityLedger => "COMMUNITY LEDGER"
    | .dossier => "DOSSIER"
    | .overrideDeclaration => "OVERRIDE DECLARATION"
    | .scorecard => "SCORECARD"
    | .declarationsVolume => "DECLARATIONS VOLUME"
    | .buildChainVolume => "BUILD CHAIN VOLUME"
    | .chainHead => "CHAIN HEAD"
    | .declarationOutsideIs => "DECLARATION OUTSIDE D_IS"
    | .topPerformer => "TOP PERFORMER"
    | .falconPage => "FALCON PAGE"
    | .falconLog => "FALCON LOG"
    | .falconRestricted => "FALCON RESTRICTED"
    | .provision => "PROVISION"
    | .proposal => "PROPOSAL"
    | .candidateCertificate => "CANDIDATE CERTIFICATE"
    | .indexAndBadge => "INDEX AND BADGE"
    | .spine => "SPINE"
    | .hubFrame => "HUB FRAME"
    | .agentHelp => "AGENT HELP"
    | .registerOpen => "REGISTER OPEN"
    | .registerFrozen => "REGISTER FROZEN"
    | .bibliographyOpen => "BIBLIOGRAPHY OPEN"
    | .bibliographyFrozen => "BIBLIOGRAPHY FROZEN"
    | .staging => "STAGING"
    | .collaboration => "COLLABORATION"
    | .lockPage => "LOCK PAGE"
    | .controlPanel => "CONTROL PANEL"
    | .syntheticContainer => "SYNTHETIC CONTAINER"
    | .retiredContainer => "RETIRED CONTAINER"
  read_toWire a := by cases a <;> decide

/-- DOSSIER READ's wire words (TPS 7.2.20: USER ONLY | USER AND AGENT | NEITHER), for
the context of a request. -/
instance : WireWord DossierRead where
  members := [.userOnly, .userAndAgent, .neither]
  toWire
    | .userOnly => "USER ONLY"
    | .userAndAgent => "USER AND AGENT"
    | .neither => "NEITHER"
  read_toWire a := by cases a <;> decide

/-- ACCESS POLICY (TPS 5.16.1): OPEN or CLOSED, per UWC, declared in UWC STATE. The
policy gates write and never read (5.16.4). -/
inductive AccessPolicy where
  /-- `OPEN`: any account in the agent group may work the UWC (5.16.2). (`open` is a
  Lean keyword: R1.) -/
  | openAccess
  /-- `CLOSED`: only accounts on its ACCESS LIST may (5.16.3). -/
  | closedAccess
  deriving DecidableEq, Repr, Inhabited

instance : WireWord AccessPolicy where
  members := [.openAccess, .closedAccess]
  toWire
    | .openAccess => "OPEN"
    | .closedAccess => "CLOSED"
  read_toWire a := by cases a <;> decide

/-- What Custos knows of the page and the asker beyond the role: the facts the table's
conditions read. Every field's default is the refusing one. -/
structure PageContext where
  /-- The ACCESS POLICY of the UWC the page belongs to; `none` for a page of no UWC. -/
  policy : Option AccessPolicy := none
  /-- The asker is on that UWC's ACCESS LIST. -/
  onAccessList : Bool := false
  /-- `some d` when the page's title names the asker's own account, `d` being the
  DOSSIER READ in force for that account (TPS 5.18.10, 7.2.20). -/
  namedAccount : Option DossierRead := none
  /-- The asker's petition heads the lock queue, inside its window (TPS 5.7). -/
  atQueueHead : Bool := false
  /-- The session is two-factor and re-authenticated at submission (TPS 5.13.3,
  5.13.6). -/
  reauthenticated : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-! ## The table -/

/-- The table's six columns (TPS 5.13.2). The Sponsor has none. -/
inductive Column where
  /-- H-DECL -/
  | declarer
  /-- H-OP -/
  | operator
  /-- H-OWN -/
  | initiator
  /-- AI-LEAD -/
  | holder
  /-- AI-CO -/
  | coworker
  /-- ANY -/
  | everyone
  deriving DecidableEq, Repr, Inhabited

open Op in
/-- The Public's cell (ANY), row by row. -/
def publicCell : PageClass → List Op
  | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail | .promptManifest
  | .falconRestricted => []
  | _ => [read]

open Op in
/-- The Initiator's cell (H-OWN) where the row states one; `none` where it omits it. -/
def initiatorStated : PageClass → Option (List Op)
  | .accessList => some [write]
  | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail | .promptManifest => some []
  | .configurationStrata | .communityLedger | .dossier | .overrideDeclaration => some []
  | .scorecard => some []
  | .declarationOutsideIs => some [read]
  | .topPerformer | .falconPage | .falconLog | .falconRestricted | .provision
  | .proposal | .bibliographyOpen | .bibliographyFrozen => some []
  | _ => none

open Op in
/-- The table's cell for a column and a page class: the operations it grants, before
any condition. The Initiator's omitted cells follow 5.13.2's last paragraph. -/
def cell : Column → PageClass → List Op
  | .everyone, c => publicCell c
  | .initiator, c =>
    (initiatorStated c).getD (if publicCell c = [read] then [read] else [])
  -- H-DECL
  | .declarer, c =>
    match c with
    -- "declares; TPX writes from the certified draft at instantiation, ...; then
    -- immutable": no operation on the page (the declaration is an append to the
    -- DECLARATIONS volume).
    | .researchAssembly => []
    | .draftUwc => [read]
    | .specification | .implementation | .calculatorSource => [write]
    | .accessList | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail
    | .promptManifest => [read]
    | .configurationStrata | .communityLedger | .dossier => []
    -- "A, in the prime-override group, two-factor and re-authenticated"
    | .overrideDeclaration => [append]
    | .scorecard => [read]
    | .declarationsVolume => [append]
    | .buildChainVolume | .chainHead => []
    | .declarationOutsideIs => [append]
    | .topPerformer => []
    | .falconPage => [read]
    | .falconLog => []
    | .falconRestricted | .provision | .proposal | .candidateCertificate => [read]
    | .indexAndBadge | .spine | .hubFrame => []
    | .agentHelp => [write]
    | .registerOpen | .registerFrozen | .bibliographyOpen | .bibliographyFrozen
    | .staging | .collaboration | .lockPage | .controlPanel => []
    | .syntheticContainer => [write]
    | .retiredContainer => []
  -- H-OP
  | .operator, c =>
    match c with
    | .draftUwc => [write]
    | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail | .promptManifest
    | .falconRestricted => [read, protect]
    | .candidateCertificate => []
    | .hubFrame => [write]
    | .agentHelp => [write, protect]
    -- "W clear, with an audit line"
    | .lockPage => [write]
    | .syntheticContainer => [write, protect]
    | _ => [protect]
  -- AI-LEAD
  | .holder, c =>
    match c with
    | .researchAssembly => [read]
    -- "W own draft" (GR + AU on ownership)
    | .draftUwc => [write]
    | .specification | .implementation | .calculatorSource | .accessList => [read]
    | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail | .promptManifest => []
    | .configurationStrata | .communityLedger | .dossier => [writeThroughCustos]
    | .overrideDeclaration => []
    | .scorecard => [writeThroughCustos]
    | .declarationsVolume => [read]
    | .buildChainVolume => [appendThroughCustos]
    | .chainHead => [writeThroughCustos]
    | .declarationOutsideIs => [read]
    | .topPerformer | .falconPage => [writeThroughCustos]
    | .falconLog => [appendThroughCustos]
    | .falconRestricted | .provision | .proposal | .candidateCertificate
    | .indexAndBadge | .spine => [writeThroughCustos]
    -- "draft to staging": no operation here; the draft is a staging subpage
    | .hubFrame => []
    | .agentHelp => [read]
    | .registerOpen => [write]
    | .registerFrozen => [read]
    -- "W via TPX (OPEN), R (FROZEN)"
    | .bibliographyOpen => [writeThroughCustos]
    | .bibliographyFrozen => [read]
    | .staging => [read, write]
    -- "W assignments" (GR + AU row ownership)
    | .collaboration => [write]
    | .lockPage => [write]
    | .controlPanel => [write, append]
    | .syntheticContainer | .retiredContainer => [read]
  -- AI-CO
  | .coworker, c =>
    match c with
    | .researchAssembly => [read]
    -- "W own draft"
    | .draftUwc => [write]
    | .specification | .implementation | .calculatorSource | .accessList => [read]
    | .declarationsVolume | .declarationOutsideIs | .agentHelp | .registerFrozen => [read]
    -- v1's "W own page" is gone: Custos writes the Coworker's return on the staging
    -- subpage and the Coworker never writes it itself. The cell grants nothing.
    | .staging => []
    -- "A own petition row" (GR + AU row ownership)
    | .collaboration => [append]
    -- "W when head, in window" (GR + EC + SC): `atQueueHead`
    | .lockPage => [write]
    | .controlPanel => [read]
    -- "R (candidate works it under supervision)"
    | .syntheticContainer | .retiredContainer => [read]
    | _ => []

/-- The restricted class (TPS 5.18.10): the namespace of its own whose pages the
Public does not read. -/
def PageClass.restricted : PageClass → Bool
  | .canaryFailureDetail | .scoreOrUserPage | .overrideDetail | .promptManifest
  | .falconRestricted => true
  | _ => false

/-- The restricted rows that add "the account named by the page title when that user's
DOSSIER READ allows": the score and user pages, and the two rows "as the score pages". -/
def PageClass.dossierReadable : PageClass → Bool
  | .scoreOrUserPage | .overrideDetail | .promptManifest => true
  | _ => false

/-- The page classes that carry a declaration: the DECLARATIONS volumes, the
declarations outside D(IS) on the DECLARATIONS page, and the override, pad and removal
declarations (TPS 5.13.3: "No agent writes on any page carrying a declaration"). The
chain heads carry none (5.13.2). -/
def PageClass.carriesDeclaration : PageClass → Bool
  | .declarationsVolume | .declarationOutsideIs | .overrideDeclaration => true
  | _ => false

/-- The asker's column: none for the Sponsor and the Contributor, and none for an agent that is neither
Holder nor Coworker in the page's UWC. -/
def Actor.column? : Actor → Option Column
  | .user .declarer => some .declarer
  | .user .operator => some .operator
  | .user .initiator => some .initiator
  | .user .sponsor => none
  | .user .contributor => none
  | .user .everyone => some .everyone
  | .agent (some .holder) => some .holder
  | .agent (some .coworker) => some .coworker
  | .agent none => none

/-- What the table grants the asker on a page class: its own column's cell and the
Public's. -/
def granted (a : Actor) (c : PageClass) : List Op :=
  (match a.column? with
    | some col => cell col c
    | none => []) ++ cell .everyone c

/-- The CLOSED PREDICATE (TPS 5.13.4): in a CLOSED UWC every write or append of an
agent account, its own or through Custos, also needs the asker on the UWC's ACCESS
LIST. Read cells are unchanged in both policies. -/
def closedPredicate : Actor → Option AccessPolicy → Bool → Op → Bool
  | .agent _, some .closedAccess, listed, op => !op.changesText || listed
  | _, _, _, _ => true

/-- The two conditions a cell carries that the server check enforces: the Coworker
writes the lock page only at the head of the queue, inside its window (5.7); the
override, pad and removal declarations are appended only two-factor and
re-authenticated (5.13.2, 5.13.3). -/
def cellCondition (a : Actor) (c : PageClass) (op : Op) (ctx : PageContext) : Bool :=
  if a = .agent (some .coworker) ∧ c = .lockPage ∧ op = .write then ctx.atQueueHead
  else if c = .overrideDeclaration ∧ op = .append then ctx.reauthenticated
  else true

/-- Whether DOSSIER READ admits the account its page names: a user account under USER
ONLY or USER AND AGENT. An agent account is admitted under none (decision item:
5.13.7 "No agent reads the restricted class" against the table's and 5.18.10's agent
read under USER AND AGENT). -/
def dossierAdmits : AccountClass → Option DossierRead → Bool
  | .user, some .userOnly => true
  | .user, some .userAndAgent => true
  | _, _ => false

/-- DOSSIER READ's addition (TPS 5.13.2, 5.18.10): the read of a restricted score,
user, override-detail or prompt page by the account its title names, when DOSSIER READ
admits it. -/
def dossierGrant (a : Actor) (c : PageClass) (op : Op) (ctx : PageContext) : Bool :=
  op == .read && c.dossierReadable && dossierAdmits a.accountClass ctx.namedAccount

/-- `permits`: whether the asker may perform the operation on a page of the class,
given what Custos knows of the page. The table's cell, its conditions, and
DOSSIER READ's addition. -/
def permits (a : Actor) (c : PageClass) (op : Op) (ctx : PageContext) : Bool :=
  (decide (op ∈ granted a c) && closedPredicate a ctx.policy ctx.onAccessList op &&
    cellCondition a c op ctx) || dossierGrant a c op ctx

/-! ## Facts of the table, by evaluation over every member -/

/-- Every asker, every page class, every operation. -/
abbrev actors : List Actor := WireWord.members
abbrev classes : List PageClass := WireWord.members
abbrev ops : List Op := WireWord.members

/-- The agent askers. -/
def agentLocks : List (Option LockState) := [none, some .holder, some .coworker]

theorem mem_agentLocks (l : Option LockState) : l ∈ agentLocks := by
  rcases l with _ | l
  · simp [agentLocks]
  · cases l <;> simp [agentLocks]

/-- The classes carrying a declaration, listed. -/
theorem carriesDeclaration_mem {c : PageClass} (h : c.carriesDeclaration = true) :
    c ∈ [PageClass.declarationsVolume, .declarationOutsideIs, .overrideDeclaration] := by
  cases c <;> simp_all [PageClass.carriesDeclaration]

/-- The restricted classes, listed. -/
theorem restricted_mem {c : PageClass} (h : c.restricted = true) :
    c ∈ [PageClass.canaryFailureDetail, .scoreOrUserPage, .overrideDetail,
      .promptManifest, .falconRestricted] := by
  cases c <;> simp_all [PageClass.restricted]

/-- In the table, only the Declarer's cell changes the text of a class carrying a
declaration. -/
theorem table_declarations :
    ∀ a ∈ actors, ∀ c ∈ [PageClass.declarationsVolume, .declarationOutsideIs,
      .overrideDeclaration], ∀ op ∈ ops, op.changesText = true → op ∈ granted a c →
      a = .user .declarer := by
  decide

/-- In the table, an agent's cells on a class carrying a declaration hold reads only. -/
theorem table_agent_declarations :
    ∀ l ∈ agentLocks, ∀ c ∈ [PageClass.declarationsVolume, .declarationOutsideIs,
      .overrideDeclaration], ∀ op ∈ ops, op ∈ granted (.agent l) c → op = .read := by
  decide

/-- In the table, a restricted class is read by the Declarer's and the Operator's cells
only. -/
theorem table_restricted :
    ∀ a ∈ actors, ∀ c ∈ [PageClass.canaryFailureDetail, .scoreOrUserPage,
      .overrideDetail, .promptManifest, .falconRestricted],
      Op.read ∈ granted a c → a = .user .declarer ∨ a = .user .operator := by
  decide

/-- In the table, no agent's cell protects. -/
theorem table_agent_protect :
    ∀ l ∈ agentLocks, ∀ c ∈ classes, Op.protect ∉ granted (.agent l) c := by
  decide

/-- In the table, the Public reads every class but the restricted ones. -/
theorem table_public_read :
    ∀ c ∈ classes, c.restricted = false → Op.read ∈ cell .everyone c := by
  decide

/-- In the table, the Initiator's cell changes the text of the access list only. -/
theorem table_initiator :
    ∀ c ∈ classes, ∀ op ∈ ops, op.changesText = true →
      op ∈ granted (.user .initiator) c → c = .accessList := by
  decide

/-- In the table, an agent's own writes and appends (not through Custos) fall on the
agent-writable classes only (TPS 5.13.3). -/
theorem table_agent_direct :
    ∀ l ∈ agentLocks, ∀ c ∈ classes, ∀ op ∈ [Op.write, .append], op ∈ granted (.agent l) c →
      c = .draftUwc ∨ c = .registerOpen ∨ c = .staging ∨ c = .collaboration ∨
        c = .lockPage ∨ c = .controlPanel := by
  decide

/-- DOSSIER READ's addition grants a read only. -/
theorem dossierGrant_read {a : Actor} {c : PageClass} {op : Op} {ctx : PageContext}
    (h : dossierGrant a c op ctx = true) : op = .read := by
  simp only [dossierGrant, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- What DOSSIER READ's addition needs: a user account named, under a setting other
than NEITHER, on a class that admits it. -/
theorem dossierGrant_spec {a : Actor} {c : PageClass} {op : Op} {ctx : PageContext}
    (h : dossierGrant a c op ctx = true) :
    a.accountClass = .user ∧ c.dossierReadable = true ∧
      ∃ d, ctx.namedAccount = some d ∧ d ≠ .neither := by
  simp only [dossierGrant, Bool.and_eq_true] at h
  obtain ⟨⟨_, hc⟩, hd⟩ := h
  refine ⟨?_, hc, ?_⟩
  · revert hd; generalize a.accountClass = k; generalize ctx.namedAccount = n
    cases k <;> rcases n with _ | d <;> (try cases d) <;> simp [dossierAdmits]
  · revert hd; generalize a.accountClass = k; generalize ctx.namedAccount = n
    cases k <;> rcases n with _ | d <;> (try cases d) <;> simp [dossierAdmits]

/-- A permitted operation that is not a read is a granted cell. -/
theorem granted_of_permits {a : Actor} {c : PageClass} {op : Op} {ctx : PageContext}
    (h : permits a c op ctx = true) (hop : op ≠ .read) : op ∈ granted a c := by
  simp only [permits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hg, _⟩, _⟩ | hd
  · exact hg
  · exact absurd (dossierGrant_read hd) hop

/-! ## The theorems of the table -/

/-- Only the Declarer appends to the DECLARATIONS volumes. -/
theorem only_declarer_appends_declarations (a : Actor) (ctx : PageContext)
    (h : permits a .declarationsVolume .append ctx = true) : a = .user .declarer :=
  table_declarations a (WireWord.mem_members a) .declarationsVolume (by simp) .append
    (WireWord.mem_members _) rfl (granted_of_permits h (by decide))

/-- More: on every class carrying a declaration, only the Declarer changes the text,
by any operation. -/
theorem only_declarer_changes_declarations (a : Actor) (c : PageClass) (op : Op)
    (ctx : PageContext) (hc : c.carriesDeclaration = true) (hop : op.changesText = true)
    (h : permits a c op ctx = true) : a = .user .declarer :=
  table_declarations a (WireWord.mem_members a) c (carriesDeclaration_mem hc) op
    (WireWord.mem_members op) hop
    (granted_of_permits h (by intro e; subst e; simp [Op.changesText] at hop))

/-- No agent writes any page carrying a declaration (TPS 5.13.3): on those
classes an agent account may only read. -/
theorem agent_never_writes_declarations (l : Option LockState) (c : PageClass) (op : Op)
    (ctx : PageContext) (hc : c.carriesDeclaration = true) (hop : op ≠ .read) :
    permits (.agent l) c op ctx = false := by
  cases h : permits (.agent l) c op ctx
  · rfl
  · exact absurd (table_agent_declarations l (mem_agentLocks l) c (carriesDeclaration_mem hc)
      op (WireWord.mem_members op) (granted_of_permits h hop)) hop

/-- The restricted namespace is readable only by the Declarer and the Operator, and by
a user account the page's title names, on a class that admits it, when its DOSSIER READ
is not NEITHER (TPS 5.18.10). -/
theorem restricted_read (a : Actor) (c : PageClass) (ctx : PageContext)
    (hc : c.restricted = true) (h : permits a c .read ctx = true) :
    a = .user .declarer ∨ a = .user .operator ∨
      (a.accountClass = .user ∧ c.dossierReadable = true ∧
        ∃ d, ctx.namedAccount = some d ∧ d ≠ .neither) := by
  simp only [permits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hg, _⟩, _⟩ | hd
  · rcases table_restricted a (WireWord.mem_members a) c (restricted_mem hc) hg with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inr (.inr (dossierGrant_spec hd))

/-- Every agent write under a CLOSED access policy requires access-list membership
(TPS 5.13.4, 5.16.3): any write or append, its own or through Custos. -/
theorem closed_requires_access_list (l : Option LockState) (c : PageClass) (op : Op)
    (ctx : PageContext) (hop : op.changesText = true)
    (hp : ctx.policy = some .closedAccess) (h : permits (.agent l) c op ctx = true) :
    ctx.onAccessList = true := by
  have hr : op ≠ .read := by intro e; subst e; simp [Op.changesText] at hop
  simp only [permits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨_, hcl⟩, _⟩⟩ | hd
  · simpa [closedPredicate, hp, hop] using hcl
  · exact absurd (dossierGrant_read hd) hr

/-! ## The account classes and the roles -/

/-- Every role is a user account's: in particular an agent account is never a Sponsor
(TPS 5.13.6: an agent "cannot sponsor"). -/
theorem role_is_user (a : Actor) (r : Role) (h : a.role? = some r) :
    a.accountClass = .user := by
  cases a <;> simp_all [Actor.role?, Actor.accountClass]

/-- A lock state is an agent account's (TPS 5.13.1: every AI-* role is an AGENT). -/
theorem lockState_is_agent (a : Actor) (l : LockState) (h : a.lockState? = some l) :
    a.accountClass = .agent := by
  cases a <;> simp_all [Actor.lockState?, Actor.accountClass]

/-- No agent protects a page (TPS 5.13.3: the agent group has no protect). -/
theorem agent_never_protects (l : Option LockState) (c : PageClass) (ctx : PageContext) :
    permits (.agent l) c .protect ctx = false := by
  cases h : permits (.agent l) c .protect ctx
  · rfl
  · exact absurd (granted_of_permits h (by decide))
      (table_agent_protect l (mem_agentLocks l) c (WireWord.mem_members c))

/-- Read is public everywhere but the restricted namespace: whatever the
asker and whatever Custos knows of the page. -/
theorem read_public (a : Actor) (c : PageClass) (ctx : PageContext)
    (hc : c.restricted = false) : permits a c .read ctx = true := by
  have hr : Op.read ∈ granted a c :=
    List.mem_append_right _ (table_public_read c (WireWord.mem_members c) hc)
  have hcl : closedPredicate a ctx.policy ctx.onAccessList .read = true := by
    unfold closedPredicate; split <;> simp [Op.changesText]
  have hcc : cellCondition a c .read ctx = true := by simp [cellCondition]
  simp [permits, hr, hcl, hcc]

/-- The restricted class is exactly the rows the Public does not read. -/
theorem restricted_iff (c : PageClass) :
    c.restricted = true ↔ Op.read ∉ cell .everyone c := by
  cases c <;> simp [PageClass.restricted, cell, publicCell]

/-- The access policy and the access list gate write and never read (TPS 5.16.4). -/
theorem read_independent_of_policy (a : Actor) (c : PageClass) (ctx : PageContext)
    (p : Option AccessPolicy) (m : Bool) :
    permits a c .read { ctx with policy := p, onAccessList := m } =
      permits a c .read ctx := by
  have h1 : ∀ q n, closedPredicate a q n .read = true := by
    intro q n; unfold closedPredicate; split <;> simp [Op.changesText]
  simp [permits, h1, cellCondition, dossierGrant]

/-- The Initiator changes the text of the access list only (TPS 5.13.2: H-OWN "writes
only the access list"). -/
theorem initiator_writes_only_access_list (c : PageClass) (op : Op) (ctx : PageContext)
    (hop : op.changesText = true) (h : permits (.user .initiator) c op ctx = true) :
    c = .accessList :=
  table_initiator c (WireWord.mem_members c) op (WireWord.mem_members op) hop
    (granted_of_permits h (by intro e; subst e; simp [Op.changesText] at hop))

/-- The Sponsor, with no column in the table, is permitted exactly what the Public is
(decision item: the table states no Sponsor cell). -/
theorem sponsor_as_public (c : PageClass) (op : Op) (ctx : PageContext) :
    permits (.user .sponsor) c op ctx = permits (.user .everyone) c op ctx := by
  have hm : (op ∈ granted (.user .sponsor) c) ↔ (op ∈ granted (.user .everyone) c) := by
    simp [granted, Actor.column?]
  simp [permits, hm, closedPredicate, cellCondition, dossierGrant, Actor.accountClass]

/-- The Contributor, with no column in the table, is permitted exactly what the Public
is: it holds nothing on the wiki beyond its account. -/
theorem contributor_as_public (c : PageClass) (op : Op) (ctx : PageContext) :
    permits (.user .contributor) c op ctx = permits (.user .everyone) c op ctx := by
  have hm : (op ∈ granted (.user .contributor) c) ↔ (op ∈ granted (.user .everyone) c) := by
    simp [granted, Actor.column?]
  simp [permits, hm, closedPredicate, cellCondition, dossierGrant, Actor.accountClass]

/-- An agent edits a page itself (a write or append of its own, not through Custos)
only on the agent-writable classes (TPS 5.13.3): DRAFT UWC pages, OPEN register
volumes, staging subpages, the collaboration page, the lock page and the control
panel. -/
theorem agent_direct_edits (l : Option LockState) (c : PageClass) (op : Op)
    (ctx : PageContext) (hop : op = .write ∨ op = .append)
    (h : permits (.agent l) c op ctx = true) :
    c = .draftUwc ∨ c = .registerOpen ∨ c = .staging ∨ c = .collaboration ∨
      c = .lockPage ∨ c = .controlPanel :=
  table_agent_direct l (mem_agentLocks l) c (WireWord.mem_members c) op
    (by rcases hop with rfl | rfl <;> simp)
    (granted_of_permits h (by rcases hop with rfl | rfl <;> decide))

/-- A Coworker never writes or appends to a staging subpage itself, whatever Custos
knows of the page: its cell on STAGING is empty, and Custos writes the Coworker's return
there. -/
theorem coworker_never_writes_staging (op : Op) (ctx : PageContext)
    (hop : op = .write ∨ op = .append) :
    permits (.agent (some .coworker)) .staging op ctx = false := by
  rcases hop with rfl | rfl <;>
    simp [permits, granted, cell, publicCell, Actor.column?, dossierGrant]

/-! ## A request on the command line -/

/-- One request to `pcalc permits`: who asks, the page class, the operation, and what
Custos knows of the page. -/
structure Request where
  /-- Who asks. -/
  actor : Actor
  /-- The page's class. -/
  pageClass : PageClass
  /-- The operation asked. -/
  op : Op
  /-- What Custos knows of the page and the asker. -/
  context : PageContext
  deriving DecidableEq, Repr

/-- Read the context words after the operation, each setting one field: `OPEN` or
`CLOSED` (the UWC's policy), `LISTED` (on its access list), `NAMED` and a DOSSIER READ
word (the title names the asker), `QUEUE HEAD`, `REAUTHENTICATED`. Any other word, or
`NAMED` without a DOSSIER READ word, reads as nothing. -/
def readContext : List String → PageContext → Option PageContext
  | [], ctx => some ctx
  | "OPEN" :: rest, ctx => readContext rest { ctx with policy := some .openAccess }
  | "CLOSED" :: rest, ctx => readContext rest { ctx with policy := some .closedAccess }
  | "LISTED" :: rest, ctx => readContext rest { ctx with onAccessList := true }
  | "NAMED" :: d :: rest, ctx =>
    match (WireWord.ofWire? d : Option DossierRead) with
    | some d => readContext rest { ctx with namedAccount := some d }
    | none => none
  | "QUEUE HEAD" :: rest, ctx => readContext rest { ctx with atQueueHead := true }
  | "REAUTHENTICATED" :: rest, ctx => readContext rest { ctx with reauthenticated := true }
  | _, _ => none

/-- Read a request from its words: the asker (`DECLARER`, `OPERATOR`, `INITIATOR`,
`SPONSOR`, `PUBLIC`, `CONTRIBUTOR`, `HOLDER`, `COWORKER`, or `AGENT` for an agent in no lock state),
the page class, the operation, then the context words. -/
def Request.parse? : List String → Option Request
  | a :: c :: o :: rest => do
    let actor ← WireWord.ofWire? a
    let pageClass ← WireWord.ofWire? c
    let op ← WireWord.ofWire? o
    let context ← readContext rest {}
    pure { actor, pageClass, op, context }
  | _ => none

/-- The answer to a request: `PERMITTED` or `REFUSED`. -/
def Request.answer (r : Request) : String :=
  if permits r.actor r.pageClass r.op r.context then "PERMITTED" else "REFUSED"

end Principia.Permissions
