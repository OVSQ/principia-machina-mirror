---
name: README
version: 0.3.0
date: 2026-10-24
status: |
  Custos (Phase 3): the extension's skeleton, the store seam, the call into the Calculator
  with the binary's residence and digest checked, the page classes and blocks, and the API
  module's seven ops (the four of the live-exercise path and the governor's STATUS, INQUIRE
  and HEARTBEAT), each write writing a ticket whose work is the job's; the page writer, the
  three page texts of the path, the permission hook and the seed script; the landing job
  (admission, the Calculator's checks, the record written, the ticket answered); the
  governor's meter, the budget roll-up and the PRE-GATE; a harness that runs without the host.
---

# Custos

Custos is Principia Machina's gatekeeper on the wiki: a thin MediaWiki extension (charter
section 8.3) that keeps in PHP only what MediaWiki forces there (hooks, the API module, the job
queue, page writes) and asks the Calculator, `pcalc`, for everything that is computed. It is
the successor of version 1's TPX, written anew: version 1's seams were read, no
line was copied.

MediaWiki 1.46 or later; PHP 8.3 or later (the host runs 8.4) with the `posix` extension.

## What this unit holds

| Path | What it is |
|---|---|
| `extension.json` | the extension's registration: name Custos, `Custos\` autoloaded from `includes/`, the API module `pma`, the job class `custosLand`, the schema hook, the group `pma-agent` with the right `custos-landing`, the groups `pma-declarer` and `pma-operator` each with only the marker right `custos-role` (it grants no action and nothing checks it; the groups exist on the wiki by it, and the permission hook, which reads groups and never a right, is their only enforcement), the configuration below |
| `includes/PageStore.php` | the store seam: `get`, `exists`, `put`, `casPut`, `appendAs` |
| `includes/MwStore.php` | the live store over MediaWiki's services; Custos's own writes are the system user "Custos"'s |
| `includes/Calculator.php` | `call(family, function, json)`: `pcalc <family> <function>` with the request on stdin, the binary's residence checked once per request cycle, then its SHA-256 digest checked against `CustosBuild` before every start, `pcalc version` read once per request cycle |
| `includes/Residence.php`, `ResidenceCheck.php` | the residence check (below); `ResidenceCheck` is the live one |
| `includes/BoxedRunner.php`, `ShellRunner.php` | the start of the binary through MediaWiki's shell framework, boxed, network disabled, firejail's default seccomp filter where firejail is the restriction method |
| `includes/UnsafeResidence.php`, `DigestMismatch.php`, `CalculatorFault.php` | the three refusals: a user other than root could change the binary (never started); the binary is not the expected one (never started); no call could be made or the answer is outside pcalc's protocol |
| `includes/PageClass.php` | the 40 page classes of the permissions table by their wire words, in `Principia/Permissions.lean`'s order; the five restricted ones |
| `includes/PageTitles.php`, `PageRef.php` | every page title Custos writes, built from the two page roots, and `classify`, which reads a title back as its page class and parts (below) |
| `includes/Blocks.php`, `PageFault.php` | the content model: a page's machine text in named preformatted blocks, written and read; what would make a block ambiguous is refused |
| `includes/Ops.php`, `Refusal.php` | the ops PETITION, PUSH, RELEASE and POLL (below), plain PHP without MediaWiki; a refusal's code, opening `custos-`, and `scrub`, which strips every path from a message |
| `includes/ApiPma.php` | `action=pma`, thin glue over `Ops`: the parameters as received, the account the authenticated one, the group `pma-agent` and a CSRF token for a write, HTTP 202 on a queued ticket |
| `includes/TicketStore.php`, `DbTicketStore.php` | the ticket seam (`create`, `get`, `answer`, `claimNext`, `claim` by id, `inWork`, `count` in a state) and the live store over MediaWiki's database |
| `includes/SeatStore.php`, `DbSeatStore.php` | the seat seam (`get`, `put` of an account's agent or sponsor bucket, `[level, since]`; `charge`, both buckets in one write, both rows or neither; `lock`, `unlock` of the account's seat lock) and the live store over the table `custos_seat` and the database's named lock |
| `includes/SchemaHooks.php`, `sql/custos_ticket.json`, `sql/custos_seat.json`, `sql/sqlite/custos_ticket.sql`, `sql/sqlite/custos_seat.sql`, `sql/mysql/custos_ticket.sql`, `sql/mysql/custos_seat.sql` | the tables `custos_ticket`, `custos_seat`, `custos_nonce`, `custos_meter`, `custos_budget` and `custos_traffic` (below; `SchemaHooks::TABLES`): each table's own abstract schema its one source, its SQL written from it by `maintenance/run.php generateSchemaSql`, one file per table per database type; the hook `LoadExtensionSchemaUpdates` registers each table by its own name with its own SQL, so `update.php` adds whichever a wiki lacks |
| `includes/NonceStore.php`, `DbNonceStore.php`, `MemNonceStore.php`, `sql/custos_nonce.json`, `sql/sqlite/custos_nonce.sql`, `sql/mysql/custos_nonce.sql` | the execution challenge's nonces (below): the seam (`put` of an account's nonce on a UWC, `take`, which removes it), the live store over the table `custos_nonce`, and one object's memory, the default of a `Landing` named no store |
| `includes/Challenge.php` | the execution challenge (TPS 5.3.19, version 1's form): `preimage`, `response` and `verify` over `pcalc digest preimage_fields` and `digest_fields` of `["TPC-EXECUTION-CHALLENGE", "1", nonce]`; the nonce's and the response's forms checked in PHP, no digest computed there |
| `includes/PageWriter.php` | one landing's page writes, batched: `begin`, `put`, `read`, `commit`; each page saved once through `casPut` against the text the landing read, the INDEX AND BADGE page last (below) |
| `includes/PageTexts.php` | the three page texts of the path in the block form: the lock, a register volume, the index and badge; each read back as its payload, whole |
| `includes/PermissionHook.php` | the hook `getUserPermissionsErrors`: the fence around the governed pages (below) |
| `includes/RestrictedRoutes.php` | the routes around the fence: transclusion, search, export, the API's results, the change and title lists and the link tables closed for the restricted pages (below, "Restricted routes") |
| `includes/Meter.php`, `lanes.json` | the governor's meter (below): GA0 on `BeforeInitialize` and `ApiBeforeMain`, GA9 on `ApiAfterExecute` and a shutdown function, one row per governed request; `lanes.json` the lane of each governed kind, `pcalc governor lane`'s table (the harness checks it against the built `pcalc`) |
| `includes/MeterStore.php`, `DbMeterStore.php`, `MemMeterStore.php`, `sql/custos_meter.json`, `sql/custos_budget.json`, `sql/custos_traffic.json`, their SQL under `sql/sqlite/` and `sql/mysql/` | the meter's seam and its stores: the rows (`custos_meter`), the roll-up per horizon with the pressure level (`custos_budget`), each account's traffic record as the Calculator's text and its stage (`custos_traffic`) |
| `includes/StructureTestJob.php` | the job class `custosStructureTest`: the structure test with register of one UWC, pushed after every PUSH that lands (below) |
| `includes/Budget.php`, `BudgetJob.php` | the budget roll-up, plain PHP without MediaWiki, and the job class `custosBudget` that runs it (below) |
| `pregate.php` | the PRE-GATE, run before MediaWiki loads (below); its wiring is the Operator's |
| `maintenance/SeedUwc.php` | `php maintenance/run.php Custos:SeedUwc --prefix <p> --draft <file>`: a new UWC's seven pages in one landing, the Operator's act |
| `includes/Landing.php`, `LandRefused.php` | the landing job's work on one ticket, plain PHP without MediaWiki (below); a refusal's word and the members its answer adds |
| `includes/LandJob.php`, `JobContext.php` | the job class `custosLand`, enqueued with each ticket's id: the job's context checked, then `Landing` over the ticket; not retried |
| `includes/CertificateStore.php`, `DbCertificateStore.php`, `sql/custos_certificate.json`, `sql/sqlite/custos_certificate.sql`, `sql/mysql/custos_certificate.sql` | the certificate seam (`get` of an agent's row, `agentsOf` a Sponsor, `put` of one row) and the live store over the table `custos_certificate` (below), its schema and generated SQL |
| `includes/BatchJob.php`, `BatchJobBase.php`, `ReauditJob.php`, `ClusterJob.php`, `RecheckJob.php`, `JobRunStore.php`, `DbJobRunStore.php`, `sql/custos_job_run.json`, `sql/sqlite/custos_job_run.sql`, `sql/mysql/custos_job_run.sql` | the frame of the batch jobs (below): the run store and the table `custos_job_run`, the frame that checks the context, asks the governor in lane 5 and writes the run record, and the three job classes registered (each answering `NOT BUILT` until its unit) |
| `maintenance/Job.php` | `php maintenance/run.php Custos:Job --job <reaudit\|cluster\|recheck>` enqueues a batch job; `--last <name>` prints its last run |
| `maintenance/Certify.php` | `php maintenance/run.php Custos:Certify --agent <a> --sponsor <s> --d-is <hex> --d-prompt <hex> --family <f> --model <m> [--state <s>]`: one agent's certificate written, the Operator's act at a declared admission |
| `maintenance/Land.php` | `php maintenance/run.php Custos:Land --ticket <id>`: one ticket run as the job runs it, its answer printed |
| `maintenance/Ticket.php` | `php maintenance/run.php Custos:Ticket --new <op> --account <name> --prefix <px> --request <json>`, `--answer <id>` or `--count <state>`: a ticket written QUEUED (its number printed, no job enqueued), a ticket's answer printed, or the tickets in a state counted, all through the ticket store |
| `tests/harness.php` | the tests without MediaWiki: the store seam on `FileStore`, the Calculator over the stand-in binary `fake_pcalc.sh` and, where it exists, the built `pcalc`, the residence check (H1-H16; `residence_probe.php` runs it as another user when the harness runs as root), the page classes and their titles (P1-P32), the blocks (B1-B23), the review's refusals (Q1-Q65), the ticket store on `FileTicketStore` (T1-T19), the ops and their refusals (O), the identity values (I1-I24), the landing job on the built `pcalc` (L1-L104, the seat races with `seat_race.php` as the second job's process; skipped with its reason when no `pcalc` is built), the execution challenge (N0-N41: the 21 cases of `vectors/challenge_corpus.json` through `pcalc digest` from PHP; the form; EXECUTED, REASONED, a nonce used twice, none outstanding), the governor's meter (G1-G75: the lane table against the built `pcalc`, the meter's rows, the roll-up and its level, the PRE-GATE's list written whole and read, each of GA2-GA6's refusals with its HTTP status and Retry-After through POLL, STATUS, INQUIRE, HEARTBEAT; the roll-up racing a landing step on one record, through `RacingMeterStore.php`, the stage's compare and set, the pruning, the step with the seat lock timing out after admission, the 400 refusals stepped SHAPE, a step never counted twice across a timeout and the next job overtaken between its read and its write (G70-G73), an unchanged step writing nothing and a changed one writing its three columns, on the store without the Calculator (G74, G75), the list's mode and a crashed run's leftover, a stale line, a spoofed User-Agent, the missing list), the structure test with register (Z1-Z36: the op's GA1 refusals and its ticket, the line's form and its composition from the Calculator's answer alone, NOT HOLDER with nothing written, the holder's line equal to the line of `pcalc`'s own answer, the line unchanged leaving the page unsaved, the job refused in lane 5 under pressure, one job pushed per landing, the line carried through a PUSH and a RELEASE) |
| `tests/wiring.php` | W1-W17 (the files) and, under `maintenance/run.php`, M1-M15 (the wiki that loaded Custos) |
| `tests/rehearsal.sh`, `tests/rehearsal.json`, `tests/schema_tools.php` | a throwaway MediaWiki 1.46.2 on SQLite, from the pinned Git sources or a cached tarball, with Custos loaded; it runs `update.php`, checks that `generateSchemaSql` reproduces each table's SQL (its libraries, MediaWiki's require-dev, cloned at pinned commits) and that a second scratch wiki installed with `custos_ticket` alone gains `custos_seat` by `update.php`, runs `wiring.php` there, asks the ops over HTTP as an agent account, seeds a UWC and runs the landing job's path (PETITION, PUSH, RELEASE, each through `runJobs` and POLL, the register read back), then repeats the wiring with a tampered binary (and a landing with it, which must halt and leave the register unchanged) and with a group-writable one, each of which must be refused |

## The ops of action=pma

The eight ops, by their wire words: the four of the live-exercise path (PETITION, PUSH, RELEASE,
POLL), below, the governor's STATUS, INQUIRE and HEARTBEAT (see "The governor's meter"), and
STRUCTURE_TEST (see "The structure test with register"). An op that writes a ticket is a
POST with a CSRF token by an account of the group `pma-agent` (the right `custos-landing`);
it checks the request's shape and nothing else (GA1): every parameter one string; `records` at
most `$wgCustosMaxRequestBytes` bytes and UTF-8, its bytes counted, never parsed; `prefix` a
record prefix `PageTitles` builds; no parameter the op does not take; no `account` parameter
(the account is the authenticated one). It then writes one ticket with the parameters as
received, enqueues `custosLand` with the ticket's id, and answers HTTP 202. No Calculator is
called in a web request: the ticket's work is the job's.

| Op | Parameters | Answer |
|---|---|---|
| `PETITION` | `prefix`, `block`, `prompt_digest`, `stated_model`, `relayed_model` (each optional) | `{"ticket": <id>, "state": "QUEUED", "poll_after": <s>}` |
| `PUSH` | `prefix`, `records`, `block`, `prompt_digest`, `relayed_model` (each optional but `records`), `challenge_response` (the answer to the outstanding challenge) | the same |
| `RELEASE` | `prefix`, `block` (optional) | the same |
| `POLL` | `ticket` (a read; no token) | `{"ticket", "ticket_op", "state", "poll_after"}`, or when DONE `{"ticket", "ticket_op", "state": "DONE", "answer": <the job's answer text>}` |

The identity values: `prompt_digest` is 64 lowercase hexadecimal; `stated_model` (PETITION only)
and `relayed_model` are 1 to `Ops::MAX_MODEL_BYTES` (128) bytes of UTF-8 with no control character.
A malformed value is refused `custos-shape`; a value on an op that does not take it (`stated_model`
on PUSH, any of them on RELEASE or POLL) `custos-unknown-param`. A presented value is carried on the
ticket's request as received, and nothing compares, maps or rewrites it. OWED, by the unit that
enforces them: the refusals FAMILY (the relayed model maps to another vendor family than the
certificate's), MODEL (the model excluded or unlisted) and PROMPT (the digest differs from the
certificate's `d_prompt`), which need the model map and the certificate's fields; the ranking
rule makes them an obligation, not a completeness defect. The client is untouched.

Every answer also carries `op`, the op asked; `ticket_op` is the ticket's own op. A work block's name is a letter or digit, then at most 63 of letters, digits, `_`, `.`, `:`,
`-`. The refusals, each an API error: `custos-op` (no op, or one outside the seven),
`custos-not-agent`, `custos-shape`, `custos-prefix`, `custos-account`, `custos-too-large`,
`custos-unknown-param`, `custos-missing-param`, `custos-no-ticket`, `custos-ticket-not-yours`
(POLL of another account's ticket), `custos-internal` (every path stripped). A POST without
its token, or a write sent by GET, is refused by MediaWiki itself (`badtoken`, `mustbeposted`).

The 202's `poll_after` is `$wgCustosPollAfter`, a constant: no Calculator is called in a web
request. The sweep: POLL of the account's own ticket that is QUEUED and at least
`$wgCustosSweepAfter` seconds old (by `ct_created`) pushes the job `custosLand` for it again, for a
ticket whose enqueue failed after its row was written or whose job the runner dropped. The job is
deduplicated (`removeDuplicates`), so one job per ticket waits in the queue, and the job's
conditional claim (QUEUED -> IN WORK) lands each ticket once: a second job for a ticket claimed or
answered writes nothing and ends without error. POLL's answer keeps its form. A push of the sweep that
throws (the job queue down, the wiki read-only) is logged to the debug log `Custos`, the
exception's class only, and POLL still answers the ticket's state. A job whose ticket does not
exist logs one line there and ends without error. The sweep runs on
POLL only (a ticket never polled stays QUEUED, holding nothing), and an IN WORK ticket is never
swept.

## The table custos_ticket

| Column | What it holds |
|---|---|
| `ct_id` | the ticket, the number POLL takes |
| `ct_op` | the op's wire word |
| `ct_account` | the authenticated account's user name |
| `ct_prefix` | the UWC's record prefix |
| `ct_request` | the request's parameters as received, a blob; never parsed by Custos's PHP |
| `ct_state` | `QUEUED`, `IN WORK` or `DONE` |
| `ct_answer` | the answer text the job wrote; NULL until DONE |
| `ct_created`, `ct_done` | when the ticket was written and answered |

The schema is the store's: a later column is a schema update, never a reinterpretation.

## The table custos_seat

| Column | What it holds |
|---|---|
| `cs_account` | the account's user name |
| `cs_kind` | `agent` or `sponsor` |
| `cs_level`, `cs_since` | the bucket, `pcalc governor admit`'s `[level, since]` |

The primary key is the account and the kind. The schema hook registers each table by its own
name with its own SQL (`sql/<type>/custos_ticket.sql`, `sql/<type>/custos_seat.sql`), so a wiki
whose `custos_ticket` was made before this table gains `custos_seat` on its next `update.php`; a
table present is passed over, and an update only adds a table.

The seat lock: the admission reads an account's two buckets, asks `governor admit` and writes its
charge under the account's named lock `custos-seat:<account>` (`IDatabase::lock`: `GET_LOCK` on
MySQL and MariaDB, the lock manager's file lock on SQLite), taken before the read and released after
the write, a refusal or a fault, and before the op's page writes. `DbSeatStore` reads, writes and
locks through the primary's autocommit connection, outside the job's transaction round, so the read
sees the last holder's committed charge and the charge is committed before the lock is released (on
SQLite MediaWiki hands the round's connection, its transactions serializable). Two jobs admitting
one account never both spend its last seat; two accounts never contend for one lock. The admission
takes the agent's lock and its Sponsor's, in the order of their names, so two agents of one Sponsor
never both spend the Sponsor's last seat, and no two admissions wait on each other in a cycle.

## The table custos_certificate

| Column | What it holds |
|---|---|
| `cc_agent` | the agent account's user name (the primary key) |
| `cc_sponsor` | the Sponsor account's user name (indexed: the agents bound to a Sponsor) |
| `cc_d_is`, `cc_d_prompt` | D(IS) and D(PROMPT), 64 lowercase hexadecimal digits each |
| `cc_family`, `cc_model` | the vendor family and the declared model |
| `cc_state` | `ACTIVE`, `SUSPENDED` or `REVOKED`; only `ACTIVE` admits |

One row per certified agent, written only by the Operator's maintenance script
`Custos:Certify` at an admission the Declarer declares:

    php maintenance/run.php Custos:Certify --agent <account> --sponsor <account> --d-is <hex64> \
        --d-prompt <hex64> --family <vendor family> --model <declared model> [--state <state>]

It inserts the agent's row or replaces it whole, and prints `certify: <agent> sponsor <sponsor>`;
it refuses, writing nothing, an agent named as its own Sponsor, a digest not of the form, an empty
or over-long name, family or model, and a state outside the three. A certificate holds no secret.
`DbCertificateStore` reads and writes it through the primary's autocommit connection.

## The batch jobs' frame

Three job classes share one frame, `BatchJob`: `custosReaudit`, `custosCluster` and
`custosRecheck` (names `reaudit`, `cluster`, `recheck`). `Custos:Job --job <name>` pushes the
job (deduplicated) and the job runner runs it; nothing here sets a timer, and the re-audit has none:
the landing that makes a successor is to enqueue it. A run:

1. writes the run record in `custos_job_run` (`DbJobRunStore`);
2. checks the context as the landing job does (`JobContext`, `CustosJobContext`): else the outcome
   `JOB CONTEXT` and the binary is never started;
3. asks `governor admit` in lane 5, the request kind `DEFERRABLE JOB` (the re-audit, the cluster
   month) or `BIBLIOGRAPHY RECHECK JOB` (the recheck), over a state with no account, no seats and
   nothing in flight, at the pressure level `CustosBatch["pressure"]` names (`CLEAR` until the level
   is metered). Lane 5 is admitted at `CLEAR` and `BUSY`; at `STRAINED` and `OVERLOADED` the run ends
   `DEFERRED`, its detail naming the governor's retry-after (else `CustosBatch["defer_wait"]`), and
   nothing is written but the run record;
4. runs the job's body; the three answer `NOTHING DUE` with the detail `NOT BUILT` until their units;
5. finishes the record once. A digest mismatch ends `INTEGRITY HALT`; any other fault ends `FAULT`
   with the words `Refusal::detail` allows (no path, query or server name), the message going to the
   error channel; a job that ends `FAULT`, `INTEGRITY HALT` or `JOB CONTEXT` fails with `setLastError`.

The outcomes are `DONE`, `NOTHING DUE`, `DEFERRED`, `JOB CONTEXT`, `SOURCE FAILING`, `REFUSED`, `FAULT`
and `INTEGRITY HALT`. The frame fetches nothing (the fetch layer is a later unit).

## The table custos_job_run

| Column | What it holds |
|---|---|
| `cj_id` | the run |
| `cj_job` | `reaudit`, `cluster` or `recheck` (indexed with `cj_id`) |
| `cj_started`, `cj_done` | when the run began and ended; `cj_done` NULL while it runs |
| `cj_outcome` | one of the outcomes above; empty until the run ends |
| `cj_detail` | the run's scrubbed words |
| `cj_counts` | the run's counts, a JSON object text |

A later column is a schema update, never a reinterpretation.

## The table custos_nonce

| Column | What it holds |
|---|---|
| `cn_account` | the account's user name |
| `cn_prefix` | the UWC's prefix |
| `cn_nonce` | the outstanding nonce, 32 lowercase hexadecimal characters (`random_bytes(16)`) |
| `cn_issued` | when it was issued, server time in whole seconds |

The primary key is the account and the prefix: one outstanding nonce each, a new one replacing it.
`take` reads the row and deletes it with that nonce, and returns the nonce only when its delete
removed the row, so a nonce is answered at most once. A schema update of this unit, registered by
the schema hook as the other two are.

## The execution challenge

At a granted PETITION and on every PUSH that reaches it, the job issues a fresh nonce,
`bin2hex(random_bytes(16))`, and answers it as `challenge`. A PUSH carries
`challenge_response`, the agent's `digest_fields(["TPC-EXECUTION-CHALLENGE", "1", nonce])`
computed by its own Calculator. After the holder and the block are checked, the job takes the
account's outstanding nonce (consumed whatever follows) and issues the next, which every answer of
that PUSH carries from then on, landed or refused. It asks `pcalc digest digest_fields` and compares:
a match is `EXECUTED` (`execution` in the answer, the landing going on); a wrong, absent or
ill-formed response, a nonce used already or none outstanding is `REASONED` and refuses the PUSH whole,
`CHALLENGE`, nothing landed. A nonce not in its form is refused in version 1's words, `nonce is not
32 lowercase hexadecimal characters`, never quoted. A PUSH refused before the challenge (not the
holder, the admission, its request unread) consumes no nonce. The record table carries no
EXECUTION field yet, so the attestation stands in the ticket's answer, as version 1's PUSH answer
carried it.

An account holds one outstanding nonce on a UWC, so its PUSHes are answered in turn. Two PUSH jobs
of one account and prefix that overlap (the second sent before the first's answer is read) each
take the nonce outstanding when they reach the challenge and issue the next: the second takes the
nonce the first issued, or none, and is refused `CHALLENGE`; the first's answer then carries a
nonce no longer outstanding, so the agent's next PUSH is refused `CHALLENGE` once and its answer
carries the fresh nonce, with which the PUSH after it goes on. The take and the issue are not run
under the account's seat lock: doing so would make them one step but would not change this
outcome, which follows from the single outstanding nonce, and would add a refusal after the
admission's charge. A client sends one PUSH at a time per UWC and resends after a `CHALLENGE`.

## The landing job

`custosLand` runs one ticket out of the web request. `LandJob` first checks its
context: the soft address-space limit (`/proc/self/limits`, else `posix_getrlimit`) at
least `$wgCustosJobContext["min_address_space"]` KiB, else `JOB CONTEXT` and the binary is never
started. `Landing::run` then claims the ticket (QUEUED to IN WORK) and:

1. reads the request through the Calculator: every text PHP needs (the request, the records, the
   lock, the badge, the register, the Research Assembly) is the member `value` of a
   `pcalc canonical canonical_json` request, so the Calculator is the one parser and PHP decodes
   only its canonical answer; a record's class and identifier come from `record record_view`;
2. reads the account's certificate from the table `custos_certificate` (below): no row, or a row
   whose state is not `ACTIVE`, is answered `ADMISSION` with the detail `the account has no
   certificate in force` before the governor is asked, nothing charged and no seat lock taken;
   then asks the governor: `governor seat_cost` for the op's seats, then `governor admit` over a
   metered state read from the table `custos_seat` (the account's agent bucket, and the sponsor
   bucket of the certificate's Sponsor, on the Sponsor's account), the tickets in work (the
   account's; the Sponsor's, those of every agent the certificates bind to it; and the fleet's by
   `governor lane`) and configuration
   (`$wgCustosAgentStop`, `$wgCustosGovernorOff`, `$wgCustosSuspended`); a refusal is answered
   `ADMISSION` with the governor's decision and its retry-after as `poll_after`, exactly (a refusing
   decision without a `retry_after` of 0 or more is a Calculator fault, answer form), nothing written;
   the read of the buckets, `admit` and the charge's write run under the account's seat lock and
   its Sponsor's, taken in the order of their names (the table custos_seat, above); a lock not obtained within `$wgCustosSeatLockSeconds` answers
   `ADMISSION` with `poll_after` SLOT RETRY-AFTER (5 s, `Principia/Parameters.lean`) plus the
   governor's jitter, nothing charged and no decision asked;
   an admission's charge is written to `custos_seat` whole, and a charge not in `admit`'s form
   `{"agent": [level, since], "sponsor": [level, since]}` faults the job (`CALCULATOR FAULT`);
   it is null, nothing charged, only with the governor off or outside lanes 2 to 4;
3. runs the op, every check before any write, each landing's pages saved through `PageWriter`,
   the INDEX AND BADGE page last:

| Op | Work | Answer |
|---|---|---|
| `PETITION` | the ACCESS POLICY asked (below); the lock granted when free, or past its expiry (`$wgCustosLockLease`, 3600 s) | `{"grant", "expires", "block", "challenge"}`, or `LOCK HELD` with `poll_after` |
| `PUSH` | the holder within the lease, under the block the lock was granted for (a request naming another refused `NOT HOLDER`); the execution challenge (above); the ACCESS POLICY asked again; the DIGEST GATE (the three RESEARCH ASSEMBLY pages carry one text whose `zone digest_research_assembly_of` is the badge's); each record `record_check` at PUSH under the UWC's BIBLIOGRAPHY SETTING (the DRAFT UWC page's block `pma-setting`, one word `OFF`, `ON` or `CLOSED`; `OFF`, the fleet default, when it states none; another word refused `UWC`), then `record_form_check` (RESULT, ASSUMPTION) and `domain_check` (RESULT); a record carrying the member SUPERSEDES refused (`RECORD CHECK`, problem `WITHDRAWAL`: the withdrawal is not built); each identifier the next free one, in order (`hold allocate_identifiers` under the UWC's own prefix, the records' prefix as in version 1, from 1, its next the register's count plus one; problem `SEQUENCE`, naming the record's index and the Calculator's identifier; a prefix the allocation refuses refuses the push; a UWC whose open volume is not volume 1 refused `REGISTER` until the volume roll is built); the fields Custos owns filled (BLOCK, AUTHOR, LANDED_BY `Custos`, LANDED, GRADE and STATUS the record table's first values, TPS `$wgCustosTps`, D_IS `$wgCustosDIs`); `derivation credit_record` for a RESULT's class, written into it as DERIVATION_CLASS before the digest (INSPECTION when the credit is refused or owed; a record of another class carries none); `record citation_check` against the register as read and the batch's records before it (no bibliography entry landed, `supersede_decided` false: a CITES or ASSUMPTIONS member not a standing RESULT or ASSUMPTION of the register refused REC-58 or REC-59, a LITERATURE member REC-61); `record_digest` as DIGEST, covering it; the filled record checked again at LANDED; the open register volume rewritten with the batch appended (the Calculator's canonical JSON) and the badge's last push and count | `{"landed": [{"id", "digest", "derivation_class"}], "block", "record_count", "execution": "EXECUTED", "challenge"}`; the execution challenge (above) before the ACCESS POLICY and the DIGEST GATE, a REASONED PUSH refused `CHALLENGE` |
| `RELEASE` | the holder's lock freed; the badge's last release advanced | `{"released", "block"}` |

A refusal is `{"refused": <word>, "detail", ...}`: `NOT READ` (the Calculator's reader refused a
text, or the value PHP decodes from its canonical text, written back, is not that text byte for
byte and the Calculator's canonical text of it is not either, detail `a number the landing cannot
hold exactly`: an integer outside PHP's 64-bit range or past binary64's; a number written with an
exponent, or a string holding U+2028 or U+2029, which PHP spells otherwise, is held; nothing landed), `REQUEST`, `RECORDS`, `ADMISSION`, `UWC`, `ACCESS`, `LOCK HELD`, `NOT HOLDER`, `CONFIGURATION`,
`DIGEST GATE`, `RECORD CHECK` (with `problems`, each record's index and the Calculator's answer;
all or nothing), `REGISTER`, `PAGE FAULT`, `CALCULATOR REFUSED` (with `calculator`, the
Calculator's own refusal code and its detail). POLL shows the answer to the ticket's account, so a
fault answers a fixed word and a detail from a closed set, never a path, a query, a host name, a
title's bytes or pcalc's stderr, all of which are RESTRICTED; the one function `Refusal::detail`
makes every answer, from its table:

| Fault | Word | What the answer says |
|---|---|---|
| DIGEST MISMATCH | `INTEGRITY HALT` | `detail` the words `digest mismatch` alone |
| UNSAFE RESIDENCE | `CALCULATOR FAULT` | `detail` `unsafe residence: ` and the check that failed: `owner`, `mode`, `path class`, `unreadable` or `unchecked` (never the path) |
| a call outside the protocol | `CALCULATOR FAULT` | `detail` the fault (`not a word`, `web request`, `not configured`, `no digest`, `exit code`, `not one line`, `not json`, `no refusal`, `version`, `answer form`), then `: pcalc` and the call's family and function |
| a page Custos will not build or read | `PAGE FAULT` | `detail` the page's class (where the job knows it), `: ` and the fault (`block form`, `page text`, `title form`, `base moved`, `landing order`, `page store`); with `poll_after` |
| any other | `JOB FAULT` | `class` the exception's short class name, and no `detail` |

The refusals the job writes itself (`LOCK HELD`, `NOT HOLDER`, `RECORD CHECK` and the rest above)
say their own sentence, written by the job from the ticket's values and the Calculator's answers.
INTEGRITY HALT, CALCULATOR FAULT and JOB FAULT fail the job, the ticket never left IN WORK; a PAGE
FAULT is answered and the job ends. The class and message of every fault go to the debug log
`Custos` and, in the rethrown exception, to the job's last error, which the Operator
reads on the host. This unit lands
RESULT, ASSUMPTION and ENTRY_STATUS; DERIVATION_CLASS is written into a RESULT's record before the digest, so the digest
covers it and the check at LANDED reads it (REC-43), and is answered per landed record as
`derivation_class`; a record of another kind carries none.

The ACCESS POLICY (TPS 5.16) is the DRAFT UWC page's block `pma-policy`, one word `OPEN` or
`CLOSED` (`OPEN` when the page states none, as version 1 read an absent policy; another word
refused `UWC`). Under `CLOSED` the ACCESS LIST page's block `pma-access`, a JSON list of account
names read by the Calculator, says whether the account is listed; an absent or unreadable list
refuses (fail closed). The decision is `permissions permits` (the CLOSED PREDICATE): a PETITION as
the Coworker's append to the collaboration page, a PUSH as the Holder's write of the open register
volume; anything but `PERMITTED` is refused `ACCESS`, nothing written.

Open items, each refused today (fail closed) where version 1 acted: the withdrawal (SUPERSEDES
carried out, WITHDRAWAL records, the cascade); the bibliography's landed entries (a LITERATURE
member is refused REC-61); the volume roll (a UWC whose open register volume is not volume 1
is refused); SeedUwc writing `pma-policy` and the access list from the Initiator's selection.
A record's identifier is the UWC's prefix and the next number; the rehearsal pushes its records
under the seeded UWC's prefix.

Every wait the job answers without the governor's retry-after (`LOCK HELD`, `PAGE FAULT`, an
`ADMISSION` refusal whose decision carries none) is `$wgCustosPollAfter` plus
`pcalc governor jitter {"base", "draw"}`, at most 10 per cent of the base (RETRY-AFTER jitter,
`Principia/Parameters.lean`), the draw made by `random_int` as admission's is: agents refused
together do not poll together. PHP adds the two and computes nothing else.

## The page classes and their titles

Every page Custos writes has a title of a fixed form, version 1's in PMA's words
(`docs/terminology_map.md`), built by `PageTitles` from `$wgCustosUwcRoot` (U) and
`$wgCustosDeclRoot` (D); `classify` reads a title back as its page class. Per UWC, `<p>` its
record prefix (an underscore is a space in the title):

| Title | Page class |
|---|---|
| `U/<p>/Draft` | DRAFT UWC |
| `U/<p>/Research Assembly/<Starting Set, Correspondence Table or Criteria Set>` | RESEARCH ASSEMBLY |
| `U/<p>/Register/Volume <v>` | REGISTER OPEN or REGISTER FROZEN |
| `U/<p>/Bibliography/Volume <v>` | BIBLIOGRAPHY OPEN or BIBLIOGRAPHY FROZEN |
| `U/<p>/Access list` | ACCESS LIST |
| `U/<p>/Lock` | LOCK PAGE |
| `U/<p>/Collaboration` | COLLABORATION |
| `U/<p>/Collaboration/Staging`, and pages beneath it | STAGING |
| `U/<p>/Control panel`, and pages beneath it (the schedule and work-block logs) | CONTROL PANEL |
| `U/<p>/Index` (the badge's page) | INDEX AND BADGE |
| `U/<p>/Reading` | SPINE |
| `U/<p>/Community View` | COMMUNITY LEDGER |
| `U/Index` (the fleet's index) | INDEX AND BADGE |
| `D/Declarations`, `D/Build chain` | CHAIN HEAD |
| `D/Declarations/Volume <v>` | DECLARATIONS VOLUME |
| `D/Build chain/Volume <v>` | BUILD CHAIN VOLUME |
| `D/Community Ledger/Volume <v>` | COMMUNITY LEDGER |
| `D/Dossier/<account>` | DOSSIER |
| `D/Falcon/<id>` | FALCON PAGE |
| `D/Top performers`, `D/Top performers/<YYYY-MM>` | TOP PERFORMER |
| `D/Configuration strata` | CONFIGURATION STRATA |
| `D/Provision/<id>/<version>` | PROVISION |
| `Restricted:Score/<account>` | SCORE OR USER PAGE |
| `Restricted:Falcon/<id>`, `Restricted:Falcon/Stratum` | FALCON RESTRICTED |

`classify` first reads a title as MediaWiki does: character references decoded once
(decimal, hexadecimal, named; one not decoded exactly makes the title unreadable), NFC (PHP's `intl`; without it a title with any
byte outside ASCII cannot be read), MediaWiki's space characters (the no-break and the other
Unicode spaces among them) and underscores folded to one space, direction marks dropped, one
leading colon dropped, the namespace in any case with spaces around its colon, the first letter
upper case. A title it cannot read exactly is governed, restricted and refused; a governed title
written with a character reference has no class (Custos never writes one); so is a governed title
MediaWiki would refuse or cut (a `#`, a `[`, a percent escape, a `.` or `..` segment). Each
root must already be in that form, in the main namespace, with no empty segment, the two not
nested; else Custos refuses to start. A title under U, in the restricted namespace, or under
one of D's segments above is governed: when it is in none of these forms it has no page class, and every check refuses it.
Facts a title cannot carry are passed to `classify`, and an absent one takes the reading that
refuses: a volume is FROZEN unless the caller states it OPEN (the Calculator decides it from the
volume's identifiers); every page of a UWC needs the fact "retired" stated true or false (else
no class), and RETIRED makes a page that fits a form RETIRED CONTAINER. A prefix the builders
refuse (`Index`, an underscore at an end) never classifies. The other 15
classes have no title form version 1 fixes; they stay without one until the Declarer's answer.
The restricted namespace "Restricted:" is registered under 7240 (`NS_CUSTOS_RESTRICTED`,
`$wgCustosRestrictedNamespace`) with no talk namespace.

Each page's machine text is a block, the payload on lines of its own:

    <pre class="pma-<name>">
    <payload>
    </pre>

`Blocks::render` writes one, `Blocks::extract` reads the payloads of a name in page order. PHP
reads no JSON: the Calculator's `canonical` family is the one parser. Refused (`PageFault`): a
name outside `a` to `z`, a payload carrying a pre tag, a comment or an unparsed tag or not
UTF-8, a page carrying a comment or an unparsed tag (`nowiki`, `syntaxhighlight`, `math` and
the like: gallery, html, ref, references, translate, poem and others), a NUL, a page whose pre tags do not all belong to closed, unnested blocks of that form, and
a page a pattern match could not search.

## The page writer, the page texts and the fence

A landing writes its pages through `PageWriter` (charter 8.3): `begin(prefix, block)` reads the
UWC's INDEX AND BADGE page; `put(title, text)` collects a page's new text, reading the page the
first time the landing names it; `commit()` checks every page still holds the text read, then
saves each once through `PageStore::casPut` as the system user Custos, the summary
"Custos: landing of block <block> on <prefix>", the INDEX AND BADGE page last. A page that
changed since it was read refuses the whole landing (`BASE MOVED`), nothing saved; a save that
fails after the check stops the landing before the badge, so the badge, the commit marker, is
never written over a partial landing. The text read stands for the revision.

The fence: `put` takes only a title in MediaWiki's canonical form that `PageTitles::classify`
reads as a page Custos writes under the landing's own UWC prefix (the DRAFT UWC page, a
RESEARCH ASSEMBLY page, a register volume, the LOCK PAGE, the INDEX AND BADGE page), or, beyond
the UWC, a class the op names at `begin(prefix, block, beyond)`: the fleet's index and the
Declarer's root's chain heads and volumes (no op names one yet). Any other title (another UWC's
page, a governed title of no class, a class Custos does not write, an ordinary page) refuses the
whole landing before anything is saved, as `BASE MOVED` does; the refusal names the title and
the class it read, and the ticket answers `PAGE FAULT` with the fault `landing order`.

`PageTexts` writes the three texts of the path, each a named block:

| Page | Blocks |
|---|---|
| LOCK PAGE | `pma-lock`: `{"block","expires_at","granted_at","holder"}`, the Calculator's canonical JSON of the members; all null when free |
| REGISTER OPEN | `pma-register`: the records as the Calculator wrote them, carried through whole |
| INDEX AND BADGE | `pma-badge`: `{"calculator_digest","calculator_version","last_push","last_release","record_count","research_assembly"}`; `pma-state`: `LIVE` or `RETIRED`; `pma-open`: the open register volume's number |

PHP reads no field of a payload and writes no JSON of its own beyond the badge. A held lock's
members are checked (times `YYYY-MM-DDThh:mm:ssZ`, a work block's name, an account name of any
spelling MediaWiki admits: UTF-8, at most 255 bytes, no control character, none of `#<>[]|{}/`,
no underscore or other character MediaWiki folds to a space, no space at an end or two together),
then the job asks `pcalc canonical canonical_json` for the payload, as it asks the register's
text, and reads it back through the same call: quotes, backslashes and letters outside ASCII
are carried exactly. The badge's values are checked so that its JSON needs no escape (digests of
64 lowercase hexadecimal digits, a version without a quote), keys sorted, so its text is the
Calculator's canonical JSON of itself (the harness checks both on the built `pcalc`). The state and
the open volume are the facts a title cannot carry, read by comparing a whole payload with a
fixed word.

`PermissionHook` fences the governed pages. It reads the permissions table (section "The permits
table") and admits nothing the table refuses:

1. A title Custos does not govern is untouched. A title in the restricted namespace is read
   through `$wgCustosRestrictedNamespace` (`NS_CUSTOS_RESTRICTED`, 7240); a title MediaWiki gives
   the next number is refused for every action.
2. A governed title that does not classify (`PageTitles::classify`, the UWC's facts read from
   its INDEX AND BADGE page, an absent fact refusing) is refused for every action and account.
3. An edit, create, createpage or createtalk by the system user Custos, the landing job's
   writes, is admitted; every other action of that user is asked as any account's.
4. Every other request is mapped to one cell: the asker (the Declarer's, the Operator's and the
   Contributor's groups of `$wgCustosRoles`, the Public for every account, an agent account in
   its lock state only), the page class, the operation (an allow-list: write, protect, read;
   any other action none, refused) and the context (the account the title names, the session
   REAUTHENTICATED). It is admitted only when the table permits the cell, under every value of a
   fact no page carries yet.
5. A refusal is `custos-governed-page` for a write-class action and for any action on a page of
   a public class, and `custos-restricted-page` for any other action on a restricted page or in
   the restricted namespace.

A configuration, a table or a store the hook cannot read refuses every title (fail closed).

`SeedUwc` writes a new UWC's pages in one landing: the DRAFT UWC page (`pma-draft`, the draft as
the Calculator's canonical JSON), the three RESEARCH ASSEMBLY pages (`pma-assembly`, each the
whole Research Assembly until the Calculator answers one zone), an empty REGISTER OPEN Volume 1,
a free LOCK PAGE and the INDEX AND BADGE page (the Research Assembly's digest from
`pcalc zone digest_research_assembly_of`, the Calculator's version and `$wgCustosBuild`'s
digest, `LIVE`, Volume 1 open). It refuses a UWC any of whose pages exists.

## Restricted routes

The permission hook refuses a read of a restricted page by its title to all but the Declarer's
and the Operator's groups. `includes/RestrictedRoutes.php` closes every other route by which
MediaWiki 1.46.2 hands out a page's text or title, each by the hook or the setting MediaWiki
gives for it. A restricted page: a title in the namespace `Restricted:` (7240) or the next
number (7241, refused for every action), or one `PageTitles::classify` reads as restricted
(every page of a restricted class lies in the namespace; a title it cannot read is restricted,
fail closed). The routes a list or a cache could carry to someone else are closed for every
reader, the Declarer and the Operator included: the parser cache is shared, a list may be
transcluded into it (`{{Special:RecentChanges}}`), and a feed is cached whole. The Declarer and
the Operator read a restricted page by its own title.

| Route | How it is closed |
|---|---|
| transclusion: `{{...}}`, `{{:...}}`, `{{msgnw:...}}`, `{{raw:...}}`, through a redirect | `$wgNonincludableNamespaces` carries 7240 and 7241 (the registration callback); `BeforeParserFetchTemplateRevisionRecord` skips a restricted template |
| the parser's reads of another page: `{{REVISIONID:}}`, `{{REVISIONUSER:}}`, `{{REVISIONTIMESTAMP:}}`, `{{PAGESIZE:}}` and the like | `ParserOptionsRegister`: the default `currentRevisionRecordCallback` answers no revision for a restricted page |
| search: Special:Search, `list=search`, `list=prefixsearch`, `action=opensearch` | `SearchableNamespaces` and `$wgNamespacesToBeSearchedDefault` (not searchable); `ShowSearchHit` (the hit shows nothing); `ApiOpenSearchSuggest`; the API's scrub |
| search by the prefix `Restricted:` or `all:` (the database search reads either without the searchable namespaces' filter, so a total or a redirect's title would still answer): Special:Search, `srsearch`, `pssearch`, `search`, the REST API's `/v1/search/page` and `/v1/search/title` | refused: `SpecialPageBeforeExecute` (the search text, `prefix` or the subpage), `ApiCheckCanExecute`, `RestCheckCanExecute` (the REST handler runs neither `ShowSearchHit` nor `ApiOpenSearchSuggest`, and names a redirect's own title as `matched_title` beside its readable target) |
| the REST API's sitemap, `/site/v1/sitemap/...` (off unless `$wgSitemapApiConfig` enables it) | `RestCheckCanExecute` refuses it whole: it lists every namespace the robot policies index, and any by `include_namespace` |
| `Special:Export`, the API's `export` | core's read check per page (the permission hook); `ModifyExportQuery` leaves the namespace out of every export outside the command line, `exportall` included; the Operator's `dumpBackup` keeps it |
| `action=raw`, `action=render`, view, `action=info`, `action=history`, `oldid=`, `diff=`, `curid=`, Special:ComparePages, `action=parse`, `action=compare` | core's read check (the permission hook); the refusal of a restricted page names no title, so an id never hands it out; `BeforeInitialize` answers the refusal 403 (MediaWiki renders it as an error page answered 200, which a cache, a crawler or a client takes for the page): for a restricted title the asker may not read, and for the view or `action=render` of a page whose redirect index.php would follow to one (not `redirect=no`, an old revision or a diff); the status is the same whether the restricted page exists or not, the body is not (below) |
| the API's `prop=revisions` (its text and its metadata), `revids`, `pageids`, `list=allpages`, `list=allrevisions`, `list=recentchanges`, `list=usercontribs`, `list=logevents`, every list and generator | `ApiCheckCanExecute` refuses a request naming 7240 or 7241 in a parameter ending in `namespace`, or a restricted page by a revision or page id (`revids`, `oldid`, `fromrev`, `torev`, `pageids`, `pageid`, `fromid`, `toid`, `curid`); `APIAfterExecute` scrubs `action=query`'s result of every item naming a restricted title |
| Special:RecentChanges, RecentChangesLinked, Watchlist, `action=feedrecentchanges`, `action=feedwatchlist` | `ChangesListSpecialPageQuery` leaves the namespace out, and every move into it: a move's row carries its source's namespace and names the target only in `rc_params`, so a row of the log type `move` whose parameters carry `Restricted:` is left out (the watchlist feed is an inner `action=query`, scrubbed, a move by its `logparams`) |
| Special:NewPages | `SpecialNewpagesConditions` |
| Special:Contributions, `action=feedcontributions` | `ContribsPager::getQueryInfo` |
| Special:Log | `LogEventsListLineEnding` empties a line about a restricted page, or a move into the namespace |
| Special:AllPages, Special:PrefixIndex | `SpecialPageBeforeExecute` refuses a restricted namespace (by number, by the prefix of `from`, `to`, `prefix` or the subpage); `SpecialPrefixIndexQuery` leaves it out |
| Special:Random, RandomRedirect, RandomRootPage (their subpage, a namespace name or a comma list of them, takes any namespace) | `SpecialPageBeforeExecute` refuses a subpage naming `Restricted`; `RandomPageQuery` leaves the namespace out of their query |
| Special:ListRedirects (the page table's redirect flag), BrokenRedirects and DoubleRedirects (the redirect table), UnwatchedPages: each lists every namespace and offers no hook | `SpecialPageBeforeExecute` refuses each whole, to every reader |
| Special:ProtectedPages, Special:ProtectedTitles (every namespace unless one is chosen) | `SpecialPageBeforeExecute` refuses each unless `namespace` names a public one |
| Special:WhatLinksHere's redirects: the redirect table is written by `WikiPage`, outside `LinksUpdate` | `SpecialWhatLinksHereQuery` leaves the namespace out of each of its queries, the redirects and the stale rows of a page moved into it included |
| WhatLinksHere, the category pages, Special:PagesWithProp, the API's `backlinks`, `categorymembers`, `alllinks`, `pageswithprop` | `RevisionDataUpdates` drops a restricted page's `LinksUpdate`: its links, categories, templates and properties are never recorded |

Not a route here, by reading `includes/`: the query pages that list content namespaces only
(ShortPages, LongPages, AncientPages, LonelyPages, UncategorizedPages, DeadendPages,
FewestRevisions, MostRevisions, MostCategories, MostInterwikis, WithoutInterwiki; the namespace
is registered `content: false`), or one fixed namespace (the file, template and category
lists), or the link tables a restricted page never writes (LinkSearch, PagesWithProp,
MostLinked, WantedPages); RandomInCategory (a restricted page records no category); Special:Redirect
(it redirects by id to `curid=` or `oldid=`, refused without the title); DeletedContributions
and Special:Undelete (the rights `deletedhistory` and `undelete`, the Operator's group's).
What a guessed title still answers: whether it exists (a link's colour, `{{PAGEID:}}`,
`{{PROTECTIONLEVEL:}}`, the API's `missing`, and the body of a public redirect's view to it, the
permission error for an existing page and the redirect page itself for an absent one, both answered
403), never its text, its summary or another title.

## The permits table

The permission hook (`PermissionHook`) answers every request on a governed page from
`custos/permits.json`, the permissions table: `pcalc permissions table {}`'s answer,
written unchanged by `python3 -I scripts/permits_table.py --write` from the built binary, its
SHA-256 in `custos/permits.sha256`. Every cell is `permits` on its asker, class, operation and
context (the theorem `table_lookup_eq_permits`); the gate custos-tests runs `--check` after
`lake build`, so a table the binary would not write fails it. `Permits` reads the file with
`json_decode`, once per request cycle: the one place Custos's PHP reads JSON, because the file is
the repository's and the Calculator's, shipped with the extension, never a page's text, and a web
request starts no Calculator. A fact no page carries yet (the UWC's access policy and access
list, an agent's lock state and queue head, the DOSSIER READ setting, the UWC's Initiator) is
unknown: the hook admits only what the table permits under every value of it. The restricted
namespace `Restricted:` is registered under 7240 (`$wgCustosRestrictedNamespace`) with no talk
namespace; a title MediaWiki gives 7241, registered by no one, is refused for every action.
An account in the Contributor's group (`pma-contributor`) asks the Contributor's cells, which are
the Public's (an agent account in it asks in its lock state only); the harness checks all 23,040.

## Configuration

| Key | Default | Meaning |
|---|---|---|
| `$wgCustosCalculator` | empty | the absolute path of `pcalc`; empty: every call is refused (no default path) |
| `$wgCustosBuild` | `["version" => "", "digest" => ""]` | the expected `pcalc version` and the binary's SHA-256 digest (64 lowercase hexadecimal digits); empty: every call is refused |
| `$wgCustosUwcRoot` | `Principia Machina/UWC` | the root of each UWC's pages |
| `$wgCustosDeclRoot` | `Principia Machina` | the root of the pages the Declarer declares |
| `$wgCustosPollAfter` | `30` | the seconds answered as `poll_after` by the 202 and POLL; the base of the job's jittered waits |
| `$wgCustosSweepAfter` | `600` | the age in seconds past which POLL of a QUEUED ticket pushes its job again (deduplicated) |
| `$wgCustosMaxRequestBytes` | `1048576` | the most bytes `records` may carry (the Calculator's reader bound) |
| `$wgCustosLockLease` | `3600` | the seconds a granted lock lasts |
| `$wgCustosAgentStop`, `$wgCustosGovernorOff` | `false` | the governor's switches, read into the metered state |
| `$wgCustosSuspended` | `[]` | the accounts suspended (CR6, CR11), refused at admission |
| `$wgCustosSeatLockSeconds` | `10` | the seconds the admission waits for the account's seat lock; past it `ADMISSION` with SLOT RETRY-AFTER plus jitter, nothing charged |
| `$wgCustosTps`, `$wgCustosDIs` | empty | the TPS and D_IS a landed record carries; empty: no PUSH lands |
| `$wgCustosJobContext` | `["min_address_space" => 2025138]` | the job's context: the KiB of address space the job needs |
| `$wgCustosBatch` | `["pressure" => "CLEAR", "defer_wait" => 300]` | the batch frame: the pressure level passed to `governor admit` until the level is metered, and the seconds answered as the retry-after when the governor gives none |
| `$wgCustosMeterSample` | `10` | the meter samples anonymous reads 1 in this many, each kept row weighted by it |
| `$wgCustosPreGateFile` | empty | the PRE-GATE's deny list the budget roll-up writes (mode 0640: the web server's group reads it); empty: none written |
| `$wgCustosRoles` | `["declarer" => "pma-declarer", "operator" => "pma-operator", "agent" => "pma-agent", "contributor" => "pma-contributor"]` | the group of each role's accounts; a restricted page is read only by the Declarer's and the Operator's groups |

## The residence of the Calculator's binary

The digest check reads the binary at `$wgCustosCalculator`, and the shell framework then
starts the binary at that path. Both read the same bytes only when no user but root can
change the binary or a folder above it. So, before the digest check, once per request cycle,
Custos checks the binary's residence (D10) and refuses the call (`UnsafeResidence`, "UNSAFE
RESIDENCE: <path> <property>") when any of these fails, the binary never started:

1. The path is absolute, in normal form, and under `/opt` or `/usr`, the folders the shell
   framework's sandbox executes from.
2. The binary is a regular file and every folder from it up to `/opt` or `/usr` is a folder;
   none is a symbolic link.
3. None of them is writable by group or by other.
4. All of them are owned by root.
5. The user the wiki runs as cannot write any of them, and owns none of them.

What cannot be read is refused, never allowed. No configuration key, environment variable or
file changes the check (the chosen rule: no residence override): the job, `Custos:SeedUwc`, `Custos:land` and the
rehearsal all run this one check, with no switch.
Property 5 refuses root too: the job runner and the maintenance scripts that call the
Calculator run as the wiki's own user, never as root.

What the deploy sets (the Operator's act):

    /opt/pma          owner root, group root, mode 755
    /opt/pma/pcalc    owner root, group root, mode 755
    $wgCustosCalculator = '/opt/pma/pcalc';

The Calculator is never called inside a web request: `Calculator` refuses a
call unless PHP runs on the command line, where the job runner and the maintenance scripts
run, and the wiki runs jobs only from its job runner (`$wgJobRunRate = 0`).

## Tests

    php custos/tests/harness.php                 # prints "harness: ALL PASS <n>/<n>"
    php custos/tests/wiring.php                  # W1-W17 alone
    bash custos/tests/rehearsal.sh [<folder>]    # "schema: current", "schema: custos_seat,
                                                 # custos_certificate, custos_job_run,
                                                 # custos_nonce, custos_meter, custos_budget
                                                 # and custos_traffic added by update to a
                                                 # wiki that had custos_ticket alone",
                                                 # "wiring: ALL PASS",
                                                 # "api: PETITION 202", "api: POLL QUEUED",
                                                 # "api: PUSH 202", "api: RELEASE 202", the
                                                 # refusals, "seed: 7 pages",
                                                 # "hook: edit refused custos-governed-page",
                                                 # "hook: Restricted read refused",
                                                 # "restricted: transclusion refused",
                                                 # "restricted: search shows nothing",
                                                 # "restricted: export refused",
                                                 # "restricted: raw refused",
                                                 # "restricted: API revisions refused",
                                                 # "restricted: history refused",
                                                 # "restricted: recent changes show
                                                 # nothing", "restricted: read admitted",
                                                 # "land: PETITION grant", "land: PUSH CHALLENGE
                                                 # REASONED", "land: PUSH landed EXECUTED",
                                                 # "land: READ 2 records", "land: RELEASE released",
                                                 # "lock: holder carried exactly",
                                                 # "sweep: a QUEUED ticket without its job,
                                                 # re-enqueued on POLL, answered",
                                                 # "land: LOCK HELD poll_after jittered",
                                                 # "job: reaudit NOTHING DUE" (cluster, recheck),
                                                 # "job: refused DEFERRED",
                                                 # then the tampered landing halted and the
                                                 # tampered and the group-writable binaries refused
    CUSTOS_TAMPER=1 bash custos/tests/rehearsal.sh [<folder>]
                                                 # the tampered pass alone: the landing halted with
                                                 # the register unchanged, "DIGEST MISMATCH", exit 1
                                                 # (exit 2 when that landing was not halted)

`rehearsal.sh` takes the MediaWiki folder: an installed one is used as it is (the test gate
installs it first); an empty or absent one is filled from `$MW_TARBALL` when that is set, else
by `git clone` of the commits `rehearsal.json` pins. Its scratch folder is `$CUSTOS_WORK`, else a
new temporary folder; the database of a wiki it installs lives there, outside the web root, and so
does the agent account's password, drawn from `/dev/urandom`, mode 600, never printed.

The rehearsal's residence is the live one: it places the binary under `/opt`, root's, mode 755
throughout, prints "calculator residence: <path>", and runs every PHP process as a user other
than root. As root (the cloud worker's container) it makes its own folder
`/opt/pma-rehearsal/run.<x>`, removed at its end, and runs PHP as uid and gid 65534 by `setpriv`.
Before the install it checks that every ancestor of the scratch folder and of the MediaWiki folder is searchable by that user, else it exits 2 naming the folder; set `$CUSTOS_WORK` under `/tmp`.
As any other user (the rehearsal host's gate account) it places the binaries in `/opt/pma-rehearsal/bin`
through the root-owned helper `/usr/local/sbin/pma-rehearsal-residence` and its sudo rule (three
arguments, `pcalc`, `pcalc-tampered`, `pcalc-writable`, alone), which the Operator installs once,
as root, on that machine:

    bash custos/tests/rehearsal.sh --install-residence <the gate's account>

Without them it cannot be set up (exit 2) and prints that command. The tampered passes swap the
tampered bytes in at the residence's `pcalc` and put the true binary back, in a trap as well.
The harness checks the live residence rule (as root, cases H9, H10 and H16 run as another user;
as any other user H9 and H10 are skipped with their reason, never passed; H15 and H16: no source
of the wiki's side reads the environment, and the live check refuses a binary outside `/opt` and
`/usr` whatever the environment holds). The check `custos-tests` of the Operator's server service runs
all three on every head that touches `custos/`.

The rehearsal opens no database by a path of its own: the table `custos_ticket` is read and written
only through the ticket store, by `Custos:Ticket` (the count of tickets QUEUED after the ops over
HTTP; the tampered landing's ticket written with `--new` and its answer read with `--answer`), so
it runs the same on a wiki it installs and on one installed before it, whose database is wherever
that wiki's `LocalSettings.php` puts it (the test gate installs with `--dbpath` under its own
folder). The second scratch wiki of the schema check is the one exception: its `custos_ticket` is
made by `maintenance/run.php sql` from that table's own SQL, as a wiki installed before the seat
table had it, and its tables are read from the database's catalog by the same script; its ticket is
written and counted through `Custos:Ticket`.

## The governor's meter

`Meter` writes one row per governed request into `custos_meter`: the account (an anonymous
request's network instead, an IPv4 /24 or an IPv6 /48), the kind (an op of `action=pma` by its
word, POLL as `POLL OTHER`; an agent's other call `AGENT CORE READ`; `SIGNED IN USER`;
`ANONYMOUS READ`), its lane from `lanes.json`, CPU and wall time in thousandths of a second, peak
memory and response bytes. Anonymous reads are sampled 1 in `$wgCustosMeterSample` (10), each kept
row weighted by it. No Calculator is called in a web request: the lane is the table's. Each row
pushes the job `custosBudget`, deduplicated.

`Budget::run` sums the rows over the hour, the day and thirty days (CPU use, weighted), asks
`governor pressure_level` with the level the last roll-up kept as `prev`, writes the roll-up and the
level to `custos_budget`, prunes the rows of `custos_meter` older than thirty days, reads each
account's stage at now (`governor traffic_stage`) and writes the PRE-GATE's list
`$wgCustosPreGateFile` (empty: none): a head line `# custos pre-gate deny list <time>` and one line
`account<TAB><name><TAB><seconds>` per CONTAINED account, the seconds `traffic_stage`'s
`served_retry_after` plus `governor jitter`, no wait chosen in PHP. The list is written to a
temporary file made mode 0640 before any byte is written, then renamed over the list; a temporary
file a crashed run left (older than 60 seconds) is removed at the next write.

The landing job steps the traffic record by a compare and set (`MeterStore::casTraffic`, an
`UPDATE` whose condition is the record read, or for an account's first record an insert only where
none is), taking no lock: a miss, another job's step written between the read and the write, is
read and stepped again (at most `Landing::STEP_TRIES`, 100, reads, each miss being another step
landed), so a step is written once, on the record as it then stands, never lost to a lock's
timeout and never written twice. A step that leaves the record's text as it was writes nothing: the
store only compares it with the record read (a miss is read and stepped again), and `ctr_stage` and
`ctr_time` keep the last write by either writer, the step's compare and set on a changed record or
the roll-up's stage, never a stage and time written over an unchanged record. The
roll-up writes only the stage beside it, and only where the stored record is still the text it
read (`MeterStore::stageTraffic`, an `UPDATE` whose condition is the record read): a landing step
written between the roll-up's read and its write is never erased. On a miss it reads and asks
again, at most three times, then leaves that account's stage to the next roll-up.

The landing job's metered state carries `pressure` (the kept level) and `use` (the roll-up), from
which `admit` takes the level in force, and the account's `traffic` record, handed back as the text
the Calculator answered. The record is stepped once, at the job's end, read again there, with the
request's end (`traffic_step`): an admitted op SUCCEEDED, or FAILED when it was refused after
admission (NOT HOLDER, CHALLENGE, RECORD CHECK, a PAGE FAULT) or faulted, so that such failures
build ERROR STREAK; a refusal by its word with its `retry_after`; a ticket refused by its shape
before admission (GA1, a 400: `NOT READ`, `REQUEST` or `RECORDS` of its request) SHAPE, nothing
charged; a CACHED ONLY decision not at all, since it ends no governed request of an AGENT account;
a seat lock not obtained at admission not at all, no decision having been made; and once more with
ERROR STREAK when the Calculator raises TE2. A relaxation: the web request's own shape refusals
(`custos-shape` and its kin, no ticket written) are not stepped, as no Calculator is called in a
web request. A refusal's answer carries the decision's
`status` (403, 429 or 503) and its `poll_after`: the decision's `retry_after`, exactly (a
refusing decision without one is a Calculator fault, as above, and steps no record); POLL answers it as the HTTP status and `Retry-After`. POLL reads those two members of the ticket's
answer, Custos's own text, the second place its PHP reads JSON besides the tables it ships.

STATUS (a read; any account or none) answers `build` (version and digest from `$wgCustosBuild`),
`governor` (the last roll-up's level and time) and the account's `stage`; INQUIRE (a read; an
account) the account's stage, NORMAL with no record; HEARTBEAT (a POST, 202) writes a ticket the job
runs: the holder's lock, within its lease, extended to now plus `$wgCustosLockLease`, its grant and
block kept, else NOT HOLDER.

`pregate.php` reads its list and nothing else. A request whose User-Agent names a listed account
(`<client>/<version> (<words>; <account>)`) is answered 429 with the Retry-After left of the listed
one (the head's time plus its seconds, less now); RELEASE and
INQUIRE of `action=pma` pass; a line holds until the head's time plus its seconds and passes from
then on, so a list the roll-up stopped writing never denies for longer than it said; a list missing
or without its head line does nothing. The account is read from the User-Agent, which the client
states: the PRE-GATE only ever denies, so a name spoofed there can deny its sender and never admit
it, MediaWiki's admission reading the authenticated account (a relaxation: the authenticated name
is known only after MediaWiki loads, which the PRE-GATE runs before). Open item, a relaxation: a
CONTAINED agent that changes its User-Agent passes the PRE-GATE for its ordinary reads; the
PRE-GATE keyed on the authenticated account is listed under "Not yet" below. The Operator
wires it on the server: `php_value auto_prepend_file <the clone>/custos/pregate.php` and `SetEnv
CUSTOS_PREGATE_FILE <the list>`, the list the same path as `$wgCustosPreGateFile`.

Not yet (later briefs): the lock's state in STATUS, INQUIRE from the account's dossier page, the
FLOOD INTERVAL at the PRE-GATE, the anonymous network cap, the events REPEAT, CAP OVERRUN and
BACKOFF VIOLATION raised from the meter, the external reading, POLL's 202 wait jittered, the PRE-GATE reading the authenticated account rather than the User-Agent.

## The structure test with register

Version 1's STRUCTURE TEST WITH REGISTER (TPS 5.3.47): the analysis of the equations of motion over
the UWC's Research Assembly and the standing records of its register whose declared form carries a
ROLE. The Calculator does the whole test: one call `pcalc eom eom_register_test {"tfk", "records"}`
over the Research Assembly (through the DIGEST GATE, as a PUSH reads it) and the open register
volume whole; PHP selects no record and orders nothing.

- The op STRUCTURE_TEST (lane 3, 2 seats): a POST with a CSRF token naming the UWC's prefix and no
  other parameter; GA1 in the request, a ticket and the job `custosLand`, as PETITION. The job
  admits it through `governor admit`, refuses it from any account but the lock's holder within its
  lease (NOT HOLDER, nothing written), runs the test and answers the ticket with the line
  (`structure_test`, and `written`: whether the page was saved). Version 1 ran the test inside the
  request; no Calculator is called in a web request.
- The job `custosStructureTest` (lane 5): pushed by the landing job after every PUSH that lands,
  deduplicated per UWC (its one parameter is the prefix); a superset of version 1's trigger, the
  line rewritten only when it changes. Admitted through `governor admit` as STRUCTURE TEST JOB with
  no account and no seats: refused under pressure (STRAINED, OVERLOADED) with nothing written. A
  batch job of charter 8.5, run outside the batch jobs' frame (`BatchJob`): it writes no run record
  in `custos_job_run`.
- The line, the block `pma-structure` on the UWC's INDEX AND BADGE page: "STRUCTURE TEST <date>
  <result> WITH <identifiers>", the result "structurally regular with register" exactly when the
  answer's findings are empty, else FINDINGS and each finding as the Calculator wrote it (its JSON),
  in the answer's order; the identifiers the answer's USED in its order (prefix, then number),
  joined by ", ", "-" when none. Written through `PageWriter` (one save, the INDEX AND BADGE page)
  only when what it says beside its date changes; a PUSH or a RELEASE that rewrites the badge carries
  it through. `Custos:SeedUwc` writes "STRUCTURE TEST none". An answer `["REFUSED", reason]` is
  refused STRUCTURE TEST, nothing written.

Not yet (later briefs): the Calculator's test reads version 1's status words (PROVISIONAL,
ESTABLISHED, ...), so it refuses a register holding a record as this Custos lands it (STATUS
UNMARKED) and the line stays as it was until the Calculator reads the register's own status words;
the control panel's button (a lane 1 request of a signed-in user); the line marked LAPSED when a
record it used stops standing; EOM-0's settlement inside a PUSH; the Research Client's side of the
op (TPS 5.4.22).

END OF ARTIFACT --- README
