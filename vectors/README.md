# vectors

Test vectors, one JSON corpus per function family. A corpus is version-free, its version
being its commit (docs/design/pma_naming_policy.md, N7).

## PMA's corpora

`netstring.json` is the first, hand-written. `lake test` (`Tests/Main.lean`) runs it and
the record types' corpora (`Principia/Record/`, `docs/design/pma_record_types.md`):

- `wire_words.json`, hand-written: each closed enumeration's wire words in table order
  (read back through `WireWord.ofWire?`, checked for R1's spelling and for repeats), and
  words that must not read (case, spacing, v1 words PMA replaced, words of a neighbouring
  enumeration).
- `record_class.json` and `record_envelope.json`, generated from the table of v1's
  tpm_record_schema 0.3.1 by `scripts/record_table_vectors.py` (`--check` compares; CI's
  docs-lint job runs it): per class its layout, whether it is pushed, landing grade,
  grades and statuses; and the envelope fields it carries in order, each with type,
  cardinality, required, writer and digest membership. PMA words replace v1's as the
  script states.
- `derivation_class.json`, hand-written: each form's check class, the form-level credit
  for every form verified and not, the credit of a derivation given the set of
  derivations the checker accepts (a verdict on another derivation, or on an attachment's
  payload, credits nothing), both orders over every pair, and the form of a derivation
  and of an attachment. The derivation input shape there is the runner's, not the wire
  form, which comes with the canonical serializer.
- `canonical_json.json`, hand-written, for the canonical serialization
  (`Principia/Canonical.lean`, run by `Tests/Canonical.lean`): TPM's canonical JSON
  (tpm_record_schema 0.3.1, 11.4) over every kind of value, with keys given out of order,
  in code point order beyond the Basic Multilingual Plane, at every depth, and a key given
  twice (refused); v1's `canon`; and the reading of a JSON number literal into an integer
  or an exact decimal. Values are written in a tagged form, so that member order and a
  repeated key survive `Lean.Json`, which reads the corpus. The expectations were checked
  against an independent transcription of v1's writers with exact decimals.
- `digest_preimage.json`, hand-written, for the digest preimages (`Principia/Digest.lean`):
  the tree encoding of a zone's preimage (v1 tpc_zone `_node`, D99), one tree being the
  hand-built preimage of a minimal Criteria Set from `zone_corpus.json`; field lists with
  integers; digest lists and the digests they refuse.
- `permissions.json`, hand-written from v1's PERMISSIONS table (TPS 0.5.0, 5.13.2; there
  is no v1 corpus), run by `Tests/Permissions.lean` against
  `Principia.Permissions.permits` (`docs/design/pma_permissions.md`): one case per table
  cell, every asker (the six roles, the Holder, the Coworker and an agent in no lock
  state) on every one of the 40 page classes, each naming the v1 cell it transcribes and
  listing the operations permitted, every other operation checked refused; the two cell
  conditions the server check enforces, refused; the CLOSED PREDICATE (CLOSED unlisted,
  listed, OPEN) over every asker and class; DOSSIER READ over every restricted class,
  asker and setting; the refusals each theorem names, one operation each; the wire words
  of the eight enumerations and words that must not read; each role's MediaWiki group
  (`Role.group`); and the request `pcalc permits` reads from its words, with its verdict.
  The Contributor, which v1 lacks, has no column and holds exactly the Public's cells
  (`contributor_as_public`), so its cases are the Sponsor's, asker for asker. The runner
  fails a corpus that leaves any asker on any class without a cell case, or any role
  without a group case. No corpus moves for the groups lines and the terminology page,
  which name `pma-contributor`.

- `units_helpers.json`, written by hand: the helpers of the units family that v1's corpora
  test only through other functions (`dimension_out_of_range`, `_dec_sign`,
  `_is_pos_finite`); `_is_pos_finite`'s expectations are CPython's `float()`, which is v1's
  definition of that test, at the exact halfway points 2^-1075 and 2^1024 - 2^970 too.
- `units_range.json`, written by hand: the double range, which v1 refused a unit scale or a
  normalized value outside of and the Calculator keeps, decided on the exact value
  (`Exact.Product.range`). Cases at each bound, just inside and just outside, exact ties
  included, with and without a power of pi, some within 2^-60 of a bound so that the
  first intervals cannot decide; and short units whose scale no double holds, refused
  without their exact value being formed. Expectations are exact (Python integers and
  fractions, pi from Machin's formula with an error bound).
- `eom_corpus.owed.json` and `settlement_corpus.owed.json`: the cases of those two v1
  corpora the Calculator does not answer yet, each with its reason; none at present.
- `units_pi.json`, written by hand: the Calculator's enclosure of pi (`Exact.piInterval` at
  64 to 4096 bits, `Exact.piPowBounds`) checked against 1400 reference digits, the sign of
  a polynomial at a power of pi (`Exact.polySignAtPiPow`) including one too close to zero
  for 4096 bits to decide, and the strike rule's wrappers across powers of pi (a degree
  against a radian), SR8's scale factor across powers of pi among them, its `S` computed
  independently by `scripts/pi_scale_check.py` (Python's decimal at 120 digits, pi by
  Machin's formula; `--check` compares it with the vectors). The digits were computed by
  two independent tools, mpmath 1.4.1 and
  pidigits 0.5, which agree on all of them; the published tables (OEIS A000796's b-file,
  Project Gutenberg eBook 50) were not reachable from the session that wrote the file, and
  its meta records the digits' SHA-256 so that a check against one is a single comparison.
  The enclosure's correctness rests on these vectors, not on a proof. Neither tool is
  installed by the build or the checks.
- `units_corpus.divergences.json`: the cases of `units_corpus.json` where the Calculator's
  answer departs from v1's, each with v1's expectation, the Calculator's answer, the cause
  and the reason (see below).
- `structured_check.json`, written by hand, for the STRUCTURED derivation checker's first
  and second increments (`Principia/StructuredCheck.lean`, run by
  `Tests/StructuredCheck.lean`): 38 derivations, each with its law table, start, steps,
  goal and verdict, 17 accepted (one citing an ASSUMPTION record, one through a quotient,
  6 citing a law by an instance of it) and 21 refused (a wrong rewrite, a missing law or
  record, a record cited as a law, a final mismatch, identities misapplied, a path off the
  tree, a law cited exactly applied to an instance; and by instance: one symbol for two
  different subterms, an operator, an exponent, a literal, a derivative's names, not as
  stated, a missing law, a missing record); 25 matches of a pattern against a target, each
  with the substitution `matchExpr` finds or none, every substitution found checked to make
  the pattern the target; and 8 values of `eval` under the runner's interpretation, a
  divisor worth zero among them.
- `json_text.json`, hand-written, for the Calculator's reader of a request
  (`Principia/CanonicalReader.lean`, run by `Tests/Calculator.lean`): valid texts with
  the value read (tagged, member order kept) or its canonical JSON, and refused texts with
  the refusal and the character it was found at; `bytes` in hexadecimal where the text is
  not UTF-8. RFC 8259's edges: white space, every escape, surrogate pairs and lone
  surrogates, raw controls, leading zeros, a byte order mark, NaN, comments, trailing
  commas, a key twice (after unescaping), nesting at the bound and one past it, the number
  bounds. Every value read must also read back alike from its canonical JSON. The valid
  texts were cross-checked against Python's strict reader with exact decimals; Python is
  laxer only on the bounds and on lone surrogates. The runner builds the texts too long
  for a line: one of exactly `maxTextBytes` bytes and one byte more, and numbers of 4096
  and 4097 digits.
- `pcalc.json`, hand-written, for `pcalc <family> <function>` (`Principia/Calculator.lean`,
  run in-process by `Tests/Calculator.lean`): per case the arguments, stdin (`stdin_hex`
  where it is not UTF-8), stdout byte for byte and the exit code. Answers were rendered
  by an independent canonical writer; the record answers are the rows of
  `record_class.json` and `record_envelope.json`; the probe answers are v1's, given by
  `docs/v1/tpc_py/tpc_probe.py` (`run_case`) for each request.
- `form_numbers.json`, written by hand: the declared forms' evaluator where a value has
  no exact form (exp, ln, sin, cos, tan, roots, sums of different powers of pi, numbers
  past the bound on their digits), held between outward-rounded bounds
  (`Principia/Form/Interval.lean`). 58 cases in eval_form's shape, run by
  `Tests/Form.lean`; their expectations were computed independently of the Lean code, with
  Python's decimal module at 120 digits (pi by Machin's formula, sin and cos by their series
  after reduction by whole turns), each value rounded once to twelve digits. `OWED` marks
  a case the Calculator must not answer: a value exactly zero but not known so, tan at an
  odd multiple of pi/2.
- `form_corpus.owed.json` and `form_corpus.divergences.json`: the cases of
  `form_corpus.json` the Calculator does not answer yet, with the reason, and those where
  its answer departs from v1's, with both texts, the cause and the reason (see below).
- `falcon_hand.json`, written by hand for the falcons (`Principia/Falcon/`, run by
  `Tests/Falcon.lean`): 240 cases in the corpus's own form, chosen to reach what
  `falcon_corpus.json` leaves out (RFC 3986's dot segments and case rules, SM2's repeated
  decodings with overlong, surrogate and truncated UTF-8, CODE HOST templates, the
  accounting reading, declared two-word affixes, the stop's resumption, equal times in the
  stage, the draw with kept and prior accounts, the reconciliation's dispositions, the
  schema's escapes). Every expectation is v1's own answer, computed by `run_case` of
  `docs/v1/tpc_py/tpc_falcon.py` through `scripts/falcon_hand_vectors.py` (`--check`
  compares). Every input lies within the NFC stopgap and no draw needs the digest, so all
  240 must pass and none is owed.
- `governor.json`, written by hand for the governor's admission (`Principia/Governor.lean`,
  run by `Tests/Governor.lean`; v1 has no corpus and no code for the governor, its TPX
  0.6.0 having none): 24 lane cases (TPS 5.3.33 with version 1's ruling at 7.2.30), 41 seat
  costs (7.2.24,
  7.2.30; `null` where the table prices nothing), 66 jitters, 127 pressure levels and
  803 admissions (the pressure levels' cases below), each with
  the decision, its HTTP status, the refusal's reason, payer or cap, the Retry-After and the
  charge to both seat buckets: every request idle, under AGENT STOP and SUSPENDED; the rate
  at each bucket's boundary, draining, both payers over, lane 2 in debt, more seats than a
  burst (conforming on an empty bucket), rates of 0, 7 and 5000 an hour, a clock
  behind a bucket; every slot cap and pool split, with the slot refusal's Retry-After and
  its jitter; every request with GOVERNOR OFF, under the switches and at each slot
  cap; the steps' order; large numbers; and a sweep of 300 drawn by a fixed
  generator. Their expectations are computed by `scripts/governor_hand_vectors.py`, a
  transcription of TPS 5.3.33, 5.3.35, 5.3.36, 5.9.18 and 7.2.24 and of the Declarer's
  answers on the slot refusal's Retry-After, the seats and GOVERNOR OFF, written apart from
  the Lean file, GCRA by
  its theoretical arrival time in exact fractions where the Lean code keeps a bucket level
  (`--check` compares; CI's docs-lint job runs it). Before each admission is compared, its
  expectation is mutated once and must be refused.
- `probe_corpus.owed.json`: the cases of `probe_corpus.json` whose answer waits on an open
  decision, each with its reason (`draw`: SHA-256; `nfc`: a FINDING holding a code point
  outside the Unicode stopgap's tables). The list was derived by running v1's reference
  module with its draw and NFC entry points instrumented; the runner checks it both ways
  (an answer owed must be listed with that reason, a listed case must be answered owed).
- `beta_corpus.divergences.json`: the 2 cases of `beta_corpus.json` where the Calculator's
  answer departs from v1's, each with both texts, the cause and the reason (see "The 33 v1
  corpora" below); `score_corpus.owed.json`: the 16 cases of `score_corpus.json` the
  Calculator does not answer yet, with the reason.
- `sha256.json`, written by hand, with `SHA256ShortMsg.rsp` and `SHA256LongMsg.rsp`,
  NIST's, for SHA-256 (`Principia/Sha256.lean`, run by `Tests/Sha256.lean`). The two
  response files are NIST's CAVP test vectors for byte-oriented SHA-256, taken whole from
  https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip,
  downloaded 2026-10-15 (the zip: 4,909,729 bytes, SHA-256
  `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`), and copied byte
  for byte with their CRLF line ends (`.gitattributes` keeps them): `SHA256ShortMsg.rsp`,
  65 messages of 0 to 64 bytes, SHA-256
  `75e1cb83994638481808e225b9eb0c1ebd0c232d952ac42b61abce6363be283c`;
  `SHA256LongMsg.rsp`, 64 messages of 163 to 6400 bytes, SHA-256
  `6fac36f37360bcf74ffcf4465c18e30d6d5a04cc90885b901fc3130c16060974`. `sha256.json`
  records those digests and counts, which the runner checks, so a changed byte fails; FIPS
  180-4's three examples, "abc" and the 448-bit two-block message from NIST's examples
  page (SHA256.pdf) and one million "a" from FIPS 180-2's Appendix B.3; and the padding's
  size at each block boundary. Every MD and every example's digest was checked with
  Python's `hashlib.sha256`, an independent implementation, before commit. The 129
  messages and the three examples take about 0.1 s in `lake test`.
- `structured_credit.json`, written by hand, for the credit through the STRUCTURED checker
  (`Principia/StructuredCredit.lean`, run by `Tests/StructuredCheck.lean`): 30 records,
  each with its RESULT's EQUATION, its laws (written out, or `sources`: a Starting Set,
  the register's records and the record's ASSUMPTIONS, assembled by `recordLaws`) and its
  derivation (its steps and, optionally, its start), and the expected verdict and
  DERIVATION_CLASS; and 5 law tables `recordLaws` assembles, entry by entry. Accepted
  (MECHANICAL): an ASSUMPTION record cited, identities only, a law backward, a table
  assembled from its sources, and starts from a law, an ASSUMPTION record, an expression,
  the right side, and a law in no step. Refused (INSPECTION): not as stated, a missing law
  or record, a final mismatch, an identity misapplied, an ASSUMPTION record the record
  does not name, a LAW in words only, a RESULT named, a Starting Set ASSUMPTION entry
  cited, a start not carried to the EQUATION, a start the table lacks. Unreadable
  (INSPECTION): a step without a site, an unreadable site, an unknown identity,
  unreadable EQUATIONs, a late unreadable step, an unreadable start. PROSE and KERNEL
  (INSPECTION).
- `structured_wire.json`, written by hand, for the wire form of a STRUCTURED payload
  (`Principia/Record/StructuredWire.lean`, run by `Tests/StructuredCheck.lean`): 28 JSON
  texts, read by the Calculator's own reader. 7 read as payloads: each is compared field
  by field with the runner-shaped derivation, written back as exactly its `canonical`
  text, read back, and 6 of them checked and credited. The canonical texts were written
  by an independent writer of section 11.4; the texts read have white space, members out
  of order and `\u` escapes, and one holds a quotation mark, a reverse solidus, a tab and
  characters beyond ASCII. 21 are refused, each with its place and word.
- `pcalc.json`'s 19 `eom` requests (`Principia/Calculator/Eom.lean`): the five functions,
  `eom_map`, `eom_findings`, `eom_class` (STRUCTURE_CHECK on and off), `eom_register_test`
  and `settlement_check` (settled by the test, and refused REC-86 and REC-88); v1's
  REFUSED values (a TFK not an object, a NAME not an identifier, an EQUATION that does not
  parse); three `BAD_ARGUMENT` refusals of the request; and each bound at its value and
  one past it (64 DOFs, 64 records, an EQUATION of 16384 code points). Their answers were
  given by `docs/v1/tpc_py/tpc_eom.py` for each request and written by an independent
  canonical JSON writer. No eom answer is owed, so there is no owed request.
  `eom_corpus.json` (421) and `settlement_corpus.json` (17) also run through `pcalc eom`
  (`Tests/Calculator.lean`, `runEomCalls`): 438 of 438, compared as v1's `canon` text and
  as canonical JSON respectively; a case in `<corpus>.owed.json` must come out `OWED`
  (none is listed). The family bounds' runner checks each eom bound at its value and one
  past it (17 cases). The bounds, measured through the built `pcalc` on 2026-10-18 (CPU
  time, the machine shared with other builds): 64 entries in each of the TPK's DOF,
  CONSTANT, LAW and CONSTRAINT kinds; 64 records, status words and namings; an EQUATION's
  text at most 16384 code points before NFC (the declared forms bound a form at 4096 after
  it). The slowest found at the bounds: a register test of 64 laws and 64 records, each a
  form of about 4096 code points naming every unknown at varied orders, 0.8 s; the 64 laws
  alone, 0.26 s; a settlement check at the bounds, 0.41 s; an EQUATION of 16384 code points
  of combining marks to reorder, 0.08 s. Without them, 200 entries took up to 14 s, and
  normalizing a 1 MiB EQUATION 1.7 s (now refused by the bound in 0.05 s).
  `Principia.Eom.augment` kept no visited columns across a failed branch, unlike v1's
  `_max_matching`, and took 12 s at 20 unknowns (more than 2 minutes at 24); it now
  shares them through the search, and every corpus answer is unchanged.
- `pcalc.json`, the falcon family (`pcalc falcon`; `Principia/Calculator/Falcon.lean`): 26
  cases, at least one per function, from the built binary; each answer is also v1's, given
  by `run_case` of `docs/v1/tpc_py/tpc_falcon.py` for the request and written by an
  independent canonical writer. The functions take v1's own names (`falcon_canon`,
  `falcon_draw`, `falcon_quote_match`, `falcon_reconcile`, `falcon_schema_canon`,
  `falcon_schema_digest`, `falcon_stop`, `quote_check`, `source_hop`, `source_match`,
  `sponsor_stage`) and v1's arguments by the names its `run_case` gives them. Among the
  cases: v1's refusals as `BAD_ARGUMENT` with v1's word (`date`, `n`, `accounting`,
  `schema`, `counts`, `publisher`), a `page` of `null` answered UNKNOWN, an output schema's
  string not in NFC refused and its NFC digested, a schema's string at its bound of 100
  characters and one past it, a missing argument, and v1's corpus name `canon` refused as an
  unknown function. None is owed. v1's corpora run through the family by
  `Tests/Calculator.lean` (`runFalconCalls`, `respondTo`): `falcon_corpus.json` 949 of 949
  and `falcon_hand.json` 259 of 259, none owed (`falcon_corpus.owed.json` names none), no
  divergence; `runFalconBounds` checks each bound at it and one past it (40 cases) and that
  the item lines' case is built at exactly its bound. The bounds, measured on the built
  binary on 2026-10-18 (best of three runs, the slowest shape found): the request's strings
  at most 200,000 characters in all, one run of 199,900 combining marks put in NFC taking
  0.9 s; the QUOTE CHECK's text sought times the text searched at most 2,000,000 (it
  compares the one at every position of the other), a page of 199,000 characters that NFC
  turns into three each, with a quote of 10, taking 1.2 s and ordinary text 0.2 s (a value
  of 15,000 characters in a quote of 30,000 took 6.3 s); `falcon_draw` at most 100
  candidates and kept accounts and 1000 prior assignees, three drawn from 80 eligible with
  20 kept taking 0.57 s (three from 300 took 13.9 s, two from 3000 101 s); schemas and specs
  at most 100 fields, 100 columns and 1000 enum values in all (50,000 values took 4.5 s)
  and strings of at most 100 characters, 0.06 s; `falcon_reconcile` at most 10 outputs and
  as many quotes entries, 1000 rows and 1000 quote outcomes in all, two outputs of 200 rows
  of 100 columns taking 0.74 s (10,000 rows took 6.9 s), and item lines of at most
  1,000,000 characters of identifiers and values, counted before the answer is written, a
  row's key standing in the line of each of its columns and votes (a key of 45,000
  characters over 100 columns wrote 13 MB in 6.8 s, now refused in 0.04 s);
  `sponsor_stage` and `falcon_stop` at most 10,000 events or records, 0.51 s and 0.78 s
  (30,000 took 5.0 s and 6.2 s); `source_match` and `source_hop` at most 1000 entries and
  CODE HOST marks and 1000 templates in all, 0.15 s (20,000 marks took 7.8 s). No falcon
  answer forms an exact fraction, so the bound on an exact value has nothing to bound here.
- `pcalc.json`, the identity, sponsor and lint families (`pcalc identity`, `pcalc sponsor`,
  `pcalc lint`; `Principia/Calculator/Identity.lean`, `Sponsor.lean`, `Lint.lean`): 34
  cases, at least one per function, from the built binary; each answer v1 gives (25) is
  also v1's, given by `run_case` of `docs/v1/tpc_py/tpc_identity.py`, `tpc_sponsor.py` and
  `tpc_lint.py` for the request. Among them: v1's refusals as `BAD_ARGUMENT` with v1's
  word, a missing argument, one the function does not take, a zone given as bytes that are
  not UTF-8 and one past v1's 1 MiB, the lint's findings one past their bound and their
  counts, and the sponsor's bounds on digits and shapes at and past them, and a half-life
  of `1e-30` refused by the bound on an exact value (`evidenceFits`, checked before each
  aged weight, sum, shape and mean is formed). None is owed. v1's corpora run through the
  families by `Tests/Calculator.lean` (`respondTo`): `identity_corpus.json` 102 of 102,
  `sponsor_corpus.json` 83 of 83, `lint_corpus.json` 231 of 231, none owed (the owed lists
  name none), no divergence; `runFamilyBounds` adds each list bound at it and one past it.
  The bounds, measured on the built binary on 2026-10-18 (the worst found): `identity` has
  none of its own beyond the request's 1 MiB, a 680,000-character template of letters and
  combining marks taking 0.55 s, a tools object of 80,000 members 0.4 s and a MODEL MAP of
  13,000 rows 0.2 s (before its port sorted them once, 6,500 members took 8.5 s and 1,000
  rows of combining marks 24.7 s). `lint` lints v1's 1 MiB of zone and of tools and writes
  at most 1,048,576 characters of findings (19,993 zero-width spaces at the bound, 19,994
  past it; 1 MiB of them wrote 18,763,246 characters in 11.7 s); the slowest `lint`,
  refused, takes 1.6 s, `counts` 1.45 s. `sponsor user_evidence` takes at most 50 events,
  numbers of 30 digits and shapes `a0 + F_u`, `b0 + A_u` from 1/10 to 1000, the slowest
  accepted 1.8 s (100 events took 2.5 s and 1000 14.5 s; `Beta(0.01, 1)` with 50 events
  over 4 s; `Beta(0.001, 1)` unsettled at 4096 bits after 110 s); `whitewash_count` at most
  4000 admissions, retirements and states, 0.3 s (6000 took 1.1 s).
- `pcalc.json`'s 39 `provision` requests (`Principia/Calculator/Provision.lean`): one per
  function, the smallest answered case of each in `module_corpus.json`; two of v1's REFUSED
  values (exit code 0); two refusals of the request (`BAD_ARGUMENT`); the owed request, a
  `module_check` whose test binding holds the law `k=exp(1)-exp(1)` with `k` 0, which no
  exact bounds settle (refused `OWED`), beside its settled control `k=exp(1)-exp(2)`; and
  each bound at its value, seven of them also one past it. Their stdout is the built
  binary's; the 28 answers v1 gives are also v1's, given by `run_case` of
  `docs/v1/tpc_py/tpc_module.py` for each request. `module_corpus.json` (418) also runs
  through `pcalc provision` (`Tests/Calculator.lean`, `runProvisionCalls`; `text_parts`
  joined as v1's `run_case` joins them): 418 of 418, each answer compared with `expected`
  through canonical JSON; a case in `module_corpus.owed.json` must come out `OWED` with its
  reason's words (none is listed). `runProvisionBounds` checks each bound at its value and
  one past it (52). The bounds, measured through the built `pcalc` on 2026-10-18 (CPU time,
  the machine shared with other builds; the slowest request found within each): 8 texts in
  `modules` and 65,536 bytes of texts in all where a function takes them, `module_check`'s
  own text counted (8 test bindings paired with 4 other Provisions, the text's 32
  PROPOSITIONs nested 128 deep, 1.37 s); in every Starting Set a request carries, its own
  and each test binding's in each text, 64 entries of each kind, 1,024 in all, 128 names in
  a REFS, 16,384 code points in an EQUATION or CONDITION and 256 in a PROPOSITION or
  PREDICATE, a text's own counted as written and once each `{SLOT}` is filled with the names
  bound to it (`draft_module_status` re-expanding 4 superseded claims over a draft of 64
  DOFs and 64 laws, 1.66 s; `module_verify` with a base and a draft of 384 entries each,
  1.15 s; `module_expand` 0.75 s; `module_bind` 0.47 s; an over-determined draft of 61
  unknowns and 62 laws, every law naming every unknown, 0.11 s); 64 term placements, each
  term on each name its target is bound to (0.46 s); 256 declaring lines (0.14 s; 1,024
  took 2.5 s, 2,048 14 s), 8 claims, 64 rounds, 64 claims carried and Provisions modified
  (the interview 0.11 s), 1,024 certificates naming 4,096 Provisions (0.23 s). Without
  them, 32 PROPOSITIONs of `{S}` filled with 16 names of 100 code points took
  `module_check` 15.9 s (`module_expand` 4.2 s and 400 MB), one PROPOSITION of 40,000 words
  17.8 s (T2's word scan in `Principia/StartingSet/Tests.lean`, quadratic in the words), and
  8 claims of 256 placements on laws of 4,096 code points 2.7 s. The structure check's times
  are measured with `Principia.Eom.augment` sharing its visited columns through a search,
  as the eom family's command makes it; without that, an over-determined draft of 24
  unknowns took 53 s and one of 32 did not finish in 300 s. The strict reader of a
  Provision's text (`Principia/Provision/Reader.lean`) measured the rest of the text for
  every string and number, appended to its lists and compared each key with all before it:
  a 256 KiB text of short strings took 34 s, of small numbers 133 s, an object of 22,800
  members 24 s; it is now linear (0.08 s each), every answer of the corpus unchanged.
- `pcalc.json`'s 53 requests of the register functions (`Principia/Calculator/Record.lean`):
  one per function, v1's smallest case (one answered `["OK", ...]` where there is one) with
  its `expected` as the answer; the verification's difference refused `OWED`, its detail
  naming what it waits on; two refusals of the request (a member the function does not
  read, a request that is not an object); and each bound at its value and one past it
  (1024 entries in a list, a string of 16384 code points, 64 records in a register, 512
  CITES, ASSUMPTIONS and ENTRIES in its records, 64 open audits), a budget's square at and
  past the bound on an exact value, and a point past it. The new requests' answers were
  given by `docs/v1/tpc_py/tpc_record.py` (`run_case`) for each request; the refusals are
  the Calculator's own. `record_corpus.json` (932) and `record_view_corpus.json` (213) also
  run through `pcalc record` (`Tests/Calculator.lean`, `runRecordCalls`): 1145 of 1145,
  each answer's canonical JSON v1's `expected`, none refused `OWED` (the owed list is empty
  since the verification's difference is computed exactly). `runRecordBounds` checks
  each bound at its value and one past it (21 cases), among them the bound on the code
  points of all a request's strings (131072), too long for a line of `pcalc.json`. The
  numbers the measured fields and `budget_check` form from a request are checked first
  against the bound on an exact value (`Principia/Record/Bounded.lean`; `normalizeWithin_ok`
  and `budgetWithin_ok` prove that an answer given is the unchecked one): no case of either
  corpus comes near it, and every answer is unchanged. The bounds, measured through the
  built `pcalc` on 2026-10-18 (CPU time, the machine shared with other work): 1024 entries
  in any list or object, 16384 code points in a string and 131072 in all, 64 records in a
  register with 512 CITES, ASSUMPTIONS and ENTRIES in all, 64 open audits. The slowest found
  at the bounds: a promotion pass over 64 records in a chain, one holding 385 ASSUMPTIONS,
  with 64 open audits, 0.70 s; the digest of a RESULT whose 1024 BUDGET components hold
  130,000 code points of combining marks to reorder, 0.49 s; a MASTER checked against a
  Starting Set of 28 laws of 4000 code points, 0.44 s; a citation check over 63
  WITHDRAWALs naming 6300 records, 0.29 s; `gap_records` writing 2048 gaps, 0.27 s; a
  request of a mebibyte past the bounds is refused in at most 0.43 s. Without them a SET
  of 64000 members took 27 s, the promotion over 256 records in a chain 9.2 s (v1's own
  module 4.0 s), over 64 records with 1024 ASSUMPTIONS 1.5 s and with 250 ENTRIES each
  3.0 s, and NFC of 500000 combining marks 4.7 s. `hunk_corpus.json`,
  `hunk_wiki_corpus.json`, `fingerprint_corpus.json`, `challenge_corpus.json` and
  `volunteer_corpus.json` test v1's `tpc_hunk`, `tpc_fingerprint`, `tpc_challenge` and
  `tpc_volunteer`, which the record functions do not port; none runs through `pcalc
  record`.
- `pcalc.json`: 57 cases for `pcalc score` (`Principia/Calculator/Score.lean`): at least one
  per function, each of those answers checked against v1's own `run_case`
  (`docs/v1/tpc_py/tpc_score.py`, `tpc_beta.py`); v1's refusals; a member the function does
  not take; the Beta layer's bounds at and past each; the evidence's bound on a coefficient;
  the bound on an exact value (see "The bound on an exact value"); and one owed request,
  `betainc` of 999 and 1 at `1e-8`, exactly `1e-7992`, below what the bounds hold.
  `Tests/Calculator.lean` sends `score_corpus.json` (487) and `beta_corpus.json` (99, its two
  recorded divergences accepted as `Tests/Beta.lean` accepts them) through `respondTo
  "score"` (`runScoreCalls`, 588 checks, none owed) and checks each of the family's bounds at
  it and one past it (`runScoreBounds`, 40 checks). The bounds, measured on the built binary
  on 2026-10-18, the slowest request found at each: the quota's window 10,000 entries,
  0.12 s (0.79 s with weights of 80 digits); accounts 2,000, 0.18 s for `rank` and 0.28 s
  for `prime_select` (0.61 s for `rank` with names of 400 characters differing only at
  their ends); pending items 5,000, 0.48 s (0.58 s with names of 110 characters); the peer
  activity's events 5,000, 0.15 s (0.22 s);
  prior ages 100,000, 0.23 s; each list of an override's or a pad's facts 10,000 (7,000 and
  7,000 fit in a request, 0.09 s); `evidence` 10,000 events whose sums F and A hold at most
  64 powers of 2 together, 1.7 s at 10,000 events and 3.0 s with shapes near 10,000; agents
  1,000, 0.03 s (0.12 s with names of 900 characters); 30 pooled events in all, 1.9 s for `user_aggregate` and 2.2 s for
  `user_score_evidence` (40 took 3.3 s and 300 took 69 s); 10,000 CONDUCT EVENTS beside them,
  3.8 s; the Beta layer's incomplete function and quantile with shapes from 0.1 to 10,000,
  tails of at least 0.000001 and numbers of at most 4096 bits, 0.94 s at the corners.
  Outside these the quantile's search ran through every precision before it was owed:
  shapes 30,000 and 1, 152 s; a shape of 0.00001, 164 s; a tail of 1e-12 beside a shape of
  100 or more, 24 s to 34 s. An owed answer within the bounds takes longer than an answer:
  8.8 s for a quantile on a rounding boundary (`betainc_inv` of 1 and 1 at
  `0.1234567890125`), up to 6.0 s for an incomplete function whose exponential falls below
  what the bounds hold.
- `pcalc.json`'s 21 requests of the family `biblio` (`Principia/Calculator/Biblio.lean`):
  one per function, taken from `biblio_corpus.json`'s first answered case of each, two of
  its refusals and two requests that do not read. `biblio_corpus.json`'s 405 cases run
  through the family in-process (`Tests/Calculator.lean`, `runBiblioCalls`), each answer
  rendered back into version 1's text (`biblioRender`) and compared byte for byte, and
  `runBiblioBounds` (8 cases) puts each bound at and past it.
- `pcalc.json`'s 8 `derivation` requests (`Principia/Calculator/Derivation.lean`): `credit`
  accepted, refused at a step (`not-as-stated`), unreadable (`no-site`), and a payload the
  reader refuses (`BAD_ARGUMENT`, `step 1: missing FORWARD`); `credit_record` refusing a
  step that cites an ASSUMPTION record outside the record's ASSUMPTIONS
  (`missing-citation`); `laws` (a LAW in words only and a RESULT named left out); and a
  Starting Set kind at 64 entries and past it. `structured_credit.json`'s 30 records run
  through `credit_record` (the DERIVATION in its shape-told wire form; KERNEL refused `OWED`)
  and each STRUCTURED one through `credit`, and `structured_wire.json`'s 28 texts through
  `credit`, the 21 refused ones `BAD_ARGUMENT` with the reader's word (`Tests/Calculator.lean`,
  "pcalc derivation (structured_credit, structured_wire)", 58 cases); "pcalc derivation
  bounds" puts each bound at and past it (15 cases).
- `pcalc.json`'s 11 requests of the family `fundamental`
  (`Principia/Calculator/Fundamental.lean`): one per function, taken from
  `tests_corpus.json`'s cases with their expectations, a final pass that passes, version 1's
  name `kernel_tests` refused `UNKNOWN_FUNCTION`, a PROPOSITION that is not a string and a
  missing argument refused `BAD_ARGUMENT`. `tests_corpus.json`'s 120 cases run through the
  family in-process (`Tests/Calculator.lean`, `runFundamentalCalls`), and
  `runFundamentalBounds` (7 cases) puts each bound at and past it.
- `pcalc.json`'s 16 requests of the families `governor`, `permissions`, `sha256` and
  `unicode` (`Principia/Calculator/Governor.lean`, `Permissions.lean`, `Sha256.lean`,
  `Unicode.lean`): one per function, the admission's `BAD_ARGUMENT` for a state without a
  switch, a hexadecimal text and a context that do not read, and a falcon RETURN of 21 rows
  refused `OWED` (inventory U4); each expectation written by hand, the digests from
  Python's `hashlib`, the domain from `permissions.json`'s members. Their corpora run
  through them, in-process (`Tests/Calculator.lean`): `governor.json`'s 709 cases, its Lean
  names given as the wire words (`wire_words.json` gains the admission's seven
  enumerations), an `admit` case checking `admit` and `charge` in one, the 4 cases whose
  seat cost is `null` refused `OWED` with the detail that names U4; `permissions.json`'s
  cases but `AccountClass`'s members (8,759 checks: a cell one per operation, a word in its
  place, a word arm's request as the same words), and the domain's 96 contexts distinct and
  complete; the 129 CAVP messages through `digest` and FIPS's 3 examples through
  `digest_text`; every line of NormalizationTest.txt (19,074) through `nfc`, `nfd` and
  `general_category`, the categories against UnicodeData.txt. `runRequestBounds` (15
  cases) puts each bound at and past it: a text of 131,072 code points and one more, a
  request of 1 MiB and a byte more, every governor number near 2^1024, 100,000 context
  words.
- `pcalc.json`'s 8 requests of the family `hold` (`Principia/Calculator/Hold.lean`): one per
  function, taken from `hold_corpus.json`'s first case of each, version 1's name
  `tpx_allocate` refused `UNKNOWN_FUNCTION` and a missing argument refused `BAD_ARGUMENT`.
  `hold_corpus.json`'s 140 cases run through the family in-process (`Tests/Calculator.lean`,
  `runHoldCalls`), and `runHoldBounds` (6 cases) puts each bound at and past it.
- `pcalc.json`'s 5 requests of the family `yardstick` (`Principia/Calculator/Yardstick.lean`):
  one per function from `yardstick_corpus.json`'s first answered case of each, a Criteria
  Set that is not well formed, refused as a value, and a request without its suite refused
  `BAD_ARGUMENT`. `yardstick_corpus.json`'s 46 cases run through the family in-process
  (`Tests/Calculator.lean`, `runYardstickCalls`), a key's values compared exactly.
- `pcalc.json`'s 23 requests of the family `zone` (`Principia/Calculator/Zone.lean`) and the
  name `criteria_set_params_ok` of `sr9`: one per function, taken from `zone_corpus.json`'s
  cases with their expectations; `dimension_out_of_range` at and past its bound; a value
  that is not a string (`null`); a zone that is not one, a zone the serializer cannot write
  and an exponent that is not an integer refused `BAD_ARGUMENT`. `zone_corpus.json`'s 335
  cases run through the family in-process (`Tests/Calculator.lean`, `runZoneCalls`), version
  1's seven coded names mapped to the Research Assembly's words, and
  `runZoneBounds` (8 cases) puts each bound at and past it.
- `pcalc.json`'s `strike conditions_of` request of a point of 90 deg, refused `OWED` before,
  now answers its value in radians to twelve digits, `157079632679e-11` (pi / 2 to 12
  significant digits, checked against Python's `decimal` at 60 digits).
- `governor.json`'s pressure levels (`Principia/Governor/Pressure.lean`, GA4 in
  `Principia/Governor.lean`): 127 `level` cases (the ratio at, below and above each
  threshold and exit point, at kappa_M 1 where a whole use reaches a threshold exactly and
  at 1.3 either side of it; each horizon the largest; the external reading in force, at
  its end and lapsed; each of the four readings away from its default) and 225 more `admit`
  cases (every request at every level passed; GA4's place after GA2 and before GA5 and
  GA6; GOVERNOR OFF skipping it; GA4's Retry-After under each reading; lane 6 at, below
  and past its slots at each level under `CACHED` and `SLOTS`; the level computed from
  the uses). Their expectations come from `scripts/governor_hand_vectors.py`'s
  transcription of TPS 5.3.31, 5.3.32, 5.3.34 and 5.3.40 and of the Declarer's four
  readings, each level's exit
  point written as its threshold less 0.05 where the Lean file raises the ratio 0.05; the
  first 709 cases are unchanged byte for byte. `Tests/Governor.lean` runs them (2,016
  checks), `Tests/Calculator.lean` through `pcalc governor` (1,061 cases, the `level`
  cases through the new function `pressure_level`), and `wire_words.json` gains
  `PressureLevel`, `Descent`, `PressureRetry`, `ThresholdRule`, `ExternalOrder` and
  `AnonymousFull` and the new members of `SlotCap`, `DecisionWord` and `RefusalWord`.
- `governor.json`'s traffic stages (`Principia/Governor/Traffic.lean`, GA3 in
  `Principia/Governor.lean`): 301 `traffic_step` cases (each event from each stage and at
  the hour's edges; three TE3 in an hour and ten in 24 hours, the oldest just in and just
  out; a second THROTTLED in an hour; a third PENALIZED in 24 hours; PENALIZED's end; the
  doubling per event and per refusal to the cap; every request's end against the streak,
  under each TE2 reading; the trial's every end under each trial reading; a CONTAINED
  account's answers; four sequences drawn by a fixed generator), 86 `traffic_stage` cases
  (what the check reads of each stage for each passing op and for others, at and past the
  breaker and the FLOOD INTERVAL; a TE3 at and after the Retry-After's end) and 179 more
  `admit` cases (every request at each stage; the breaker at its edge; CONTAINED's INQUIRE,
  RELEASE and STATUS inside and past the FLOOD INTERVAL; GA3's place after GA2 and before
  GA4, GA5 and GA6; GOVERNOR OFF skipping it; the halved seat rate under each payer
  reading; the breaker's Retry-After under each doubling reading). Their expectations come
  from `scripts/governor_hand_vectors.py`'s transcription of TPS 5.3.35, 5.3.37, 5.9.18 and
  7.2.21 and of the Declarer's four readings; the first 1,061 cases are unchanged byte for
  byte.
  `Tests/Governor.lean` runs them (3,148 checks), `Tests/Calculator.lean` through
  `pcalc governor` (1,627 cases, the new ones through `traffic_step` and `traffic_stage`),
  and `wire_words.json` gains `TrafficEvent`, `TrafficStage`, `Ending`, `PenalizedPayer`,
  `Doubling`, `TrialSuccess` and `Te2Causes` and the new members of `Switch` and
  `RefusalWord`.
- `pi_scale.json`, written by hand: SR3's test with the scale factor's square a ratio of
  polynomials in pi (`Strike.PiScale.exceedsPi`), 12 cases: both outcomes, a negative
  denominator, a Laurent ratio, the cases where the scale factor does not enter, a zero
  denominator left undecided, and four that pair a smaller scale square with a larger one
  (1, pi/3 and pi^2/9), the excess found at the larger found at the smaller, as
  `exceeds_pi_of_le` (`Principia/Strike/PiEnclosure.lean`) proves. The cases that compare
  are checked at 120 digits by `scripts/pi_scale_check.py --check`.
- `record_forms.json`, written by hand, for the record check's reading of a DERIVATION by
  its shape (`Principia/Record/Check.lean`, `checkDerivationForms`), run by
  `Tests/Record.lean` and through `pcalc record` (`Tests/Calculator.lean`,
  `runRecordCalls`): 20 cases. Passing at PUSH: a STRUCTURED derivation, one with a
  START, a KERNEL one, a PROSE one with a STRUCTURED and with a KERNEL attachment.
  Refused REC-41 with the reader's word: `mixed-forms` twice, `not-a-count STEPS`, a step
  with two citations, a step without FORWARD, an attachment that does not read, an
  unknown member beside a list STEPS. A PROSE derivation with an attachment keeps version
  1's STEPS bound (REC-19) and NOTBLANK (REC-11). At LANDED, REC-42 for a STRUCTURED, a
  KERNEL and an attached PROSE derivation, and `record_preimage` likewise; version 1's
  PROSE at LANDED passes. An empty DERIVATION is version 1's case (REC-08 twice), never
  `no-form`. `pcalc.json` gains 4 of them as requests.
- `record_forms.json` since the PMA row (DERIVATION_CLASS, the PMA table's row beside
  version 1's record table): 50 cases, 16 added. At LANDED, a RESULT with each of
  INSPECTION, MECHANICAL and PROVED passes; PROSE, a form word, and a number are REC-43;
  at PUSH the row is REC-07; on an ASSUMPTION it is an unknown field, REC-06.
  `record_preimage` carries the row after version 1's fields, counted with them;
  `record_digest` of the three classes answers three digests, none version 1's; at LANDED
  with its own digest the record passes, with another class's or version 1's digest
  REC-29; the view SUITE shows `derivation_class` when the row is present and is version
  1's view without it. The 7 cases at LANDED without the row now expect REC-43. Written
  from the Calculator and checked outside it: each preimage version 1's field list with
  the row appended, each digest SHA-256 of its netstrings. Of `pcalc.json`'s requests,
  the STRUCTURED record at LANDED is now refused REC-43, and one request added with
  INSPECTION is answered `["OK"]`.
- `record_corpus.json`, version 1's: its `record_check` cases are judged against version
  1's check (`recordCheckV1M`), and `record_check`'s answer must be that check's with
  REC-43 added for a RESULT at LANDED (`Checked.withAbsence`); its digests are unchanged.
- `digest_preimage.json` gains 3 `preimageFields` cases: the TPC-RECORD form 1 field list
  of a PROSE RESULT with DERIVATION_CLASS INSPECTION, MECHANICAL and PROVED, with their
  netstring preimages, checked outside the Calculator.
- `pcalc.json`'s 20 requests of the family `form` (`Principia/Calculator/Form.lean`): one
  per function, taken from `form_corpus.json`'s cases with their expectations; a missing
  `mode` refused `BAD_ARGUMENT`; 64 parentheses open at once read and 65 refused as version
  1 refused them; an evaluation the Calculator owes refused `OWED`; a binding past the bound
  on an exact value refused `BAD_ARGUMENT`, "exact value too large". `form_corpus.json`'s
  555 cases and `form_numbers.json`'s 58 run through the family in-process
  (`Tests/Calculator.lean`, `runFormCalls`, "pcalc form (form_corpus, form_numbers)", 613
  cases), the forms' runner (`Tests/Form.lean`) the reference: a case it agrees on must
  agree, compared as it compares; one it owes must be refused `OWED`; the recorded
  divergence `eval/cos` must give its recorded text. `runFormBounds` (12 cases) puts each
  bound at and past it.
- `record_forms.json` since the non-PROSE encoding (TPC-RECORD form 1's encoding of a DERIVATION
  in a form other than version 1's PROSE, `encodeDerivation`): 34 cases, the item above
  as it stood for its first 15. At LANDED with its own digest, each of the five non-PROSE
  shapes passes, where REC-42 refused three of them, and version 1's PROSE passes; with
  another record's digest, REC-29. `record_preimage` of a STRUCTURED, a KERNEL and an
  attached PROSE record, its DERIVATION one canonical JSON text; `record_digest` of each
  shape and of version 1's PROSE; a different digest when one step's EQUATION differs,
  when the PROOF differs and when a step is left out. These cases were written from the
  Calculator and checked outside it: each DERIVATION field the input's canonical JSON,
  each digest SHA-256 of the field list's netstrings. Of `pcalc.json`'s 4 requests, the
  STRUCTURED record at LANDED is now answered `["OK"]`.
- `digest_preimage.json` gains 2 `preimageFields` cases: the TPC-RECORD form 1 field
  lists of a STRUCTURED and of a KERNEL record, each DERIVATION one text field, with
  their netstring preimages, checked outside the Calculator.
- `record_forms.json` since the record check reads every text inside a derivation: 74
  cases, 24 added. RF51 to RF65 refuse one text each with REC-41 at the text's own path
  (`DERIVATION.STEPS[<i>].SITE`, `.EQUATION`, `.LAW`, `.ASSUMPTION`, `.IDENTITY`;
  `DERIVATION.START.EXPRESSION`, `.LAW`, `.ASSUMPTION`; `DERIVATION.PROOF`;
  `DERIVATION.ATTACHMENT.STEPS[<i>].SITE`, `DERIVATION.ATTACHMENT.PROOF`): a SITE with a
  disallowed code point, an empty SITE, a SITE that does not read, a step's EQUATION and a
  START's EXPRESSION that do not parse, an identity not on the checker's list, a blank or
  disallowed cited name, a PROOF with a CR, not in NFC, blank or with a disallowed code
  point; RF62 two texts, two problems. RF66 passes a clean STRUCTURED derivation with a
  START EXPRESSION and RF67 reads a clean two-line PROOF (since refused REC-44 alone, a
  bare KERNEL); RF68 refuses at LANDED before the
  digest is compared; RF69 `record_preimage` refuses a PROOF with a CR. RF70 to RF74:
  `record_view` STRIKE and SUITE give a STRUCTURED derivation's `steps` as the count of its
  steps (3, 3, 2); a KERNEL derivation's view and version 1's PROSE count are unchanged.
  Written from the Calculator and checked against `pcalc derivation credit_record` on the
  same derivations: every structured text refused here that command answers `UNREADABLE`
  with the same word, every cited name refused here it answers `REFUSED`
  `missing-citation`.
- `record_forms.json` since a bare KERNEL is refused (REC-44, `Principia/Record/Check.lean`
  `kernelProblems`): 76 cases, 2 added, 6 changed. RF03, RF67 (PUSH) and RF75 (LANDED with
  DERIVATION_CLASS INSPECTION and its digest) refuse a bare KERNEL `{PROOF}` with REC-44
  alone; RF17 answers REC-43 then REC-44; RF54 to RF56 answer REC-41 at the PROOF then
  REC-44. RF76 passes PROSE with a KERNEL attachment at LANDED, DERIVATION_CLASS INSPECTION,
  its digest from `record_digest`; RF05 and RF18 are unchanged. No digest changes: the
  preimage's check never adds REC-44. `pcalc.json`'s bare KERNEL request at PUSH now answers
  REC-44, and one request added passes PROSE with the same PROOF attached. Written from the
  Calculator.
- No corpus moves; the Custos README states DERIVATION_CLASS written at landing.
- None: machinery for the Lean edition's pages (a Python check and its three tests), no corpus.
- `ops/wiki_pages/specification/test_spec_pages.py` (the specification pages' tests, no corpus):
  now run by the wiki tests gate on every pull request touching the specification pages'
  builder, inventory or checker and on `main`, main's copy as every test file of a gate, so a
  red run no longer goes unseen.
- `docs/progress/prototype.md` (the prototype ladder, no corpus): the Acceptance cells of five
  features restated in the gate reader's grammar, so each reads whole and none is "not run":
  the minimal client (`Ran <n> tests`, n at least 78), the live exercise (the ten `step <n>`
  lines and the `PASS` line with its `;`), the refusal scrub (the cases of section F), the
  bibliography setting (the lines `PASS  L62` to `PASS  L66`) and the client's residence check
  (n at least 100). No Feature cell changed.
- `pcalc.json`'s 32 added requests (552 in all): the nine `volunteer` functions (`standing`,
  `refill`, `take`, `retry`, `intake`, `p_nw`, `pv`, `share`, `draw`), each with one answered
  pair and one `BAD_ARGUMENT` pair, a second missing-argument refusal and an unknown
  function refused `UNKNOWN_FUNCTION`; the four `probe` functions reached before only
  through `probe_corpus.json` (`probe_step`, `ratio_step`, `reset_update`, `schedule_step`),
  an answered and a refused pair each; `sr9_c2` and `sr9_c4`, two answered pairs each (the
  corpus holds no refusal of them). Each request and answer is a corpus case's: the
  `volunteer` and `probe` answers are the case's `expected` text as a JSON string, a
  refusal's detail the text after `ERROR:`, and the `sr9` answers the case's `expect` with
  its names quoted; the runner (`Tests/Calculator.lean`, `runPcalcCoverage`) takes the
  answers as they stand. The same runner reads `Principia.Calculator.families` and fails
  `lake test`, naming the family and the function, when a function has no pair in
  `pcalc.json`; on success it prints `pcalc.json: every function of the 27 families has a
  pair`.
- `ops/wiki_pages/specification/test_spec_pages.py` (the specification pages' tests, no corpus): the
  release-order test asserts the rule, not a title: the row before the release's root is the last
  version 2 row of the manifest before the release. No phase and no status row moves.
- No corpus moves. `scripts/wiki_progress.py`, `scripts/fold_landing.py`,
  `scripts/landing_notice.py`, `scripts/wiki_probe.py`, `scripts/identity_preimages.py` and
  `scripts/provision_digests.py` print their usage on `--help` and `-h` and exit 0, before any
  other work; an unknown argument keeps its nonzero exit. The tests `scripts/test_wiki_tools.py`
  and `scripts/test_landing.py` carry one case each (the first four, the second two).
- `landing_screen.json`, hand-written with the screen, for `pcalc landing strike_screen`
  (`Principia/Strike/Landing.lean`): 19 cases, each `args` through the function and its
  canonical JSON answer `expected`, or the refusal by `pcalc` written `refused <code>:
  <detail>`: pairs held CONTRADICTS (M-M, across mm and m, L-M, both records incoming, a
  citation and a citation of a citation), pairs cleared (within k u, not reached, a REFUTED
  record, a CONVENTION pair of units of different KIND), pairs held UNDECIDED (no U_C, no K,
  a dimension mismatch, a VALUE or a U_C past 1024 characters), no QUANTITY reached, the
  REC-50 refusal of a register that is not one, nine quantities reached (owed), and a
  register past the screen's bound on ASSUMPTIONS and CITES entries.
- `pcalc.json`'s 553rd request, `eval_form` of `(ln(x0)+...+ln(x63))-(ln(x0)+...+ln(x63))`
  (3,405 bytes), refused `BAD_ARGUMENT`, "budget exceeded: ...", where it took 66 s before
  and was owed. `runFormBounds` (`Tests/Calculator.lean`, 17 cases) gains five on either
  side of the precision-step budget (`Calculator.Form.stepBudget`, 1,200): one `ln` less
  itself still owed, two and 64 refused; `t3_laws` over 4 LAWs of 4 `ln` answered, over 64
  LAWs of 40 `ln` refused. `form_corpus.json`'s 555 cases, `form_numbers.json`'s 58 and the
  613 run through the family pass under the budget, unchanged; their most costly request
  spends 894 steps.
- `governor.json`, `pcalc.json` and `wire_words.json`, the Provision proposal op and the
  falcon RETURN's rounding (`Principia/Parameters.lean`, `Principia/Governor.lean`,
  `Principia/Calculator/Governor.lean`): the governed request `proposeProvision`, wire word
  `PROPOSE_PROVISION`, runs in LANE 4 beside VOLUNTEER at 4 seats, as the Declarer chose;
  a falcon RETURN costs 4 plus 1 per started group of 20 rows, as the Declarer chose, so
  `seat_cost` answers a number for every row count and never refuses `OWED`.
  `scripts/governor_hand_vectors.py` gains both rules: 4 seat cost cases that expected
  `null` now expect 6, 6, 5 and 8 (21, 39 and 1 rows; 35 rows at 10 per seat), and 19
  cases of the new kind are added (its lane, its cost, idle, the switches, the rate at its
  boundary, GOVERNOR OFF, the pressure levels, the traffic stages); the random sweep draws
  from the kinds as they stood, so its cases are unchanged. `pcalc.json` gains 4 requests
  (a falcon RETURN of 1 and 20 rows, the proposal op's cost and lane) and its 21-row
  request answers 6. `wire_words.json` lists `PROPOSE_PROVISION` among the governed
  requests. `Tests/Governor.lean` runs them (3,197 checks), `Tests/Calculator.lean`
  through `pcalc governor` (1,652 cases).
- `governor.json` and `pcalc.json`, every refusal with its Retry-After (`Principia/Governor.lean`,
  `Principia/Calculator/Governor.lean`): a switch's refusal (403), and the rate's for a
  request that never conforms (a seat rate of 0), now carry RETRY-AFTER's base with its
  jitter, as the Declarer chose, where they carried none (`null`). The 107 `admit` cases
  that changed are recomputed by `scripts/governor_hand_vectors.py`, which gains the rule;
  6 cases are added, a switch and a never-conforming rate, each with a draw, with none (a
  request's `draw` may be absent, the draw `[0, 1]` then) and with a RETRY-AFTER base of
  120 seconds; `pcalc.json` gains 2 `admit` requests, a switch's refusal with a draw and a
  never-conforming rate with none. No `admit` expectation carries `"retry_after": null`.
  `Tests/Governor.lean` runs them (3,160 checks), `Tests/Calculator.lean` through
  `pcalc governor` (1,633 cases).
- `permissions.json` (1,751 cases, two more): the Coworker's STAGING cell reads READ
  alone in the plain, OPEN and CLOSED-and-listed cases; the CLOSED PREDICATE case of the
  Coworker's listed WRITE on STAGING now expects a refusal; two cases of
  `coworker_never_writes_staging` refuse its WRITE and APPEND with every condition set.
- `reaudit_corpus.json` (13 cases, `Tests/Record.lean`, `runReaudit`): `reaudit_batch`
  (`Principia/Record/Reaudit.lean`), hand-written from `record_corpus.json`'s RB01, RA01 and
  RA04, each RESULT given DERIVATION_CLASS INSPECTION so that it passes `record_check` at
  LANDED, a failed re-check made by removing it (REC-43). The scope naming no check (nothing
  re-checked, a record that would fail included); a changed Criteria Set (K) with every record
  passing; a failed premise HELD, a gap opened and its dependent not re-promoted; a failed
  dependent HELD and its premise re-promoted; a REFUTED record not re-checked; a HELD record
  that fails staying HELD; an IC2 gap; refusals from the scope, the words, the gap records, a
  gap ID already in the register (REC-57) and the PROMOTION record. Expectations written from
  the Calculator and checked outside it against the functions the batch composes, each
  called alone (`reaudit_scope`, `record_check`, `status_next` on HOLD, `gap_records`,
  `repromote_batch` over the changed words with the gap IDs as open audits,
  `promotion_record`). `pcalc.json` gains one request of `reaudit_batch` (the failed premise),
  and the record bounds one case (a successor of 65 records refused whole).
- No corpus moves; the client README's Owed line restated.
- No corpus moves; the client README's Owed line restated.
- No corpus moves.
- `cluster_rows.json` (39 cases, `Tests/Cluster.lean`, `runRows`): `cluster cluster_rows`
  (`Principia/Cluster/Rows.lean`), each ROW's COMPOSITE SCORE, its SE under ITEM-SAMPLING (the
  exact square `se2` and six decimals) and its state, LISTED or UNLISTED with its reasons
  (TPS 5.19.6). One benchmark, three, two ROWs and two configurations, a missing core score, a
  score outside the CORE SET, SE above SE MAX, exactly at it and just above, a late release
  and a release on the update day, every refusal word and a request past the bound on an exact
  value. Expectations worked from 5.19.6 in exact fractions outside the Calculator.
  `cluster_rows.owed.json` lists the 2 cases answered `OWED`: the SE DEFINITION FIXED-SET and
  an item count in place of an SE. `pcalc.json` gains four requests of `cluster_rows`.
- `cluster_schedule.json` (59 cases, `Tests/Cluster.lean`, `runSchedule`):
  `cluster cluster_schedule` (`Principia/Cluster/Schedule.lean`), the cluster month's due rule
  from the clock and the prior page's state block, and the page's next state from each declared
  source's outcome (TPS 5.19.3, 5.19.4; SOURCE RETRY and SOURCE LOST, 7.2.24). The first run of
  a month and a second the same month, the month's last second and the next month's first, the
  year's end, the leap days of 2000 and 2028 and the common year 2100, the clock's first and
  last seconds; every source served, a failure keeping the prior page, retries inside, one
  second inside and just past SOURCE RETRY, a source recovered, the second cycle to SOURCE LOST
  and a third, a new failure beside a lost source, the first page ever failing, a failure
  carried across a month boundary; every refusal word, the block malformed and borne out by its
  sources and month or not. Expectations worked by hand from 5.19.3 and 5.19.4, the clocks
  computed apart from the Calculator. One case is owed (`cluster_schedule.owed.json`): a failing
  source the outcomes no longer name. `pcalc.json` gains three requests of the function.
- `cluster_screen.json` (50 cases, `Tests/Cluster.lean`, `runScreen`): `cluster cluster_screen`
  and `cluster cluster_text_check` (`Principia/Cluster/Screen.lean`), the EXCLUSION LIST matched
  as whole tokens without regard to ASCII case on the raw rows at ingestion and on the canonical
  identifiers after the MODEL MAP, the UNMAPPED rows held out and counted, and the page text
  check answering the first position only (TPS 5.19.5; the token rule's TK0 and TK1, TPS
  5.20.11). A token in the model, the configuration, another member and a member's name, in
  another case, as a substring of a longer token (not matched), split by a hyphen or an
  underscore, joined by an invisible character, after the map only (the family, the
  quantization), an UNMAPPED row, an empty list, a two-word pattern, a letter outside ASCII,
  page texts clean and dirty, every refusal word and the work bound. Expectations worked by hand
  from 5.19.5. No case is owed. `pcalc.json` gains five requests of the two functions.
- No corpus moves.
- No corpus moves; the Custos README states the hook that reads the table.
- No corpus moves.
- `biblio_recheck_urls.json` (48 cases, `Tests/Biblio.lean`, `runRecheckUrls`):
  `biblio recheck_urls` (`Principia/Biblio/Recheck.lean`), a recheck run's first-round lookups
  before the fetch: the due entries (an identifier a declared registry takes, and a CHECK date at
  least BIBLIO RECHECK old, or no CHECK line), no CHECK line first, then the oldest CHECK date,
  ties by `bib_id`; each identifier to its first round (DOI to the agency lookup, ARXIV, PMID,
  PMCID), its URL built by `url`; entries taken whole while they fit BIBLIO RECHECK BATCH and what
  BIBLIO LOOKUP CAP leaves of the day, the first that does not fit ending the choice (TPS 5.21.14,
  5.21.18, 5.21.19, 5.21.21). Nothing due, no CHECK line, the period's boundary and a declared
  period, a leap February in the age, ties, the order, the batch, the cap and a declared cap
  binding, an entry larger than what is left, each kind's first round in order, a kind no
  registry takes, a DOI with no agency lookup declared, no declaration, the first declaration of
  a kind, the `.` and `..` segments and a PMID `url` refuses answered LOOKUP FAILED (against the
  batch, not the cap), and every refusal word. Expectations worked by hand; the URLs those the
  `url` cases of `biblio_corpus.json` state. No case is owed. `pcalc.json` gains three requests of
  the function.

A corpus that checks nothing fails `lake test`.

## The units and dimensions corpora

`Tests/Units.lean` (the units and dimensions family) runs:
- `units_corpus.json`: all 91 cases, of `unit_parse`, `unit_scale`, `unit_matches`,
  `normalize_measurement`, `mm_contradicts_units`, `lm_contradicts_units` and
  `sr8_scale_factor_units`. 86 agree with v1; 5 are recorded divergences. The three
  wrappers call the strike rule (`Principia.Strike`), which takes rationals: measurements
  whose values share one power of pi have it divided out; SR3's tests across two powers
  (a degree against a radian, as both L-M cases do) are decided as the sign of a
  polynomial at a power of pi, with certainty, since pi is transcendental; SR8 across two
  powers is refused, owed. SR8's `S` is compared by value, v1's twelve digits against the
  exact root correctly rounded.
- `zone_corpus.json`: the 69 cases of `canon_dimension`, `normalize_dimension`,
  `is_canonical_dimension` and `canon_decimal`, all agreeing with v1. The other 266 cases
  belong to the zones' runner, and this runner counts them as left to it.
- Through `pcalc units` (`Tests/Calculator.lean`, `runUnitsCalls`, by
  `Calculator.respondTo`): every case of the seven functions in `units_corpus.json` (91,
  5 of them checked against `units_corpus.divergences.json`'s recorded answer, the record's
  v1 text against the corpus), `units_range.json` (18) and `units_pi.json` (12): 121 of
  121.
  The answer is v1's list as canonical JSON, `["OK", ...]`, `["REFUSED", reason]` or
  `["CONVENTION", reason]`, exit code 0; an exact number is a string, `Exact.render`'s
  spelling, compared with v1's digits by value; SR8's `S` a number correctly rounded to
  twelve digits, as `pcalc strike` gives it. Two answers are owed, refused `OWED` with the
  library's words: SR8 across powers of pi (`wrap/sr8-mixed-powers`) and an SR3 test that
  4096 bits of pi do not decide (`wrap/lm-straddle`). The other cases of these corpora (the
  range of an unevaluated product, pi's enclosure, the polynomial's sign) and all of
  `units_helpers.json` test the library's helpers, not a function of the family, and stay
  with `Tests/Units.lean`. `pcalc.json` gains 27 units cases, each expectation written from
  v1's corpus or the recorded divergence and checked on the built binary: at least one per
  function, v1's refusals as values, a request argument refused, the token and digit
  bounds, the bound on an exact value at a scale of 65,537 bits and at SR3 over scales of
  32,748 and 32,780 bits (answered, refused), and the owed SR8 across powers of pi.
- The family's bounds (`Principia/Calculator/Units.lean`), measured on the built binary on
  2026-10-18, where the shortest request takes 0.017 s: a UNIT or DIMENSION of 1024
  characters and 128 tokens is parsed and scaled in 0.02 s, and one of a mebibyte refused in
  0.10 s; a VALUE and UNCERTAINTY of 4096 characters in such a unit normalize in 0.03 s and
  SR3's tests over them take 0.04 s; SR8 over 100 measurements of 30 digits takes 0.29 s in
  metres, 0.39 s with exponents spread from -300 to 250 and 0.54 s each in a unit of 1024
  characters, where 100 measurements of 4096 characters took 1.8 s. `runFamilyBounds` checks
  each at its bound and one past it (11 cases).


It also checks that every number `unit_scale` and `normalize_measurement` return, over
both corpora, lies within the double range as v1 bounded it.
`Tests/Zone.lean` (the zones) runs 225 of those 266 cases of `zone_corpus.json`, the zone
checks' (`t1_well_formed` 118, `trm_well_formed` 25, `tms_well_formed` 39, `canonical_term` 10)
and `classify_successor` 33): 190 pass and 35 are owed, listed with their reasons in
`zone_corpus.owed.json` (33 the zone digests, 2 Unicode's tables). The declared forms are
read through `Principia.Form`. An owed case is neither a pass nor a failure; the runner
requires the owed cases to be exactly the listed ones. It also runs `zone_text.json`,
written by hand: the Unicode stopgap's class of every boundary of
its two tables, kept as probe points now that the stopgap is gone: each code point's
general category in Unicode 15.1.0 and v1's verdict on it, which the Calculator's
(`Principia.Unicode.generalCategory`, `Principia.Zone.disallowed`) must equal, and a refused
code point shown `<U+XXXX>` (63 of 63).

v1's expectations are its results in canonical form (`canon` of tpc_strike): a string as
itself, a list as its items joined by commas in brackets, a double to twelve significant
digits. That form is not injective (a string is written unquoted; an item holding a comma
reads as two), so the runner reads v1's text against typed values: each function's result
has fixed kinds (strings, a boolean, numbers), a text item holding a comma or a bracket
fails its case, and a number agrees when v1's digits, read as a decimal, equal the
Calculator's exact value.

The Calculator's numbers are exact, a rational times a power of pi, while the decision
between exact values and binary64 is open; v1's refusal of a scale or value that is zero
or infinite as a double is kept, decided on the exact value. A v2 divergence is recorded in
`<corpus>.divergences.json` beside the corpus, never in it: case id, v1's expectation, the
Calculator's answer (its numbers written exactly: `5e-2`, `1/60`, `1/32400 pi2`), the cause
and the reason. The runner checks both strings for every entry, refuses an entry with no
case, and checks the cause: for `rounding`, that v1's printed number is the exact value
rounded to twelve significant digits (pi bounded by Machin's formula); for
`partial product`, that v1 refused the case.
## The bibliography corpus

`Tests/Biblio.lean` (the bibliography) runs all 405 cases of `biblio_corpus.json` against
`Principia.Biblio`: 397 pass and 8 are owed, listed with their reasons in
`biblio_corpus.owed.json`, which the runner requires to be exactly the owed cases. The 8
are canonical entries, whose digest is SHA-256 (decision D2); their canonical text is still
checked and fails the case on a difference. The key form's NFD and NFC and the zones' text
rule are Unicode 15.1.0's (decision D3, `Principia.Unicode`); the 16 cases that waited on
them (13 the key form on a text that is not ASCII, 3 the text rule beyond the interim
tables) pass, no divergence. A refusal is compared by its message; an answer is read back from v1's
render (its `_esc` undone) into the function's typed result and compared as a typed value.
It also runs `biblio_table`: v1's embedded class table, carried as v1's data in
`Principia/Biblio/Table.lean`, equals the literal in `docs/v1/tpc_py/tpc_biblio.py`
character for character, every item reads, and the ranges increase without overlap.
## The Calculator's interface: `pcalc`

`pcalc <family> <function>` reads one JSON value on stdin, the request, an object of
named arguments, and writes one line on stdout: the answer's canonical JSON
(tpm_record_schema 11.4) and a line feed, exit code 0. `pcalc version` writes the
version. A refusal is the line `{"detail":"<sentence>","refused":"<CODE>"}`, exit code
2 for how `pcalc` was called (`USAGE`, `UNKNOWN_FAMILY`, `UNKNOWN_FUNCTION`) and 1 for
the request: its text (the reader's 15 codes, `Principia.Canonical.ReadError`), its
arguments (`BAD_ARGUMENT`), an answer with no canonical JSON (`NO_CANONICAL_TEXT`), or an
answer the Calculator does not compute yet (`OWED`), its detail saying what is owed. The
strike rule, the units, the sponsor, score, the Provisions and the records owe answers
today, each named in its family's corpus entry; the equations of motion, identity, the
lint and the falcons owe none.
A function's own refusals that v1 wrote as values stay values, exit code 0.

The reader's bounds: 1 MiB of UTF-8; 64 levels of arrays and objects; 4096 digits
before a number's exponent and 4 in it; a non-integer v1 would have read as an infinite
double (`|x| ≥ 2^1024 - 2^970`) refused. At the size bound a request reads and writes in
under half a second in about 120 MB.

Families now, in code point order: `biblio` (`arxiv`, `canon`, `check`, `compare`, `doi`,
`dupe`, `holdlist`, `isbn`, `issn`, `key`, `pmcid`, `pmid`, `preimage`, `shape`, `url`,
`view`, `withdrawn`), `canonical` (`canon`, `canonical_json`), `cluster`
(`cluster`, `resolving_step`), `derivation` (`credit`, `credit_record`, `laws`), `digest`
(`combine_digests`, `digest_fields`,
`digest_instruction_set`, `digest_research_assembly`, `digest_specification`, `pre_texts`,
`preimage_fields`, `preimage_instruction_set`, `preimage_digests`,
`preimage_research_assembly`, `preimage_specification`, `specification_pages`,
`tree_preimage`), `eom` (`eom_class`, `eom_findings`, `eom_map`, `eom_register_test`,
`settlement_check`), `falcon` (`falcon_canon`, `falcon_draw`, `falcon_quote_match`,
`falcon_reconcile`, `falcon_schema_canon`, `falcon_schema_digest`, `falcon_stop`,
`quote_check`, `source_hop`, `source_match`, `sponsor_stage`), `governor` (`admit`,
`charge`, `jitter`, `lane`, `seat_cost`), `identity`
(`canonical_tools`, `change_class`, `family_of`, `identity_compare`, `prompt_digest`),
`landing` (`strike_screen`), `lint` (`counts`, `lint`, `lint_counts`, `lint_norm`,
`name_tokens`, `tables`),
`permissions` (`domain`, `permits`), `probe`
(`compare`, `expected_loss`, `historical_view`, `load`, `probe_draw`, `probe_step`,
`ratio_step`, `reset_update`, `schedule_step`, `uniform`), `provision` (`catalogue_state`,
`draft_module_status`, `interview_check`, `module_bind`, `module_check`, `module_digest`,
`module_expand`, `module_parse`, `module_use_view`, `module_verify`,
`not_included_lines`), `record` (`class_row`, `envelope`, `check_class`, `form_credit`,
and v1's register functions `budget_check`, `citation_check`, `domain_check`,
`entry_view`, `eom0_open`, `field_values`, `gap_record`, `gap_records`, `gap_state`,
`gap_view`, `grade_next`, `grade_now`, `grade_values`, `inherit_grade`, `is_standing`,
`l_finding_pair`, `prec_decimal`, `promotion_eligible`, `promotion_pass`,
`promotion_record`, `reaudit_scope`, `record_check`, `record_digest`, `record_form_check`,
`record_preimage`, `record_view`, `repromote_batch`, `schema_json`, `status_next`,
`status_values`, `status_word`, `status_words`, `verification_difference`,
`verification_order`, `withdrawal_preimage`, `withdrawal_record`, `withdrawal_scope`),
`score` (`beta_interval`, `beta_mean`, `betainc`, `betainc_inv`, `canon`,
`diversity_quota`, `evidence`, `inherit`, `inquire`, `lgamma`, `override_check`,
`override_effective`, `override_mark`, `pad_check`, `pad_weight`, `peer_activity`,
`pending_level`, `prime_select`, `rank`, `score_interval`, `score_update`, `sponsor_cut`,
`standing`, `state_step`, `tier_gate_release`, `trip`, `user_aggregate`,
`user_score_evidence`, `violation_cut`), `sha256` (`digest`, `digest_text`), `sponsor`
(`conduct_resolve`, `user_evidence`,
`whitewash_count`), `sr9` (`criteria_set_params_ok`, `sr9_c1`, `sr9_c2`, `sr9_c4`,
`sr9_harness`, `tms_params_ok`, its earlier name),
`strike` (`assumption_closure`, `a_of_r`, `d_of_r`, `d_compare`, `sr5_order`,
`sr6_independence_count`, `sr6_audit_opens`, `sr8_scale_factor`, `mm_contradicts`,
`lm_contradicts`, `sr3_scope`, `conditions_of`, `comparison_set`, `sr8_groups`),
`unicode` (`general_category`, `nfc`, `nfd`) and
`units` (`lm_contradicts_units`, `mm_contradicts_units`, `normalize_measurement`,
`sr8_scale_factor_units`, `unit_matches`, `unit_parse`, `unit_scale`). The family `zone`
holds `canon_decimal`, `canon_dimension`, `canonical_term`, `classify_successor`,
`correspondence_table_well_formed`, `criteria_set_well_formed`,
`digest_correspondence_table`, `digest_criteria_set`, `digest_research_assembly_of`,
`digest_starting_set`, `dimension_out_of_range`, `is_canonical_dimension`,
`normalize_dimension`, `starting_set_well_formed` and `zone_preimage`. The family `form`
holds version 1's 15 functions under version 1's names: `d_variable_check`, `d_variables`,
`eval_form`, `form_coverage`, `form_dimension`, `form_names`, `form_totality`,
`form_tree`, `grammar_witness_count`, `ic4a_signature`, `names_check`, `parse_form`,
`t3_laws`, `t4_homogeneity` and `t6_totality`. The units family's
argument form, `pcalc units <function> <argument>...`, is retired. The family `fundamental`
holds `final_checks`, `fundamental_tests`, `ic_checks`, `t2_atomicity`, `t2_findings`,
`t3_consistency` and `t5_dof_yield`.

The functions that port v1's take v1's arguments by the names v1's corpora give them, and
v1's corpora run through them (`Tests/Calculator.lean`: cluster 67 cases, strike 150, SR9
31, probe 252, eom 438, units 117, identity 102, lint 231, sponsor 83, falcon 1208, score
588, Provisions 418 and records 1145). Each answer is v1's text of the result or a typed
value, as its family's corpus entry says: the cluster's spacings are square roots, written
to six decimals as v1 wrote them; a probe's or a score's numbers, a drawn value among
them, are exact values correctly rounded to twelve significant digits; a typed value's
canonical JSON, or its v1 `canon` text, is v1's expectation; SR8's scale factor is
correctly rounded to twelve significant digits. A request v1 refused is refused with v1's
word or message as the detail; a refusal v1 wrote as a value stays a value.

Where a function's cost grows faster than its input, its family states the most it
takes, measured on the built binary, and refuses more (`BAD_ARGUMENT`, "the Calculator's
bound"):

| Family | Bound | The worst accepted |
| --- | --- | --- |
| `biblio` | 1024 entries a list; 64 identifiers; 16,384 code points a string, 131,072 in all | 0.28 s (`check`, the slowest of the 405 corpus cases) (measured 2026-10-21) |
| `cluster` | 1000 rows or SEs; 5000 paired SEs | 0.06 s (1.6 s with scores of 400 digits); 0.43 s |
| `strike` | 2000 records holding 20,000 assumptions and citations | 0.11 s; 1.15 s when the 18,000 assumptions are distinct (measured 2026-10-18) |
| `strike` | SR6: 1000 sets; those kept (at most v1's 24) holding 128 identifiers | 0.34 s, the slowest found |
| `strike` | SR8: 100 measurements of at most 30 digits each, and the bound on an exact value (below) | 0.33 s, and with exponents spread from -9999 to 250 1.9 s before that bound, which now refuses them in 0.05 s (measured 2026-10-17) |
| `strike` | `sr3_scope`: the Research Assembly, by the reader's bounds alone | 0.47 s |
| `strike` | `conditions_of`: 2000 records holding 5000 ASSUMPTIONS and CITES entries; `comparison_set`, `sr8_groups`: 200 records holding 500; 1000 AT points, each VALUE and UNIT of at most 64 characters, each point's value within the bound on an exact value and 2048 bits | 0.58 s; 0.77 s (measured 2026-10-18) |
| `sr9` | 50 records and 50 contradictions; 500 assumptions and citations | 0.04 s |
| `zone` | 1024 entries a list; 32,768 code points a string (version 1's corpus holds a term of 20,005), 131,072 in all | 2.9 s (a Starting Set check of 1000 DOF and 26 laws of about 4,000 code points); 0.15 s (a check of 1024 entries of each of three kinds); 0.12 s (a preimage or a digest); 0.06 s (a term nested 8,191 deep) (measured 2026-10-20) |
| `eom` | 64 DOFs, CONSTANTs, LAWs and CONSTRAINTs each; 64 records, status words and namings; an EQUATION of 16,384 code points | 0.8 s; 0.41 s (settlement); 0.08 s (measured 2026-10-18) |
| `derivation` | 1024 steps; an EQUATION of 16,384 code points; 64 entries a Starting Set kind; 1024 register records; 512 ASSUMPTIONS | 0.39 s (1,024 steps of about 500 code points); 0.38 s (250 steps of about 3,900); 0.23 s (64 LAWs and 512 named ASSUMPTION records) (measured 2026-10-20) |
| `falcon` | 200,000 characters of request strings; QUOTE CHECK's product of lengths 2,000,000; 100 candidates; 1000 rows; 1,000,000 characters of item lines; 10,000 events and stop records | 0.9 s; 1.2 s; 0.57 s; 0.74 s; 0.04 s to refuse; 0.78 s (measured 2026-10-18) |
| `identity` | the reader's 1 MiB alone | 0.55 s (a template of 680,000 characters) (measured 2026-10-18) |
| `fundamental` | 64 entries a list; 16,384 code points a string, 131,072 in all | 0.25 s (the run and the final pass over a Starting Set of 60 DOF, 30 laws of about 4,000 code points and 60 CONSTRAINTs); 0.11 s (T3) (measured 2026-10-20) |
| `form` | 64 entries a list (1,024 in `form_dimension` and `form_totality`); 32,768 code points a string (version 1's corpus holds forms of 20,011), 131,072 in all; the grammar's 4,096 code points and 64 parentheses | 0.24 s (`names_check` over 64 LAWs of 1,900 code points); 0.07 s (`form_dimension`, 1,024 dimensions); 15 s (`t3_laws` over 64 LAWs of 40 `ln` each) and 66 s, refused `OWED` (`eval_form` over 128 `ln` whose digits do not settle): a bound on the functions a request calls is owed (measured 2026-10-25) |
| `lint` | 1 MiB of zone and tools; 1,048,576 characters of findings written | 1.6 s, refused; `counts` 1.45 s (measured 2026-10-18) |
| `sponsor` | `user_evidence`: 50 events of at most 30 digits, shapes 1/10 to 1000; `whitewash_count`: 4000 admissions, retirements and states | 1.8 s; 0.3 s (measured 2026-10-18) |
| `score` | 10,000 quota window, evidence events and conduct events; 2000 accounts; 5000 pending items and activity events; 30 pooled events; Beta shapes 0.1 to 10^4, tails at least 10^-6, 4096 bits | 3.0 s (evidence); 3.8 s (conduct); 2.2 s (pooled); 0.94 s (Beta) (measured 2026-10-18) |
| `provision` | 8 texts, 64 KiB in all; a Starting Set of 64 entries a kind, 1024 in all; 64 term placements; 256 lines | 1.66 s (draft status); 1.37 s (module check); 0.46 s; 0.14 s (measured 2026-10-18) |
| `record` | 1024 entries a list; 16,384 code points a string, 131,072 in all; 64 records citing, assuming and naming 512 in all; 64 open audits | 0.70 s (promotion over 64 records); 0.49 s (a digest) (measured 2026-10-18) |
| `hold` | 4,000 entries a list; 1,000 records of a register; 16,384 code points a string, 262,144 in all | 2.4 s (`held_closure` along a chain of 1,000 citations; 2,000 took 17 s); 0.12 s (`release_record` over 1,000 records); 0.09 s (`hold_scope` over 4,000 blocks) (measured 2026-10-21) |
| `probe` | `load`: 400 records; `historical_view`: 4000 revisions, and 4000 allocated identifiers; an M `compare`: 100 standing records of at most 30 digits each, as SR8's, and the bound on an exact value (below) | 0.19 s; 0.18 s, and 0.09 s; 0.33 s, and with exponents spread from -9999 to 250 1.8 s before that bound, which now refuses them in 0.06 s |
| `units` | a UNIT or DIMENSION of 1024 characters and 128 tokens; a decimal of 4096 characters; SR8: 100 measurements of at most 30 digits each, as `strike`'s; the bound on an exact value (below) | 0.02 s; 0.04 s; 0.54 s in units of 1024 characters (1.8 s with 4096-character values before the digit bound) (measured 2026-10-18) |
| `governor` | the reader's alone: a fixed number of sums, products and quotients of numbers below 2^1024 | 0.08 s, every number near 2^1024, about `pcalc`'s start (measured 2026-10-20) |
| `permissions` | the reader's 1 MiB alone | 0.13 s, 116,496 context words (measured 2026-10-20) |
| `sha256` | the reader's 1 MiB alone | 0.16 s (`digest` of 1 MiB of hexadecimal); 0.13 s (`digest_text`) (measured 2026-10-20) |
| `unicode` | a text of 131,072 code points | 1.45 s (`nfc` of a letter and 131,071 marks drawn from ten, four decomposing into two: a run of 183,409 marks); 1.19 s (`nfd`); 0.19 s (`general_category`) (measured 2026-10-20) |

Without them, 16,000 cluster rows took 8.6 s, 24 SR6 sets holding 256 identifiers 1.3 s,
100 SR8 measurements of 4096 digits 183 s, an SR9 suite of 200 records citing each other
99 s, the strike rule's comparison set over 2000 records 422 s, a register test over 200
entries 14 s, a falcon draw of two from 3000 candidates 101 s, a lint zone of 1 MiB of
hidden characters 11.7 s, a score pad 10^6 half-lives old 25 s, a PROPOSITION of 40,000
words 17.8 s and promotion over 256 records 9.2 s. A family joins with its
`calls : Family` (each function's name v1's where it ports v1's, its arguments read with
`Principia.Calculator.Interface`), one line in `Principia.Calculator.families`, and its
request and answer pairs in `pcalc.json`; the table's theorems refuse two families or two
functions of one name.
## The hold corpus

`Tests/Hold.lean` (hold scope) runs all 140 cases of `hold_corpus.json` against
`Principia.Hold`: all 140 pass, none owed, no divergence. A HOLD and a RELEASE end with
their digests, SHA-256 over their field lists (`Principia.Sha256`; decision D2, option 1),
compared with v1's as every other field is: the 5 `hold_record` answers, and the 45
`release_record` cases that get past the reading of their HOLD, whose next step compares
the HOLD's digest with the digest of its fields (2 of them expect it refused).
`hold_corpus.owed.json` lists no case, and the runner requires it so. A
refusal is compared by its reason; an answer is read from v1's text into the function's
typed result and compared as a typed value, and a word v1's text cannot carry one to one
(empty, or holding a comma or a bracket) fails the case.

## The declared-forms corpus

`Tests/Form.lean` runs all 555 cases of `form_corpus.json` (v1's `tpc_form` 0.2.1, corpus
0.5.1) against `Principia.Form`: 552 pass, 1 of them a recorded v2 divergence, and 3 are
owed. Per function: parse_form 184 of 187 (3 owed), form_dimension 91, eval_form 65,
form_totality 47, form_tree 35, d_variable_check 27, t3_laws 22, names_check 17,
t4_homogeneity 16, d_variables 13, t6_totality 11, ic4a_signature 11, form_names 6,
form_coverage 6, grammar_witness_count 1.

- **Owed** (`form_corpus.owed.json`): the 3 parse cases whose text holds a code point
  outside the Unicode stopgap's tables (U+1D465, and U+0301 that NFC composes), which v1
  read after NFC and escaped by general category: decision D3. The runner requires the
  owed cases to be exactly the listed ones.
- **Divergence** (`form_corpus.divergences.json`): `eval/cos`, cos of 90 deg, which is
  exactly 0; v1 printed the cosine of the double nearest pi/2, 6.12323399574e-17.
- **Comparison.** v1's `canon` text writes a string unquoted, so the runner reads it
  against each result's shape and compares typed values: a two-item answer by its word
  and the rest (a canonical spelling may hold a comma, `D(x,t,2)`); names, trees and
  DIMENSIONs item by item, each item the Calculator gives checked to hold no comma or
  bracket; numbers by value, v1's twelve digits read as an exact decimal against the
  Calculator's number rounded once to twelve digits; a validator's pass flag as a value
  and its problems, which may hold commas, by v1's text, as the zones' runner compares
  them (form_totality's problems so too).
- **Numbers.** eval_form and t3_laws evaluate on exact numbers (a rational times a power
  of pi) where they have that form, and on enclosures elsewhere (`form_numbers.json`
  above), D6's standing default; a decision no bounds up to 4096 bits settle is owed. No
  case of this corpus is owed so.

## SHA-256 in the families

Decision D2, option 1: every family that computes a digest reads `Principia.Sha256`, SHA-256
in Lean, through `Principia.Digest` (`digestFields`, `combineDigests`, `ofPreimage`), and
every case that waited on it is compared with v1's answer, exactly. The zones' canonical
serialization (D99) is `Principia/Zone/Preimage.lean`: v1's `_entry_list`,
`_sorted_entries`, the three trees, `_node`, `zone_preimage`, `d_tpk`, `d_trm`, `d_tms`,
`d_tfk_of` and `classify_successor`. It is the one port: the Provision functions' D(TPK) and
`_entry_list` and the record check's zone digests (REC-34) read it. No owed list carries a
digest reason any more, and no runner a stand-in digest. The counts, before and after (where
an entry elsewhere in this file still calls a case owed to SHA-256 or to D2, these hold):

- `zone_corpus.json` (the zones' runner): 192 pass, 33 owed (digests), and 41 cases not run
  (`zone_preimage` 17, `d_tpk` 12, `d_trm` 3, `d_tms` 6, `d_tfk_of` 3) -> all 266 pass, none
  owed: every preimage, digest and successor class as v1's. `zone_corpus.owed.json` lists
  none.
- `hold_corpus.json`: 90 pass, 50 owed (digests) -> 140 pass, none owed.
- `biblio_corpus.json`: 397 pass, 8 owed (digests) -> 405 pass, none owed.
- `identity_corpus.json`: 91 pass, 11 owed (digest) -> 102 pass, none owed; each of the 11
  digests is SHA-256 over the preimage v1 digested (`identity_corpus.preimages.json`). Its
  fault checks are 17 (the one built on an owed outcome gone, two on a digest added).
- `record_corpus.json`: 75 owed (67 digest, RD013 among them; 8 number) -> 8 owed (number);
  924 of 932 cases pass (857 before). The runner's 7 mutation checks of its stand-in
  comparison are gone with the stand-in: every answer is compared byte for byte.
- `module_corpus.json`: 227 of 418 answered as v1 answered, 191 owed (digests) -> all 418,
  none owed; with v1's digests, all 418 as before; and the Calculator's SHA-256 of each of
  the 75 preimages in `module_corpus.digests.json` is v1's value.
- `lint_corpus.json`'s tables (`lint_tables`): 10 -> 11 checks, the new one SHA-256 of
  `tablesJson` against the value v1 records (`LINT_TABLES_SHA256`), as v1 checked it on
  loading.
- Every other runner is unchanged; `lake test` fails nothing. No divergence is recorded.

## SHA-256 in the falcons and the probes

Decision D2, option 1: the falcons and the probes take their digests from
`Principia.Sha256`, and the probes' draws compare exactly (decision D6, option 1). No owed
list of either family carries a reason any more. Where an entry elsewhere in this file
still counts a falcon or probe case owed to SHA-256, says a hand vector needs no digest, or
counts 240 falcon hand vectors, these hold:

- `falcon_corpus.json`: 912 pass, 37 owed (digests: 35 `schema_digest`, 2 `draw`) -> 949
  pass, none owed; `falcon_corpus.owed.json` lists none, and the runner requires it so.
  The draw's `h(r, account)` is `Principia.Falcon.Draw.drawKey`, and DR18 and DR33, whose
  eligible accounts are equal on window and share, are answered as v1 answered them; a
  schema's digest is SHA-256 over the netstring of `TPC-FALCON-SCHEMA`, `1` and its
  canonical text (`Principia.Falcon.Schema.digestOfText`). No number in either is inexact,
  so no divergence is possible there.
- `falcon_hand.json`: 240 -> 259 cases, all passing: `HV-DH01` to `HV-DH13`, draws whose
  eligible accounts are equal on window and share (on 9 of them `h` orders the accounts
  otherwise than their names would), and `HV-FD01` to `HV-FD06`, the digests of the
  `HV-FS` schemas (2 refused), each expectation v1's `run_case`
  (`scripts/falcon_hand_vectors.py --check` passes).
- `falcon_table`: 6 -> 7 checks: the class table's SHA-256 is v1's `UNICODE_TABLE_SHA256`,
  as v1 checked it on first use.
- `probe_corpus.json`: 169 computed, 83 owed (draw: 25 `uniform`, 10 `ratio`, 13
  `schedule`, 18 `probe`, 17 `step`) -> 252 computed, all agreeing with v1's text byte for
  byte, none owed; `probe_corpus.owed.json` lists none, and the runner requires it so. For
  each `uniform` case the runner also reads the draw's 52 bits from the first 13 characters
  of the digest's hexadecimal text, as v1 read them, and requires them to equal the
  bytes' reading. No divergence: on every case each exact comparison falls as v1's double
  did. `scripts/probe_draw_margins.py` mirrors each of v1's draws exactly beside v1's own
  doubles (it exits 1 on a comparison where the two fall apart): the nearest a drawn value
  comes to what it is compared with is 1.24e-2 (R05, the third weight's running sum), and
  the nearest a scaled count comes to a whole number 2.13e-2 (S07, the burst rate's
  index), where the doubles' rounding is about 1e-16. The largest exact
  values: a numerator of 52 bits (a uniform value) and a denominator of 55 (B14, `k / (1 +
  k)` at `k` = 0.14285714285714285), a scaled count's product of 60 bits (S11), and a
  comparison's cross-multiplication of 105 bits (B14): no case needs a bound on an exact
  value's size.

## The falcon corpus

`Tests/Falcon.lean` (the falcons) runs all 949 cases of `falcon_corpus.json` against
`Principia.Falcon`: 820 pass and 129 are owed, listed with their reasons in
`falcon_corpus.owed.json`, which the runner requires to be exactly the owed cases. 96 need
NFC on a text holding a code point outside those the Calculator knows to be their own NFC
(`normalization U+XXXX`, decision D3; `Principia.Falcon.nfcKnown`, the code points below
U+0300 and those of the zones' stopgap): 70 `qmatch`, 10 `schema_canon`, 10
`schema_digest`, 4 `canon`, 1 `reconcile`, 1 `qcheck`. 33 wait on SHA-256 (`digests`,
decision D2): the 31 `schema_digest` cases whose schema is accepted, and 2 `draw` cases
whose OK answer names accounts in an order the digest `h(r, account)` decides (where no two
eligible accounts are equal on window and share, `h` is never consulted and the draw is
answered). A refusal is found before any normalization or digest is needed, so a refused
case is always judged. The Calculator writes v1's render (each `render_*` ported) and the
two texts are compared character for character; the canonical form's render is proved
injective. It also runs `falcon_table`: v1's class table for the QUOTE CHECK, carried as
v1's data in `Principia/Falcon/Classes.lean`, equals the literal in
`docs/v1/tpc_py/tpc_falcon.py` character for character, reads into 1247 ranges that
increase without overlap, and v1's binary search agrees with a scan at and beside every
range's ends; and `falcon_hand` (see "PMA's corpora" above).

## The Provision corpus

`Tests/Provision.lean` runs all 418 cases of `module_corpus.json` (v1's `tpc_module` 0.1.1,
corpus 0.2.1) against `Principia.Provision`, each case twice.

- **As the Calculator answers today**, with no SHA-256: 226 come out as v1's and 192 are
  owed, listed in `module_corpus.owed.json` (190 digests, decision D2; 2 whose text holds
  U+0301, which v1 read in NFC, decision D3); the runner requires the owed cases to be exactly
  the listed ones. Answered of all, per function: module_parse 107 of 108, module_bind 39 of
  39, catalogue_state 38 of 52, module_use_view 15 of 15, module_expand 19 of 68, module_check
  3 of 22, interview_check 2 of 55, module_digest 1 of 19, module_verify 1 of 15,
  draft_module_status 1 of 11, not_included_lines 0 of 14.
- **With v1's SHA-256 values** for the very preimages the Calculator computes
  (`module_corpus.digests.json`: 75 preimages, written by `scripts/provision_digests.py` with
  v1's own `tpc_module.py`, which must answer every case as the corpus expects, each SHA-256
  recomputed with hashlib; `--check` compares): all 416 cases not owed to D3 come out as v1's.
  A preimage the table lacks leaves the case owed and fails it, so the table also checks that
  every preimage the Calculator computes (a Provision's canonical text, a catalogue state, a
  Starting Set's D(TPK) tree) is the one v1 digested.
- **Comparison.** v1's expected text is JSON; it is read into `Principia.Canonical.Value` and
  compared with the answer's value through canonical JSON, which writes two values alike only
  when they are equal. Fault checks run first: a changed or reordered expectation, an owed list
  missing or adding a case, and a digest the table lacks must be refused. The first
  catalogue's kinds (decision D5) are checked against its texts: each Interaction writes a
  term, the Convention writes none and binds no slot.

## The record corpora

`Tests/Record.lean` runs all 932 cases of `record_corpus.json` and all 213 of
`record_view_corpus.json` against `Principia.Record` (`Principia/Record/Table.lean`,
`Answer.lean`, `Check.lean`, `Register.lean`, `Measured.lean`), the port of v1's `tpc_record`
0.1.0 (tpm_record_schema 0.4.0, tpm_record_functions 0.3.0). A case's arguments are read
exactly (an integer stays one, a number with a fraction keeps its decimal value); its answer
is written in TPM's canonical JSON and compared with `expected` byte for byte. 852 and 213
pass, no divergence. 80 are owed and listed in `record_corpus.owed.json`, which the runner
requires to be exactly the owed cases, each for its reason: 66 to SHA-256 (D2; the cases of
`record_digest`, `withdrawal_record`, `gap_record`, `gap_records` and `promotion_record`, and
the `record_check` and `record_preimage` cases that compare a DIGEST or a MASTER's D_TFK or
zone digests), 6 to Unicode's tables (D3: NFC, and T2's joining symbol U+2227) and 8 to the
numeric meaning (D6: `verification_difference`'s difference, square root and quotient, which
v1 computed in doubles). An owed case still checks what it finds without the missing piece
and fails on a difference: a check's other problems (v1's less REC-29, REC-33 and REC-34),
and a written record's every other field under a stand-in digest function. The runner's
mutation checks show that comparison refusing a changed or missing field. v1's record table
is carried as v1's text (`TABLE_TEXT`) and read by its own line grammar; the runner checks
it byte for byte against `docs/v1/tpc_py/tpc_record.py` and field by field against Phase 1's
`record_class.json` and `record_envelope.json` types (`record_table`, 570 checks).

## The specification's and the instruction set's digests

v1's `tpc_digest` 0.3.0 functions for D(TPS) (PMA's D(PFS), the Principia Framework
Specification's digest) and D(IS), never ported before, are `Principia/Digest/Specification.lean`:
`pre_texts` (`preTexts`), `tps_pages` (`specificationPages`), `d_tps`
(`digestSpecification`) and `d_is` (`digestInstructionSet`), each refusing with v1's reason
in v1's order; the `…Of` functions take v1's arguments as JSON values and refuse what v1
refused for their type. v1's root title `The Principia Machina/TPS`, its contents page and
the tags `TPC-TPS` and `TPC-DIS` are kept, so every digest of v1's corpus is reproduced.

- `dis_corpus.json`, all 189 cases, run twice: by `Tests/Canonical.lean`
  (`runDisCorpus`, 212 checks: the 189 answers, the preimages of the 22 digest cases
  answered OK, and the corpus's count by function) and through `pcalc digest` by
  `Tests/Calculator.lean` (`runDisCalls`, 211 checks), each input read by the Calculator's
  reader, which keeps a value's kind. An answer is written as v1's `canon` text and
  compared with `expect`; a string of it holding `,`, `[` or `]` fails its case rather than
  compares. `pre/empty-block`'s text, `[OK,[]]`, cannot tell an empty block from none; it is
  answered `[""]`, as v1 answered it, and the digest cases
  `tps/section-with-an-empty-block` and `pages/empty-block-on-the-root` pin the difference.
  No case is owed and none diverges.
- The digest family on `pcalc` gains `pre_texts`, `specification_pages`,
  `digest_specification`, `preimage_specification`, `digest_instruction_set` and
  `preimage_instruction_set` (v1's `d_is` argument `d_tps` named `specification`), which
  answer as v1 answered, `["OK", answer]` or `["REFUSED", reason]`; `pcalc.json` gains 15
  request and answer pairs, their answers computed with v1's `tpc_digest` and an independent
  canonical writer. Their family bound: at most 1000 pages and 1000 members, whose titles
  are compared pair by pair for a repeat (the worst accepted, 1000 pages at the reader's
  1 MiB, takes 0.3 s; a page of 1 MiB holding 340,000 `<`, 0.3 s; 1000 members, 0.04 s);
  the family bounds' runner checks each at the bound and one past it (7 cases).
- SC5, the PROVED class's first row, by `Principia/Digest/Injective.lean`: the netstring
  encoding of a list of texts is injective (`preimage_injective`); a field list's preimage
  gives every field's bytes, and the field list itself when the kinds agree position by
  position (`preimageFields_injective`; a text "10" and the integer 10 share one preimage,
  as in v1); the combination rule and D(RAS) (`preimageDigests_injective`,
  `preimageResearchAssembly_injective`); and the type-tagged tree encoding of a zone, over
  every tree (`Tree.preimage_injective`). What is proved is SHA-256's input, not SHA-256. A
  page's own `h` is over its blocks' text joined by line feeds, as v1 defines it, not an
  encoding of a list. For D(PFS) and D(IS): their preimages give back the version and the
  kept pages' list, and the version, D(PFS) and the members (`specificationFields_injective`,
  `instructionSetFields_injective`); D(PFS) is the digest of `specificationPages`'s list
  (`digestSpecification_pages`); text outside the blocks moves nothing
  (`specificationPages_blocks`); and the list, the refusal and the digest do not depend on
  the pages' order (`specificationPages_perm`, `digestSpecification_perm`).

## Unicode's tables in the families

Decision D3, option 1: every family reads text with `Principia.Unicode` (Unicode
15.1.0, v1's `unicodedata`) where the interim tables stood. `Principia.Zone.disallowed` is
v1's `_disallowed` over the general category, `Principia.Zone.text` v1's `_text` (line
endings as LF, then NFC), and each family normalizes where v1 normalized: the strict
readers of identity and of Provisions put every string they decode in NFC, keys included,
and find a duplicate key after NFC; the key form takes NFD, the classes, the fold, then
NFC; the falcons' `canon_text` and the lint's `_lint_text` are NFC; a falcon output
schema's string not in NFC is refused; the units escape a reason's code points by v1's
rule, not every code point past ASCII. No owed list carries a Unicode reason any more, and
every case that carried one is compared with v1's answer. The counts, before and after
(where an entry elsewhere in this file still names the interim tables, the stopgap,
`nfcKnown` or a count owed to Unicode's tables, these hold):

- `biblio_corpus.json`: 381 pass, 24 owed (8 digests, 13 `normalization`, 3 `unicode`) ->
  397 pass, 8 owed (digests).
- `identity_corpus.json`: 82 pass, 20 owed (11 digest, 9 `unicode`) -> 91 pass, 11 owed
  (digest); all 11 digest cases' preimages now equal the ones v1 digested (9 before).
- `form_corpus.json`: 552 pass, 3 owed -> 555 pass, none owed (`parse_form` 187 of 187);
  `form_corpus.owed.json` lists none.
- `zone_corpus.json` (the zones' runner): 190 pass, 35 owed (33 digests, 1 `unicode`, 1
  `normalization`) -> 192 pass, 33 owed (digests). `zone_text.json` no longer carries the
  stopgap's class.
- `tests_corpus.json`: 118 pass, 2 owed -> 120 pass, none owed.
- `record_corpus.json`: 80 owed (66 digest, 6 `unicode`, 8 number) -> 75 owed (67 digest, 8
  number); the runner's checks 859 -> 864 pass. RD013 now reaches its digest and is owed to
  SHA-256, its other fields checked.
- `probe_corpus.json`: 168 computed, 84 owed (83 draw, 1 `nfc`) -> 169 computed, all
  agreeing, 83 owed (draw); `probe_corpus.owed.json`'s reason `nfc` is gone.
- `module_corpus.json`: 226 of 418 answered as v1 answered, 192 owed (190 digests, 2
  `unicode`) -> 227, 191 owed (digests); P14 is answered, G12 reaches its digest and is
  owed to SHA-256. With v1's digests all 418 are answered as v1 answered them (416 before).
- `falcon_corpus.json`: 820 pass, 129 owed (96 `normalization`, 33 digests) -> 912 pass, 37
  owed (digests); the digest cases of FSX07, FSX13, FSX14 and FSX15 now reach the digest,
  their canonical texts passing as `schema_canon` cases. `falcon_hand.json`'s note no
  longer names the stopgap (`scripts/falcon_hand_vectors.py --check` passes).
- `lint_corpus.json`: 218 pass, 13 owed (`unicode`) -> 231 pass, none owed;
  `lint_corpus.owed.json` lists none, and the runner requires it so. Its fault checks are
  20 (the one that built an owed outcome is gone with the owed outcome).
- `units_corpus.json` and the units' hand corpora: unchanged, 91 pass with the same 5
  recorded divergences, now that a reason's escaping is v1's.
- Every other runner is unchanged; `lake test` fails nothing. No divergence is recorded for
  any of the 150 cases.

## Unicode's data

`vectors/unicode/` holds Unicode 15.1.0's own files, unchanged, from
<https://www.unicode.org/Public/15.1.0/ucd/>, under Unicode's licence (`LICENSE` beside
them, the Unicode License v3), for the normalization version 1 does at version 1's Unicode.
`scripts/gen_unicode_tables.py` refuses each unless its SHA-256 is the one below.

- `UnicodeData.txt`, SHA-256
  `2fc713e6a31a87c4850a37fe2caffa4218180fadb5de86b43a143ddb4581fb86`: the generator's
  input for the general category, the canonical combining class and the canonical
  decompositions; `Tests/Unicode.lean` also reads it directly and compares, with
  `Principia.Unicode`, the general category of all 1,114,112 code points and the combining
  class and full canonical decomposition of all 1,112,064 scalar values (the 11,172 Hangul
  syllables, decomposed by arithmetic, through NormalizationTest.txt's Part 1).
- `CompositionExclusions.txt`, SHA-256
  `59d2d9e3dfdf0a999cf9dae11d594f053631222679a2f5710315ea07f7fe82af`: the exclusions
  UnicodeData.txt cannot give. With the singletons and the non-starter decompositions they
  make Full_Composition_Exclusion, 1,120 code points, the set DerivedNormalizationProps.txt
  lists at 15.1.0 (compared when the tables were generated; that file is not kept).
- `NormalizationTest.txt`, SHA-256
  `871238e37e3be0696ec2bd0891119a041b052da1a84485eda05a5438724b223e`: run whole by
  `Tests/Unicode.lean`, 19,074 lines: NFC, c2 = NFC(c1) = NFC(c2) = NFC(c3) and c4 =
  NFC(c4) = NFC(c5), and NFD, c3 = NFD(c1) = NFD(c2) = NFD(c3) and c5 = NFD(c4) = NFD(c5),
  190,740 checks; then the 1,095,035 scalar values its Part 1 does not list, each its own
  NFC and NFD. About 3 s with the UnicodeData.txt checks.

`Principia/Unicode/Tables.lean` is generated from the first two by
`python3 -I scripts/gen_unicode_tables.py` (388 combining-class runs, 2,061 decompositions,
941 primary composites, 3,302 general-category runs, each table a text read once); `--check`,
run by CI's docs-lint job, regenerates it and compares byte for byte; `--cross-check`
compares it with a Python whose `unicodedata` is 15.1.0, v1's: the general category, the
combining class, NFD and NFC of all 1,114,112 code points, the 941 composition pairs and
NFC over every column of NormalizationTest.txt, with no disagreement.

## The bound on an exact value

`Principia/ValueBound.lean` holds the bound the Declarer chose: an exact value's
numerator and denominator each at most 65,536 bits (`maxBits`), checked before a value is
formed (`add`, `sub`, `mul`, `div`, `sumBy`): the factors the operands share are divided
out first, as `Rat` does, by a greatest common divisor of numbers already within the bound,
and the result's bits are then bounded from what is left; a value that would cross it is
refused "exact value too large" (`tooLarge`), in `pcalc` a refusal of what was read,
`BAD_ARGUMENT`, exit code 1. Each checked operation, when it answers, is the plain one
(`mul_ok`, ..., `sumBy_ok`).

Built so far, the other sites following in the order the Phase 2 Open item gives: SR8's scale factor and
SR3's M-M and L-M tests (`Principia/Strike/Bounded.lean`, each with a theorem that its
answer is `Principia.Strike`'s), used by `pcalc strike` (`sr8_scale_factor`,
`mm_contradicts`, `lm_contradicts`) and by the probes' M comparison (`pcalc probe
compare`, `Principia.Probe.compare`).

- `pcalc.json`: five cases at the bound, from the built binary: SR8 with an uncertainty of
  `1e-9999` (its square has 66,432 bits), the M-M test at `1e-9999` and, under the bound,
  at `1e-9000` (`false`, v1's answer), the L-M test and the probes' comparison at
  `1e-9999`.
- Measured with the strike corpus, the SR8 order corpus and the probe corpus through
  `pcalc`: no case crosses the bound (all 25 and 252 answer as before).
- Measured on the built binary on 2026-10-17, SR8 over 100 measurements of 30-digit
  values (the probes' M comparison over as many standing records takes the same): near 1,
  0.33 s; exponents spread from -300 to 250, 0.39 s; from -1000 to 250, 0.56 s; from -9999
  to 250, refused in 0.05 s, where before the bound the same measurements took 1.9 s.
  Without the common factors divided out first, the 100 values near 1 were refused, the
  check seeing twice the denominator their sum holds.
- Score and beta (`Principia/Score/Bounded.lean`, each function with a theorem that its
  answer is the plain one of `Principia.Score`, `Principia.Beta` or `Principia.Sponsor`):
  the quota's sums; the evidence's, the pool's and the user evidence's sums of rational
  multiples of powers of 2, each coefficient checked as it is formed and a power `2^n` held
  to `|n| < 65,536`; the score's interval, the update, the cuts, the inquiry, the
  inheritance, the Beta mean and the interval's tails; used by `pcalc score`. Its
  `posteriorOf` bounds the sponsor's user evidence on the score's input, and serves the
  sponsor's own `user_evidence` alike. The Beta layer's incomplete function and quantile
  take numbers of at most 4096 bits (the family's bound), which keeps the values their
  methods form within the bound. Measured on the built binary on 2026-10-18: a pad 65,534
  half-lives old answers in 0.15 s and one 65,536 old is refused in 0.02 s, where the weight
  computed without the check (in Lean's interpreter) took 25 s at 1,000,000 half-lives and
  more than two minutes at 100,000,000. `pcalc.json` holds those two, an event 10^9
  half-lives old refused, a cut at `1e-9999` refused and at `1e-5000` answered, and an
  update whose products cross the bound refused. Measured with `score_corpus.json` and
  `beta_corpus.json` through `pcalc`: no case crosses the bound (all 487 and 99 answer as
  before).
- The units (`Principia/Units/Bounded.lean`, each function with a theorem that its answer
  is the plain one's, `pcalc units`): a unit's scale is held as exponents over five pairwise
  coprime atoms (2, 3, 5 and the cofactors of `au` and `eV`), so it is in lowest terms
  before any number is formed (`Units.scaleProduct`; kernel-checked: the atoms are
  coprime, every catalogue factor is a product of their powers, and each of the 807 token
  strings has the scale it had); its numerator and denominator are formed by checked whole
  powers and products, each a factor of the whole, so the refusal is exact: `arcsec9286
  Qrad1635 hrad` (a denominator of 65,536 bits) answers in 0.03 s and `arcsec9286 Qrad1635
  darad` (65,537) is refused. Normalized values, SR3's polynomial coefficients across powers
  of pi and SR8 (`Strike.Bounded`) are checked alike. The 253-character unit of 21 prefixed
  arcseconds whose scale near 10^12 has a numerator and a denominator of 1.07 and 1.39
  million bits is refused in 0.016 s. No case of `units_corpus.json`, `units_range.json`
  or `units_pi.json` crosses the bound (117 answer as before). `runFamilyBounds` checks 5
  cases at it.
- The declared forms (`Principia/Form/Within.lean`): a literal is formed only when its
  value, numerator and denominator together, holds at most `maxBits` bits
  (`literalValue`, its exponent first held to 19,728), and a binding is read through
  `Units.Bounded.normalizeMeasurementArg` and held alike (`readBindings`, which T3's laws
  use too); past either, the evaluation is refused "exact value too large". Every operation
  of the evaluator that answers an exact number from exact numbers within the bound answers
  one within it, and encloses the value otherwise (`Num.add_within`, ...,
  `Num.powRat_within`); `eval_exact_within_read` assembles them: under bindings
  `readBindings` has read, every exact number an expression evaluates to is within the
  bound. `form_numbers.json` holds five cases at it: the longest literal the form's 4096
  code points allow, answered; a binding of `1e-19728` (65,536 bits) answered and one of
  `1e-19729` refused; a binding of 19,000 digits refused; and the square of a binding of
  8,000 digits, whose exact value would cross the bound, enclosed and answered to twelve
  digits. All 555 cases of `form_corpus.json` and the 53 earlier cases of
  `form_numbers.json` answer as before.
- The yardsticks (`Principia/Yardstick/Bounded.lean`, with theorems that the key, the checks
  and the harness, when they answer, answer as `Principia.Yardstick`'s: `yardstickKey_ok`,
  `yardstickChecks_ok`, `yardstickHarness_ok`): every Criteria Set constant's VALUE and every
  U_C cell is read through `Record.Bounded.decimalWithin` before the Criteria Set is compiled,
  every record's steps checked, and each weighted sum's product and running sum formed
  through `ValueBound.mul` and `add`; `yardstick_checks` and `yardstick_harness` first
  evaluate every key the checks evaluate. `Tests/Yardstick.lean`'s `runBound`
  (`yardstick_bound`, 51 cases): `yardstick_corpus.json`'s 46 cases through the checked
  functions, each answering as the plain one; a U_C of 10^19725 + 1 not refused by the bound,
  one of 10^19729 + 1 refused, a weight of 10^19729 refused before the Criteria Set's own
  checks, a product of a weight of 1e300 and a U_C of 10^19700 + 1 refused, and the corpus's
  own sizes answered. Version 1's double overflow (`overflows`) is kept beside the bound.
- The cluster (`Principia/Cluster/Bounded.lean`, with theorems that the cluster rule and the
  resolving step, when they answer, answer as `Principia.Cluster`'s: `cluster_ok`,
  `resolvingStep_ok`): before the plain function runs, its computation is walked in its own
  order, each `sd²` (`se_a² + se_b²` or a paired SE's square), gap, step, `Z² sd²`, the
  spacing's square, every squaring `sqrtSumLt` makes, each step in spacings, the resolving
  step's `CUSP MAX u` and `IN MAX u`, and the answer's text (`fixed6`'s scaling by 10^6,
  `Surd.floor`'s `c² b`) formed through `ValueBound.mul`, `add`, `sub` and `div`; used by
  `pcalc cluster` (`cluster`, `resolving_step`). `pcalc.json` holds four cases, from the
  built binary: three rows with SEs of `1e-9861` answered and of `1e-9862` refused (the
  noise term `Z² (se_a² + se_b²)`, whose denominator would hold 65,536 bits, refused by the
  check's estimate, one bit conservative), and the resolving step over three SEs of
  `1e-9864` (each square's denominator 65,535 bits) answered and of `1e-9865` (65,542)
  refused. Measured with
  `cluster_corpus.json` through `pcalc`: no case is near the bound (its largest input holds
  10 bits; all 67 answer as before). Measured on the built binary on 2026-10-22, the slowest
  accepted requests: 1000 rows with SEs of `1e-9861`, 0.57 s (0.25 s before the bound), and
  the resolving step over 1000 SEs of `1e-9864`, 0.51 s (0.33 s before); 1000 rows of
  ordinary scores, 0.14 s.

## The verification's difference, exactly

`Principia/Record/Verification.lean` computes what v1's `verification_difference` computed in
doubles (tpm_record_functions 14.2): VALUE = x_t - x_e, U = sqrt(u_t^2 + u_e^2) (REC-95 when
it is 0) and ZETA = VALUE / U, each the exact value rounded once to twelve significant
digits, ties to even, as a canonical decimal; the contradiction test is the strike rule's
exact M-M test with S = 1 (`Strike.mmContradicts`, through `Units.mmCompare`); REC-96
compares the presented DIFFERENCE. With one power of pi divided out, the rationals are
formed through `ValueBound` and U and ZETA are exact square roots
(`Exact.sqrtSig`); across powers of pi, the declared forms' numbers (`Form.Num`), owed only
where 4096 bits of pi do not settle a text. Theorems: `verification_ok`, `uZero_iff`,
`plainParts_none_iff`, `zeta_sign`, `contradicts_eq_mm`, `contradicts_symm`.

- `record_corpus.json`: 8 owed (number) -> 0 owed; VD01-VD17 give v1's answer, none a
  divergence (v1's doubles and the exact values agree to the twelfth digit in every case).
  `record_corpus.owed.json`'s owed list is empty.
- `pcalc.json`: the verification request answered as `OWED` now gives VD01's answer, and
  two requests in units that carry pi, a degree against a radian and a degree against a
  degree, each expectation computed independently with Python's `decimal` at 60 digits.
- `runRecordBounds` (21 cases): a verification whose ZETA squared has a denominator of
  65,532 bits, answered in full (`7e-9863` s against 0 s, U 3), and one of 65,538 bits,
  refused "exact value too large".

## The 33 v1 corpora

The `*_corpus.json` files are v1's: the `vectors/` folder of the increment-13 TPC tree
(TPC-PY 0.3.0, tree digest `63ef0f2d...64f1`), unchanged, copied from its pages on the
public wiki at pinned revisions (charter section 11). 33 files, 6,786 cases, 13,289,027
bytes. Provenance is `docs/v1/export_tpc_py.json` (per file: page title(s), revision ID(s),
the wiki's sha1, the file's SHA-256, bytes, cases and the hub's version);
`ops/v1_seed/fetch_corpora.py` re-fetches the pinned revisions and re-checks every digest
(`--offline`: the files alone). Their generators are in `docs/v1/generators/`, for
regeneration only; `docs/v1/README.md` tells the rest.
- **Run by `lake test` as each family is ported.** They test v1's functions, as TPC-PY
  computed them. Phase 2 ports those functions to the Calculator and wires each corpus into
  `Tests/Main.lean` with the function family it tests; the section above lists what runs. SC4: all 6,786 cases pass, or each failing case is
  explained by a recorded v2 divergence. Run so far, besides those:
  - `cluster_corpus.json`, by `Tests/Cluster.lean` against `Principia.Cluster`: 67 of 67
    (26 `cluster` cases without a paired input, 21 with one, 20 `resolving`), each case's
    typed outcome compared with its `expected` text field by field: every line split into
    exactly its fields, ids compared as ids, words read into their enumerations, ranks as
    numbers and each number as v1's six-decimal text of the exact value, so an id holding
    `|` or a newline cannot pass; mutation checks first show a swapped or changed field
    refused. No divergence: the Calculator computes exactly
    (no floating point) and agrees with v1's floats on every case.
  - `strike_corpus.json` (20), `sr8_order_corpus.json` (5) and `sr9_corpus.json` (31), by
    `Tests/Strike.lean` against `Principia.Strike` and `Principia.Strike.SR9`: 56 of 56, no
    divergence. Numbers are read exactly from the corpus's decimal text and computed exactly
    (`Rat`). A boolean, a count, a word or a list of them is compared with v1's `canon` text
    of the result, written by the runner (a case whose words could collide in that text, a
    word empty or holding a comma or a bracket, fails rather than compares); SR8's scale
    factor by value, the exact root correctly rounded to the corpus's twelve significant
    digits. The `sr8_order` cases pin v1's floating-point operation order; their
    expectations are also the exact values correctly rounded, so under decision D6's exact
    default none diverges. One v2 difference no case reaches: `sr6_independence_count`
    refuses a SAME-MODEL flag list whose length differs from the contradictions', where v1's
    `zip` dropped the unpaired contradictions silently.
  - `sr3_scope_corpus.json` (91) and `conditions_corpus.json` (34), by `Tests/Strike.lean`
    against `Principia.Strike.Conditions` (`sr3_scope`, `conditions_of`, `comparison_set`,
    `sr8_groups`, on the zones' and the units' functions): 125 of 125, no divergence.
    `sr3_scope`'s answer is read back from v1's text into its kind (a word, or a refusal
    whose reason is everything between `[REFUSED,` and the last `]`) and compared typed;
    the register functions' answers are compared as TPM's canonical JSON, which quotes
    every string. An AT point's value is v1's `canon_decimal(canon(v))`, with the canonical
    serialization's `canon` of the exact coherent-SI value. A message escapes the code
    points v1 escaped, by Unicode 15.1.0's general category (D3). Owed, and in no case of
    the corpus: an AT value carrying a power of pi (D6).
  - `eom_corpus.json` (421) and `settlement_corpus.json` (17), by `Tests/Eom.lean` against
    `Principia.Eom`, its forms read by the declared forms' `formTree`: all 438 pass, no
    divergence. A form is read after NFC and a message escaped by general category, at
    Unicode 15.1.0 (D3); none is owed, and the runner requires the owed cases to be exactly
    those listed in `<corpus>.owed.json`. `eom_corpus.json`'s answers are compared as v1's `canon` text,
    written by the canonical serialization: their structure is the answer's type, and a
    question's commas are compared within the text, as v1 wrote it. `settlement_corpus.json`'s
    are compared as canonical JSON.
  - `canon_corpus.json`, by `Tests/Canonical.lean`, all 17 cases: 15 as v1 wrote them and
    2 as recorded v2 divergences (`canon_corpus.divergences.json`). v1 wrote a number by
    first reading it as the nearest IEEE double; the Calculator keeps the exact value and
    rounds it once, ties to even, so the two part where the double and the exact value
    round apart. The runner checks each divergence's two texts, so an entry that stops
    applying fails.
  - `digest_corpus.json`, all 8 cases, by `Tests/Canonical.lean`: each case's preimage,
    then its digest, SHA-256 by `Principia.Sha256`; and through `pcalc digest` by
    `Tests/Calculator.lean`, v1's `d_tfk` answered by `digest_research_assembly` (its
    zones' digests named by their zones) and `hex_digests` read as `digests`. No case is
    owed and none diverges.
  - `units_corpus.json` (91 of 91 cases) and `zone_corpus.json` (69 of 335), by
    `Tests/Units.lean`: see "The units and dimensions corpora" above.
  - `zone_corpus.json`'s zone checks and successor classes (225 of 335), by
    `Tests/Zone.lean` against `Principia.StartingSet`, `Principia.Correspondence` and
    `Principia.Criteria`: 190 pass, 35 owed and listed in `zone_corpus.owed.json` (see
    "The units and dimensions corpora" above).
  - `biblio_corpus.json` (397 of 405 cases; 8 owed to SHA-256), by
    `Tests/Biblio.lean`: see "The bibliography corpus" above.
  - `tests_corpus.json` (120), by `Tests/FundamentalTests.lean` against
    `Principia.StartingSet.Tests`, `Principia.Correspondence.isomorphismChecks` and
    `Principia.ResearchAssembly.finalChecks`: 118 pass, 2 owed and listed in
    `tests_corpus.owed.json` (Unicode's tables). A result is
    written as v1's `canon` writes it and compared as text, its pass flag or verdict word
    as a value. T3 compares two FIX values in coherent SI through the twelve-digit form of
    the exact value (`Principia.ExactText`), bracketing a power of pi.
  - `hold_corpus.json` (140 of 140 cases), by `Tests/Hold.lean`: see
    "The hold corpus" above.
  - `yardstick_corpus.json` (46: `yardstick_key` 25, `yardstick_harness` 17,
    `yardstick_checks` 4), by `Tests/Yardstick.lean` against `Principia.Yardstick`: 46 of 46,
    none owed, no divergence. Each `expect` is read back into typed values and compared with
    the typed result: a key's values as exact numbers (v1's decimal text read exactly), the
    harness's flags and count, the checks' flags and record lists (a list whose words could
    collide in v1's text fails rather than compares), a refusal's reason as a string. The
    Criteria Set is read as the zones read it; the field table is placed on the suite's
    records as v1's `_placed` placed it. Values are exact; v1's two refusals that come from
    doubles (a weight whose nearest double is infinite, a value that overflows the double
    range at any step v1 computed in doubles) are decided on exact values. Differences no
    case reaches: a value v1's rounding pushes over or under the threshold near 2^1024; a
    magnitude below the least double, which v1 rounded to zero and the Calculator keeps, so
    it can separate keys v1 found equal; any other rounding of v1's that could order two
    keys differently; `steps` of 2^1024 or more, where v1 raised and the Calculator refuses.
    A refusal's text is escaped by general category and a record's DOMAIN compared with
    LIMITING DOMAINs after NFC, at Unicode 15.1.0 (D3). Owed, never passed: a Criteria Set
    the zones owe. An owed result fails this runner, since the corpus has none.
  - `form_corpus.json`, all 555 cases, by `Tests/Form.lean` against `Principia.Form`: 552
    pass (1 a recorded v2 divergence) and 3 are owed (see "The declared-forms corpus"
    above).
  - `falcon_corpus.json` (820 of 949 cases; 129 owed to Unicode's tables and to SHA-256),
    by `Tests/Falcon.lean`: see "The falcon corpus" above.
  - `identity_corpus.json`, all 102 cases, by `Tests/Identity.lean` against
    `Principia.Identity`: 82 pass, 20 owed and listed in `identity_corpus.owed.json` (11
    digests, SHA-256 being decision D2; 9 whose result depends on the NFC of a text outside
    the Unicode stopgap's tables, decision D3). Each outcome is compared typed: a refusal
    by its word, a family answer, a change class and a comparison read back from v1's text
    into their types, the canonical tools as text. The owed digest cases are still checked:
    each is one v1 answered with a digest, and on the 9 whose preimage the Calculator
    computes, the preimage equals the one v1 took the digest of, recorded in
    `identity_corpus.preimages.json` by `scripts/identity_preimages.py` from v1's own module
    with each SHA-256 checked (`--check` compares). Fault checks run first: mutated
    expectations and a wrong owed list must be refused.
  - `lint_corpus.json`, all 231 cases, by `Tests/Lint.lean` against `Principia.Lint`: 218
    pass, 13 owed and listed in `lint_corpus.owed.json`, all 13 on Unicode's tables
    (decision D3): a zone, a text or a name holding a code point outside the Unicode
    stopgap's tables, whose NFC or general category the result depends on. Each outcome is
    compared typed and as v1's text: a finding list read back into findings (its code, item
    and locator each read into its type, an entry's id from its own table, a path's names
    from `KNOWN_KEYS`), the counts per code, the tokens, a refusal by its word. v1's tables
    are carried as v1's text in `Principia/Lint/Tables.lean`, which the runner
    `lint_tables` checks against `docs/v1/tpc_py/tpc_lint.py` character for character;
    the SHA-256 v1 checked them against waits on decision D2. Fault checks run first:
    mutated expectations, the order and the owed list's check.
  - `probe_corpus.json`, by `Tests/Probe.lean` against `Principia.Probe`: 168 of 252
    computed, all agreeing with v1's text byte for byte; 84 owed and listed in
    `probe_corpus.owed.json` (83 draws, 1 TEXT finding holding a code point outside the
    Unicode stopgap's tables). Every check v1 makes before a draw is made, so a refusal is
    computed even where the answer would draw. An EQUATION finding is canonical when the
    declared forms' `parseForm` gives it back unchanged, as v1's `parse_form` did; a TEXT
    finding over the code points the stopgap knows is its own NFC. Numbers v1 printed with
    `%.12g` are the exact values correctly rounded to twelve significant digits; no case
    diverges. LOAD's and the view's lists separate identifiers by commas, which v1 does not
    escape, so a case whose identifier holds a comma fails rather than compare; mutation
    checks first confirm that the comparison refuses swapped fields and changed words.
  - `module_corpus.json` (226 of 418 cases; 190 owed to SHA-256 and 2 to Unicode's tables;
    with v1's digests, all 416 not owed to Unicode's tables pass), by `Tests/Provision.lean`
    against `Principia.Provision`: see "The Provision corpus" above.
  - `record_corpus.json` (852 of 932 cases; 80 owed: 66 to SHA-256, 6 to Unicode's tables,
    8 to the numeric meaning) and `record_view_corpus.json` (213 of 213), by
    `Tests/Record.lean`: see "The record corpora" above.
  - `beta_corpus.json` (99), by `Tests/Beta.lean` against `Principia.Beta`: 99 of 99, 2 as
    recorded v2 divergences (`beta_corpus.divergences.json`): L01, `lgamma(1)`, exactly 0
    where v1's Lanczos sum printed -8.881784197e-16; B11, `I_0.51(1000, 1000)`, whose
    twelfth digit v1's error in `lgamma(2000)` (about 1e-12) moved. Under decision D6,
    option 1, every number is exact: the mean a rational, and `ln Γ`, `I_x(a, b)` and the
    quantile between outward-rounded bounds narrowed until their twelve digits settle
    (`Principia/Beta/Enclosure.lean`: Stirling's series with exact Bernoulli numbers and its
    stated remainder, or exact factorials; the hypergeometric series with its tail bound; a
    bracket placed only where the bounds of `I` lie wholly on one side). Every expected value
    was also computed independently with mpmath 1.4.1 at 80 digits (installed by none of the
    checks). A number is compared as its twelve-digit form, rounded once from the exact
    value.
  - `score_corpus.json` (487), by `Tests/Score.lean` against `Principia.Score`: 471 pass, no
    divergence, 16 owed and listed in `score_corpus.owed.json`: the `user_evidence` cases
    that reach `tpc_sponsor.user_evidence`, the sponsor's port, which follows (the 4 that
    tpc_score answers or refuses before that call are compared). Each case's answer is
    written in v1's form and compared line by line and field by field, an account name as
    v1's `_esc` escapes it, so a name holding `|` cannot pass for two fields (mutation
    checks first). The event weights `2^(-age / HALF-LIFE)` are exact sums of rational
    multiples of powers of 2 (`Principia/Score/PowSum.lean`). The runner also prints the
    largest numerator and denominator any exact value of the two corpora reaches (1022 and
    101 bits): no case needs a bound on an exact value's size.
  - `dis_corpus.json` (189: `pre_texts` 28, `d_tps` 58, `d_is` 15, `tps_pages` 88), by
    `Tests/Canonical.lean` against `Principia.Digest.Specification` and by
    `Tests/Calculator.lean` through `pcalc digest`: 189 of 189, none owed, no divergence;
    see "The specification's and the instruction set's digests" above.
  - `sponsor_corpus.json` (83: `resolve` 40, `evidence` 23, `whitewash` 20), by
    `Tests/Sponsor.lean` against `Principia.Sponsor`: 83 of 83, no divergence, none owed.
    Each case's typed outcome is written in v1's form and compared with its `expected`
    text line by line and field by field (`Tests.Score.agrees`), words read back from
    their enumerations and an agent name escaped as v1's `_esc` escapes it, so a name
    holding `|` cannot pass for two fields (mutation checks first). Under decision D6,
    option 1, every number is exact: each aged weight `w 2^(-age / half_life)` and the
    sums `F_u`, `A_u` are exact sums of rational multiples of powers of 2
    (`Principia/Score/PowSum.lean`), `E_u` a rational where it is one, and the interval's
    ends the Beta layer's bounds narrowed until their twelve digits settle; on every case
    v1's double and the exact value round to the same twelve digits. The same port makes
    the call that ends `tpc_score.user_score_evidence`
    (`Principia.Sponsor.scoreUserEvidence`): the 16 `user_evidence` cases of
    `score_corpus.json` that `score_corpus.owed.json` listed now pass with no divergence,
    `score_corpus.json` passes 487 of 487, and `score_corpus.owed.json` lists none. The
    largest exact value: in `sponsor_corpus.json` a numerator of 101 bits and a
    denominator of 102 (E22, an event 100 half-lives old); in the score's `user_evidence`
    answers 16 and 18 bits (Y17). No size bound is needed.
  - `sr3_scope_corpus.json` (91) and `conditions_corpus.json` (34) through `pcalc strike`
    (`sr3_scope`, `conditions_of`, `comparison_set`, `sr8_groups`), by
    `Tests/Calculator.lean` (`runSr3ScopeCalls`, `runConditionsCalls`, each case's input
    through `respondTo "strike"`): 125 of 125, none owed, no divergence. `sr3_scope`'s
    answer is the word or v1's refusal as the value `["REFUSED", reason]`, compared typed
    with v1's text read back (`Tests.Strike.sr3Expect`); the register functions' answers
    are compared as TPM's canonical JSON with the case's `expected`. With these, all five
    of v1's strike test sets run through `pcalc` (`strike_corpus.json`,
    `sr8_order_corpus.json`, `sr9_corpus.json` before). Owed (`OWED`, exit code 1), in no
    case: the CONDITIONS of a record with an AT point whose coherent-SI value carries a
    power of pi. `pcalc.json` gains 22 strike cases, from the built binary: each of the four
    functions, v1's refusals as values (`sr3_scope`'s escaped reason, REC-50, REC-52,
    REC-74), two missing arguments, the owed request, and each AT point bound at and past
    it (a VALUE and a UNIT of 64 and 65 characters, `EeV63` within 2048 bits and `EeV64`
    past them), and `EeV2000 ZeV700`, refused "exact value too large"; the 15 answers v1
    gives were checked against `docs/v1/tpc_py/tpc_strike.py` (`_ccj` of its answer).
    `runFamilyBounds` gains 20 cases at and past the register's bounds. The bounds,
    measured on the built binary on 2026-10-18: the Research Assembly only by the reader's
    1 MiB and 64 levels, `sr3_scope`'s slowest found 0.47 s (an entry name of 349,506
    hidden characters quoted escaped; 37,842 entries 0.13 s); `conditions_of` at most
    2000 records and 5000 ASSUMPTIONS and CITES entries, 0.58 s at worst found (a cycle of
    2000 records, 3000 distinct assumptions, 1000 AT points of 2047 bits on the record
    read); `comparison_set` and `sr8_groups` at most 200 records and 500 entries, 0.77 s
    and 0.67 s (200 standing records in a cycle, 300 distinct assumptions, five AT points
    of 2047 bits each, a Research Assembly filling the rest of 1 MiB; 19,900 pairs
    written); at most 1000 AT points in all, each VALUE and UNIT at most 64 characters, and
    each point of a RESULT or a VERIFICATION within the bound on an exact value and at most
    2048 bits above and below its fraction line (1000 such points 0.4 s). Without them,
    `comparison_set` over 2000 records holding 20,000 citations took 422 s,
    `conditions_of` over 50,000 records 17.8 s, and one AT point in `ZeV1500 EeV4159
    J-5659` (a value of 52,097 digits) 1.4 s, a hundred of them 138 s. The strike closure's
    own bound (2000 records, 20,000 entries) was measured again: 1.15 s when the 18,000
    assumptions are distinct.
  - `volunteer_corpus.json` (202: `standing` 21, `refill` 20, `take` 20, `retry` 23,
    `intake` 21, `p_nw` 21, `pv` 20, `share` 20, `draw` 36), through `pcalc volunteer`
    (`Principia/Calculator/Volunteer.lean`, on `Principia.Volunteer`), by
    `Tests/Volunteer.lean` (each case's `args` read by the Calculator's reader and given to
    `respondTo "volunteer"`; the answer's text, or `ERROR:` and a `BAD_ARGUMENT` refusal's
    detail, compared byte for byte with `expected`): 202 of 202, none owed, no divergence.
    Every uniform value is the probe draw's (SHA-256, `Probe.uniformValue`) and every
    number exact (`Rat`), printed correctly rounded to twelve significant digits where v1
    printed `%.12g` of a double; on every case the exact comparisons and v1's doubles fall
    the same way. A case listed in `volunteer_corpus.divergences.json`, when that file is
    present, must answer exactly its listed text and differ from v1's; the file is absent,
    as no case diverges. PROVED: the bucket's tokens after `refill` never exceed VOLUNTEER
    BURST, `p_nw` lies in [0, 1], RETRY AFTER lies in [0, BACKOFF CAP], a drawn `p_v` lies
    inside P_V BOUNDS and a `p_v` kept inside them stays inside.
- **Never edited.** A corpus's bytes are its identity: each file's SHA-256 is the tree
  manifest's. `.gitattributes` turns line-ending conversion off for `vectors/*.json`;
  seven files (`beta`, `biblio`, `cluster`, `falcon`, `hunk`, `identity`, `sponsor`) end
  without a final newline, and an editor or formatter that adds one changes the digest. A
  v2 divergence is recorded beside the corpus, never in it: `<corpus>.divergences.json`,
  one entry per case with its id, v1's text, the Calculator's text and the cause.
- **Shapes differ from file to file.** Every file has a top-level `"cases"` list; the case
  objects differ (for example `canon`: `{"id", "fn", "input", "expect"}` under a `"meta"`
  object; `biblio`: `{"name", "fn", "args", "hand_checked", "expected"}`). Each family's
  runner reads its own shape.
- They carry public wiki account handles as test data (people are named by role; a public
  handle needs no placeholder).

| Corpus | Cases | Version (hub) |
| --- | ---: | --- |
| `beta_corpus.json` | 99 | 0.1.0 |
| `biblio_corpus.json` | 405 | 0.2.0 |
| `canon_corpus.json` | 17 | 0.1.0 |
| `challenge_corpus.json` | 21 | 0.1.0 |
| `cluster_corpus.json` | 67 | 0.3.0 |
| `conditions_corpus.json` | 34 | 0.1.0 |
| `digest_corpus.json` | 8 | 0.1.0 |
| `dis_corpus.json` | 189 | 0.2.0 |
| `eom_corpus.json` | 421 | 0.2.0 |
| `falcon_corpus.json` | 949 | 0.2.0 |
| `fingerprint_corpus.json` | 127 | 0.1.0 |
| `form_corpus.json` | 555 | 0.5.1 |
| `hold_corpus.json` | 140 | 0.3.0 |
| `hunk_corpus.json` | 30 | 0.1.0 |
| `hunk_wiki_corpus.json` | 48 | 0.1.0 |
| `identity_corpus.json` | 102 | 0.1.0 |
| `lint_corpus.json` | 231 | 0.1.0 |
| `module_corpus.json` | 418 | 0.2.1 |
| `probe_corpus.json` | 252 | 0.2.0 |
| `record_corpus.json` | 932 | 0.1.0 |
| `record_view_corpus.json` | 213 | 0.1.0 |
| `score_corpus.json` | 487 | 0.1.0 |
| `settlement_corpus.json` | 17 | 0.1.0 |
| `sponsor_corpus.json` | 83 | 0.1.0 |
| `sr3_scope_corpus.json` | 91 | 0.1.3 |
| `sr8_order_corpus.json` | 5 | 0.1.0 |
| `sr9_corpus.json` | 31 | 0.1.0 |
| `strike_corpus.json` | 20 | 0.1.0 |
| `tests_corpus.json` | 120 | 0.3.2 |
| `units_corpus.json` | 91 | 0.1.1 |
| `volunteer_corpus.json` | 202 | 0.1.0 |
| `yardstick_corpus.json` | 46 | 0.2.0 |
| `zone_corpus.json` | 335 | 0.5.2 |
| **33 files** | **6,786** | |
