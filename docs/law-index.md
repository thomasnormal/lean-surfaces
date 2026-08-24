# THE LAW INDEX — every rule, and where it lives

**This is the page a lane loads at session start.** It restates nothing. Each
row is a **hook phrase** — the project's own words wherever possible — and a
**pointer to the law's durable home**. Go there to read it; come back here to
find it.

Why an index and not a summary: §7.1a's lesson generalizes past the lock —
*a protocol that lives only in the scratchpad is one purge from gone, and a
pointer to a durable home is not a durable home.* A summary would be a
fourteenth copy of each rule, which is the exact defect
`docs/duplication-audit.md` measured. So: pointers only.

**The index's own ids are `MEAS-`, `STMT-`, `PROOF-`, `OPS-` and `CLONE-`.**
They are *not* amendment numbers — `A4` already means amendment 4 in §7.1a,
and a second numbering over the same letter would be a citation trap.

### Reading the pointers

* `docs/family-architecture.md §7.1a` — section numbers, the doc's own `§N.N`
  and `§N.Na` spelling.
* `docs/backlog.md §Lnn` — the archive's `## Lnn` headings, cited the way the
  doc cites them.
* `docs/backlog/<lane>.md YYYY-MM-DD-<lane>-<n>` — per-lane entries (§9.5).
* `AGENTS.md § <heading>` — AGENTS.md has **eight `##` headings and no `###`
  at all**, so its laws are cited by heading plus the bullet, row or rule
  name.
* A script path — some laws live as **code**, and that is deliberate:
  *the doc DESCRIBES, this script IS.*

### Three traps in the citations themselves

1. **Two amendment rows are marked LOST at source.** §7.1a's register carries
   no recovered text for amendments 1 and 3. Any claim that the protocol is
   fully written down is false by the register's own admission.
2. **`docs/backlog.md`'s bare "law N" numbering has drifted** — §L41 records
   *"the FIFTH renumber this lane has taken today"*, and §L34/§L38 cite a
   "law 5" of an entry whose own list has three. Cite by the `§Lnn` that
   houses the law, never by a bare law number.
3. **`§5.1`/`§5.2` resolve differently depending on which file you stand in.**
   `docs/duplication-audit.md` has its own `§5.1`/`§5.2`, unrelated to
   `docs/family-architecture.md`'s. Always carry the filename.

---

## A. MEASUREMENT LAWS — how you measure, count, compare

| id | hook | home |
| --- | --- | --- |
| MEAS-1 | census before pricing | `docs/family-architecture.md §3.2` item 4 |
| MEAS-2 | one census-instrument pattern per tier; fixed name → fixed JSON path | `docs/family-architecture.md §5.4` |
| MEAS-3 | a `--compare` mode against the committed JSON | `docs/family-architecture.md §5.4` |
| MEAS-4 | every refusal path RUN, not admired | `docs/family-architecture.md §5.4` |
| MEAS-5 | an empty census is an instrument fault, never a finding | `docs/family-architecture.md §5.4` |
| MEAS-6 | double-run byte-identical, verified | `docs/family-architecture.md §5.4` |
| MEAS-7 | every quoted number paired with the STATE it came from | `docs/family-architecture.md §5.4` |
| MEAS-8 | the instrument stamps the frontend FAMILY and the profile | `docs/family-architecture.md §5.4` |
| MEAS-9 | a gate that is a permanent SKIP is a check pretending | `docs/family-architecture.md §5.4` |
| MEAS-10 | A NUMBER CARRIES THE STATE IT WAS MEASURED IN — the provenance law | `docs/family-architecture.md §5.4a` |
| MEAS-11 | an axiom print is meaningful only from a zero-error elaboration | `docs/family-architecture.md §0.1 II(a)` |
| MEAS-12 | a grep that agrees with your prior is the one to re-run | `docs/family-architecture.md §5.4a` |
| MEAS-13 | a bare-word grep over prose is not a type census | `docs/family-architecture.md §3.1` |
| MEAS-14 | two measurements of one fact, never checked against each other | `docs/family-architecture.md §3.1` |
| MEAS-15 | VACUOUS is not a verdict — a nothing-run never scores agreement | `docs/family-architecture.md §5.3` |
| MEAS-16 | DIVERGE must be zero, and REFUSE is never agreement | `docs/family-architecture.md §5.1` |
| MEAS-17 | MATCH is MEMBERSHIP at enumerated sites, not equality | `docs/family-architecture.md §5.1` |
| MEAS-18 | REFUSE's four causes retire on different schedules; never pooled | `docs/family-architecture.md §5.2` |
| MEAS-19 | the manifest is generated and checked, never hand-maintained | `docs/family-architecture.md §5.5` |
| MEAS-20 | coverage = stated / (stated + refused + out-of-tier), per edition | `docs/family-architecture.md §5.5` |
| MEAS-21 | suites drive SCOPE; one exemplar drives the PROOF LIBRARY | `docs/family-architecture.md §5.6` |
| MEAS-22 | a number is adopted when a SECOND rule reproduces it | `docs/family-architecture.md §1.2` |
| MEAS-23 | a corpus's LICENSE and PROVENANCE are registry fields | `docs/family-architecture.md §1.2`, carried at §8 step 0 |
| MEAS-24 | a corpus that vendors the standard it tests is disqualified | `docs/family-architecture.md §1.2` |
| MEAS-25 | no ISO text is reproduced anywhere in this repository | `docs/family-architecture.md §2.1`, restated §11 |
| MEAS-26 | the neutral layer is the measured INTERSECTION | `docs/family-architecture.md §1.3` |
| MEAS-27 | CENSUS-GATED PLACEMENT — a sibling only when a measurement convicts | `docs/family-architecture.md §2.4` clause (1) |
| MEAS-28 | duplication policed by an instrument, not by discipline | `docs/family-architecture.md §2.4` — gate: `tools/dupes.sh` |
| MEAS-29 | clause citations must be checked data, not prose | `docs/family-architecture.md §2.5` |
| MEAS-30 | inside a `.md` an untagged `§` is an internal reference | `docs/family-architecture.md §2.5` |
| MEAS-31 | no step's claim is real until an instrument re-derives it | `docs/family-architecture.md §8` preamble |
| MEAS-32 | LIGHT audit every keeper tick, FULL every ~10 landings | `docs/family-architecture.md §9.7` |
| MEAS-33 | an audit that does not re-measure what it reported is prose again | `docs/family-architecture.md §9.7` |
| MEAS-34 | an amendment from an incident is a hypothesis until re-run | `docs/family-architecture.md §9.7` |
| MEAS-35 | a `--compare` that cannot exit nonzero cannot gate | `docs/family-architecture.md §9.1`; `docs/duplication-audit.md §1.2` (a) |
| MEAS-36 | four `git_rev` copies swallow failure and stamp null | `docs/family-architecture.md §9.1`; `docs/duplication-audit.md §1.2` (b) |
| MEAS-37 | the double-run clause is implemented ZERO times | `docs/duplication-audit.md §0` finding 2 |
| MEAS-38 | nine + five spellings for two provenance concepts | `docs/duplication-audit.md §1.2` (c) |
| MEAS-39 | 28 except-and-pass sites — silent degrade, censused | `docs/duplication-audit.md §1.2` (b) |
| MEAS-40 | exit codes: 0 agree / 1 drift / 2 refusal | `docs/duplication-audit.md §1.3`, restated §10 |
| MEAS-41 | a failed revision lookup must refuse, never stamp null | `docs/duplication-audit.md §10` item (b) |
| MEAS-42 | verify a fix in BOTH directions (agree and drift) | `docs/duplication-audit.md §10`, the verification table |
| MEAS-43 | say when no Lean was executed for a document's numbers | `docs/duplication-audit.md` front-matter |
| MEAS-44 | a gate is not a census — §5.4 does not bind it | `docs/duplication-audit.md §7` |
| MEAS-45 | non-vacuity reported as DELTAS is the law's stronger form | `docs/duplication-audit.md §7` |
| MEAS-46 | rank tiers by `sole`, never by `present` | `AGENTS.md § Orientation` item 3 |
| MEAS-47 | rank by `sole`, THEN price the winner before building it | `AGENTS.md § Orientation` item 3 |
| MEAS-48 | BOTH ENDS pinned separately — oracle and frontend | `AGENTS.md § Orientation` item 3 |
| MEAS-49 | a `live` count, so definitions-only never counts as a run | `AGENTS.md § Orientation` item 3 |
| MEAS-50 | a routine harness run never executes arbitrary stdlib top level | `AGENTS.md § Orientation` item 3 |
| MEAS-51 | never spawn one runner per row — one `--batch` process | `AGENTS.md § The workflow` |
| MEAS-52 | both harnesses compare the exception CLASS, not just stdout+exit | `AGENTS.md § Orientation` item 3 |
| MEAS-53 | `--self-test` walks a tree built to make the tool answer PURE | `AGENTS.md § Orientation` item 3, "Instrument discipline" |
| MEAS-54 | do not ask a command that has nothing to say | `docs/backlog.md §L82` |
| MEAS-55 | run the expression on the fixture and compare heap sizes FIRST | `docs/backlog.md §L25`, standing-law item 1 |
| MEAS-56 | before writing a fuel NUMERAL, measure the minimum | `docs/backlog.md §L25`, standing-law item 2 |
| MEAS-57 | eight seconds each, before any premise is written | `docs/backlog.md §L27` |
| MEAS-58 | cache a computed fixture as a literal, pin it once | `docs/backlog.md §L28` finding 3 |
| MEAS-59 | a classifier that absorbs what it does not recognize is confidently wrong | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-2` |
| MEAS-60 | an empty diff measured nothing — it is not a docs-only landing | `docs/backlog/qol.md 2026-08-22-qol-1` — gate: `tools/triad.sh` |
| MEAS-61 | sized from the pinned spec BEFORE being written | `docs/backlog/es.md 2026-08-22-es-1` |
| MEAS-62 | CONFIDENCE, priced — HIGH only for what was read at the pin | `docs/backlog/wasm.md 2026-08-22-wasm-1` |
| MEAS-63 | a decoder that matches must also cite; an honest miss is loud | `docs/backlog/qol.md 2026-08-22-qol-3` |
| MEAS-64 | a cross-lane transcription carries a TRIPWIRE, or it is a lie with a fuse | `docs/family-architecture.md §5.4` |
| MEAS-65 | stamp the copy — a stamped copy goes out of date, an unstamped one goes wrong | `docs/family-architecture.md §5.4` |
| MEAS-66 | enumerate what each gate is pointed AT; an unpointed claim is ungated | `docs/family-architecture.md §5.4b` |
| MEAS-67 | a gate set is audited by ENUMERATION, never by execution | `docs/family-architecture.md §5.4b` |
| MEAS-68 | an expected-to-fail artifact is the weakest gate in any set — pin the COUNT | `docs/family-architecture.md §5.4b` |
| MEAS-69 | present-tense prose is FIXED; a dated record is ANNOTATED | `docs/family-architecture.md §5.4b` |
| MEAS-70 | a pattern position is a position IN A DECLARATION, never a shape in a file | `docs/family-architecture.md §5.4a` |
| MEAS-71 | a number a gate PUBLISHED is a second artifact — correct it where it was published | `docs/family-architecture.md §5.4a` |
| MEAS-72 | an instrument selecting by content excludes ITSELF by identity, never by pattern | `docs/family-architecture.md §5.4` |
| MEAS-73 | a check that cannot fire is the audit's own VACUOUS category | `docs/family-architecture.md §9.7` |
| MEAS-74 | a no-code closure is closed when the AUDIT FILE carries the reason | `docs/family-architecture.md §9.7` |
| MEAS-75 | MEAS-28's first consolidation: the Lean lexer once | `docs/family-architecture.md §2.4` — gate: `tools/leanlex.sh` |
| MEAS-76 | an entry point REFUSES unknown arguments at line one | `docs/family-architecture.md §5.4` |
| MEAS-77 | a correct refusal is not a mitigation — the hazard sits behind it | `docs/family-architecture.md §7.1a` A13 corollary |
| MEAS-78 | an instrument optimization is proved by OUTPUT EQUALITY, never by speed | `docs/family-architecture.md §5.4a` |
| MEAS-79 | the optimization that is also a SIMPLIFICATION deletes a distinction — pin it in a row | `docs/family-architecture.md §5.4a` |
| MEAS-80 | two tools disagreeing: find the artifact that DEFINES the fact, one reader | `docs/family-architecture.md §5.4a` — gate: `tools/lakeinfo.sh` |
| MEAS-81 | a guard must ask the question its MESSAGE claims to answer | `docs/family-architecture.md §5.4a` |
| MEAS-82 | a guessed pointer is worse than a missing one — `UNRESOLVED`, never guessed | `docs/family-architecture.md §5.4b` — gate: `tools/laws.sh --gate-set` |
| MEAS-83 | an empty field in a whitespace-separated record is not a field | `docs/family-architecture.md §5.4b` |
| MEAS-84 | a fixture is not enforcement — strip the self-test before attributing | `docs/family-architecture.md §9.7` — gate: `tools/laws.sh` |
| MEAS-85 | past the budget every count is a FLOOR, and the verdict goes to a FILE | `docs/family-architecture.md §9.7` |
| MEAS-86 | heartbeats are a DETERMINISTIC step count; wall time is not — say why it was dropped | `docs/family-architecture.md §5.4a` |
| MEAS-87 | a probe cannot certify its own definitions — the TREE's green ledger does | `docs/family-architecture.md §5.4a` |
| MEAS-88 | check whose CLOSURE a file sits in before placing two things side by side | `docs/family-architecture.md §2.4` clause (1a) |
| MEAS-89 | a table asserting how the interpreter classifies is unfalsifiable until the interpreter confirms it | `docs/family-architecture.md §5.2` |
| MEAS-90 | a false blanket claim HIDES the real gap — the claim is why nobody looked | `docs/family-architecture.md §5.4` |
| MEAS-91 | cite by NAME — fixing offsets buys one landing of accuracy | `docs/family-architecture.md §5.4` |
| MEAS-92 | a row is closed when the CLAIM is true; a substituted remedy must SAY WHICH | `docs/family-architecture.md §9.7` |
| MEAS-93 | a new instrument's FIRST finding is the one to re-run against the OLD input | `docs/family-architecture.md §5.4b` |
| MEAS-94 | a DECLARATION is not a CALL; a CALL is not a RUN — the gate ladder's four states | `docs/family-architecture.md §5.4b` |
| MEAS-95 | enumeration over-reports, execution under-reports — a gate set needs both | `docs/family-architecture.md §5.4b` |
| MEAS-96 | a right action taken for a wrong STATED reason survives the fix | `docs/family-architecture.md §5.4b`; `docs/backlog/architecture.md 2026-08-23-architecture-32` |
| MEAS-97 | an unconditional byte-comparing gate inherits every unpinned input it compares | `docs/family-architecture.md §5.4b` |
| MEAS-98 | a green that holds because nobody has released is evidence about the WORLD | `docs/family-architecture.md §5.4b` |
| MEAS-99 | a flagged wart plus a new gate is an armed bomb — re-read dormancy records | `docs/family-architecture.md §5.4b`, §9.7 trigger |
| MEAS-100 | a RED BUILD is an outage of every gate behind it | `docs/family-architecture.md §5.4b` |
| MEAS-101 | the PIN AUDIT belongs to the arming commit — both arms of any `||` fallback | `docs/family-architecture.md §5.4b` |
| MEAS-102 | a hint is an instruction; one that reproduces the defect IS the defect | `docs/family-architecture.md §5.4b` |
| MEAS-103 | a number from another tier prices yours only if the STRUCTURES match | cookbook §22; `docs/family-architecture.md §9.7` |
| MEAS-104 | a NAMED blocker is a next step; an unnamed one is a wall | `docs/family-architecture.md §9.7` |
| MEAS-105 | a census that names a LANGUAGE when it measured one of its TIERS | cookbook §22; `docs/backlog/architecture.md 2026-08-23-architecture-35` |
| MEAS-106 | the tell is the UNIFORMITY, not the count — a wrong column, not a systemic bug | `docs/family-architecture.md §5.4b` |
| MEAS-107 | an unexercised gate is not a gate; it is a claim | `docs/family-architecture.md §5.4b` |
| MEAS-108 | zero for a class the tier CAN emit is about the CORPUS; cannot build, about the TIER | `docs/family-architecture.md §5.2` |
| MEAS-109 | a well-named blocker NARROWS each time it is re-stated | `docs/family-architecture.md §9.7` |
| MEAS-110 | a proof demotes the rows about the RELATION IT PROVED, and no others | `docs/family-architecture.md §5.4a` |
| MEAS-111 | generalization by composition — a consumer widening a quantifier for free is a measurement | `docs/family-architecture.md §5.6` |
| MEAS-112 | corpus-driven selection finds the frontier's traversable point BY CONSTRUCTION | `docs/family-architecture.md §9` |
| MEAS-113 | an upstream representation's unit is not YOUR unit — a parser's kinds are the parser's | `docs/family-architecture.md §5.4a` |
| MEAS-114 | re-run the census when the plan becomes EXPENSIVE — the last point a refutation is free | `docs/family-architecture.md §9.0a` |
| MEAS-115 | a PERFORMANCE SYMPTOM is a modelling question — the faithful shape is often the cheap one | `docs/family-architecture.md §5.4a` |
| MEAS-116 | once PROVED for one implementation, a spec adjudicates its SIBLINGS — a third adjudicator kind | `docs/family-architecture.md §5.6` |
| MEAS-117 | named single rows beside an exhaustive sweep — so a failure lands BY NAME | `docs/family-architecture.md §5.6` |
| MEAS-118 | ~~`+0` is a precedence fact~~ **RETRACTED** — a construct's delta is a function of the CURRENT VOCABULARY | `docs/family-architecture.md §9.0b` |
| MEAS-118a | a law minted from a DELTA inherits the delta's baseline — state it, or it is a measurement pretending to be a principle | `docs/family-architecture.md §9.0b` |
| MEAS-118b | a number from a one-off script can only be WITHDRAWN, never corrected | `docs/family-architecture.md §9.0b` |
| MEAS-119 | THE CONJUNCTIVE LAW — price a rung against the FAMILY it belongs to, report both numbers | `docs/family-architecture.md §9.0b` |
| MEAS-120 | decide whether a blocker lives in the VALUE or in the REFERENCE — different owners | `docs/family-architecture.md §5.4a` |
| MEAS-121 | the discriminating case is `(FUNCTION, ARGUMENT)` — not the function alone | `docs/family-architecture.md §5.6` |
| MEAS-122 | rows the wrong model PASSES < rows it FAILS < rows it CANNOT STATE | `docs/family-architecture.md §5.6` |
| MEAS-123 | every symptom of a missing LEMMA is also a symptom of a missing IMPORT — grep the TREE | `docs/family-architecture.md §9.0a` |
| MEAS-124 | pre-flight a name-collision grep for every name a landing DECLARES | `docs/family-architecture.md §9.0a` |
| MEAS-125 | attribute staleness to a PHASE — queue and build are different costs | `docs/family-architecture.md §7.2` |
| MEAS-126 | order work by what is SHARED, not by what is NEXT | `docs/family-architecture.md §9.0b` |
| MEAS-127 | a predicted maintenance COST inherits the unit error of the construct it prices | `docs/family-architecture.md §5.4a` |
| MEAS-128 | an OPENING is witnessed with the oracle's expectation, never a second decision site | `docs/family-architecture.md §5.4a` |
| MEAS-129 | a coverage PIN is maintained in the landing that grows the artifact | `docs/family-architecture.md §5.4a` |
| MEAS-130 | NO STANDING EXCEPTION — another lane's dated record is annotated by that lane, not on instruction | `docs/family-architecture.md §9.5a` |
| MEAS-131 | enumerate a gate's scope by DISCOVERY — a list is maintained by the attention that wrote the defect | `docs/family-architecture.md §5.4b` — gate: `tools/ci.sh` argv-guards |
| MEAS-132 | a newly written READER defaults to UNDER-reading, the direction that reports all clear | `docs/family-architecture.md §5.4b` |
| MEAS-133 | a fixture is not a TOOL — the mirror of a fixture is not enforcement | `docs/family-architecture.md §5.4b` |
| MEAS-134 | FLAG a duplicate, never de-dupe — a de-dupe could silently shrink a set | `docs/family-architecture.md §5.4b` |
| MEAS-135 | a guard that ALWAYS fires is as useless as one that never can — MEAS-35's mirror | `docs/family-architecture.md §5.4b` |
| MEAS-136 | a re-baseline names what the guard now watches AND reports that no published fact moved | `docs/family-architecture.md §5.4b` |
| MEAS-137 | a duty that has never been EXECUTED is a plan, not a duty | `docs/family-architecture.md §5.4b` |
| MEAS-138 | a PROCEDURE is not a GATE — instrument it, or rename it | `docs/family-architecture.md §5.4b` |
| MEAS-139 | WAITING names an EXECUTABLE trigger, or it is a euphemism for stopped | `docs/family-architecture.md §9` |
| MEAS-140 | a channel that greps the CONSTRUCTOR cannot see the TYPE — enumerate the KINDS of position | `docs/family-architecture.md §5.4a`; `tools/sites.sh` |
| MEAS-141 | a leading dot and a qualifier are different dots — what PRECEDES the dot decides | `docs/family-architecture.md §5.4a` |
| MEAS-142 | DUPLICATION IS DISCOVERED BY CHANGING, not by reading — grep the OLD VALUE | `docs/family-architecture.md §7.2` |
| MEAS-143 | pair every "did not change" row with a "did happen" sibling | `docs/family-architecture.md §5.4b` |
| MEAS-144 | a document that ENUMERATES a set owns that set's maintenance | `docs/family-architecture.md §7.2` |
| MEAS-145 | a WITNESS must fail for the reason it names — the SPELLING has to be in tier | `docs/family-architecture.md §5.4` |
| MEAS-146 | INAPPLICABLE, NOT OPTIONAL — a requested artifact with no subject | `docs/family-architecture.md §9.7` |
| MEAS-147 | a zero DELTA across a capability inch is a claim about the INCH — three zeroes, never pooled | `docs/family-architecture.md §5.2` |
| MEAS-148 | scope evidence per WORKING DIRECTORY (`--git-dir`) — the cache is part of what produced the green | `docs/family-architecture.md §5.4a-i` |
| MEAS-149 | a ledger of ATTEMPTS is a log; a log is not evidence of a verdict | `docs/family-architecture.md §5.4a-i` |
| MEAS-150 | A FULL BUILD IS ITS OWN ROOT, however it was reached | `docs/family-architecture.md §5.4a-i` |
| MEAS-151 | unit rows test the CALLEE's arguments; only the seam tests the CALL SITE | `docs/family-architecture.md §5.4b` |
| MEAS-152 | a transform on NOTHING produces nothing and reports success doing it | `docs/family-architecture.md §5.4b` |
| MEAS-153 | when one predicate SUBSUMES another, ask it FIRST | `docs/family-architecture.md §5.4a-i` |
| MEAS-154 | THE GOAL IS COMPLETION — full-spec support, measured by the tier's own conformance suite | `docs/family-architecture.md §9.0` |
| MEAS-155 | every lane ledger carries its standing SPEC-COVERAGE number, per landing, stamped | `docs/family-architecture.md §9.0` |
| MEAS-156 | a milestone is a WAYPOINT — "the exemplar is complete" never describes a TIER | `docs/family-architecture.md §9.0` |
| MEAS-157 | a completion claim cites a SUITE NUMBER and its SHA, or it is about an artifact | `docs/family-architecture.md §9.0` |
| MEAS-158 | THE SPEC SURFACE IS A CONSUMER — completion unlocks a deferral; the census still orders it | `docs/family-architecture.md §9.0` |
| MEAS-159 | WAITING is a property of a SLICE, never of a LANE | `docs/family-architecture.md §9` |
| MEAS-160 | the strongest row kills TWO wrong models in OPPOSITE directions — the direction names the culprit | `docs/family-architecture.md §5.6` |
| MEAS-161 | a minted law caught its own lane's FUTURE error — the register is predictive, not only descriptive | `docs/family-architecture.md §9.7` |
| MEAS-162 | a coverage table publishes TWO denominators and the cost of the choice | `docs/family-architecture.md §9.0` |
| MEAS-163 | a SYNTACTIC-ONLY win must never be banked in a coverage number | `docs/family-architecture.md §9.0` |
| MEAS-164 | no corpus witness RELOCATES the discriminator into the call — census, relocate, confirm | `docs/family-architecture.md §9.0` |
| MEAS-165 | the conjunctive law's third level — a file needs every FUNCTION it calls, not the package's name | `docs/family-architecture.md §9.0b` |
| MEAS-166 | an ALTERNATION derived from a census is a consequence; one adopted as convention is a rhythm | `docs/family-architecture.md §9.0b` |
| MEAS-167 | a mechanism's acceptance case needs TWO entries — one row proves an answer, two prove a lookup | `docs/family-architecture.md §5.6` |
| MEAS-168 | the gate lands WITH the capability — fixes-live-in-gates applied at birth skips the incident | `docs/family-architecture.md §5.6` |
| MEAS-169 | import-REACHABILITY completes the pre-flight pair: names you USE that resolve nowhere | `docs/family-architecture.md §9.0a` |
| MEAS-170 | a coverage number's DENOMINATOR counts what could have DISAGREED | `docs/family-architecture.md §9.0` |
| MEAS-171 | a numerator earned by FORWARDING needs the theorem that the forwarding is faithful | `docs/family-architecture.md §9.0` |
| MEAS-172 | a goal theorem nobody has TYPED is one nobody can typecheck against | `docs/family-architecture.md §9.0` |
| MEAS-173 | a DECLINED alternative is recorded with the measurement that declined it | `docs/family-architecture.md §9.0` |
| MEAS-174 | the NUMERATOR counts only what the family's definition ADMITS | `docs/family-architecture.md §9.0` |
| MEAS-175 | a census that predicts its own gain TO THE UNIT is calibration evidence — **AMENDED**: only when PREDICTOR and SCORER are independent; a same-instrument match verifies TRANSCRIPTION, not truth | `docs/family-architecture.md §9.0` |
| MEAS-176 | NAMED, NOT COUNTED — a live obligation kept out of the denominator until its premise is proved | `docs/family-architecture.md §9.0` |
| MEAS-177 | a RE-FOUNDING's size is the count of statements that NAME the interpreter | `docs/family-architecture.md §5.4a` |
| MEAS-178 | a SECTION CITATION is mechanically checkable — same class as the docs_check anchors | `docs/family-architecture.md §5.4b` |
| MEAS-179 | when the ambient verdict is CONSTANT, every bit of information is in the pin | `docs/family-architecture.md §5.4b` |
| MEAS-180 | "does not apply at all" is a claim about a LIBRARY — only writing the bridge measures it | `docs/family-architecture.md §8` item 11 |
| MEAS-181 | record a correction as a REFINEMENT with both halves, never as an erratum | `docs/family-architecture.md §8` item 11 |
| MEAS-182 | a qualifier may attach to a RANGE of dated entries — rewriting destroys what was known when | `docs/family-architecture.md §8` item 11 |
| MEAS-183 | a STATUS COLUMN names what it measures — in-tree and rostered are separate facts | `docs/family-architecture.md §1.2` |
| MEAS-184 | a verdict certifies a TREE, never a TITLE — compare the certified tree against the claim | `docs/family-architecture.md §5.4a-i` |
| MEAS-185 | witness ranking **AMENDED**: tree identity FIRST, `Built`/`Replayed` SECOND, clock THIRD (duration is a corroborator, not the witness) | `docs/family-architecture.md §5.4a-i` |
| MEAS-186 | a REFUSAL is a pending measurement — the model emits the datum the census cannot see | `docs/family-architecture.md §5.2` |
| MEAS-187 | a clause number RESOLVES; a RANGE enumerates, and a range is edition-relative | `docs/family-architecture.md §2.5` |
| MEAS-188 | a CORPUS can settle an edition question a missing document cannot — presence, never semantics | `docs/family-architecture.md §2.5` |
| MEAS-189 | after "what is it pointed at", ask WHAT MAKES IT RUN — a gate reached by accident retires by accident | `docs/family-architecture.md §5.4b` |
| MEAS-190 | PARTITION instruments by corpus dependence; the one that needs it names its re-acquisition | `docs/family-architecture.md §5.4b` |
| MEAS-191 | a `+0` disclosed in the PLAN is a control; the same number in the retrospective is accounting | `docs/family-architecture.md §9.0b` |
| MEAS-192 | non-vacuity is a CHAIN OF LINKS — a link whose only guard is nested within it is unguarded | `docs/family-architecture.md §5.3` |
| MEAS-193 | a coverage bound has a DIRECTION and must state it — "syntactic ⇒ upper" is not general | `docs/family-architecture.md §9.0` |
| MEAS-194 | a COUNT IN PROSE without its unit becomes whichever count the reader needs | `docs/family-architecture.md §3.2` |
| MEAS-195 | an open-obligation census reads the DECLARATION, never the commentary | `docs/family-architecture.md §5.4a` |
| MEAS-196 | a standing DISCLOSURE lives where the claim is served, not where the apology is filed | `docs/family-architecture.md §9.0` |
| MEAS-197 | a loudness guard present in 1 of 163 files is DECLARED, not POINTED — record the ladder position with the law | `docs/family-architecture.md §7.1a` |
| MEAS-198 | completeness is counted PER ORIENTATION, not per lemma NAME | `docs/family-architecture.md §9.0` |
| MEAS-199 | a pin move is drift or deliberate — PRIOR DECLARATION plus named departures decides | `docs/family-architecture.md §5.4b` |
| MEAS-200 | the LAST RUNG is the tall one — the census says so in advance, not after | `docs/family-architecture.md §9.0b` |
| MEAS-201 | the acceptance hierarchy ranks CLAIMS, not CLAIMANTS — a coordinator's hypothesis enters at the same rung | `docs/family-architecture.md §5.6` |
| MEAS-202 | a guard's REPUTATION and its MECHANISM drift apart silently — read the mechanism | `docs/family-architecture.md §7.2` |
| MEAS-203 | RE-POINTING a guard is not monotone tightening — each flipped verdict owes its reasoning where the check lives | `docs/family-architecture.md §7.2` |
| MEAS-204 | a defect in a PRIMITIVE: census its other callers before closing | `docs/family-architecture.md §7.2` |
| MEAS-205 | ask the ORACLE that already answers — a label re-derived inline is a second, weaker classifier | `docs/family-architecture.md §7.2` |
| MEAS-206 | a TAXONOMY OF ABSENCE belongs at the print statement, where a zero and a non-answer become one | `docs/family-architecture.md §7.2` |
| MEAS-207 | a failure that only ever costs TIME has no constituency for fixing it | `docs/family-architecture.md §5.4b` |
| MEAS-208 | AN ID IS ONE TOKEN — a migration-tolerant gate separates old-valid from never-valid | `docs/family-architecture.md §9.5` |
| MEAS-209 | a CONVENTION in a charter can be a DEFECT in a tool — re-check prose rules against the program that reads them | `docs/family-architecture.md §9.5a` |
| MEAS-210 | reconciliation splits: TENSE/STATUS at the merge, REASONING/LAWS inbound — does the edit change what it CLAIMS or WHEN | `docs/family-architecture.md §9.5a` |
| MEAS-211 | the merge fixes what is FALSE; only the owner sees what is now REDUNDANT | `docs/family-architecture.md §9.5a` |
| MEAS-212 | two remedies for one symptom: an ENTRY gets an id, a SECTION HEADER gets demoted — never an invented id | `docs/family-architecture.md §9.5` |
| MEAS-213 | a guard that can NAME a defect it cannot CLASSIFY must hand it to someone who can | `docs/family-architecture.md §9.5` |
| MEAS-214 | a DECLARED divergence is a DEBT, not a verdict — registered, aged and gated, never narrated | `docs/family-architecture.md §5.0a` |
| MEAS-215 | the divergence register is gated BOTH ways — silently fixed is a stale claim, silently widened is worse | `docs/family-architecture.md §5.0a` |
| MEAS-216 | declared divergences are a THIRD quantity in §9.0 — neither numerator nor denominator | `docs/family-architecture.md §5.0a` |
| MEAS-217 | INHERITED is not ORIGINATED — the retirement condition lives upstream, and the citation is the obligation | `docs/family-architecture.md §5.0a` |
| MEAS-218 | an INGESTION REWRITE is available exactly when the construct's meaning is decided by SYNTAX | `docs/family-architecture.md §5.4a` |
| MEAS-219 | a census sampling from ONE POSITION measures that position's rule, not the construct's | `docs/family-architecture.md §5.4a` |
| MEAS-220 | a docstring that ENUMERATES is a census no instrument re-runs; a CLOSED LIST argues against its own repair | `docs/family-architecture.md §5.4` |
| MEAS-221 | a debt row's MODEL field is a MEASUREMENT — the row and its instrument land in one commit | `docs/family-architecture.md §5.0a` |
| MEAS-222 | LAYERED INSTRUMENTS — the build gates the CONTENT, the harness gates the EXISTENCE | `docs/family-architecture.md §5.0a` |
| MEAS-223 | a retirement condition names what must CHANGE and what must NOT — the negative half blocks the flattering repair | `docs/family-architecture.md §5.0a` |
| MEAS-224 | INHERITED-FROM-SELF keeps the field: origin ≠ site, and the condition gets STRONGER | `docs/family-architecture.md §5.0a` |
| MEAS-225 | reading master and BEING on master are different needs — a bare mirror satisfies the first | `docs/family-architecture.md §7.2` |
| MEAS-226 | a witness is a TOKEN PLUS THE PHASE it was read from — a log is not a bag of lines | `docs/family-architecture.md §5.4a-i` |
| MEAS-227 | the certified-tree boundary is expressed at MERGE GRANULARITY — separate shas, declared before | `docs/family-architecture.md §5.4a-i` |
| MEAS-228 | to choose between model SHAPES, ask which one ACCEPTS a program the oracle REJECTS | `docs/family-architecture.md §5.6` |
| MEAS-229 | a ROW COUNT is not acceptance power — the non-vacuity flips measure which rows do the work | `docs/family-architecture.md §5.6` |
| MEAS-230 | a duplicated SPECIFICATION is found by the namespace, not by review | `docs/family-architecture.md §2.4` |
| MEAS-231 | a plan that prices its next rung EXACTLY makes a falsifiable claim — the landing calibrates the instrument | `docs/family-architecture.md §9.0b` |
| MEAS-232 | a refusal can be honest about the MODEL and false about the WORLD — only corpus-derived shapes catch it | `docs/family-architecture.md §5.2` |
| MEAS-233 | where duplication is tempting, PIN BY `rfl` — not a second implementation that agrees | `docs/family-architecture.md §2.4` |
| MEAS-234 | "empty for a statable reason" is a third kind of zero — the debt belongs on the refusal, not the gate | `docs/family-architecture.md §5.4b` |
| MEAS-235 | a DEFERRAL carries its ladder position and its trigger, like a law | `docs/family-architecture.md §5.4b` |
| MEAS-236 | COUNT DEFECTS AFTER UNIFICATION, never by error lines | `docs/family-architecture.md §7.1a` |
| MEAS-237 | a library's own WORKAROUNDS are evidence about what it cannot do — the simprocs are the confession | `docs/family-architecture.md §7.1a` |
| MEAS-238 | NOTHING CHECKS a ticket's base was ever green — the queue outlasts the fix | `docs/family-architecture.md §7.2` |
| MEAS-239 | THREE STATES: green, red-on-my-work, ABORTED — collapsing the third concedes a defect you do not have | `docs/family-architecture.md §7.2` |
| MEAS-240 | a finding about the TOOL that is also true of your own IN-FLIGHT tenure is an INCIDENT, not a finding | `docs/family-architecture.md §5.4a-i` |
| MEAS-241 | check whether a tool defect is ALREADY FIXED UPSTREAM before reporting it as residual | `docs/family-architecture.md §7.2` |
| MEAS-242 | a SOUND NARROWING has residual classes — safe-by-construction bounds what it LOSES, not what it ADMITS | `docs/family-architecture.md §5.4a` |
| MEAS-243 | hand resolutions are TRAINING DATA for a rule; the rule's acceptance test is reproducing them EXACTLY | `docs/family-architecture.md §5.4a` |
| MEAS-244 | the tell that an instrument ladder is climbed rather than dismantled: the SELF-TEST GETS LONGER | `docs/family-architecture.md §5.4b` |
| MEAS-245 | a shape the rules once REQUIRED cannot become a failure the day a new rule lands | `docs/family-architecture.md §9.5a` |
| MEAS-246 | conforming to one rule is when you are most likely to break its NEIGHBOUR | `docs/family-architecture.md §9.5a` |
| MEAS-247 | a RECIPE transfers by reading; a FUNCTION is a constant — alike in the source, different in the tree | `docs/family-architecture.md §9.0` |
| MEAS-248 | a standing block is a `###` SECTION, only landings are `##` ENTRIES — say the level or three lanes pick one | `docs/family-architecture.md §9.0` |
| MEAS-249 | REGISTER SHAPE — per-tier DATA, one shared CHECKER, per-tier PROBE named in the row | `docs/family-architecture.md §5.0a` |
| MEAS-250 | a divergence row names its KIND — `semantic` retires by remodelling, `provenance` by re-running | `docs/family-architecture.md §5.0a` |
| MEAS-251 | REACHABILITY is part of a guard's definition — an unreachable refusal guards nothing | `docs/family-architecture.md §5.2` |
| MEAS-252 | a DISPOSITION without its applied diff is aged like a divergence row | `docs/family-architecture.md §9.7` |
| MEAS-253 | the RECIPIENT's measurement, not the sender's, closes an INBOUND row | `docs/family-architecture.md §9.5a` |
| MEAS-254 | a diff between two censuses is only a number if both answered the SAME QUESTION | `docs/family-architecture.md §5.4` |
| MEAS-255 | a registered UNASSERTED expectation is the falsifiable version of a TODO | `docs/family-architecture.md §5.6` |
| MEAS-256 | the defect is not unreachability — it is a REFUSAL BELIEVED TO BE A BOUNDARY that is not one | `docs/family-architecture.md §5.2` |
| MEAS-257 | a verification claim carries WHAT was verified — a sha-less "verified" is a TITLE | `docs/family-architecture.md §5.4a-i` |
| MEAS-258 | the witness taxonomy is `Built` / `Replayed` / SILENT-CURRENT — only the DEPENDENTS disambiguate the third | `docs/family-architecture.md §5.4a-i` |
| MEAS-259 | ANONYMOUS EVIDENCE CANNOT BE CITED — a probe is a NAMED declaration | `docs/family-architecture.md §5.0a` |
| MEAS-260 | the register's checker FAILS on an empty set — a test passing because it found nothing is the unexercised gate | `docs/family-architecture.md §5.0a` |
| MEAS-261 | the best retirement conditions have NO PLACE FOR AN OPINION TO ENTER — artifact presence, or a count reaching zero | `docs/family-architecture.md §5.0a` |
| MEAS-262 | KIND changes the GUARD VOCABULARY, not just the retirement condition | `docs/family-architecture.md §5.0a` |
| MEAS-263 | a row that says what it CANNOT measure is the register's honesty applied to itself | `docs/family-architecture.md §5.0a` |
| MEAS-264 | convert a CLAIMS LIST into a THEOREM — where claim and subject share a build, the check belongs in the build | `docs/family-architecture.md §5.4` |
| MEAS-265 | a check whose failure does not STOP THE NEXT STEP is not a gate, it is a comment | `docs/family-architecture.md §5.4b` |
| MEAS-266 | a cross-lane instrument firing on another lane's code is the instrument WORKING — fix adjudication, never scope | `docs/family-architecture.md §5.4a` |
| MEAS-267 | a census may return DONE — trustworthy only from a census that could have returned otherwise | `docs/family-architecture.md §9.0b` |
| MEAS-268 | a REFUSAL names a SITE, not its CAUSE — witness the cause separately or the site gets blamed | `docs/family-architecture.md §5.2` |
| MEAS-269 | an EPISTEMIC BOUNDARY is a fact about the instrument, not a gap in the model — **AMENDED**: it is itself a CLAIM and lands only after a witness attempt that failed to CONSTRUCT | `docs/family-architecture.md §5.2` |
| MEAS-270 | an unreachable CHECK is kept; an unreachable REFUSAL is a defect — the claim is the discriminator | `docs/family-architecture.md §5.2` |
| MEAS-271 | ORPHANED is the shape a deleted row leaves behind — check from the GUARDS back to the ROWS | `docs/family-architecture.md §5.0a` |
| MEAS-272 | between a RULED IDIOM and an IMPLEMENTED PRECEDENT, follow the instance until the ruling has one | `docs/family-architecture.md §5.0a` |
| MEAS-273 | an acceptance test written against a PATTERN inherits every future instance for free | `docs/family-architecture.md §5.0a` |
| MEAS-274 | an exhaustiveness arm: PROVABLE → discharge in the type; otherwise REFUSAL-FORM, and GATE the by-construction claim | `docs/family-architecture.md §5.2` |
| MEAS-275 | a warning is validated by a documented decision NOT to act, not by a saved incident | `docs/family-architecture.md §7.2` |
| MEAS-276 | a clean rebase still produces a DIFFERENT COMMIT — the certificate names the one that was BUILT | `docs/family-architecture.md §5.4a-i` |
| MEAS-277 | COMPOSITION is a census axis — singles find nothing on it, by construction | `docs/family-architecture.md §5.2` |
| MEAS-278 | a refusal adopted to AVOID A DEBT is a weakening wearing a boundary's clothes | `docs/family-architecture.md §5.0a` |
| MEAS-279 | a `has_not_widened` guard whose content is a passing AGREEMENT case exhibits the window's edge | `docs/family-architecture.md §5.0a` |
| MEAS-280 | a divergence localized to a CONSTRUCTION-SITE difference has a mechanical retirement | `docs/family-architecture.md §5.0a` |
| MEAS-281 | a milestone survives a divergence only by MEASUREMENT against it, stated where the number is read | `docs/family-architecture.md §9.0` |
| MEAS-282 | a standing number landing in the SAME TREE as its last rung is SELF-CERTIFYING | `docs/family-architecture.md §9.0` |
| MEAS-283 | LAWS DO NOT INOCULATE THEIR AUTHORS — gates do | `docs/family-architecture.md §5.3` |
| MEAS-284 | a STRUCTURAL EDIT needs a structural bound and a counted check | `docs/family-architecture.md §5.4b` |
| MEAS-285 | FALSE positives on another lane are worse than no gate — ship the cases it must NOT fire on | `docs/family-architecture.md §5.4a` |
| MEAS-286 | a RESIDUE without its POPULATION is a number wearing a context it does not have | `docs/family-architecture.md §9.0` |
| MEAS-287 | a refusal gate whose instrument measures a MONOTONE PROXY makes a transient condition permanent | `docs/family-architecture.md §7.1a` A17 |
| MEAS-288 | COST STRUCTURE IS SET BY INSTRUMENTS, NOT BY DEFECTS | `docs/family-architecture.md §7.1a` A17 |
| MEAS-289 | "my lane is blocked" is the worst reason to move a shared safety line — the fix lives with the gate's OWNER | `docs/family-architecture.md §5.4a` |
| MEAS-290 | a requested acceptance clause is a HYPOTHESIS; the implementer's counter-measurement is part of the acceptance | `docs/family-architecture.md §5.0a` |
| MEAS-291 | isolation demanded of TESTS is demanded of every process the session spawns — the informal ones are the gap | `docs/family-architecture.md §5.0a` |
| MEAS-292 | §5.0a admits NO PERMANENT ROW — can the closing condition be NAMED? no experiment ⇒ epistemic boundary | `docs/family-architecture.md §5.0a` |
| MEAS-293 | an oracle DISAGREEMENT is not a divergence when the SPEC admits both answers | `docs/family-architecture.md §5.0a` |
| MEAS-294 | a SAMPLE whose order differs from its label's order is a different sample wearing the label | `docs/family-architecture.md §5.4b` |
| MEAS-295 | a row that checks the CAPTION while the picture is wrong is not a test of the picture | `docs/family-architecture.md §5.4b` |
| MEAS-296 | a WIDENING flag that silently does nothing makes an honest lane state a false coverage claim | `docs/family-architecture.md §5.4b` |
| MEAS-297 | an instrument earns a NEW number by first reproducing an OLD one already gated | `docs/family-architecture.md §5.4b` |
| MEAS-298 | a WHITELIST of legal positions claims the grammar; a BLACKLIST claims a few commands — only the second is parser-free | `docs/family-architecture.md §5.4a` |
| MEAS-299 | MEMBERSHIP IN THE GREEN CORPUS as a parser proxy — admissible only when stated as WEAKER than parsing | `docs/family-architecture.md §5.4a` |
| MEAS-300 | a fleet status is THREE NUMBERS — rungs assigned, executing, building — never "N lanes live" | `docs/family-architecture.md §1.2`, §9.0 |
| MEAS-301 | DURABILITY LIVES IN ARTIFACTS, NOT IN AGENTS | `docs/family-architecture.md §7.2` |
| MEAS-302 | a certificate over the WORKING TREE makes even uncommitted state recoverable | `docs/family-architecture.md §7.2` |

## B. STATEMENT LAWS — how a claim must be worded to mean something

The worked forms, with the trap and the incident for each, are in
**`docs/statement-cookbook.md`**. This section indexes the laws themselves.

| id | hook | home |
| --- | --- | --- |
| STMT-1 | THE DEFINITION IS NEVER WEAKENED FOR PROVABILITY | `docs/family-architecture.md §0.1` principle I |
| STMT-2 | definitional completeness outranks proof convenience, always | `docs/family-architecture.md §0.1` principle I |
| STMT-3 | the trust boundary — DEFINITION trusted and minimal, LIBRARY never | `docs/family-architecture.md §0.1` principle II |
| STMT-4 | the library grows BY DEMAND; its gaps are published, never papered | `docs/family-architecture.md §0.1` principle II |
| STMT-5 | the preference ladder: symbolic ▸ kernel `decide` ▸ decide-class | `docs/family-architecture.md §0.1 II(a)` |
| STMT-6 | the trust boundary is per-theorem and visible, never ambient | `docs/family-architecture.md §0.1 II(a)` |
| STMT-7 | HARDNESS IS A SIGNAL TO THE PROGRAM, not to the definition | `docs/family-architecture.md §0.1` principle III |
| STMT-8 | narrowing the ∀ until the theorem goes through is not available | `docs/family-architecture.md §0.1` principle III |
| STMT-9 | the five model assumptions (discrete, finite, generated, quantified, termination-indexed) | `docs/family-architecture.md §6` |
| STMT-10 | determinism quantifies over the TRACE, so it moves with the trace type | `docs/family-architecture.md §6` |
| STMT-11 | every determinism/agreement claim is OBSERVATION-INDEXED | `docs/family-architecture.md §6`; cookbook §1 |
| STMT-12 | THE ANTI-TAUTOLOGY RULE — determinism is a premise or a per-design theorem | `docs/family-architecture.md §6`; cookbook §1 |
| STMT-13 | the permitted set is a per-site datum the tier carries | `docs/family-architecture.md §5.1` |
| STMT-14 | FAMILY LAW — one `Except`/`throw` pattern, every tier | `docs/family-architecture.md §3.4` |
| STMT-15 | `ρ` is what the program can talk about; `Halt` is what only the model can say | `docs/family-architecture.md §3.4` |
| STMT-16 | no tier-local outcome types going forward | `docs/family-architecture.md §3.4` |
| STMT-17 | refusal stays in `Halt`, with a STRUCTURED PAYLOAD | `docs/family-architecture.md §3.4` (the `unsupported` ruling) |
| STMT-18 | the payload is never an observable | `docs/family-architecture.md §3.4` |
| STMT-19 | the uncatchability invariant is TYPE-level, never lemma-level | `docs/family-architecture.md §3.4` |
| STMT-20 | the monad layer ORDER is load-bearing | `docs/family-architecture.md §3.4` |
| STMT-21 | adopted by SHAPE, not by spelling | `docs/family-architecture.md §3.4` |
| STMT-22 | THE FIT BOUNDARY — "does this tier HAVE a run?" | `docs/family-architecture.md §3.4.1` |
| STMT-23 | share only what is ALREADY parametric, measured | `docs/family-architecture.md §3.3` |
| STMT-24 | WIDTH-PARAMETRICITY IS A REQUIREMENT, not a description | `docs/family-architecture.md §3.5.1` |
| STMT-25 | widths are INSTANCES, never separate definitions | `docs/family-architecture.md §3.5.1` clause (1) |
| STMT-26 | every layer-2 theorem stated over the general format | `docs/family-architecture.md §3.5.1` clause (2) |
| STMT-27 | build over the general format, never over a fixed-width type | `docs/family-architecture.md §3.5.1` clause (3) |
| STMT-28 | where core forces a fixed width, FLAG it — never absorb it | `docs/family-architecture.md §3.5.1` clause (3) |
| STMT-29 | the flagship theorem factors through a shared vertex | `docs/family-architecture.md §3.5.2` |
| STMT-30 | the unspecified residue routes to ∀-parameter / profile / REFUSE(environment) | `docs/family-architecture.md §3.5.4` |
| STMT-31 | the schedule is an explicit parameter; the ∀ lives at theorem level | `docs/family-architecture.md §3.6` piece (1) |
| STMT-32 | the monad carries one process's step; `W` carries the concurrency | `docs/family-architecture.md §3.6 (1a)` |
| STMT-33 | the counterexample is FIRST-CLASS — a finite schedule replayed by `#guard` | `docs/family-architecture.md §3.6` piece (2); cookbook §3 |
| STMT-34 | the DRF-SC fence is the standard's own clause, cited not invented | `docs/family-architecture.md §3.6` piece (3) |
| STMT-35 | a racy program is a MEMBERSHIP site, not a refusal | `docs/family-architecture.md §3.6` |
| STMT-36 | halt-with-race-report is always in the permitted set | `docs/family-architecture.md §3.6` |
| STMT-37 | a lane may narrow the family span, never redeclare it at another shape | `docs/family-architecture.md §3.7` |
| STMT-38 | the four-constructor outcome covenant | `docs/family-architecture.md §3.2` item 1 |
| STMT-39 | the ∃-fuel threshold form, and `fuelMono` | `docs/family-architecture.md §3.2` item 2; cookbook §5, §10 |
| STMT-40 | READ THE MODE OUT OF THE ARTEFACT, never out of an ambient setting | `docs/family-architecture.md §3.2` item 5 |
| STMT-41 | the three envelope edges: schema version, top module, source-path spelling | `docs/family-architecture.md §3.2` item 5 |
| STMT-42 | the batch protocol — one runner, one line per job, a `runner-error` row | `docs/family-architecture.md §3.2` item 6 |
| STMT-43 | exit-code convention 0/1/3/4/5 — 3 and 4 are never agreement | `docs/family-architecture.md §3.2` item 7 |
| STMT-44 | effects as world data; inputs as traces with a loud underrun | `docs/family-architecture.md §3.2` item 8 |
| STMT-45 | "core only, no packages" is a PER-TIER discipline, not a repo fact | `docs/family-architecture.md §3.2` item 4 |
| STMT-46 | three authorities — a tier declares which it is | `docs/family-architecture.md §4.1` |
| STMT-47 | SPEC target / IMPLEMENTATION oracle / SUITE OWNER verdict authority | `docs/family-architecture.md §4.2` |
| STMT-48 | a divergence between any two is a FINDING, and blocks none of them | `docs/family-architecture.md §4.2` |
| STMT-49 | where the spec is silent or ambiguous: REFUSE | `docs/family-architecture.md §4.2` |
| STMT-50 | the behavior-classes → refusal-taxonomy table before any semantics | `docs/family-architecture.md §4.3` |
| STMT-51 | a near-empty `undefined` bucket is GATED, not hoped for | `docs/family-architecture.md §4.3` |
| STMT-52 | the ∀/∃ flip distinguishes order-dependence from a membership site | `docs/family-architecture.md §4.3`; cookbook §19 |
| STMT-53 | edition token — a valid Lean identifier | `docs/family-architecture.md §1.1` law 1 |
| STMT-54 | edition token — self-identifying out of context | `docs/family-architecture.md §1.1` law 2 |
| STMT-55 | edition token — an edition a reader can hold, never a point release | `docs/family-architecture.md §1.1` law 3 |
| STMT-56 | edition token — it never renames | `docs/family-architecture.md §1.1` law 4 |
| STMT-57 | `language_version` is first-class; the ingester REFUSES a mismatch | `docs/family-architecture.md §1.5` |
| STMT-58 | `frontend.version` is the FRONTEND's FAMILY, never a point release | `docs/family-architecture.md §1.5` |
| STMT-59 | THIN SIBLINGS OVER A THICK SHARED TRUNK | `docs/family-architecture.md §2.4` — gate: `tools/editions.sh` |
| STMT-60 | no definition takes a version parameter | `docs/family-architecture.md §2.4` — gate: `tools/editions.sh` |
| STMT-61 | theorems prove ONCE on the trunk | `docs/family-architecture.md §2.4` clause (2) — gate: `tools/editions.sh` reports the sibling/trunk theorem split; a duplicate finder cannot fire while the trunk holds 0 |
| STMT-62 | THE ONE HONEST FORK — an arity change forks type and consumers | `docs/family-architecture.md §2.4` clause (3) |
| STMT-63 | the edition parameter's granularity is language-decided | `docs/family-architecture.md §2.4` clause (4) |
| STMT-64 | ONE extractor per language, never per edition | `docs/family-architecture.md §1.6` |
| STMT-65 | SEPARATE THE SPEC HALF FROM THE INTERPRETER HALF, from theorem one | `docs/family-architecture.md §8` step 9; cookbook §6 |
| STMT-66 | DECIDE FUEL'S FATE before writing the interpreter | `docs/family-architecture.md §8` step 7 |
| STMT-67 | a second semantics owes an adequacy theorem | `docs/family-architecture.md §8.5` (with §3.4 clause b) |
| STMT-68 | typed surface in statements — never `Val`, fuel, or the AST | `AGENTS.md § House rules`, "Typed surface in statements" |
| STMT-69 | the strengthened partial-correctness form is the only admissible one | `AGENTS.md § Failure modes` closing; prohibition at `§ Never` bullet 6; cookbook §12 |
| STMT-70 | threshold form for every spliced run | `AGENTS.md § House rules`, "Threshold form for every spliced run" |
| STMT-71 | `@[spec]` only on Hoare-triple / simp shapes | `AGENTS.md § House rules` |
| STMT-72 | the four judgment forms | `AGENTS.md § Judgment vocabulary`, the table |
| STMT-73 | never prettify `//` to `/` without a sign hypothesis | `AGENTS.md § Judgment vocabulary`, elaboration notes |
| STMT-74 | statements are NORMATIVE — reproduce them exactly | `AGENTS.md § Failure modes`, "Statement discipline when re-proving"; cookbook §21 |
| STMT-75 | TIME IS AN INPUT — the clock is a finite trace, quantified | `AGENTS.md § Orientation` item 3, PASS 6 |
| STMT-76 | the world is a free variable, stronger than a pinned initial world | `AGENTS.md § Orientation` item 3; cookbook §9, §11 |
| STMT-77 | THE EXIT LAW — fuel as a PARAMETER, worlds THREADED | `docs/backlog.md §L24`; cookbook §5 |
| STMT-78 | name the world, do not hide it in an `∃` | `docs/backlog.md §L26`; cookbook §9 |
| STMT-79 | specs must be OUTPUT-DETERMINED | `docs/backlog.md §L61`; `docs/mvcgen-pilot.md §3.3`; cookbook §7 |
| STMT-80 | `Triple` does not frame the state | `docs/backlog.md §L61`; `docs/mvcgen-pilot.md §3.3`; cookbook §16 |
| STMT-81 | a membership site must never be spelled with `⊕` | `docs/backlog/research.md 2026-08-22-research-1`; `docs/proof-framework-research.md §5.4`; cookbook §2 |
| STMT-82 | DIVERGE-with-witness is a LISBON triple, not an Incorrectness one | `docs/proof-framework-research.md §5.3`; cookbook §3 |
| STMT-83 | refinement is ∀∃, and a function-valued projection kills the witness obligations | `docs/proof-framework-research.md §7.3`, §6.4; cookbook §18 |
| STMT-84 | never write a bare polymorphic `throw` — named refusal primitives | `docs/mvcgen-pilot.md §1.4`; cookbook §8 |
| STMT-85 | altitude lemmas persist, and `@[spec]` is their registry | `docs/backlog.md §L61`, origin §L17 |
| STMT-86 | conclude in the residue's own spelling, with the computed heap | `docs/backlog.md §L61`, origin §L20; cookbook §14 |
| STMT-87 | a conditional is a premise until a `rfl` retires it | `docs/backlog.md §L45` |
| STMT-88 | no engine, no fixture, no depth means the general layer | `docs/backlog.md §L65` |
| STMT-89 | if the TYPE enumerated the kinds, the type would BE the vocabulary claim | `docs/backlog.md §L86` |
| STMT-90 | `Deterministic` is design-indexed — discharged or refuted, never assumed | `docs/backlog/sv.md 2026-08-22-sv-1` |
| STMT-91 | THROW vs REFUSE kept straight; only the unmodeled refuses | `docs/backlog/es.md 2026-08-22-es-1` |
| STMT-92 | a rung moves a refusal down the stack and makes it narrower | `docs/backlog/es.md 2026-08-22-es-1` |
| STMT-93 | TIMEOUT is never conflated with REFUSE | `docs/backlog/c.md 2026-08-22-c-1` |
| STMT-94 | a gate states what it cannot emit, and why | `docs/backlog/ada.md 2026-08-22-ada-1` |
| STMT-95 | a short-circuit's out-world goes in the HYPOTHESIS, not the conclusion | `docs/c-semantics-design.md §4.3`; `docs/backlog.md §L83`; cookbook §13 |
| STMT-96 | `FoldInv` carries the round obligation only — never both boundary directions | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-4`; cookbook §4 |
| STMT-97 | a threshold judgment's inverses are THEOREMS, not `cases` | `docs/backlog.md §L58`; cookbook §10 |
| STMT-98 | a premise is not paid until something DISCHARGES it | `docs/backlog.md §L25` standing-law item 3; cookbook §21 |
| STMT-99 | an existential judgment is earned across theorems, not within one | `docs/backlog.md §L38`; cookbook §15 |
| STMT-100 | a definition a LEMMA cannot state about is a fidelity gap | `docs/backlog.md §L88`, sharper form of §L82; cookbook §17 |
| STMT-101 | ONE EXECUTION, TWO PROJECTIONS — an outcome and its class cannot drift | `docs/family-architecture.md §5.2` |
| STMT-102 | the refusal-class field's PRESENCE is a theorem; absence means it did not refuse | `docs/family-architecture.md §5.2` |
| STMT-103 | a stepper RECOVERS the walker as its non-suspending case — never a parallel implementation | `docs/family-architecture.md §3.6` (1a) |
| STMT-104 | two executable implementations cost a parity APPARATUS; one plus a special case costs a THEOREM | `docs/family-architecture.md §3.6` (1a) |
| STMT-105 | a datatype run costs CONGRUENCES; a transformer stack costs an OPENER | cookbook §22; `docs/family-architecture.md §3.4` |
| STMT-106 | write the PROVED/CHECKED boundary before either half can close | `docs/family-architecture.md §5.4a`; cookbook §12 |
| STMT-107 | a mis-bucketed refusal is MIS-SCHEDULED — the class determines who owes the work | `docs/family-architecture.md §5.2` |
| STMT-108 | when a fix moves a boundary, guard BOTH sides — a paired guard | `docs/family-architecture.md §5.2` |
| STMT-109 | choose the acceptance case that can FAIL under the wrong model, and take it NOW | `docs/family-architecture.md §5.6` |
| STMT-110 | a guarantee inside an IMPLICATION guarantees nothing when the antecedent fails | `docs/family-architecture.md §8` (the polarity pair) |
| STMT-111 | THE HONEST SIGNATURE — omit a redundant hypothesis; never accept-and-ignore | `docs/family-architecture.md §8` |
| STMT-112 | a snapshot is WRONG BY ANSWERING, not by answering wrongly | `docs/family-architecture.md §5.1` |
| STMT-113 | a nonstandard generated relation is not ORPHANED — price the BRIDGE (the crossing IFF) first | `docs/family-architecture.md §8` item 11 |
| STMT-114 | A RESOLUTION CAN BE WRONG, NOT MERELY MISSING — every resolution rung owes a shadowing row | `docs/family-architecture.md §5.2` |
| STMT-115 | a correctness gate bounds BOTH error directions — over-refusing is a failure mode | `docs/family-architecture.md §5.2` |
| STMT-116 | a FALSE PREMISE does not weaken a theorem — it VACATES it, and a vacated theorem PASSES | `docs/family-architecture.md §5.3` |
| STMT-117 | an `op_correct` statement mentions NO algorithm; the tie rule is a PARAMETER | cookbook §24 |
| STMT-118 | an OMISSION is stated in the file, never silently completed | cookbook §24 |
| STMT-119 | convergence on the PARAMETER plus divergence on the INSTANTIATION is a correct parameterization | `docs/family-architecture.md §5.2` |
| STMT-120 | a goal theorem that only appears as the LAST LINE OF PLANS will never be written | `docs/family-architecture.md §9.0` |
| STMT-121 | no part of a flagship's difficulty lives in its ASSEMBLY — a hard assembly is an obligation list that lies about its length | `docs/family-architecture.md §9.0` |
| STMT-122 | a hypothesis's RATIONALE is checkable only as a row: drop it, and a specific named thing must happen | `docs/family-architecture.md §5.3` |
| STMT-123 | a hypothesis can change LOUD → QUIET while statement and theorem hold still — observability is not measured | `docs/family-architecture.md §5.3` |
| STMT-124 | hypothesis KINDS — tier / modelling / bridging — determine the retirement move | `docs/family-architecture.md §5.3` |
| STMT-125 | a FALLBACK arm returning `true` converts a failing run into a passing row — vacuity by INVERSION | `docs/family-architecture.md §5.3` |
| STMT-126 | the ATTESTING INSTRUMENT constrains how a definition must be written (`partial` blocks `#guard`) | `docs/family-architecture.md §7.1a` |
| STMT-127 | "the RUN is correct" and "the CERTIFICATE is correct" are different claims — only the second is what a green IS | `docs/family-architecture.md §5.4a-i` |
| STMT-128 | a lemma that CANNOT FAIL is not a lemma — symmetry is a reason to LOOK, never to KEEP | `docs/family-architecture.md §5.3` |
| STMT-129 | a behaviour the language DEFINES as a failure is a value of the outcome type, never a tier gap | `docs/family-architecture.md §5.2` |

## C. PROOF-ENGINEERING LAWS — how proofs are built and kept

| id | hook | home |
| --- | --- | --- |
| PROOF-1 | never `sorry` or `admit` — anywhere, ever | `AGENTS.md § Never` bullet 1 |
| PROOF-2 | decide-class tactics discouraged, not banned — receipt at the use site | `AGENTS.md § Never` bullet 2 |
| PROOF-3 | a file whose header contracts their absence stays true or stops saying so | `AGENTS.md § Never` bullet 2 |
| PROOF-4 | never edit generated files — edit the source, re-extract | `AGENTS.md § Never` bullet 3 |
| PROOF-5 | never weaken, strengthen or "simplify" a recorded statement | `AGENTS.md § Never` bullet 4 |
| PROOF-6 | never whitelist a mismatch into silence | `AGENTS.md § Never` bullet 5 |
| PROOF-7 | a non-whitelisted mismatch is an interpreter bug: report it | `AGENTS.md § Never` bullet 5 |
| PROOF-8 | never leave `lake build` red, and never `git commit` | `AGENTS.md § Never` bullet 7 |
| PROOF-9 | never touch another lane's files or the spine as a side effect | `AGENTS.md § Never` bullet 8 |
| PROOF-10 | induction on math variables, never on fuel | `AGENTS.md § House rules` |
| PROOF-11 | non-vacuity FIRST — a `#py_check` before any theorem | `AGENTS.md § House rules`; restated `§ The workflow` |
| PROOF-12 | `#print axioms` of every `@[spec]` theorem shows only the three axioms | `AGENTS.md § House rules` |
| PROOF-13 | `py_simp` freezes recursion points | `AGENTS.md § House rules` |
| PROOF-14 | kernel-reducibility is a tier constraint | `AGENTS.md § House rules` |
| PROOF-15 | the three-file layout; ALL real proofs in `proof.lean` | `AGENTS.md § Orientation` item 4 |
| PROOF-16 | statement duplication is typechecked by `:= by proofs` | `AGENTS.md § Orientation` item 4 |
| PROOF-17 | do not "fix" a twin mismatch by proving in the spec file | `AGENTS.md § Failure modes` |
| PROOF-18 | the differential must exit 0 before proving a new function's spec | `AGENTS.md § The workflow` |
| PROOF-19 | validated against CPython, not against your reading of the docs | `AGENTS.md § The workflow` |
| PROOF-20 | fix the doc, never the tree | `AGENTS.md § The workflow` |
| PROOF-21 | the triad — build, then `docs_check`, then the differential | `AGENTS.md § The workflow`; `tools/triad.sh` |
| PROOF-22 | the goal-shape → tactic table IS the tactic-choice law | `AGENTS.md § GOAL-SHAPE → TACTIC` |
| PROOF-23 | a recursive function means induction on the math argument | `AGENTS.md § GOAL-SHAPE → TACTIC` row 8 |
| PROOF-24 | `grind` e-matches ATOMIC facts — never re-conjoin split invariants | `AGENTS.md § Failure modes`; cookbook §20 |
| PROOF-25 | `omega` ingests only unbranded `Int`/`Nat`-headed comparisons | `AGENTS.md § Failure modes`; `tools/diagnose.sh` `omega-no-constraints` |
| PROOF-26 | never hand-count interpreter steps — threshold forms and generous slack | `AGENTS.md § Failure modes` |
| PROOF-27 | doc comments attach to declarations only | `AGENTS.md § Failure modes`; `docs/backlog.md §L66`, §L82 |
| PROOF-28 | `exact … (by …)` commits inside `first` — all-tactic attempts first | `AGENTS.md § Failure modes` |
| PROOF-29 | any unclosed obligation is appended, never dropped | `AGENTS.md § GOAL-SHAPE → TACTIC`, closing |
| PROOF-30 | never add a hypothesis to make a proof pass — that is a semantics finding | `AGENTS.md § Failure modes`, "Statement discipline when re-proving" |
| PROOF-31 | never delete a hypothesis that turns out unneeded — record the fact | `AGENTS.md § Failure modes`, same paragraph |
| PROOF-32 | SIMP DOCTRINE — dispatchers in, workers deliberately out | `AGENTS.md § Orientation` item 3 |
| PROOF-33 | `cases` never abstracts hypotheses — use `split at h` | `AGENTS.md § Orientation` item 3 |
| PROOF-34 | explicit `termination_by structural fuel` on every mutual member | `AGENTS.md § Orientation` item 3 |
| PROOF-35 | conjuncts appended LAST, so existing projection paths survive | `AGENTS.md § Orientation` item 3 |
| PROOF-36 | `cbv` is for the interpreter's residue, and its bound is `maxRecDepth` | `docs/family-architecture.md §5.6`; `docs/lean-structures-census.md §1.3` |
| PROOF-37 | BUG BEFORE REFACTOR | `docs/family-architecture.md §9.1` |
| PROOF-38 | CONSOLIDATION BY TOUCH, never big-bang; byte-identical across the move | `docs/family-architecture.md §9.2` |
| PROOF-39 | port the SUCCESSOR; keep the predecessor as the record of what it fixed | `docs/family-architecture.md §9.2` |
| PROOF-40 | the migration must never cost more than the defect it removes | `docs/family-architecture.md §9.2` — ungateable: cost is a judgement over lane-time and build invalidation; the only mechanical proxy is the half never in dispute |
| PROOF-41 | the law gets ENFORCED in the shared helper, not remembered | `docs/family-architecture.md §9.4` |
| PROOF-42 | THE LAZINESS LAW — every field takes its successor level inside its lambda | `docs/family-architecture.md §3.6 (1a)`; from `docs/backlog.md §L84` |
| PROOF-43 | defunctionalize — the continuation becomes DATA in the world | `docs/family-architecture.md §3.6 (1a)` |
| PROOF-44 | `show` for a residue's spelling — `rw` is syntactic | `docs/backlog.md §L41` |
| PROOF-45 | `#guard` is a WEAKER oracle than `rfl` | `docs/backlog.md §L82`, sharpened §L88 |
| PROOF-46 | a lint's first run accusing a passing file is the LINT being wrong | `docs/backlog.md §L82` |
| PROOF-47 | a gate that cannot fail is decoration — the self-test breaks each edge | `docs/backlog.md §L75` |
| PROOF-48 | NEVER HIDE ERRORS — no except-and-pass, no silent degrade | `docs/backlog.md` §L60, §L67, §L76 (named law, no single numbered home) |
| PROOF-49 | model-matches-code — the model and the code land together | `docs/backlog.md §L61`, instance §L3; `AGENTS.md § Orientation` item 3 |
| PROOF-50 | refuse rather than invent against a model that cannot express the notion | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-4` |
| PROOF-51 | a skip arm pins existentially; an ADD arm must SPELL it | `docs/backlog.md §L28` finding 1 |
| PROOF-52 | run the activity check BEFORE choosing a target | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-2` |
| PROOF-53 | the dependency graph is SEMANTIC, not nominal — name rules run first | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-2` |
| PROOF-54 | strip comments and strings before counting `sorry` | `docs/backlog/wasm.md 2026-08-22-wasm-1`; `harness/wasm_sorry_census.py` |
| PROOF-55 | "0 sorry" can distinguish the emission MODE, not the progress | `docs/backlog/wasm.md 2026-08-22-wasm-1` |
| PROOF-56 | open the monad stack ONCE, where it is defined — the tell is unfolding `Functor.map` | cookbook §22 |
| PROOF-57 | the covenant made mechanical — `run_bind`'s arms ARE the layer order | `docs/family-architecture.md §3.4` |
| PROOF-58 | never touch the SCRUTINEE — rewrite the whole bind from a head equation | cookbook §23 |
| PROOF-59 | `dsimp only` for the iota step; `simp only` will not reduce a literal-constructor match | cookbook §23 |

## D. BUILD + OPS AMENDMENTS — the lock protocol and its register

**§7.1a is the protocol's ONLY durable home**, and `tools/triad.sh` is the
canonical implementation — *the doc DESCRIBES, this script IS.* Amendment
numbers below are the register's own.

| id | hook | home |
| --- | --- | --- |
| OPS-1 | base 1 — ONE full build at a time, machine-wide (`mkdir` spinlock) | `docs/family-architecture.md §7.1` rule 1; `tools/triad.sh` |
| OPS-2 | never hold the lock while thinking or editing | `docs/family-architecture.md §7.1` rule 1 |
| OPS-3 | A2 — release is `rm -rf` with a CHECKED status | `docs/family-architecture.md §7.1` rule 2 / §7.1a row 2; `tools/triad.sh` |
| OPS-4 | `-j4` is an argument error on this lake — throttle by environment | `docs/family-architecture.md §7.1` rule 2; `tools/diagnose.sh` `unknown-option` |
| OPS-5 | exit 143 (and 137) is a RESOURCE KILL, not a build failure | `docs/family-architecture.md §7.1` rule 2; `tools/triad.sh`; `tools/diagnose.sh` `resource-kill` |
| OPS-6 | the 143/137 retry — re-run once, never record a red | `docs/family-architecture.md §7.1a` (OBSERVED WORKING); `tools/triad.sh` |
| OPS-7 | base 3 — scratch loops without the lock, under `nice -n 19` | `docs/family-architecture.md §7.1` rule 3 |
| OPS-8 | the scratch exemption is a property of the CLONE, not of the file | `docs/family-architecture.md §7.1` rule 3 |
| OPS-9 | base 4 — one triad per landing, never per edit | `docs/family-architecture.md §7.1` rule 4; `tools/triad.sh` |
| OPS-10 | stage, then build; no speculative builds | `docs/family-architecture.md §7.1` rule 4 |
| OPS-11 | base 5 — a stale lock cleared only after verifying by parentage and cwd | `docs/family-architecture.md §7.1` rule 5 |
| OPS-12 | THE TWO-PART STALENESS TEST, never simplified to pid-only | `docs/family-architecture.md §7.1` rule 5; `tools/triad.sh` |
| OPS-13 | a lane's death does not imply its build's death | `docs/family-architecture.md §7.1` rule 5 |
| OPS-14 | a broken liveness check falls FORWARD, into reclaiming a live lock | `docs/family-architecture.md §7.1` rule 5 |
| OPS-15 | base 6 — never kill another lane's processes; kills by PARENTAGE only | `docs/family-architecture.md §7.1` rule 6; `tools/triad.sh` |
| OPS-16 | the amendment register is the protocol's ONLY durable home | `docs/family-architecture.md §7.1a` |
| OPS-17 | anything a lane must obey belongs in a git-tracked file | `docs/family-architecture.md §7.1a` |
| OPS-18 | amendment 1 — LOST, no text recovered from any durable source | `docs/family-architecture.md §7.1a` register row 1 |
| OPS-19 | amendment 3 — LOST, attribution survives, text does not | `docs/family-architecture.md §7.1a` register row 3 |
| OPS-20 | A4 — the owner file is written ONCE, under `set -C` | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-21 | owner is a HINT; the process tree is the truth | `docs/family-architecture.md §7.1a` amendment 4 |
| OPS-22 | A5 — the owner file is exactly `<lane> <pid>`, pid LAST | `docs/family-architecture.md §7.1a` row 5; `tools/triad.sh` |
| OPS-23 | A7 — the release trap is OWNERSHIP-CHECKED | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-24 | "LOCK NOT MINE — left alone" is A7 firing, not a failure | `docs/family-architecture.md §7.1a` OBSERVED WORKING |
| OPS-25 | A8 — a staleness verdict comes from ONE atomic re-read before the removal | `docs/family-architecture.md §7.1a` row 8; `tools/triad.sh` |
| OPS-26 | A9 — a FIFO TICKET QUEUE, because the spinlock starves | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-27 | only the OLDEST ticket attempts the `mkdir` | `docs/family-architecture.md §7.1a` amendment 9 |
| OPS-28 | tickets are `<epoch>-<pid>-<lane>`, reaped by pid liveness | `docs/family-architecture.md §7.1a` amendment 9 |
| OPS-29 | refuse rather than enqueue an unsortable ticket | `tools/triad.sh` (ticket timestamps); `docs/duplication-audit.md §2.4` |
| OPS-30 | A10 — the owner pid must SPAN THE TENURE, never a child stage's | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-31 | A11 — the lock covers ALL Lean execution, not just `lake build` | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-32 | `LEAN_NUM_THREADS=2`, `nice -n 19`, a 3 GB RSS line over OWN descendants | `docs/family-architecture.md §7.1a` amendment 11; `tools/triad.sh` |
| OPS-33 | Thomas's own processes have ABSOLUTE priority | `docs/family-architecture.md §7.1a` amendment 11 |
| OPS-34 | A12 — traps kill descendants RECURSIVELY; never bare-kill a wrapper | `docs/family-architecture.md §7.1a`; `tools/triad.sh` |
| OPS-35 | `pkill -P` misses grandchildren — walk `ps -eo pid,ppid` as a BFS | `docs/family-architecture.md §7.1a` amendment 12; `tools/triad.sh` |
| OPS-36 | `--lane` rejects hyphens, because A9's ticket format field-parses | `docs/family-architecture.md §7.1a`, operational note; `tools/triad.sh` |
| OPS-37 | `tools/triad.sh` is the canonical wrapper; private scripts ran 38% violations | `docs/family-architecture.md §7.1a`; `docs/duplication-audit.md §2.2` |
| OPS-38 | a missing amendment in a script is a DIFF | `docs/family-architecture.md §7.1a`; `docs/duplication-audit.md §2.3` |
| OPS-39 | the doc DESCRIBES, this script IS | `tools/triad.sh` header |
| OPS-40 | an amendment becomes a commit, and every lane gets it by rebase | `tools/triad.sh` header |
| OPS-41 | assert success POSITIVELY — grep for `Build completed successfully` | `docs/family-architecture.md §7.1a`; `tools/triad.sh`; `tools/diagnose.sh` `build-did-not-happen` |
| OPS-42 | `--classify` — docs / tier / spine; the tenure follows the LEAN | `tools/triad.sh`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| OPS-43 | the classification is a FLOOR, never a ceiling | `tools/triad.sh`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| OPS-44 | anything UNRECOGNIZED escalates and is NAMED, never absorbed | `tools/triad.sh`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| OPS-45 | a scoped green PRINTS its coverage statement beside the verdict | `tools/triad.sh`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| OPS-46 | less scope, ZERO invention — never run Lean to decide a target's spelling | `docs/backlog/qol.md 2026-08-22-qol-1` — gate: `tools/triad.sh` |
| OPS-47 | `--self-test` runs NO Lean; `--classify-only` takes no tenure | `tools/triad.sh` usage |
| OPS-48 | lock and queue paths overridable for sandboxing; a live run uses the real ones | `tools/triad.sh` header |
| OPS-49 | the header IS the usage text | `tools/triad.sh` |
| OPS-50 | SIGKILL a superseded runner, and delete the file in the same breath | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-5` |
| OPS-51 | reading the fix is not the same as disarming the thing it fixes | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-5` |
| OPS-52 | an amendment takes effect when the last script predating it is DEAD | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-5` |
| OPS-53 | release must RE-READ ownership, never infer it from history | `docs/backlog/c.md 2026-08-22-c-1` |
| OPS-54 | the 3 GB per-process line can kill correct builds — raise it deliberately | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-5` |
| OPS-55 | `maybe`: present ⇒ run, absent ⇒ SKIP, reported, never silently omitted | `docs/family-architecture.md §3.2` item 9; `tools/ci.sh` |
| OPS-56 | the summary always states what was and was not verified | `tools/ci.sh` header |
| OPS-57 | an unlicensed binary is infrastructure absence, not disagreement | `tools/ci.sh` |
| OPS-58 | the MARKER CONVENTION is normative; illustrative blocks skipped AND counted | `tools/docs_check.py` module docstring |
| OPS-59 | the workspace ladder: CoW now, shared packages next, shared build REJECTED | `docs/family-architecture.md §9.6` |
| OPS-60 | the LIGHT keeper-tick checks: lock owner, queue, concurrent builds by parentage | `docs/family-architecture.md §9.7` |
| OPS-61 | a pre-push gate is PRICED and deliberately not proposed | `docs/duplication-audit.md §2.4` |
| OPS-62 | adoption is per-lane, on dispatch | `tools/triad.sh` header; `docs/duplication-audit.md §2.4` |
| OPS-63 | refuse to start a build inside a rebase/merge/cherry-pick | `tools/triad.sh` (A6 precondition); `docs/duplication-audit.md §2.4` |
| OPS-64 | the register can sit one amendment behind its own birth | `docs/duplication-audit.md §2.3` |
| OPS-65 | the rule applies to YOUR OWN runners first — the author's process predates the fix | `docs/family-architecture.md §7.1a` A16.2 |
| OPS-66 | an unseeded clone is one accident away from a full Mathlib build | `docs/family-architecture.md §7.1a` A13 |
| OPS-67 | a re-entry guard lives in something INHERITED, never something PASSED | `docs/family-architecture.md §7.1a` A11 |
| OPS-68 | a step that can start Lean names the HOST it may start it on | `docs/family-architecture.md §7.1a` A11; `tools/ci.sh` |
| OPS-69 | an announcement is GENERATED BY the code it announces, or it is prose about a plan | `docs/family-architecture.md §7.2` |
| OPS-70 | NOT COMPILED IS NOT NOT RUN — A11 covers a file no target builds | `docs/family-architecture.md §7.1a` A11 |
| OPS-71 | a value-taking flag REFUSES a missing value; it never defaults | `docs/family-architecture.md §5.4b`; `tools/argv.sh` |
| OPS-72 | CLASSIFICATION NARROWS — default-on would make narrowing the default | `docs/family-architecture.md §7.2` |
| OPS-73 | an advisory runs in a SUBSHELL — one that leaked would narrow the build it describes | `docs/family-architecture.md §7.2` |
| OPS-74 | a build log says whose it is; an artifact with no identity is storage, not evidence | `docs/family-architecture.md §7.2` |
| OPS-75 | a stamp added to a measured artifact owes a DIFFERENTIAL — same verdicts with and without | `docs/family-architecture.md §7.2` |
| OPS-76 | A COMMIT CANNOT CONTAIN ITS OWN HASH — each rung's sha lands in the FOLLOWING commit | `docs/family-architecture.md §7.2` |
| OPS-77 | `set_option autoImplicit false` in model files — a required LOUDNESS guard | `docs/family-architecture.md §7.1a` |
| OPS-78 | a guard must hash the object the BUILD reads, never the one beside it (the enqueue stamp hashed the INDEX while `lake` built the WORKING TREE; fixed `22ed755`) | `docs/family-architecture.md §7.2`; `tools/triad.sh` |
| OPS-79 | working within a known-imperfect protocol is DECLARED at enqueue, never relied on silently | `docs/family-architecture.md §7.2` — **SUNSET**: stamp v2 is live; applies only to v1-stamped tickets |
| OPS-80 | accept-and-log tolerance is for tickets IN FLIGHT — a migration's grace window needs a DIRECTION | `docs/family-architecture.md §7.2` |
| OPS-81 | the module system is opt-in per ROOT — unfolding proofs are portable only to legacy roots | `docs/family-architecture.md §7.1a` |
| OPS-82 | a comment describing comment syntax cannot QUOTE it — name the delimiters, never spell them | `docs/family-architecture.md §7.1a` |
| OPS-83 | a tactic dispatching on a goal's HEAD needs a stable head — a `def` unfolding to a binder has none | `docs/family-architecture.md §7.1a` |
| OPS-84 | `with_reducible` per `apply` — each failure is one HEAD COMPARISON, not one unfolding | `docs/family-architecture.md §7.1a` |
| OPS-85 | REPORT-THEN-CONTINUE — proceed to the named next rung; stop only on a ruling, a merge you consume, or a pending verdict | `docs/family-architecture.md §9.0-pre` |
| OPS-86 | commit provenance comes from the ENVIRONMENT, never from a flag someone types | `docs/family-architecture.md §7.2` |

## E. CLONE-IDENTITY RULES — branch, remotes, push, staging

| id | hook | home |
| --- | --- | --- |
| CLONE-1 | A13 — cache seeding is MANDATORY, and it is copy-on-write | `docs/family-architecture.md §7.1a` |
| CLONE-2 | `cp -Rpc` — `-c` clones the blocks, `-p` preserves Lake's timestamps | `docs/family-architecture.md §7.1a` amendment 13 |
| CLONE-3 | seed only from a peer with NO build running and an untorn tree | `docs/family-architecture.md §7.1a` amendment 13 |
| CLONE-4 | THE A13 CAVEAT — seeding takes the peer's BRANCH too | `docs/family-architecture.md §7.1a` |
| CLONE-5 | check `git branch --show-current` immediately after seeding | `docs/family-architecture.md §7.1a` |
| CLONE-6 | push `HEAD:master`, never bare `master` | `docs/family-architecture.md §7.1a` |
| CLONE-7 | seeding inherits the REMOTES too — `origin` may be a stale local bundle | `docs/family-architecture.md §7.1a` |
| CLONE-8 | identity — BRANCH AND REMOTES BOTH — is INHERITED, not chosen | `docs/family-architecture.md §7.1a` |
| CLONE-9 | after seeding run `git remote -v`; compare only against `github/master` | `docs/family-architecture.md §7.1a`; `tools/triad.sh --classify` |
| CLONE-10 | `git rev-list HEAD..origin/master` reading 0 against a bundle is not proof | `docs/family-architecture.md §7.1a`; `tools/diagnose.sh` `seeded-clone-identity` |
| CLONE-11 | fetch-rebase before every push | `docs/family-architecture.md §7.2` |
| CLONE-12 | read your own backlog section at PUSH time, not at draft time | `docs/family-architecture.md §7.2` |
| CLONE-13 | after a rebase touching `.lean`, re-run build and differential before pushing | `docs/family-architecture.md §7.2` |
| CLONE-14 | A6 — never fetch-rebase while a build runs in the same clone | `docs/family-architecture.md §7.2` / §7.1a row 6; `tools/triad.sh` |
| CLONE-15 | the order is `stage → build → rebase`, or `rebase → build` | `docs/family-architecture.md §7.2` |
| CLONE-16 | a red from a torn tree is not evidence of anything | `docs/family-architecture.md §7.2`; `tools/diagnose.sh` `unknown-constant` |
| CLONE-17 | it discharges nothing and convicts nothing — re-run clean | `docs/family-architecture.md §7.2` |
| CLONE-18 | BACKLOG V2 — `docs/backlog/<lane>.md`, appended only by its own lane | `docs/family-architecture.md §9.5` |
| CLONE-19 | ids `YYYY-MM-DD-<lane>-<n>` need no reservation | `docs/family-architecture.md §9.5` |
| CLONE-20 | migration is append-only; every existing `§Lnn` keeps resolving | `docs/family-architecture.md §9.5` |
| CLONE-21 | `docs/backlog.md` becomes a GENERATED index | `docs/family-architecture.md §9.5` |
| CLONE-22 | verify `git remote -v` AND the upstream in a clone you did not create | `docs/backlog.md §L86`; `docs/duplication-audit.md §6.3` |
| CLONE-23 | the branch trap is current state, not folklore | `docs/duplication-audit.md §6.3`; `docs/backlog.md §L89` |
| CLONE-24 | an audit that only confirms is not an audit | `docs/duplication-audit.md §6.3` |
| CLONE-25 | a workspace helper refuses if the peer builds or the tree is torn | `docs/duplication-audit.md §6.5` |
| CLONE-26 | the merge target prints ref, sha AND remote URL; the A13 caveat is loud | `tools/triad.sh --classify`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| CLONE-27 | unstaged `.lean` files the classification did not cover are counted and named | `tools/triad.sh --classify`; `docs/backlog/qol.md 2026-08-22-qol-1` |
| CLONE-28 | local branch, no upstream tracking, no PR, no comment, no contact | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-4` |
| CLONE-29 | "no Lean run, no build, no ticket taken" — the docs-only declaration | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-4`; `docs/duplication-audit.md §7` |
| CLONE-30 | sparse-fetch a foreign corpus read-only, and `df` first (A11) | `docs/backlog/lean-tier.md 2026-08-22-lean-tier-4` |
| CLONE-31 | no private hostnames in tracked files | `docs/family-architecture.md §1.2` (one standing violation flagged there) |
| CLONE-32 | sweep, do not note — a stale artifact is not disarmed by being recorded | `docs/backlog/sunfish-rtrack.md 2026-08-22-sunfish-rtrack-5` |
| CLONE-33 | a lane tag is a bare word, and it replaces the lane's private script | `docs/backlog/es.md 2026-08-22-es-1`; `tools/triad.sh` |

---

## What this index does not do

It does not rank. Every row here is standing law, and a lane that needs to
know which one *bites first* on a given landing should read
`docs/family-architecture.md §9` — the standing strategy — rather than
inferring priority from position in a table.

And it does not close. A law arrives when an incident mints it: append the
row when you append the backlog entry, in the same landing, so the index
never becomes the thing a lane has to remember to update.
