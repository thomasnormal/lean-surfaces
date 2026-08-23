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
