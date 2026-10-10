# C++ canonical metadata: real-artifact pricing

2026-10-09. **Tooling evidence, not declaration-semantic admission.** The
[declaration contract](cpp-declarations.md) and
[optional probe](../extractors/cpp/README.md) remain separate from admitted
`cpp-0.1` extraction and Lean ingestion. Every C++ execution still refuses
`rung-0:no-executable-semantics`. No prototype correctness theorem is supplied.

## Pinned original inputs and cost

The unchanged TinyXML2 `321ea883` and nlohmann/json `9cca280a` translation inputs
are those of the hardened translation census, including the original
include-only json TU. Clang/LLVM 21.1.8, exact subject flags, working directory,
environment, source/dependency hashes and plugin provenance are retained in
external receipts. The plugin source remains `a8713810…01b4ec`; the admitted
extractor remains `14948926…fb8`. This item changes neither implementation.

| Probe input | Runs / exits | Output bytes per run | Wall seconds | Child maximum RSS KiB |
| --- | --- | --- | --- | --- |
| TinyXML2 | 2 / both 0 | 31,162,165 | 0.264 / 0.314 | 130,560 / 619,768 |
| json | 2 / both 0 | 1,791,432,144 | 10.582 / 10.492 | 1,319,944 / 1,318,716 |

Both json runs have empty diagnostics. All **350 actual dependency paths and
their hashes** match admission and remain unchanged before/after probing;
TinyXML2's corresponding count is 104. Compiler, plugin, libraries and the
original json envelope are also unchanged. The json measurement parent reads
only the small admission-summary metadata and hashes the 530,684,762-byte
original envelope incrementally; it never loads that AST merely to recover
the compiler command. Its compiler RSS is therefore not inflated by inheriting
a parent-held parsed envelope.

The json frontend bounds are 180 seconds, 2 GiB output and a 16 GiB per-process
address/RSS envelope. Neither run triggers a bound. Formatting and the metadata
ledger account for additional output; bytes are not admitted-function counts.
Earlier extraction timings include additional envelope/dependency work and
are not a directly comparable frontend benchmark.

## Declaration graph census

Both fresh json probes agree on these counts. Positions include every nested
declaration-shaped dictionary, including reference descriptions; they are not
a count of declarations introduced by source code.

| Measure | XML | json |
| --- | ---: | ---: |
| Raw declaration-shaped positions / IDs | 7,031 / 4,512 | 463,333 / 162,667 |
| Ledger rows / IDs | 4,527 / 4,527 | 164,810 / 161,120 |
| Repeated ledger rows beyond unique IDs | 0 | 3,690 |
| Raw IDs without metadata | 2 | 3,765 |
| Metadata IDs without raw witnesses | 17 | 2,218 |
| Fully witnessed source nodes agreeing across runs | 4,509 | 158,586 |
| Raw source nodes refusing complete relationship alignment | 3 | 4,081 |

The repeated json ledger rows have **no conflicting present evidence**; joined
kinds also agree. Retaining and checking repetitions is necessary, not a reason
to select the first/last row. All **8,668 injected names** are self-canonical
and designate separate witnessed represented-class targets. There are 61,396
dependent contexts; all 161,120 owning-module observations are null. These
fields are API telemetry, not complete dependence/module admission checks.

The raw metadata gaps comprise 3,636 `ImplicitConceptSpecializationDecl`,
127 `ParmVarDecl`, and two builtin `CXXRecordDecl` IDs. Metadata-only IDs comprise
1,344 template-type parameters, 360 requires-expression bodies, 350 function
parameters, 149 using shadows, 11 non-type template parameters and four
lifetime-extended temporaries. This is not merely the two builtin omissions
seen in XML. No omission is repaired by name/location matching.

Among unique ledger source nodes, canonical/predecessor targets are absent
from metadata on 11/9 edges; semantic/lexical context targets are absent on
six edges each. Raw occurrence witnesses are missing for canonical targets
on 2,229 edges and for each context family on 345 edges. These are edge-source
counts, not distinct-target counts. Required closure evidence remains unknown.

Fresh path alignment has **zero differing witnessed results**. Its 4,081
source refusals are 3,765 missing source records, 305 missing context witnesses
and 11 missing canonical witnesses; first-refusal categories do not count all
walls independently. The 2,218 metadata-only sources refuse alignment separately.
Aligned nonnull edges agree: canonical 158,891, predecessor 2,940,
semantic/lexical context 158,596 each, original namespace 707, represented
class 8,668. These agreements do not establish general entity identity.

## Earlier analysis cost and limits

The existing complete analyzer was bounded to 600 seconds and 16 GiB virtual
address space with a 2 GiB per-input cap. It **timed out** after 600.361 seconds,
with 6,045,572 KiB child maximum RSS. No completed whole-AST result was produced.

A separate, explicitly narrower census reuses its tested indexing/consensus/
edge-comparison functions, parses one input at a time and retains declaration
paths plus metadata states, not entire ASTs. It completes in 92.196 seconds
with 6,022,956 KiB child maximum RSS under the same bounds. It supplies the
counts and witnessed relationships above. It deliberately omits expensive
AST fingerprints: that run left **whole/nonpointer AST comparison and
equivalence to the original admitted json AST NOT PERFORMED / REFUSED**,
not successful. Matching input hashes and declaration observations could not
fill that gap. The subsequent complete traversal is recorded separately below.

A separately bounded original-declaration inventory completes in 53.830 seconds
with 3,882,480 KiB maximum RSS. Its seven aggregate inventory counts, all 46
declaration-kind counts and complete pointer-independent declaration-path groups
match a fresh probe. That rules out a changed declaration inventory at this
projection; it does not establish equality of statement/type/value payloads or
the whole AST. That projection left the structural-comparison obligation open.
The existing analyzer's 10 assertions, 13 census-fallback assertions and three
projection tests pass; no successful full comparison is manufactured.

The result prices the supplement as feasible to emit but incomplete to trust
generally. Before integration, resolve or explicitly refuse required graph gaps
and define each
supported declaration-family/entity rule. Definition evidence remains
`not-queried` for 52,674 ledger nodes. Template/compiler integer categories,
null owning-module fields and false context-dependence flags never supply
missing semantic classifications. No new runtime cache or consumer-specific
fast path is introduced by this measurement.

## Bounded complete AST traversal

The separate [comparison tool](../extractors/cpp/compare_ast.py) replaces repeated
full-occurrence-group expansion with one deterministic first-path identity
index and a complete, typed, length-framed traversal. Every AST field and every
`id` slot remains observable, so first-path witnesses preserve the complete
identity partition rather than guessing entities by name or location.
Dictionary key order is normalized; array order and all nonpointer payloads
remain significant. Envelope/frontend metadata is not part of this comparison.

A bounded synthetic profile identifies quadratic expansion in the previous
witness encoding: 256/2,048 repeated occurrences emit 0.84/56.57 MB of witness
tokens. The replacement visits 1,545/12,297 tokens in 0.00147/0.01088 seconds.
This diagnoses the scaling defect; it does not attribute every second of the
earlier 600-second timeout to that defect. No cache or special-case path is
introduced.

The first full three-input run completes in 211.139 seconds, but refuses on
42 unknown `targetLabelDeclId` slots per input. Their retained raw handles make
the diagnostic digests differ; those differences are **not AST drift**.
Clang 21.1.8's `JSONNodeDumper::VisitGotoStmt` explicitly emits a label pointer
under that field; `VisitLabelStmt` emits a label pointer under `declId`.
The exact tagged source is retained with SHA-256 `63574c29…fb81ba3`. Adding this
documented pointer role produces `cpp-ast-fingerprint-2`, not a guessed witness
or a relaxed missing-target guard.

The final bounded run compares the original hardened json envelope and both
unchanged probes in **208.429 seconds / 3,902,212 KiB maximum child RSS**, exit 0.
Bounds remain 600 seconds, 16 GiB virtual address space and 2 GiB per input;
inputs parse sequentially, and all before/after input and comparator hashes
match. Each AST visits 44,051,683 tokens, 1,143,278 ID-bearing records, 613,112
distinct IDs and 1,251,951 pointer-shaped slots. These are operational timings
alongside repository validation, not an isolated compiler benchmark.

The original and both probes have matching **complete nonpointer projections**
(`a6bccce2…c531a5`), with zero unrecognized slots. Their diagnostic witnessed
digests also match, but **complete pointer comparison REFUSES** on 775 missing
raw occurrence witnesses per input:

| Pointer field | Unwitnessed positions |
| --- | ---: |
| `temp` | 621 |
| `typeAliasDeclId` | 85 |
| `targetLabelDeclId` | 42 |
| `declId` | 18 |
| `previousDecl` | 9 |

Recognizing label references does not turn them into ID-bearing occurrences.
Neither metadata nor a `LabelStmt.declId` field manufactures the missing
witness. Matching diagnostic hashes cannot certify the absent relationships;
the declaration-ledger closure gaps above also remain unchanged. This is
completed fingerprint computation, not full graph equivalence or semantic
declaration admission. Exit 0 alone is never the agreement predicate.

The small original/probe XML regression completes in 3.275 seconds / 126,428 KiB
RSS under a 90-second wall / 16 GiB address / 64 MiB per-input bound. All three
nonpointer projections match, and all retain the same one unwitnessed
`previousDecl`; full pointer comparison still refuses. Each visits 1,043,384
tokens and 22,936 ID-bearing records / 19,664 IDs. No frontend is rerun.

The 38 focused diagnostic tests cover complete payload changes, scalar types,
key/array order, alias partitions, forward references, conservative refusals,
strict input loading, output aliases and atomic publication. An independent
bounded audit checks 1,369 pairs across 37 small identity-partition/reference
states. These are tooling tests, not correctness proofs about prototypes or
executed C++ applications. SHA-256 projection agreement is evidence, not a Lean
theorem or frontend-conformance claim.

## Scope and receipts

The subsequent [query-local declaration pricing](cpp-declaration-pricing.md)
consumes only the witnessed relationships needed by each candidate query.
Neither its local eligibility nor these complete projection hashes imply
semantic declaration admission or repair the global dangling-pointer refusal.
The later schema 0.2 own-template inventory and bounded repricing are recorded
separately there; they do not reinterpret these schema 0.1 projection receipts.

The prior XML result aligns 4,509 fully witnessed source nodes with zero
differences; three raw nodes and 17 metadata-only sources remain unalignable.
All 80 injected names are self-canonical and retain distinct represented-class
targets. Complete pointer-witnessed AST comparison refuses at its dangling
predecessor, despite matching nonpointer structure and partial hashes.

Receipts are external under `state/ls-cpp/canonical-probe` for XML and
`state/ls-cpp/canonical-json-20261009/{probe,analysis}` for json. They retain
commands, hashes, process measurements, raw dumps, ledger/edge censuses,
occurrence witnesses and refusals. Full/skeletal repetitions remain distinct
positions; fresh-process relationships are never matched by pointer strings.
The complete-comparison receipts are under
`state/ls-cpp/canonical-comparison-20261009/{review,measurement,xml-validation}`;
the final json run is `measurement/labels`. Earlier refused results remain
archived, with separate format/source pins rather than overwritten headlines.

The strict Mox source remains refused by its four recorded extension errors;
this item does not relax its profile or rerun it. Neither admitted corpus
gains a declaration query or runtime verdict. Tooling feasibility, semantic
admission and actual execution remain three separate measurements.
