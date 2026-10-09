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

## Analysis cost and explicit limits

The existing complete analyzer was bounded to 600 seconds and 16 GiB virtual
address space with a 2 GiB per-input cap. It **timed out** after 600.361 seconds,
with 6,045,572 KiB child maximum RSS. No completed whole-AST result was produced.

A separate, explicitly narrower census reuses its tested indexing/consensus/
edge-comparison functions, parses one input at a time and retains declaration
paths plus metadata states, not entire ASTs. It completes in 92.196 seconds
with 6,022,956 KiB child maximum RSS under the same bounds. It supplies the
counts and witnessed relationships above. It deliberately omits expensive
AST fingerprints: **whole/nonpointer AST comparison and equivalence to the
original admitted json AST are NOT PERFORMED / REFUSED**, not successful.
The matching input hashes and declaration observations cannot fill that gap.

A separately bounded original-declaration inventory completes in 53.830 seconds
with 3,882,480 KiB maximum RSS. Its seven aggregate inventory counts, all 46
declaration-kind counts and complete pointer-independent declaration-path groups
match a fresh probe. That rules out a changed declaration inventory at this
projection; it does not establish equality of statement/type/value payloads or
the whole AST. The original/probe structural-comparison obligation remains open.
The existing analyzer's 10 assertions, 13 census-fallback assertions and three
projection tests pass; no successful full comparison is manufactured.

The result prices the supplement as feasible to emit but incomplete to trust
generally. Before integration, complete the bounded original/probe structural
comparison, resolve or explicitly refuse required graph gaps, and define each
supported declaration-family/entity rule. Definition evidence remains
`not-queried` for 52,674 ledger nodes. Template/compiler integer categories,
null owning-module fields and false context-dependence flags never supply
missing semantic classifications. No new runtime cache or consumer-specific
fast path is introduced by this measurement.

## Scope and receipts

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

The strict Mox source remains refused by its four recorded extension errors;
this item does not relax its profile or rerun it. Neither admitted corpus
gains a declaration query or runtime verdict. Tooling feasibility, semantic
admission and actual execution remain three separate measurements.
