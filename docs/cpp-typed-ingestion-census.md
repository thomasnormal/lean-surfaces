# C++ typed declaration-evidence census

2026-10-10. **Frontend tooling evidence only.** This receipt separates runtime
typed parsing, literal compilation and independent aggregate auditing. It
exercises the existing evidence bridges in `LeanModels/Cpp/Identity.lean`.
It does not establish entities, ISO scope, linkage, ODR, source ownership or
executable semantics.

## Inputs and admission

The input is the original-profile TinyXML2 probe from the schema-0.3
function-shape measurement: 32,723,259 bytes, SHA-256
`e8392538c33e8d69a2bdbea093e41afa9a41b4d00d3c1d7f6f7aab06797cdad3`.
Clang and LLVM are pinned to 21.1.8. The new
`extractors/cpp/inspect_probe.lean` parses its complete bytes through
`parseDeclarationProbeString` at runtime, obtains a typed `DeclarationProbe`,
and executes the unchanged bridge functions on selected real AST paths.
The same-probe AST view supplies no translation-envelope provenance claim.
No frontend is rerun.

The original schema-0.1 XML receipt failed `load_cpp_probe`'s schema check.
The adjacent schema-0.2 template receipt is also outside the pinned schema;
synthetic schema-0.2 regressions confirm refusal without supplying shape
defaults. These are format refusals, not semantic disagreements.

Full XML literal compilation still has no completed success in this item:
the default loader attempt reaches the 200,000-heartbeat LCNF limit; larger
heartbeat/recursion settings were explored, then interrupted after roughly
20 minutes without completion. An interruption is not a parser refusal or a
finished literal. A three-row metadata projection with a manually assembled
three-node AST compiled separately; it is a derived control, not ingestion of
the original corpus or a kernel theorem about it.

For nlohmann/json, the earlier capture-loader measurement records an internal
out-of-memory refusal on the 1,835,697,710-byte schema-0.3 probe. It is not
rerun here, and there is no new runtime-inspection result for that corpus.
The extension-heavy systems input remains frontend-refused on its recorded
non-standard declarations and has no successful probe to inspect. This item
therefore completes runtime inspection of one public corpus, no original
corpus literal compilation and no three-corpus typed-ingestion result.

## XML occurrence census

The independent Python audit reproduces `Artifact.indexNode`'s path rule:
zero-based indices through every nested `inner` array, retaining declaration
occurrences even when an ID repeats. Runtime Lean parsing independently confirms
the 4,527 metadata rows, 4,546 indexed occurrences and 442 function rows.
These include dependencies and implicit/skeletal occurrences, not just
source-owned declarations.

| Measure | Result |
| --- | ---: |
| Metadata rows | 4,527 |
| Indexed declaration occurrences | 4,546 |
| Unique artifact IDs | 4,510 |
| Metadata-only IDs | 17 |
| Repeated metadata rows | 0 |
| Artifact IDs without metadata | 0 |

The following **Python-audited** bridge-condition counts cover all indexed
occurrences. They are not a full Lean bridge sweep or kernel-certified counts.

| Bridge conditions audited | Satisfied | Unsatisfied | Boundary |
| --- | ---: | ---: | --- |
| `canonicalTargetCandidates` | 4,545 | 1 | one canonical target is absent from the artifact index |
| `canonicalRootEvidence` | 4,545 | 1 | the same absent canonical target |
| `canonicalPredecessorChainEvidence` | 4,545 | 1 | the same absent predecessor/canonical target |
| `semanticContextChainEvidence` | 4,546 | 0 | — |
| `lexicalContextChainEvidence` | 4,546 | 0 | — |
| `functionDefinitionEvidence` | 442 | 4,104 | non-`FunctionDecl` occurrences refuse if queried |
| `linkageEvidence` | 4,420 | 126 | 125 occurrences lack linkage fields: 66 `AccessSpecDecl`, 43 `LinkageSpecDecl`, 14 `FriendDecl`, 2 `StaticAssertDecl`; the translation unit also refuses |

The single canonical gap is retained, not repaired by name or location: the
`EnumDecl` occurrence's predecessor and canonical handle have no corresponding
artifact occurrence. Context chains nevertheless close to the translation
unit for every indexed occurrence. The function bridge has all required local
shape fields for the 442 function declarations. Linkage acceptance is compiler
telemetry only; it does not map the enum strings to ISO linkage rules.

## Runtime Lean smoke

The inspector calls each of the seven bridge functions on these real paths:

| Path | Observed behavior |
| --- | --- |
| `[]` | root canonical chain has one handle; context chains are empty; function/linkage evidence refuses |
| `[5]` | namespace self-root, one-handle context chains, external compiler linkage |
| `[6]` | namespace predecessor chain has two handles |
| `[5,3]` | context closure succeeds; linkage evidence refuses its missing field |
| `[5,3,0]` | function definition flag is true; context chains have three handles |
| `[8,0]` | function definition flag is true; context chains have two handles |
| `[78,78]` | function definition flag is false; predecessor chain has two handles and language linkage is C |
| `[137,0,0]` | all three canonical queries refuse the missing target; both context chains have three handles |

From the repository root, with an external schema-0.3 XML probe:

```sh
lake env lean --run extractors/cpp/inspect_probe.lean /path/to/xml-probe.json \
  root 5 6 5.3 5.3.0 8.0 78.78 137.0.0
```

The process is capped externally at 120 seconds and completes in **37.159
seconds**, exit 0, with **1,740,648 KiB** maximum child RSS. This includes Lake
startup and is an operational receipt, not an isolated compiler benchmark.
Each bridge reports `OK` or its unchanged `REFUSE` message. Exit zero means the
inspection completed, not that the program executed or that all relationships
were admitted. No name/location-based target repair, deduplication or interpreter
change is used.
Receipts under `state/ls-cpp/typed-ingestion-census-20261010` retain the independent
audit script/output, real-input SHA-256, inspector output and validation logs.

## Decision

Keep the typed declaration bridges as occurrence-witnessed tooling evidence.
Do not widen the loader's schema gate, add a resource-specific fast path, or
call runtime parsing completed original literal compilation. The next rung
must use these observed refusals to specify an explicit declaration-validation
boundary; no further evidence wrapper alone establishes semantic admission.
