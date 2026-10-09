# Query-local C++ declaration evidence pricing

2026-10-09. **Tooling census only; no semantic declaration queries admitted.**
This prices part of the [declaration contract](cpp-declarations.md), using the
existing optional [canonical probe](cpp-canonical-evidence.md). It does not
change extraction, Lean ingestion, entity semantics or execution:
`rung-0:no-executable-semantics` remains the execution refusal.

## Evidence policy

`extractors/cpp/price_declarations.py` accepts the pinned
`cpp-canonical-probe-0.1` wrapper with Clang and LLVM headers 21.1.8 and matching
runtime version. It indexes declaration-shaped ID-bearing records at **every
dict/list path**, not only `inner`, and preserves repeated raw occurrences and
metadata row indices. Handles are local to this one input; matching a name is
never an identity rule.

The candidate families are `TranslationUnitDecl`, `NamespaceDecl`,
`FunctionDecl`, `VarDecl`, `EnumDecl` and non-injected `CXXRecordDecl`.
Common gates require witnessed raw and metadata records, agreeing kinds,
explicit `implicit=false`, `dependent_context=false`, `owning_module=null`
and a string name for named families. Namespace flags are explicit booleans;
record candidates require `injected_class_name=false` and
`represented_class=null`. Function candidates require an integer specialization
kind of zero. None of these observations is a semantic admission rule.

A richer raw witness has a correctly typed `loc`, `range`, `inner` or
`completeDefinition` field, or is the actual translation-unit root. These are
structural emission signals, **not proof that all semantic facts were dumped**.
Malformed present witness fields refuse. Skeletal-only references cannot
establish a declaration candidate, and a richer occurrence does not erase a
conflicting or template-associated occurrence elsewhere.

An ancestor kind containing `Template` or `Specialization` yields a named
`template-associated-occurrence` refusal. This is deliberately conservative:
an ordinary declaration referenced beneath a template can be excluded too.
Absent wrappers and a specialization kind of zero **do not establish a
non-template declaration**. Namespace-level primary patterns can have
`dependent_context=false`; the probe lacks the complete templated-kind evidence
needed to discharge this obligation. Every eligible function, variable and
record therefore retains `non-template-evidence-unestablished` as a semantic
barrier.

Metadata consensus is **query-local**. Every row must supply each consumed
field; missing, ill-typed or conflicting relevant fields refuse. Null, false,
zero and absence are distinct. Conflicts in unused definition fields do not
invalidate a canonical observation, and an unrelated missing graph target
does not invalidate another declaration's query. No first/last row wins.

## Four independently priced queries

| Query | Consumed evidence and limits |
| --- | --- |
| `canonical-node` | Witnessed same-family, same-name canonical root; root idempotence; acyclic predecessor chain with the same root; root has explicit null predecessor, and nonroots cannot have null predecessors. Semantic context chains must agree after witnessed namespace canonical normalization. Names are checked only after the supplied relation, never used to construct it. |
| `contexts` | Separate semantic and lexical chains through witnessed TU/namespace contexts, ending at the actual artifact root. Cycles, missing parents, class/function/linkage-spec contexts and incompatible namespace canonical parents refuse. Reopenings retain inline/anonymous flags; incompatible canonical flags refuse. Lexical and semantic chains need not be equal. |
| `definition` | Exact family-specific API label and declaration-local Boolean for functions/tags; function body/defaulted/deleted flags remain separate observations. Variables retain their compiler enum as evidence but refuse with `variable-definition-rule-unestablished`. Namespace/TU definition queries refuse rather than interpreting API null as false. |
| `linkage` | Explicit compiler internal/formal linkage enums and applicable function/variable language-linkage enum, preserved separately. This is **compiler-inventory telemetry**, including named `Invalid`, not a mapping to ISO name linkage or entity identity. Unknown enum values and absent applicable fields refuse. |

Definition and linkage observations do not consume canonical or context edges.
Their eligibility can exceed graph-query eligibility without certifying entity
identity, a unique callable body, exhaustive definitions or ODR. Language-linkage
entity rules, including C-linkage's cross-namespace cases, remain unimplemented.
The artifact does not become a program-wide or cross-TU certificate.

## Report and operational bounds

Each per-ID query returns either `eligible-tooling-evidence` or `refused`, used
field/row/path evidence and a sorted refusal set. **All results retain
`semantic-validator-not-implemented`.** The aggregate always reports
`semantic_admitted_queries=0`, per-family eligible/refused counts, encountered
all-wall counts, exact encountered wall sets, eligibility intersections and
mandatory semantic-barrier counts. A traversal blocked by absent evidence
cannot discover hypothetical further ancestors; the wall sets do not claim
those unknown causes are independent or exhaustive.

The default input cap is 64 MiB. Larger runs must opt into an explicit cap and
retain external wall-time/address-space limits and source/input hashes.
Inputs are parsed strictly: duplicate JSON fields and noninteger numeric tokens
refuse. Output aliases refuse; publication is atomic. `--sample-limit` bounds
only the included examples, not the census; zero omits examples. The per-ID API
can recover all consumed evidence for a selected query without treating samples
as a complete semantic ledger.

```sh
python3 extractors/cpp/test_price_declarations.py
python3 extractors/cpp/price_declarations.py probe.json --out pricing.json
```

The index and census accumulators are evidence bookkeeping, not memoized query
results or runtime caches. Queries walk their consumed chains afresh. Long
predecessor chains can therefore have quadratic aggregate cost; explicit
resource bounds and receipts remain necessary. This item does not repeat the
unchanged complete-AST fingerprints or reinterpret their global pointer
closure refusal as either local-query success or universal local-query failure.

## Measurements

Both original, unchanged probe inputs complete under 600-second wall / 16 GiB
address-space / 2 GiB input caps. XML: **1.621 seconds / 95,992 KiB RSS**;
json: **171.203 seconds / 3,871,784 KiB RSS**. Before/after input, pricing-tool
and imported comparison-utility hashes match. The production pricing tool is
pinned as `ebb3a233…6d4909`. These are operational measurements alongside
repository gates, not isolated compiler benchmarks or frontend rescans.

The union contains 4,529 XML / 164,885 json declaration IDs, including dependency
declarations and metadata-only sources, not just application functions. Cells
below are **eligible-tooling-evidence / refused**, never semantic admissions:

| Query | XML | json |
| --- | ---: | ---: |
| Canonical node | 60 / 4,469 | 1,172 / 163,713 |
| Both independent contexts | 61 / 4,468 | 1,430 / 163,455 |
| Local definition observations | 485 / 4,044 | 2,923 / 161,962 |
| Compiler linkage telemetry | 774 / 3,755 | 4,161 / 160,724 |

All four queries are eligible for **26 XML / 616 json IDs**. Canonical and context
eligibility intersect at 59 / 1,088; canonical and definition at 27 / 700.
The queries are not nested: 1 / 84 sources have canonical, definition and linkage
evidence but lack lexical-context eligibility. Local function definition and
linkage observations number 406 / 2,477, without implying graph-query closure.
Raw/source ownership has not been reconstructed by guessing elided locations.

The reports retain 108/102/60/57 distinct XML refusal sets and
390/395/158/151 json sets for the four queries respectively. Template association,
dependent contexts, unsupported methods/parameters, class contexts and linkage
specification contexts overlap; counts are not independent predicted tier wins.
Semantic admissions remain **zero**, even for every all-four candidate.

The dated external receipts under
`state/ls-cpp/declaration-subset-20261009/{review,measurement,gates}` retain the
policy review, five independent deep-closure audits, bounded original-input runs
and validation. The 69 focused synthetic diagnostics are tooling tests, not
correctness theorems about prototype programs. Candidate counts are separate
from the unchanged corpus declaration/body census and still-zero runtime
admissions. Strict Mox extraction remains refused by its four previously recorded
extension diagnostics; no profile is relaxed. Missing own-template evidence and
ISO mapping still need faithful, versioned rules before semantic admission.
