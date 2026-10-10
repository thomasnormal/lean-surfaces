# Query-local C++ declaration evidence pricing

2026-10-10. **Tooling census only; no semantic declaration queries admitted.**
This prices part of the [declaration contract](cpp-declarations.md), using the
existing optional [canonical probe](cpp-canonical-evidence.md). It does not
change extraction, Lean ingestion, entity semantics or execution:
`rung-0:no-executable-semantics` remains the execution refusal.

## Evidence policy

`extractors/cpp/price_declarations.py` accepts the pinned
`cpp-canonical-probe-0.3` wrapper with Clang and LLVM headers 21.1.8 and matching
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
`represented_class=null`. Applicable own-template API observations below must
also establish an ordinary compiler role. None of these observations is a
semantic admission rule.

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
`dependent_context=false`. Since schema 0.2 the probe supplies own-template
API evidence rather than inferring it from an enclosing context or AST shape.

### Versioned own-template evidence

| Family | Required field and exact API provenance | Ordinary-role gate |
| --- | --- | --- |
| Function | `function_templated_kind`, `FunctionDecl.getTemplatedKind` | Integer `0` (`TK_NonTemplate`) |
| Variable | `described_template`, `VarDecl.getDescribedVarTemplate` | Explicit null, not an absent field |
| C++ record | `described_template`, `CXXRecordDecl.getDescribedClassTemplate` | Explicit null, not an absent field |
| Function, variable, C++ record, enum | `template_specialization_kind`, the applicable family's `getTemplateSpecializationKind` | Integer `0` (`TSK_Undeclared`) |

Each provenance is carried in the corresponding `_api` field. Described-template
values are session-local handles or null, not entity identifiers. The function
enum inventory is 0 non-template, 1 primary template, 2 member specialization,
3 function-template specialization, 4 dependent specialization, 5 dependent
non-template. The specialization inventory is 0 undeclared, 1 implicit
instantiation, 2 explicit specialization, 3 explicit instantiation declaration,
4 explicit instantiation definition. These are **Clang 21.1.8 enums**, not ISO
classifications; bool, unknown integers, missing or conflicting fields and wrong
API labels refuse.

The applicable specialization getter includes member-specialization information;
Clang's pinned `MemberSpecializationInfo` forbids the undeclared kind. An enum
cannot itself be a template but can be a specialized member, so its getter is
required even for local definition/linkage observations that do not walk context
edges. Class/variable specialization and partial-specialization families remain
unsupported, including nodes whose specialization getter returns zero. TU and
namespace families do not consume these inapplicable fields.

This inventory is checked against the exact `llvmorg-21.1.8` headers and
`Decl.cpp`/`DeclCXX.cpp` implementations, with source pins in the external review
receipt. Schema 0.1 and 0.2 inputs refuse: no upgrade invents missing evidence.
The earlier format `cpp-declaration-pricing-2` removed the missing-own-template
barrier only because applicable queries gate on explicit API evidence; current
format `cpp-declaration-pricing-3` additionally requires the function-shape
evidence below for local definition observations.
**Every result still retains `semantic-validator-not-implemented`; semantic
admissions remain zero.** Raw template-ancestor refusals remain conservative.
The [proposed ordinary bridge](cpp-ordinary-bridge.md) specifies what must be
established before interpreting these candidates as ISO declaration answers;
the pricing tool does not implement that bridge.
The context guard also remains independent: an uninstantiated ordinary member
can report function kind zero while its enclosing context is dependent.

Metadata consensus is **query-local**. Every row must supply each consumed
field; missing, ill-typed or conflicting relevant fields refuse. Null, false,
zero and absence are distinct. Conflicts in unused definition fields do not
invalidate a canonical observation, and an unrelated missing graph target
does not invalidate another declaration's query. No first/last row wins.

## Four independently priced queries

### Versioned function-definition shape

Schema 0.3 records the complete pinned FunctionDecl local-definition predicate,
not merely its earlier body/defaulted/deleted flags. Every new field has exact
API provenance and query-local consensus:

| Field | API label | Local-shape tooling gate |
| --- | --- | --- |
| `function_has_skipped_body` | `FunctionDecl.hasSkippedBody` | Explicit false |
| `function_will_have_body` | `FunctionDecl.willHaveBody` | Explicit false |
| `function_has_defining_attr` | `FunctionDecl.hasDefiningAttr` | Explicit false |
| `function_late_template_parsed` | `FunctionDecl.isLateTemplateParsed` | Explicit false |
| `function_explicitly_defaulted` | `FunctionDecl.isExplicitlyDefaulted` | Must agree with admitted defaulting evidence |
| `function_attribute_count` | `Decl.hasAttrs/Decl.getAttrs.size` | Nonnegative integer, exactly zero for the initial empty-AST-attribute policy |
| `own_body_kind`, `own_body_owner` | Shared `own_body_api = FunctionDecl.getBody` | Both null without a body; otherwise CompoundStmt/CXXTryStmt and this declaration's witnessed handle |

Boolean fields reject integers/null; the count rejects booleans, negative
integers and noninteger tokens. API tags, absent/conflicting fields, malformed
handles, unknown body kinds and body/presence/owner mismatches refuse. A defaulted
flag without explicit defaulting refuses; explicit defaulting without defaulted
status is inconsistent evidence. The definition Boolean must equal the OR of
deletion-as-written, defaulting, body presence, skipped body, pending body and
defining attributes, exactly as `Decl.h` implements it. Late parsing participates
in body presence, not as a seventh independent definition branch.

The guarded attribute count matters: `Decl.getAttrs()` asserts when
`hasAttrs()` is false. The defining-attribute predicate covers AliasAttr,
IFuncAttr and LoaderUninitializedAttr in pinned `DeclBase.cpp`; neither this
predicate nor an empty AST attribute list proves all source annotations are
represented or semantically supported.

`FunctionDecl.getBody(owner)` searches redeclarations. The probe calls it only
for an own-body-present, non-late-parsed declaration and records the returned
owner rather than assuming locality. It does not acquire the later definition's
body for a prototype. The body kind comes from `Stmt.getStmtClassName` on the
retrieved body. A null retrieval or foreign owner refuses the local-shape
query instead of becoming declaration-only. Compound and function-try bodies,
explicit defaulting and deletion remain separate observations; none is an
executable admission. Skipped/pending/late/defining-attribute branches and
nonempty AST attributes are conservatively refused.

These checks close the getter-branch and body-owner evidence gap, **not the
ISO/source-form bridge**. Friend and linkage associations, type origins,
module/export assumptions, correspondence/group completeness and strict typed
Lean ingestion remain separate obligations. Canonical, context and linkage
queries do not consume these new definition-only fields. All semantic barriers
remain, including `variable-definition-rule-unestablished`.

| Query | Consumed evidence and limits |
| --- | --- |
| `canonical-node` | Witnessed same-family, same-name canonical root; root idempotence; acyclic predecessor chain with the same root; root has explicit null predecessor, and nonroots cannot have null predecessors. Semantic context chains must agree after witnessed namespace canonical normalization. Names are checked only after the supplied relation, never used to construct it. |
| `contexts` | Separate semantic and lexical chains through witnessed TU/namespace contexts, ending at the actual artifact root. Cycles, missing parents, class/function/linkage-spec contexts and incompatible namespace canonical parents refuse. Reopenings retain inline/anonymous flags; incompatible canonical flags refuse. Lexical and semantic chains need not be equal. |
| `definition` | Exact family-specific API label and declaration-local Boolean for functions/tags; functions require the versioned shape gates above. Variables retain their compiler enum as evidence but refuse with `variable-definition-rule-unestablished`. Namespace/TU definition queries refuse rather than interpreting API null as false. |
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
as a complete semantic ledger. `build_index` and `price_query` are low-level
tooling helpers over already validated pinned-probe rows; `price_probe` checks
the wrapper schema/compiler versions, and the CLI performs strict JSON decoding.
Helper callers must establish both preconditions. Calling a helper does not
itself certify those versions or acquire a semantic admission.

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

## Historical schema 0.1 measurements

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
extension diagnostics; no profile is relaxed. These counts and hashes belong to
schema 0.1 and pricing format 1, not a rerun under the new evidence policy.
ISO entity/linkage mapping and a semantic validator remain unimplemented.

## Historical schema 0.2 measurements

2026-10-10: one freshly compiled pinned probe and one production-pricing
invocation per unchanged corpus/profile. Compiler runs retain 180-second / 16 GiB
address-space / 2 GiB output bounds; pricing retains 600-second / 16 GiB / 2 GiB
input bounds. XML probe: **0.334 seconds / 130,560 KiB RSS / 31,810,905 bytes**;
json probe: **10.168 seconds / 1,320,136 KiB RSS / 1,812,360,748 bytes**. XML
pricing: **1.518 seconds / 97,268 KiB RSS**; json pricing: **163.506 seconds /
3,922,996 KiB RSS**. These are operational receipts, not isolated benchmarks.

| Query | XML eligible / refused | json eligible / refused |
| --- | ---: | ---: |
| Canonical node | 60 / 4,469 | 1,172 / 163,713 |
| Both independent contexts | 61 / 4,468 | 1,430 / 163,455 |
| Local definition observations | 485 / 4,044 | 2,923 / 161,962 |
| Compiler linkage telemetry | 774 / 3,755 | 4,143 / 160,742 |

The source-union counts remain 4,529 / 164,885; all-four intersections remain
26 / 616. Relative to the historical aggregates, json linkage has 18 fewer
eligible `VarDecl` candidates and 18 fresh candidates whose sole refusal is
`specialization-or-unestablished`. No cross-session handle join
identifies those candidates as a per-ID flip set. The other query aggregates are
unchanged; **semantic/runtime admissions remain zero**.

The focused regression separately pins an explicitly specialized member enum
emitted directly below the TU, with no template ancestor and with explicit
nonimplicit/nondependent/nonmodule evidence. Its local definition/linkage queries
now refuse solely on the specialization gate. Ordinary member patterns can
still report function kind zero with a dependent context; the independent guards
remain necessary.

Before/after production, imported-tool, compiler/library/header/package and
dependency hashes validate. Fresh `-MD` sets match all 104 XML / 350 json original
dependencies. Probe source SHA is `8a17ed7a…00bc7`, pricing source
`55ce155f…d0d72`, plugin `d39ec63f…1818`. No full AST-fingerprint/equivalence
rescan was run, and matching aggregate counts do not establish AST equivalence
or graph closure. The unchanged source declaration/body/declaration-only census
is XML 205/202/3 and json 1,572/963/609; Mox remains strictly refused.

Receipts under `state/ls-cpp/template-evidence-20261010/{review,tests,measurement}`
retain exact source/API pins, strict-domain diagnostics, full refusal matrices,
API-family field histograms and commands/resources/dependency provenance.
The schema-0.2 focused batteries had 25 compiler-probe and 82 pricing tests. They are
tooling acceptance/diagnostic cases, not semantic correctness theorems.

## Schema 0.3 measurements

2026-10-10: one fresh pinned probe and one production-pricing invocation per
unchanged corpus/profile, with retained wall-time, address-space and byte bounds.
XML probe: **0.319 seconds / 132,096 KiB RSS / 32,723,259 bytes**; json probe:
**10.720 seconds / 1,319,692 KiB RSS / 1,835,697,710 bytes**. Single-parse
production pricing plus same-parse field telemetry: XML **1.619 seconds /
98,856 KiB RSS**; json **173.004 seconds / 3,965,940 KiB RSS**. All runs exit
zero without triggering their bounds; these are operational receipts, not
isolated benchmarks.

| Query | XML eligible / refused | json eligible / refused |
| --- | ---: | ---: |
| Canonical node | 60 / 4,469 | 1,172 / 163,713 |
| Both independent contexts | 61 / 4,468 | 1,430 / 163,455 |
| Local definition observations | 221 / 4,308 | 1,925 / 162,960 |
| Compiler linkage telemetry | 774 / 3,755 | 4,143 / 160,742 |

Relative to schema-0.2 aggregates, definition eligibility drops **264 XML /
998 json**, while the other three queries are unchanged. All-four intersections
move **26 to 25 / 616 to 467**. Source-ID totals remain **4,529 / 164,885**.
These are aggregate comparisons only: no cross-process pointer join or
complete-AST equivalence claim is made.

Eligible exact `FunctionDecl` local forms are **125 declaration-only + 17
CompoundStmt** for XML, and **1,170 declaration-only + 301 CompoundStmt + 6
explicitly defaulted + 2 deleted-as-written** for json. Every eligible function
has zero AST attributes, false skipped/pending/defining-attribute/late-parsing
flags and, when a body is retrieved, an owner equal to the queried declaration.
No eligible corpus function has a CXXTryStmt body; a focused compiler fixture
covers that getter path, without semantic admission. Positive-attribute refusal
walls affect **300 XML / 2,458 json** exact FunctionDecl queries, overlapping
template, implicit and dependent-context walls; they are not the net losses.

All **104 XML / 350 json** dependency hashes and fresh `-MD` path sets agree
before/after, alongside compiler, plugin, source and pricing-tool pins. An
additional retained-toolchain verification passes **3,529 headers and two
development packages**. Probe source SHA is `0ba07c0f…925e681`, pricing source
`15ddc2d3…9f31154f`, plugin `d9ab70dc…626aea`. The source declaration/body/
declaration-only census remains XML **205/202/3** and json **1,572/963/609**;
strict Mox refusal is unchanged. **Semantic/runtime admissions remain zero.**

Receipts under `state/ls-cpp/function-shape-20261010/{review,tests,measurement,gates}`
retain exact API/tool/source pins, full same-parse field distributions and
refusal sets, resources, dependency integrity and focused acceptance diagnostics.
The focused batteries pass **31 compiler-probe / 108 pricing / 38 comparison /
35 extractor tests**, including Lean ingestion of the existing extraction
surface. They do not implement typed ingestion of the optional evidence or
prove the ISO bridge. No interpreter, theorem, cache or CI policy changes.
