# C++ translation tooling

`extract.py` produces the admitted `cpp-0.1` translation envelope described in
[the translation contract](../../docs/cpp-translation.md). No C++ execution
semantics are admitted. `test_extract.py` tests that boundary.

`test_integral.py` independently checks the pure C++23 integral value layer
against actual Clang-compiled expressions at two optimization levels. It is
not AST ingestion or program admission; see
[the value-layer contract](../../docs/cpp-integral.md). Its standalone Lean
driver is `run_integral.lean` and its compiler oracle is `integral_oracle.cpp`.

`test_type_resolution.py` separately checks the named-integer target-profile
bridge against Clang's C++23 `decltype` rules; this remains type/value-layer
evidence rather than AST or execution admission.

`LeanModels/Cpp/TypeEvidence.lean` defines the structured type-row contract and
occurrence/canonical validator. The canonical declaration probe now emits the
same recursive tree from `clang::QualType` in its `metadata.type_evidence`
supplement; unsupported type families are omitted, never reconstructed from
`qualType` spelling. `parseValidatedTypeEvidence` checks the supplement against
the declaration rows before any later admission layer consumes it.
`LeanModels/Cpp/ExpressionEvidence.lean` separately validates the probe's
ordered `BinaryOperator` operand rows against the same AST occurrence and
direct-child handles, preserving both source and converted types so the
explicit `TargetProfile` promotion bridge can check builtin integral rows;
unsupported operand/result families stay in the refusal ledger.
The optional `Clang::Expr type projection v1` supplement additionally retains
structured types for individual expressions, including implicit cast
destinations and promoted unary operands. Its strict occurrence/kind join and
legacy compatibility rule are specified in the
[type-evidence contract](../../docs/cpp-type-evidence.md).

`census_callable.lean` performs a bounded runtime callable census of complete
probes, with explicit source-file selection and compiler-reported physical
expansion/spelling origins. It preserves body occurrences, separates
dependencies and macros, and reports admission's first refusal beside full
raw body-kind counts. See the [census contract](../../docs/cpp-callable-census.md);
it claims neither source execution nor original literal compilation.

`LeanModels/Cpp/VariableEvidence.lean` validates a separately versioned,
optional variable-storage and initializer supplement from the same probe.
It joins only AST root/`inner` occurrences, requires structured declaration
types, and retains unsupported types/pending defaults in a refusal ledger.
See the [getter and validation contract](../../docs/cpp-variable-evidence.md).
These observations do not admit `DeclStmt` or execute local declarations.

## Optional declaration metadata probe

`canonical_probe.cpp` is an **experimental, tooling-only** Clang plugin. It
prices the frontend supplement required by
[the declaration specification](../../docs/cpp-declarations.md); it does not
implement that specification. It is not loaded by `extract.py` or required by
the default build or CI. Its output is not an admitted translation envelope;
the optional literal evidence loader below is separate from that boundary.

The only supported development headers are **Clang and LLVM 21.1.8**. Compile
against the matching frontend's libraries, not an unrelated installed
`libclang`. Compilation rejects other header versions; plugin initialization
rejects a different runtime Clang version and nonempty plugin arguments.
These checks do not make loading ABI-incompatible libraries safe. Pin the
compiler, headers, libraries and plugin before loading it.

For the measured Linux shared-library installation, with externally staged
matching development headers:

```sh
export LEANCPP_CLANG=/path/to/clang++
export LEANCPP_HEADERS=/path/to/21.1.8-development-headers
export LEANCPP_PROBE_INCLUDE="$LEANCPP_HEADERS/include"
export LEANCPP_LIBS=/path/to/matching-libraries
export LEANCPP_PROBE_LIBRARY=/outside/the/repo/canonical_probe.so
"$LEANCPP_CLANG" --no-default-config -std=c++17 -fPIC -shared -fno-rtti \
  -I"$LEANCPP_HEADERS/include" extractors/cpp/canonical_probe.cpp \
  -L"$LEANCPP_LIBS" -Wl,-rpath,"$LEANCPP_LIBS" -Wl,--no-undefined \
  -l:libclang-cpp.so.21.1 -l:libLLVM.so.21.1 \
  -o "$LEANCPP_PROBE_LIBRARY"
"$LEANCPP_CLANG" --no-default-config -x c++ -std=c++23 -pedantic-errors \
  -fsyntax-only -Xclang -load -Xclang "$LEANCPP_PROBE_LIBRARY" \
  -Xclang -plugin -Xclang leancpp-canonical-probe original.cpp > probe.json
python3 extractors/cpp/test_canonical_probe.py
python3 extractors/cpp/test_dump_reachability.py
```

The plugin's host build language is separate from the subject's C++23 profile.
Carry the original source, include flags, target, macros, working directory and
environment into the probe invocation. Do not combine it with another AST dump
action. Record the full command, dependency hashes before/after translation,
compiler/header/library/plugin/source hashes, diagnostics, exit status, time
and memory externally. A zero exit and parseable JSON are required but are not
semantic admission. Compiler error diagnostics prevent successful artifact
publication; callers must discard output on any nonzero exit or parse failure.

The [capture provenance contract](../../docs/cpp-provenance.md) separates a
versioned, exact-byte launch/input receipt from stronger input-world closure.
The optional observational runner below implements positive-input checks;
the separate literal capture loader binds bundle payloads without authenticating
the producer or establishing input-world closure. The existing schema-0.3
wrapper has not acquired provenance fields.

### Observational capture

`capture_probe.py` runs the pinned plugin in one frontend action and publishes
a new `cpp-probe-capture-0.1` bundle only after successful completion, strict
JSON wrapper/header checks and matching positive-input/image checks. It is
separate from `extract.py`, literal probe ingestion and query pricing. It
requires Linux, Clang 21.1.8 and an externally built compatible plugin; it does
not build or download any toolchain image.

```sh
python3 extractors/cpp/capture_probe.py original.cpp \
  --clang "$LEANCPP_CLANG" --plugin "$LEANCPP_PROBE_LIBRARY" \
  --runtime-library "$LEANCPP_LIBS/libclang-cpp.so.21.1" \
  --runtime-library "$LEANCPP_LIBS/libLLVM.so.21.1" \
  --out-dir /outside/the/repo/probe-capture \
  --timeout 300 --memory-mib 16384 -- -I/path/to/subject/includes
python3 extractors/cpp/test_capture_probe.py
```

The output directory must not already exist, including as a dangling symlink;
its parent must exist. Successful publication is an atomic no-overwrite
directory rename, not an access-controlled immutable snapshot. `probe.json`
and `stderr.txt` retain exact frontend bytes; `inputs.d`, the discovery depfile,
per-command outputs/process receipts and `capture.json` retain the observation
trail. Once staging exists, failures retain it with `failure.json` and never
publish it as the requested successful bundle. Preflight refusals may happen
before there is a staging directory.

Subject flags after `--` follow the existing strict single-TU C++23 allow-list,
with their order preserved. This validates launch flags, not source-form
exclusion: module syntax may parse, and `ordinary_source_profile` remains
unestablished even when every observed `owning_module` is null. Source arguments
starting with `@` or `-` refuse; use `./` for a literal filename with that prefix.
The effective frontend environment is constructed
from fixed `PATH`, `LC_ALL=C`, `TZ=UTC` and allowed include/platform variables;
absent `SOURCE_DATE_EPOCH` becomes `0`, while a present-empty value stays empty.
Driver overrides and dynamic-loader injection refuse; unrelated inherited
variables and credentials are not copied into frontend launches or receipts.

Defaults are 300 seconds per subprocess and 16,384 MiB per child address space;
an inherited per-file size limit is 4 GiB. These are not aggregate disk limits.
Resource bounds and Linux child RSS measurements do not bound the parent JSON
parser or establish hermeticity. The supported launcher is the standalone,
single-threaded CLI; detected additional Python threads refuse before launch.
This guard does not establish absence of native threads or make concurrent
library calls supported. Compiler/plugin and the supplied runtime
library files are **declared images**, not an observed dynamic-loader closure;
even an empty declared library list leaves image closure unestablished.
The resource-directory manifest records symlinks without traversing symlink
directories. All input-world, actual-loaded-image and effective-cc1 closure
statuses stay unestablished.

Exit 0 means **observed positive-input stability under the trusted launcher**,
not producer authentication, complete bytes read, replay safety or successful
Lean ingestion. The strict runner validates JSON and wrapper/header pins, not
all typed declaration fields. No graph/row consensus, ISO declaration query,
cross-TU entity relation or executable semantics follows. A bounded capture
census attempted one original registered TU/profile from each of TinyXML2,
nlohmann/json and a strict extension-heavy corpus: two observational bundles
were published; the latter retained its frontend rejection. This is not a repository-wide TU
sweep or new literal/semantic admission. There is no CI wiring in this item;
the optional real-toolchain test reports an explicit skip when matching
compiler/plugin inputs are absent.

### Optional literal capture ingestion

For a published `cpp-probe-capture-0.1` bundle, use the directory command:

```lean
import LeanModels.Cpp.CaptureLoad

load_cpp_capture captured from "path/to/capture-bundle"
```

This embeds a literal `DeclarationCapture`: the complete parsed receipt with
typed binding records, and the existing raw/typed `DeclarationProbe`. It checks
all declared bundle payload byte counts and SHA-256, requires the four core
payloads and bound process stdout/stderr, and parses the exact checked probe
bytes. Auxiliary payload bytes are checked, not duplicated in the literal.
Receipt numeric tokens retain exact decimal/exponent spelling without float
coercion; the probe parser and typed integer fields stay integer-only.

The loader trusts Lean IO, the host executable `/usr/bin/sha256sum` and SHA-256
integrity; this is not a kernel hash theorem or producer/process authentication.
Payload paths are ordinary basenames. Symlinks, traversal and non-file payloads
refuse, but the caller must provide a quiescent bundle: path/metadata checks do
not defeat adversarial concurrent filesystem mutation. Original source and
toolchain paths need not remain installed for this portable literal binding.
Their hashes remain recorded claims, not new image/source checks or replay.

Successful binding leaves input-world, actual-loaded-image, effective-cc1 and
ordinary-source-profile closure unestablished, with semantic/runtime admissions
false. It neither creates an `Artifact` nor enables ISO/entity/ODR queries or
execution. `load_cpp_probe` remains the separate observation-only command.

A bounded literal-loader census of the two published original-profile captures
completes **zero** original-corpus literal compilations: TinyXML2 hits Lean's
default 200,000-heartbeat LCNF timeout (41.540 s), and nlohmann/json reports
internal out-of-memory (23.750 s), under `-j1`, 8 GiB address-space and 180-second
wall bounds. The strict extension-heavy corpus has no successful receipt to
load. Partial elaboration
or `#check` output is not completion. A separate small actual-module observation
with eight declaration rows loads successfully but supplies no ordinary-source,
ISO or runtime admission. These explicit resource refusals do not change the
historical corpus syntax counts or semantic/runtime admissions of zero.

See [capture-literal resource pricing](../../docs/cpp-capture-pricing.md) for
whole-original-artifact phase measurements and finite-budget controls. Its
kernel-only experiment is not completed public-loader compilation or C++
semantic admission; production loading remains unchanged.

### Runtime probe inspection

The separate [source-local function rule](../../docs/cpp-local-functions.md)
admits prototypes, compound/try bodies and deleted definitions as distinct
local declaration forms. It does not admit entities or execution. Inspect
every FunctionDecl occurrence and count these forms/refusals with:

```sh
lake env lean --run extractors/cpp/inspect_probe.lean /outside/the/repo/probe.json \
  --local-functions
```

`inspect_probe.lean` parses the same strict schema-0.3 evidence at runtime and
invokes the existing declaration-evidence bridges at selected occurrence paths:

```sh
lake env lean --run extractors/cpp/inspect_probe.lean /outside/the/repo/probe.json \
  root 5 5.3.0
```

`root` denotes `[]`; dotted indices follow nested `inner` arrays. With no
selected paths it prints metadata, occurrence/function-row counts and the
validated structured type-row count.
Unknown paths, invalid syntax, invalid UTF-8 and schema/parse failures exit
nonzero. A bridge refusal is printed as `REFUSE`; exit zero means the inspection
completed, not that every bridge succeeded. The AST view is taken from the same
probe, without a translation-envelope provenance claim. This runtime tool does
not register a literal Lean declaration, repair resource-limited literal
compilation, authenticate a producer, or admit C++ execution. The
[real-input census](../../docs/cpp-typed-ingestion-census.md) separates runtime
inspection from literal loading and independent Python aggregate auditing.

The typed callable bridge is a separate ingestion step documented in
[`cpp-callable-functions.md`](../../docs/cpp-callable-functions.md). It consumes
the same validated type and binary-expression supplements and admits only a
single direct-return body; it is not enabled by `--local-functions` and does
not change the execution refusal.

### Evidence contract

Output is one JSON object with `ast` and `metadata`. The former is Clang's stock
JSON dump from the **same ASTContext** used for the supplement. The latter has
schema `cpp-canonical-probe-0.3`, compiled/runtime Clang and LLVM-header versions,
and a declaration ledger from `RecursiveASTVisitor`, with implicit code and
template instantiations enabled. It also carries an additive
`type_evidence_api`/`type_evidence` supplement built from the same
`clang::QualType` objects; unsupported type families are omitted. No
declaration family or header is filtered from the raw ledger.
The `expression_evidence_api`/`expression_evidence` supplement carries only
Clang builtin `BinaryOperator` nodes, including its `CompoundAssignOperator`
subclass: the operator, structured result type and two ordered direct-child
handles with source/converted types. The row's `kind` identifies the base
API family; the raw AST retains the exact subclass kind. The probe observes
the JSON dump while emitting it from the same `ASTContext`; a visited binary
expression whose handle is absent from that dump is retained in
`expression_refusals` with `dump_visible: false`, rather than published as
unverifiable evidence. Other refusals record unsupported operand or result
types. The Lean bridge checks integral promotions and usual arithmetic
conversion types when an admitted row is builtin integral. This is typed
frontend evidence, not expression evaluation or executable admission.

- `id`, `canonical`, `previous`, `semantic_context` and `lexical_context` are
  exact session-local frontend handles, not entity identifiers. Context IDs
  are obtained by converting the context to its declaration, not by casting
  its address. Preserve every raw occurrence, including repeated skeletal ones.
- `original_namespace` is the namespace's canonical declaration;
  `inline_namespace` and `anonymous_namespace` are separate API observations.
- Injected class names can be self-canonical. `represented_class` separately
  records the class designated by the injected name's type. Do not merge all
  declarations by `canonical` and call the result C++ entity identity.
- `linkage_internal`, `linkage_formal` and `language_linkage` are distinct Clang
  API results. Language linkage is queried only for functions and variables;
  it is not a complete classification of function-type language linkage.
- Definition evidence names its API. Function and tag results are Boolean;
  variable definition categories and template-specialization kinds
  are **versioned compiler integer enums**, not ISO classifications. Function
  body presence, defaulting and deletion-as-written remain separate evidence.
  Unqueried definition families carry `null` and `not-queried`.
- Function-shape evidence records all six branches of the local definition
  predicate, late-template parsing, explicit defaulting and AST attribute count,
  with exact API tags. `getAttrs()` is guarded by `hasAttrs()`. Own-body kind
  and owner are queried only when this declaration reports a body and is not
  late-template-parsed; otherwise both fields are explicit null. The body
  getter searches redeclarations, so a nonnull body owner must independently
  match the queried declaration for a local-shape candidate. These observations
  do not admit source forms, select an executable body or prove entity closure.
- Own-template evidence names its API in `_api` fields: function
  `function_templated_kind` from `FunctionDecl.getTemplatedKind`; variable/record
  `described_template` from `getDescribedVarTemplate`/`getDescribedClassTemplate`;
  function/variable/record/enum `template_specialization_kind` from the applicable
  `getTemplateSpecializationKind`. Described-template pointers are handles or
  null; enums retain their exact compiler integers. The
  [versioned policy](../../docs/cpp-declaration-pricing.md) pins their inventory
  and ordinary-role gates, including member-enum specializations. Neither a zero
  specialization kind nor `dependent_context=false` alone proves no own template.
- `dependent_context` only queries the declaration's context. `owning_module`
  reports its owning module name, if any. Neither field proves a declaration
  is dependence-free or satisfies the initial non-module admission contract.
- `type_evidence` contains rows for typed value/function declarations whose
  complete recursive tree is in the admitted structured vocabulary. Rows retain
  occurrence and canonical handles; record/enum nodes point to canonical
  declaration handles that the visitor witnessed. `parseValidatedTypeEvidence`
  validates this supplement. It is not a `qualType` parser and it does not
  admit an operand, callable body or executable program.
- `type_refusals` records typed declarations whose exact Clang type cannot be
  represented without guessing (for example, unsupported qualifiers or
  function properties). A refusal is retained as evidence; it is not silently
  turned into a scalar or a spelling-based fallback.
- `expression_evidence` is validated by `parseValidatedBinaryExpressionEvidence`:
  the occurrence kind/opcode, direct-child order/kinds and structured type
  references must agree with the retained AST and declaration ledger. It does
  not cover overloaded operators, conversions, calls or expression execution.
  A visitor occurrence absent from the same-process JSON dump is retained only
  in `expression_refusals` (`dump_visible: false`), never as an evidence row.

The visitor can miss declarations that the stock dumper emits as nested type
references. Canonical/predecessor/context/represented-class targets can also be
absent from the ledger or raw dump. Repeated ledger IDs may occur: retain and
check agreement rather than selecting a row. Census every nested dictionary
and list in the dump, not just `inner`. Missing, conflicting or unaligned
evidence stays unknown. This probe supplies no graph closure or query fallback.

Fresh invocations have different pointer handles. Compare relationships only
after witnessed occurrence alignment, and report unalignable targets. A fresh
stock dump and independent API review check the tooling, not independent
compiler conformance or C++ program correctness. Focused temporary fixtures
test tooling behavior; they are neither proof examples nor runtime verdicts.

### Optional strict literal ingestion

`LeanModels.Cpp.Load` provides a separate command for schema-0.3 probe files:

```lean
import LeanModels.Cpp.Load

load_cpp_probe observations from "probe.json"
```

The result is a literal `DeclarationProbe`, not an `Artifact` or a semantic
certificate. Its `ast` and `metadata` retain the complete raw trees. Its
`declarations` retain ledger order and repeated handles, with original row
ordinals and raw rows alongside typed common declaration fields. Exact
`FunctionDecl` rows additionally have typed `FunctionShapeEvidence`;
`DeclarationProbe.functions` is an ordered filter, not a cache or canonical
grouping. Other families and template/linkage enums remain raw beyond the
common header; this is not complete typed schema coverage.

`parseDeclarationProbeString` uses the strict raw JSON parser before field
conversion. Duplicate fields at any depth, malformed Unicode and noninteger
number tokens refuse. Schema, compiler/runtime/header pins, common field
types and handles, and the exact function-shape types/API tags are checked.
The existing translation-envelope loader is unchanged and does not inherit
these parser guarantees.

Unsupported or incoherent function-shape observations, foreign body owners
and conflicting repeated rows remain evidence rather than becoming successful
query answers. Ingestion establishes no original compiler invocation or
dependency provenance, raw-occurrence witnesses, graph/group closure,
source-form exclusions, ISO entity/definition/linkage result or executable
body. Those require separate query-local checks; the Python pricer remains
independent and all semantic/runtime admissions remain zero.

Focused validation, after building the Lean modules:

```sh
lake build LeanModels.Cpp.Tests
env LEANCPP_TEST_LEAN=1 python3 extractors/cpp/test_evidence_ingestion.py
```

The actual compiler-to-literal test additionally requires the explicitly
pinned matching `LEANCPP_CLANG` and `LEANCPP_PROBE_LIBRARY` settings above;
without them that row reports an explicit skip. These checks add no CI wiring
or implicit probe build. No new full-corpus literal-ingestion sweep has run.
The historical three-corpus pricing, syntax and runtime census is unchanged
and cannot be relabeled as typed-ingestion admissions.

### Bounded XML measurement

The historical schema 0.1 `canonical-probe` receipt dated 2026-10-09 retains two fresh runs
on unchanged TinyXML2 `321ea883` under its admitted strict profile; all 104
dependency paths and their hashes match the original envelope. Each probe
exited zero with empty diagnostics and emitted 31,162,165 bytes. CLI wall times
were 0.264 and 0.314 seconds; per-run child maximum RSS receipts were 130,560
and 619,768 KiB. These are process measurements, not semantic coverage.

Walking every nested field finds **7,031 declaration-shaped positions / 4,512
IDs**, identically in the original AST and both probes. The earlier `inner`
index's 4,546 positions / 4,510 IDs is a different, narrower measurement. The
ledger has 4,527 rows/IDs, no duplicate or conflicting rows, and no joined-kind
mismatches: 4,510 IDs join, two skeletal builtin record IDs lack metadata, and
17 metadata-only parameter IDs lack raw occurrence witnesses. One canonical
and predecessor target remains absent. All 80 injected names are
self-canonical with separate represented-class targets.

Fresh path alignment finds 4,509 fully witnessed source nodes agreeing and
zero differing witnessed results. Three raw source nodes and the 17
metadata-only sources remain unalignable. Nonpointer AST structure matches the
original, but the **complete pointer-witnessed AST comparison refuses** at the
dangling predecessor; equal partial hashes are not complete graph agreement.
The analyzer's synthetic assertions and the 15 focused plugin tests pass.
No declaration-semantic query or C++ runtime becomes admitted. The large json
corpus and strict-refused extension-heavy corpus receive no new verdict in this bounded
measurement; full corpus-wide supplement coverage remains future work.

The subsequent [real-artifact pricing receipt](../../docs/cpp-canonical-evidence.md)
adds two unchanged original json probes. This does not integrate the supplement
or change either corpus's declaration-semantic/runtime admission status.

## Complete parsed-AST comparison

`compare_ast.py` is a separate, standard-library-only diagnostic tool. It reads
wrapped `ast` objects sequentially, visits **every AST field**, and computes
versioned, typed, length-framed SHA-256 projections. Object keys are sorted;
array order, scalar types, Unicode code points, absent fields and explicit nulls
remain distinct. It does not compare frontend/envelope metadata or execute C++.

The nonpointer projection erases only hexadecimal handles in the ten explicit
pointer-field families. The witnessed projection replaces each such handle with
its first deterministic same-process AST occurrence path. Every `id` field
remains in the complete traversal, so this preserves the full identity partition
without expanding every occurrence group again at every reference. All nested
ID-bearing records count, including skeletal reference descriptions; metadata
cannot manufacture a raw witness. No name/location heuristic or cache is used.

The observed `targetLabelDeclId` field is pinned to Clang 21.1.8's
`JSONNodeDumper::VisitGotoStmt`, which emits the label's pointer representation;
`VisitLabelStmt` emits its label through `declId`. Recognizing these as pointer
slots does not promote either reference into an ID-bearing raw witness.

Unknown pointer-shaped slots retain their literal payload and refuse both
comparisons. Missing recognized targets refuse the witnessed comparison even
when its diagnostic digest matches. **Exit 0 means the computation completed,
not that the ASTs agree**: inspect `nonpointer_comparison_status` and
`witnessed_comparison_status`. Hash agreement is tooling evidence, not a theorem
or semantic declaration admission; graph closure is a separate obligation.

```console
python3 extractors/cpp/test_compare_ast.py
python3 extractors/cpp/compare_ast.py original.json probe1.json probe2.json --max-input-mib 2048 --out comparison.json
```

The default input-byte cap is 64 MiB. Larger bounds must be explicit; wall time
and process memory limits belong to the measurement wrapper. Duplicate JSON
object fields, non-integer/nonfinite numeric tokens, malformed envelopes and
input/output aliases refuse loudly. Reports publish atomically only after all
inputs complete. Preflight guards are not protection against adversarial
concurrent filesystem mutation; real-artifact receipts retain before/after
hashes. The [pricing receipt](../../docs/cpp-canonical-evidence.md) records the
bounded original/probe measurement and any remaining refusals.

## Query-local declaration pricing

`price_declarations.py` measures witnessed candidates separately for canonical
nodes, TU/namespace context chains, declaration-local definition flags and raw
compiler linkage enums. The [pricing policy](../../docs/cpp-declaration-pricing.md)
names the common gates, query-specific closures and conservative refusals.
Each candidate retains explicit semantic barriers; `semantic_admitted_queries`
is always zero. This tool is not part of extraction or Lean ingestion.
It requires schema 0.3 and emits pricing format 3; schema 0.1 and 0.2 inputs
refuse rather than manufacturing missing own-template or function-shape
observations. Function definition queries additionally require exact getter
branches, empty AST attributes and local own-body evidence; the other three
queries do not consume these shape fields.

```console
python3 extractors/cpp/test_price_declarations.py
python3 extractors/cpp/price_declarations.py probe.json --max-input-mib 2048 --sample-limit 10 --out pricing.json
```

Reports distinguish per-family counts, encountered wall sets, query intersections
and bounded evidence examples. Complete-AST pointer closure and local query
eligibility remain different measurements. Pin input/tool hashes and explicit
time/memory bounds externally; the default input-byte cap remains 64 MiB.

## Automatic declaration pricing

`price_local_declarations.py` reads archived source-body inventories, not raw
translation envelopes. It separates implicit bodies, methods, dependencies and
ordinary declaration-containing bodies, retaining full remaining raw-kind sets.
Its permissive kind-only candidates establish neither signature/type admission
nor execution. The [declaration contract](../../docs/cpp-local-declarations.md)
records the measured public inventories and the required object/scope bridge.

```console
python3 extractors/cpp/test_price_local_declarations.py
python3 extractors/cpp/price_local_declarations.py BODY_INVENTORY.json --out local-pricing.json
```

Reports pin input bytes/hash and omit corpus labels, source paths and names.
Ownership comes from the input receipt, not an independent frontend query.
Schema and integer node counts are strict; input/output aliases refuse and
reports publish atomically. The default input-byte bound is 64 MiB.

## Integral record schemas

The probe retains complete aggregate shape and direct field order using
`CXXRecordDecl`/`FieldDecl` getters. `admitIntegralRecordSchema` joins these
observations to source occurrences and structured field types. The admitted
profile and its member-storage API are specified in
[Integral record member subobjects](../../docs/cpp-record-subobjects.md).

```console
lake env lean --run extractors/cpp/census_records.lean probe.json --sources source.cpp header.h
```

This bounded census validates the complete probe and queries every retained
complete record occurrence. It reports selected-source and dependency ownership,
admitted schemas and first refusals separately. It performs no function or
instance-method execution. Source hashes, frontend/plugin identity, process
limits and input provenance must be pinned by the external launch receipt.
