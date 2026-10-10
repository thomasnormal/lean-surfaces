# C++ translation tooling

`extract.py` produces the admitted `cpp-0.1` translation envelope described in
[the translation contract](../../docs/cpp-translation.md). No C++ execution
semantics are admitted. `test_extract.py` tests that boundary.

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
```

The plugin's host build language is separate from the subject's C++23 profile.
Carry the original source, include flags, target, macros, working directory and
environment into the probe invocation. Do not combine it with another AST dump
action. Record the full command, dependency hashes before/after translation,
compiler/header/library/plugin/source hashes, diagnostics, exit status, time
and memory externally. A zero exit and parseable JSON are required but are not
semantic admission. Compiler diagnostics prevent successful artifact
publication; callers must discard output on any nonzero exit or parse failure.

The [proposed capture contract](../../docs/cpp-provenance.md) separates a
versioned, exact-byte launch/input receipt from stronger input-world closure.
It is specification only: no capture runner or receipt loader is implemented,
and the existing schema-0.3 wrapper has not acquired provenance fields.

### Evidence contract

Output is one JSON object with `ast` and `metadata`. The former is Clang's stock
JSON dump from the **same ASTContext** used for the supplement. The latter has
schema `cpp-canonical-probe-0.3`, compiled/runtime Clang and LLVM-header versions,
and a declaration ledger from `RecursiveASTVisitor`, with implicit code and
template instantiations enabled. No declaration family or header is filtered.

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
corpus and strict-refused Mox corpus receive no new verdict in this bounded
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
