# C++ translation tooling

`extract.py` produces the admitted `cpp-0.1` translation envelope described in
[the translation contract](../../docs/cpp-translation.md). No C++ execution
semantics are admitted. `test_extract.py` tests that boundary.

## Optional declaration metadata probe

`canonical_probe.cpp` is an **experimental, tooling-only** Clang plugin. It
prices the frontend supplement required by
[the declaration specification](../../docs/cpp-declarations.md); it does not
implement that specification. It is not loaded by `extract.py`, Lean ingestion,
the default build or CI. Its output is not an admitted translation envelope.

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

### Evidence contract

Output is one JSON object with `ast` and `metadata`. The former is Clang's stock
JSON dump from the **same ASTContext** used for the supplement. The latter has
schema `cpp-canonical-probe-0.1`, compiled/runtime Clang and LLVM-header versions,
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
  variable definition categories and function template-specialization kinds
  are **versioned compiler integer enums**, not ISO classifications. Function
  body presence, defaulting and deletion-as-written remain separate evidence.
  Unqueried definition families carry `null` and `not-queried`.
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

### Bounded real-source measurement

The external `canonical-probe` receipt dated 2026-10-09 retains two fresh runs
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
