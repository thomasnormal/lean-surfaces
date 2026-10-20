# C++ tier charter

2026-10-20 — specification plan; [translation artifact admission](cpp-translation.md)
and [bounded integral callable execution](cpp-callable-evaluation.md) are implemented.
Complete [declaration semantics](cpp-declarations.md) and translation-unit execution
remain outside the admitted profile. General C++ is
the destination; the corpora are evidence, not the definition of the language.

## Contract and trusted boundary

Baseline: C++23, ISO/IEC 14882:2024. Cite WG21's public
[N4950 draft](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2023/n4950.pdf)
(2023-05-10) by clause **and bracketed name**, paraphrased. Each artifact
declares its edition; C++20, later editions and extensions need explicit gates.

Pipeline: real source → Clang JSON AST → thin, versioned extractor → literal
Lean AST → definitional interpreter → typed specification surface. The
**trusted source-to-AST base is Clang plus the extractor**, including
preprocessing, lookup, type checking, overload selection and instantiation.
Reject partial ASTs after compiler errors. Preserve declaration identity,
qualified names, types, value categories, conversions, cleanup nodes,
source/header hashes and instantiated bodies; never erase unknown nodes.
Lean checks proofs about the artifact, not Clang's correctness. Differential
execution additionally trusts compiler/linker/runtime; agreement is not conformance.

Reuse the C tier's architecture, not its semantic claims:
`extractors/c/extract.py`, `LeanModels/C/{Ast,Json,Load}.lean`,
`LeanModels/C/C23/`, `docs/c23-spec-mirror.md` and
`harness/c_torture_score.py`. C++ lifetime/type-accessibility needs independent
definitions, not inherited C gaps. Keep semantics kernel-reducible and proofs
typed Lean contracts, hiding fuel/AST details. No new axioms or proof holes.

## Clause-indexed ladder

Rows follow **clause order**, with smaller admissions respecting dependencies.
Declaration metadata comes first; execution waits for its rules. Lambda
closures wait for reference/class semantics despite belonging to expressions.

| Rung / N4950 clauses | Semantic admission | Differential oracle on compiled real-source calls |
| --- | --- | --- |
| 0 — §5, §6.2–6.6 `[lex]`, `[basic.def]`, `[basic.link]` | Translation units, definitions, scopes, linkage and resolved declaration identities; record the complete dependency manifest. | Cross-TU calls and namespace/overload identity; reject ill-formed inputs and missing dependencies. |
| 1 — §6.7, §6.9 `[basic.memobj]`, `[basic.exec]` | Objects/subobjects, storage duration, lifetime start/end, provenance, initialization and destruction obligations; retained state. | Aliasing and object/storage-reuse traces, global initialization and scope exits; no execution verdict for UB. |
| 2 — §6.8 `[basic.types]` | Scalar/class type identity, cv-qualification, widths, representation and layout profile; arrays and pointer types. | Boundary arithmetic/conversions and `sizeof`/`alignof`; class layout only for admitted class shapes. |
| 3 — §7 `[expr]`; §7.5.5 `[expr.prim.lambda]` | Value categories, sequencing, conversions, scalar operations and calls; later capture-by-value/reference, closure calls and generic-lambda instantiations. | Return values plus mutation/order traces; closure identity, capture mutation and dangling-capture refusal. |
| 4 — §8 `[stmt.stmt]` | Blocks, branches, loops, jumps, returns and scope-exit cleanup. | Control-flow results and destruction order across normal exits, `break`, `continue` and return. |
| 5 — §9 `[dcl.dcl]`, especially §9.3.4.3 `[dcl.ref]` | Declarators, initialization, functions, namespaces/enums, references, binding and temporary lifetime extension. | Lvalue/rvalue binding, alias-visible writes, temporary lifetimes, copy/move and elision traces. |
| 6 — §10 `[module]` | Module units, imports, visibility/reachability and their dependency boundary; refused until represented. | Same-source separately compiled module/import clients and negative visibility fixtures. |
| 7 — §11 `[class]`, `[class.derived]`, `[class.virtual]` | Members, constructors/destructors, special members, base subobjects, inheritance and virtual dispatch; construction-phase dispatch included. | Exact object-state and constructor/destructor/dispatch traces, including multiple inheritance. |
| 8 — §12 `[over]` | Clang-selected overloads, operators and user-defined conversions; execute the selected body, not a name-based substitute. | Distinct overload/conversion results and observable argument effects; invalid-call compile fixtures. |
| 9 — §13 `[temp]` | Concrete emitted instantiations, specializations, packs and constraints; no unresolved dependent execution. | Invoke actual instantiated bodies; compile-time type/constraint fixtures accompany runtime results. |
| 10 — §14 `[except]` | Throw/catch, matching, stack unwinding, RAII, rethrow, `noexcept` and termination. | Exception identity/payload, cleanup order, retained state and termination observations. |
| 11 — §15 `[cpp]` | Preprocessing remains Clang-owned; preserve includes/macros and their configuration in the trusted manifest. | Macro/include-conditioned source calls and extraction round trips under identical definitions. |
| 12 — §16 onward `[library]` | First API contracts: `move/forward`, `pair` construction/fields, `array` size/index, `vector` construction/size/index/`push_back`; expand explicitly through ownership (§20), utilities (§22), strings (§23), containers (§24), iterators/ranges/algorithms (§25–27). | Same API calls compiled against a pinned standard-library implementation; allocation, invalidation and exception behavior count. |

Each rung: specification → extractor/embedding/interpreter → proofs against
**unchanged real artifacts**, never handwritten twins. Libraries use bodies or
explicit standard contracts, never consumer-name special cases. Floating point,
atomics, coroutines, concurrency and environment remain named future frontiers.

## Oracle and refusal discipline

Pin frontend family/full version, edition, target/ABI, flags, dependency hashes
and standard-library version for extraction **and execution**. Probe
implementation-defined choices rather than inherit C's profile. Nondeterminism
is an explicit oracle parameter, not one compiler's unspecified order. Compare
defined runs with aligned choices, or prove choice-independent observations.
Distinguish language exceptions, UB, unsupported construct/environment and
exhaustion. Refusals name clauses/constructs and never count as agreement.
Compare result, reachable state, effects and termination. Optimization/sanitizer
runs detect bugs; they do not define semantics.

## Three evidence corpora

Sources stay external/read-only; drivers call the original declarations.
Pins are starting evidence snapshots, not claims of admission:

- **An extension-heavy systems reference input**: enums, aggregates,
  unsigned arithmetic, member access and mutation, followed by references,
  moves, containers and lambdas. Its identifying source details remain outside
  this public repository. Whole-program execution waits for allocation/lifetime
  and environment rules:
  `mmap`/`madvise`, pointer/integer casts, anonymous-struct extensions, builtins
  and external RNG hooks are genuine boundaries, not no-ops. Sources stay read-only.
- **[TinyXML-2](https://github.com/leethomason/tinyxml2)**, zlib license,
  `10.0.0` / `321ea883b7190d4e85cae5512a12e5eaa8f8731f`: conventional
  object-oriented parser; in-memory parsing/tree traversal exercises heap
  lifetime, inheritance/virtual visitors and ownership without file I/O.
- **[nlohmann/json](https://github.com/nlohmann/json)**, MIT license,
  `v3.11.3` / `9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03`: header-only
  template-heavy library; concrete construction/access/iteration and parse
  errors exercise instantiation, overloads, containers and exceptions.

End each rung with a three-corpus census: source-owned functions admitted /
refused, full wall sets by construct, separate library dependencies, and
MATCH/DIVERGE/REFUSE/TIMEOUT executions. Extraction/compilation errors and missing
corpora are separate failures. Journal revisions, commands and results;
this charter claims no measured C++ coverage.
