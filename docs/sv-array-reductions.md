# Fixed-array reduction methods

IEEE 1800-2023 §7.12 and §7.12.3 `sum`, `product`, `and`, `or` and `xor`
operate on the existing one-dimensional fixed unpacked integral-cell store.
The result has the element type when no `with` clause is present, and the
bound `with` expression's type otherwise. An outer assignment does not widen
the reduction. Every combining operation retains this intrinsic width, so
narrow sums and products wrap before copyback; an explicit cast inside `with`
changes the accumulation width.

The frontend binds the actual iterator symbol to each actual array cell in
declared index order. Explicit iterator names, lexical shadowing, packed
member reads, pure nested reductions and live surrounding reads retain their
bindings. Array cells already carry their original local, package or hierarchy
identities. The expression uses the existing four-state integral operators;
there is no new value evaluator, store or scheduler. Pure terms are combined
in a balanced tree: fixed-width addition, multiplication and bitwise operators
are associative here, and effects are refused. This keeps a large fixed array
within ordinary expression-depth limits without selecting an effect order.

Two-state conversion, X/Z arithmetic and bitwise propagation, assignment
conversion, automatic lifetimes, copies, delays and NBA capture use their
existing rules. The existing fixed-cell resource limit still applies.
Dynamic arrays, queues and associative arrays need their own storage semantics;
unsupported element/result types, effectful `with` expressions and iterator
queries such as `item.index` remain explicit `ArrayReduction` refusals. Invalid
or redefined source retains a whole-design barrier. Symbolic extraction is
unchanged.

The paired **22,035** paths gain **11 clean extractions**, no losses:
**4,309 → 4,320 clean**, **17,660 → 17,649 partial**, **66 include skips**,
zero errors. All 4,309 previously clean extracted designs remain identical.
All eleven gains match complete independent transcripts under both tested
region oracles. Six authored programs also match both orders; two retain
explicit effect and iterator-query refusals despite successful references.
Nineteen final source/key/status/stdout/provenance bindings were authenticated.
Four kernel theorems bind the actual parsed two-cell source reduction and
copyback: live reads, modular four-bit addition, retained work/output and
source-cell preservation. These are properties of that real fixture, not a
general frontend correctness theorem. Extraction is distinct from whole-corpus
runtime conformance.

See [the fixtures and receipts](../Examples/system-verilog/array_reductions/README.md).
