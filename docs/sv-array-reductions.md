# Fixed-array reduction methods

IEEE 1800-2023 §7.12 and §7.12.3 `sum`, `product`, `and`, `or` and `xor`
operate on the existing finite fixed unpacked integral-cell store, consuming
one unpacked dimension at a time.
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

An untouched, default-empty dynamic array is a scalar exception: `sum()` and
`product()` lower to the specified zero result because no element or aggregate
state exists to observe. Writes, resizes, selected elements, and other
reductions remain loud.

Finite dynamic arrays of untagged unpacked structs also admit a pure `with`
clause that selects one integral field. The row iterator is bound directly to
the already-flattened `array[index].field` cell; whole-struct reductions,
aggregate fields, and iterator-index queries remain outside the representation.

For a finite zero-based dynamic array, the iterator `index()` method is also
pure: each expanded reduction term receives its sampled position as an
integral literal. Dynamic or nonzero-index uncertainty and non-reduction
iterator calls remain loud.

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

## Nested finite fixed-array reductions — 2026-10-26

Reduction methods now consume one finite unpacked dimension at a time when a
pure `with` expression reduces each row to the scalar result type. A 2-D
`matrix.sum with (item.sum)` therefore expands the outer rows to their flat
cell names and recursively folds each inner row; an explicit inner iterator,
`item.sum with (item)`, retains the same binding. Direct aggregate results,
dynamic/queue/associative storage, and effectful inner expressions remain
loud. The `nested_2d_reductions` fixture and differential row cover both
forms and their common `PASS` transcript.

## Dynamic-array struct-field reductions — 2026-10-26

An allocated finite dynamic array of untagged unpacked structs may reduce a
direct integral field with a pure `with` expression. The existing per-element
field cells provide the row binding, so `items.sum() with (item.weight)` keeps
the ordinary scalar width and signedness. Aggregate results, nested aggregate
fields, and `item.index()` remain loud. The `dynamic_struct_reduction` fixture
and differential row cover this field form.

## Dynamic-array iterator-index reductions — 2026-10-26

The finite sampled dynamic-array surface now admits `item.index()` inside a
pure reduction `with` expression. The index is the expanded zero-based cell
position, so `values.sum with (item + item.index())` retains intrinsic width
and evaluates deterministically. The `dynamic_array_index_reduction` fixture
and differential row cover this method; unrelated iterator calls remain loud.

## Empty dynamic-array reductions — 2026-10-26

The self-check surface admits `sum()` and `product()` on an untouched empty
dynamic array as zero-valued scalar identities. The admission rejects any
write, resize, element selection, unsupported `with` expression, or other
reduction method, preserving the flat-state boundary. The
`empty_array_reductions` fixture and differential row cover both identities.
