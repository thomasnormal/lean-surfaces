# SystemVerilog tier changelog

## [0.1.122] — 2026-10-28

Blocking `string.putc(index, character)` calls now replay through source-pure
ASCII string history, including low-byte integral characters and ignored or
out-of-range writes. Dynamic, timed, control-dependent, aliased, and
non-ASCII forms remain loud. The new fixture and Lean receipt pass;
differential coverage grows **378 rows / 372 matches / 0 disagreements / 6
recorded refusals → 379 / 373 / 0 / 6**. The fresh 22,065-path census moves
**5,629 → 5,637 clean / 16,369 → 16,361 partial** with 67 include skips;
`ExpressionStatement:CallExpression` falls **2,722 → 2,710** and
`AssignmentExpression:target` remains **2,751**.

## [0.1.121] — 2026-10-28

Blocking assignments from literal text wrapped around the metadata-only
top-level `$sformatf("%m")` query now replay through source-pure string
history. Nested hierarchy, functions, generated scopes, dynamic formats,
timed writes, and nonblocking publication remain loud. The new fixture and
Lean receipt pass; differential coverage grows **377 rows / 371 matches / 0
disagreements / 6 refusals → 378 / 372 / 0 / 6**. The committed 22,065-path
census remains **5,622 clean / 16,376 partial** with 67 include skips, and
`AssignmentExpression:target` remains **2,757**.

## [0.1.120] — 2026-10-28

Blocking assignments from the metadata-only top-level `$sformatf("%m")` query
now replay the module scope through source-pure string history. Nested
hierarchy, functions, generated scopes, and other dynamic format forms remain
loud. The new fixture and Lean receipt pass; differential coverage grows
**376 rows / 370 matches / 0 disagreements / 6 refusals → 377 / 371 / 0 / 6**.
The committed 22,065-path census remains **5,622 clean / 16,376 partial** with
67 include skips, and `AssignmentExpression:target` remains **2,757**.

## [0.1.119] — 2026-10-28

Blocking assignments from metadata-only `$typename` queries now replay the
resolved ASCII type spelling through source-pure string history. Effectful,
dynamic, timed, and nonblocking forms remain loud. The new fixture and Lean
receipt pass; differential coverage grows **375 rows / 369 matches / 0
disagreements / 6 refusals → 376 / 370 / 0 / 6**. The fresh 22,065-path census
reports **5,622 clean / 16,376 partial** with 67 include skips, and
`AssignmentExpression:target` falls **2,782 → 2,757**.

## [0.1.118] — 2026-10-28

Constant nested subarray references now copy into multidimensional fixed
unpacked integral destinations by ordinal leaf cell. Same-root overlap, dynamic
selections, and effectful sources remain loud. The new fixture and Lean receipt
pass; differential coverage grows **374 rows / 368 matches / 0 disagreements /
6 refusals → 375 / 369 / 0 / 6**. A fresh 22,065-path census reports **5,611
clean / 16,387 partial** with 67 include skips; the target wall remains 2,782
after the corpus revision added six paths.

## [0.1.117] — 2026-10-28

Blocking conditional assignments over multidimensional fixed unpacked integral
arrays now lower each ordinal cell to a source-preserving ternary, including
arrays with differing declared bounds but equal shapes. Nonblocking self-alias
branches remain loud. The new fixture and Lean receipt pass; differential
coverage grows **373 rows / 367 matches / 0 disagreements / 6 refusals → 374 /
368 / 0 / 6**, while the committed census remains **5,602 clean / 16,390
partial** because the shape is absent from the unavailable external checkout.

## [0.1.116] — 2026-10-28

Exact blocking self-copies of multidimensional fixed unpacked integral arrays
now lower to an inert `Empty` path over the flattened cells. Nonblocking,
partial, dynamic, and effectful copies remain loud. The new fixture and Lean
receipt pass; differential coverage grows **372 rows / 366 matches / 0
disagreements / 6 refusals → 373 / 367 / 0 / 6**, while the committed census
remains **5,602 clean / 16,390 partial** because the shape is absent from the
unavailable external checkout.

## [0.1.44] — 2026-10-28

The SystemVerilog self-check surface now has 372 differential rows: 366
matches, zero disagreements, and 6 recorded refusals. The grammar census has
218 pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path
committed corpus snapshot has 5,602 clean files and 16,390 partial files, with
67 include skips. The latest rungs cover multiple literal integral
`$sformatf` conversions and blocking self-aliasing in unpacked structs and
one-dimensional fixed arrays; nonblocking publication and scheduler-owned
forms remain loud.

## [0.1.115] — 2026-10-28

Blocking conditional whole-array assignments with a self-alias branch now
lower each fixed-array cell to a source-preserving ternary. Nonblocking
self-alias branches remain loud because publication is scheduler-visible. The
new fixture and Lean receipt pass; differential coverage grows **371 rows / 365
matches / 0 disagreements / 6 refusals → 372 / 366 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.114] — 2026-10-28

Blocking conditional whole-struct assignments with a self-alias branch now
lower each integral field to a source-preserving ternary. Nonblocking
self-alias branches remain loud because publication is scheduler-visible. The
new fixture and Lean receipt pass; differential coverage grows **370 rows / 364
matches / 0 disagreements / 6 refusals → 371 / 365 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.113] — 2026-10-28

Exact blocking self-copies of flattened integral unpacked structs now lower to
an inert `Empty` path. Nonblocking self-copies remain loud because publication
is scheduler-visible. The new fixture and Lean receipt pass; differential
coverage grows **369 rows / 363 matches / 0 disagreements / 6 refusals → 370 /
364 / 0 / 6**. The committed census is unchanged at **5,602 clean / 16,390
partial** because this fixture shape is absent from the unavailable external
checkout.

## [0.1.112] — 2026-10-28

Exact blocking self-copies of one-dimensional fixed unpacked arrays of
integral unpacked structs now lower to an inert `Empty` path. Nonblocking
self-copies remain loud because publication is scheduler-visible. The new
fixture and Lean receipt pass; differential coverage grows **368 rows / 362
matches / 0 disagreements / 6 refusals → 369 / 363 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.111] — 2026-10-28

Literal `$sformatf` results with multiple integral conversions now replay exact
ASCII text when assigned to strings. Dynamic or nested operands, unsupported
conversion markers, timed forms, and nonblocking writes remain loud. The new
fixture and Lean receipt pass; differential coverage grows **367 rows / 361
matches / 0 disagreements / 6 refusals → 368 / 362 / 0 / 6**, and the fresh
census moves **5,601 → 5,602 clean / 16,391 → 16,390 partial** with
`AssignmentExpression:target` at **2,782**.

## [0.1.110] — 2026-10-28

Literal escaped-percent `$sformatf` results with one integral conversion now
replay exact ASCII text when assigned to strings. Multiple conversions or
escaped percents, dynamic operands, timed forms, and nonblocking writes remain
loud. The new fixture and Lean receipt pass; differential coverage grows **366
rows / 360 matches / 0 disagreements / 6 refusals → 367 / 361 / 0 / 6**, and
the fresh census moves **5,600 → 5,601 clean / 16,392 → 16,391 partial** with
`AssignmentExpression:target` at **2,783**.

## [0.1.109] — 2026-10-28

Integral literal operands of `%s`/`%S` `$sformatf` assignments now replay as
packed printable ASCII bytes when the width is a multiple of eight. Unknown,
non-byte-width, NUL/control, dynamic, timed, and nonblocking forms remain
loud. The new fixture and Lean receipt pass; differential coverage grows **365
rows / 359 matches / 0 disagreements / 6 refusals → 366 / 360 / 0 / 6**, and
the fresh census moves **5,599 → 5,600 clean / 16,393 → 16,392 partial** with
`AssignmentExpression:target` at **2,784**.

## [0.1.108] — 2026-10-28

Literal-prefix/suffix `$sformatf` results with one integral conversion now
replay exact ASCII text when assigned to strings. Decimal, hexadecimal,
binary, octal, and character forms are covered; dynamic operands, multiple
conversions, escaped-percent formats, timed forms, and nonblocking writes
remain loud. The new fixture and Lean receipt pass; differential coverage
grows **364 rows / 358 matches / 0 disagreements / 6 refusals → 365 / 359 / 0 /
6**, and the fresh census moves **5,597 → 5,599 clean / 16,395 → 16,393
partial** with `AssignmentExpression:target` at **2,785**.

## [0.1.107] — 2026-10-28

Zero-width string `$sformatf` results (`%0s`/`%0S`) assigned to strings now
replay exact ASCII text for literal operands and source-pure string history,
including one literal prefix and suffix around the conversion. Dynamic or
non-ASCII operands, additional conversions, timed forms, and nonblocking
writes remain loud. The new fixture and Lean receipt pass; differential
coverage grows **363 rows / 357 matches / 0 disagreements / 6 refusals → 364 /
358 / 0 / 6**, and the fresh 22,059-path census moves **5,596 → 5,597 clean /
16,396 → 16,395 partial** with `AssignmentExpression:target` at **2,787**.

## [0.1.106] — 2026-10-28

Zero-width binary and octal `$sformatf` results (`%0b/%0B` and `%0o/%0O`)
assigned to strings now replay minimal exact text for known integral literals.
Unknown or dynamic operands, timed forms, and nonblocking writes remain loud.
The new fixture and Lean receipt pass; differential coverage is **363 rows / 357
matches / 0 disagreements / 6 recorded refusals**, and the census remains
**5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.105] — 2026-10-28

Literal integral decimal `$sformatf` results (`%d`, `%D`, `%0d`, `%0D`) assigned
to strings now replay exact decimal text. Unknown or dynamic operands, timed
forms, and nonblocking writes remain loud. The new fixture and Lean receipt
pass; differential coverage is **362 rows / 356 matches / 0 disagreements / 6
recorded refusals**, and the census remains **5,584 clean / 16,414 partial**
with `AssignmentExpression:target` at **2,810**.

## [0.1.104] — 2026-10-28

Literal integral `$sformatf("%o", ...)` and `$sformatf("%O", ...)` results
assigned to strings now replay exact lower-case octal text. Unknown or dynamic
operands, timed forms, and nonblocking writes remain loud. The new fixture and
Lean receipt pass; differential coverage is **361 rows / 355 matches / 0
disagreements / 6 recorded refusals**, and the census remains **5,584 clean /
16,414 partial** with `AssignmentExpression:target` at **2,810**.

## [0.1.103] — 2026-10-28

Literal integral `$sformatf("%b", ...)` and `$sformatf("%B", ...)` results
assigned to strings now replay their exact packed 0/1 text, retaining literal
width. Unknown or dynamic operands, timed forms, and nonblocking writes remain
loud. The new fixture and Lean receipt pass; differential coverage is **360
rows / 354 matches / 0 disagreements / 6 recorded refusals**, and the census
remains **5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.102] — 2026-10-28

Literal integral `$sformatf("%c", ...)` and `$sformatf("%C", ...)` results
assigned to strings now replay their low-byte ASCII character. Unknown, zero,
non-ASCII/control, dynamic, timed, and nonblocking forms remain loud. The new
fixture and Lean receipt pass; differential coverage is **359 rows / 353
matches / 0 disagreements / 6 recorded refusals**, and the census remains
**5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.101] — 2026-10-28

Source-pure ASCII `$sformatf("%s", ...)` and `$sformatf("%S", ...)` results
assigned to strings now replay exact text from literal operands or earlier
literal string history. Dynamic operands, unsupported formats, timed forms, and
nonblocking writes remain loud. The new fixture and Lean receipt pass;
differential coverage is **358 rows / 352 matches / 0 disagreements / 6
recorded refusals**, and the census remains **5,584 clean / 16,414 partial**
with `AssignmentExpression:target` at **2,810**.

## [0.1.100] — 2026-10-28

Literal `$sformatf("%h", ...)` and `$sformatf("%H", ...)` results from
integral literals now replay as source-pure ASCII string assignments. Later
comparisons and diagnostics see the exact hexadecimal value; dynamic operands,
other formats, timed forms, and nonblocking writes remain loud. The
`string_sformatf_literal_assignment` fixture and Lean receipt supply the `PASS`
evidence; differential coverage is **357 rows / 351 matches / 0 disagreements
/ 6 recorded refusals**, and the fresh census is **5,584 clean / 16,414
partial** with `AssignmentExpression:target` at **2,810**.

## [0.1.99] — 2026-10-28

Constant-index string-byte assignments from one-byte ASCII literals now replay
the source-pure string history, so later comparisons and `%0s` diagnostics
observe the updated character. Dynamic, out-of-range, multi-byte, timed, and
nonblocking forms remain loud. The `string_index_literal_character` fixture and
Lean receipt supply the `PASS` evidence; differential coverage is **356 rows /
350 matches / 0 disagreements / 6 recorded refusals**, and the fresh census is
**5,582 clean / 16,416 partial** with `AssignmentExpression:target` at
**2,812**.

## [0.1.98] — 2026-10-28

Blocking assignment of the one-byte NUL string literal to a constant-indexed
string character now lowers to the existing §6.16 ignored-write rule. Dynamic,
nonzero, timed, and nonblocking forms remain loud. The
`string_null_literal_character` fixture and Lean receipt supply the `PASS`
evidence; differential coverage is **355 rows / 349 matches / 0 disagreements
/ 6 recorded refusals**, and the fresh corpus census is **5,580 clean / 16,418
partial** with `AssignmentExpression:target` at **2,814**.

## [0.1.97] — 2026-10-28

Source-pure `string.toupper()`, `string.tolower()`, and bounded `substr()`
assignments now use ASCII literal history and fold subsequent comparisons.
Dynamic, aliased, timed, nonblocking, and non-ASCII forms remain loud. The
`string_case_assignment` and `string_substr_assignment` fixtures and Lean
receipts supply the `PASS` evidence; differential coverage is **354 rows / 348
matches / 0 disagreements / 6 recorded refusals** and grammar coverage remains
**218 / 97 / 121**.

## [0.1.96] — 2026-10-28

Blocking literal queue writes followed by an empty queue concatenation now
remain admissible when the only later observation is `.size()`. The
`queue_literal_then_empty_concat` fixture and Lean receipt cover the exact
zero-size history; dynamic or nonliteral writes and queue element observations
remain loud. Differential coverage is **352 rows / 346 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**.

## [0.1.95] — 2026-10-28

The integral power family now has unsigned, signed, and zero-to-negative
self-check rows in the executable differential matrix. All three match their
committed `PASS` declarations. The zero-to-negative case remains a documented
IEEE 1800-2023 §11.4.3 Table 11-4 / Icarus divergence from the separate
reference run. Differential coverage is **351 rows / 345 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**.

## [0.1.94] — 2026-10-28

Exact blocking self-copies of constant subarrays now lower to an `Empty`
no-op, matching the existing whole-array self-copy rule. Nonblocking,
overlapping, dynamic, and nonintegral forms remain loud because their
publication or storage behavior is not erased. The
`fixed_array_subarray_self_copy` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **348 rows / 342 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census remains **5,401 clean / 16,597 partial** with
67 include skips.

## [0.1.93] — 2026-10-28

Blocking copies between two disjoint constant subarrays of one fixed
multidimensional integral array now lower to cellwise writes. The extractor
checks that the source and destination cell sets do not overlap, preserving
the complete source snapshot; overlapping, dynamic, timed, and nonblocking
forms remain loud. The `fixed_array_disjoint_subarray_copy` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **347 rows /
341 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121** and the committed census remains **5,401 clean /
16,597 partial** with 67 include skips.

## [0.1.92] — 2026-10-28

Unpacked concatenations assigned to scalar-integral dynamic arrays now admit a
zero-argument function whose complete body assigns one integral literal through
the implicit function name. The call is materialized as one sampled cell while
effectful or state-dependent function operands remain loud. The
`dynamic_array_concat_literal_function` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **346 rows / 340 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census remains **5,401 clean / 16,597 partial** with
67 include skips.

## [0.1.91] — 2026-10-28

Source-pure ASCII string history now flows through constant replication and
concatenation writes. A named string with only earlier unconditional blocking
literal writes can be reconstructed for a blocking target and a matching `%s`
diagnostic; computed, control-dependent, timed, nonblocking, and non-ASCII
forms remain loud. The existing `replication/dynamic_string` fixture now
matches `dynamic abab`. Differential coverage is **345 rows / 339 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census is unchanged at **5,401 clean / 16,597
partial** with 67 include skips.

## [0.1.90] — 2026-10-28

Blocking assignments of literal integral zero to a constant-indexed string
byte now lower to `Empty`, matching IEEE 1800-2023 §6.16's ignored
null-character rule. Dynamic indices, nonzero values, timed forms, and
nonblocking writes remain loud. The `string_null_character` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **344 rows /
338 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121**. The external census snapshot remains **5,401
clean / 16,597 partial** with 67 include skips.

## [0.1.89] — 2026-10-28

Whole-array continuous assignment now admits a one-dimensional fixed-unpacked
variable source with a complete literal declaration initializer and no later
writes. The extractor expands that immutable source into ordinal per-cell
time-zero writes, including opposite source and destination range directions;
mutable, net, sliced, dynamic, timed, and nonblocking forms remain loud. The
`static_fixed_array_continuous_copy` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **343 rows / 337 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**. The external census snapshot remains **5,401 clean / 16,597 partial**
with 67 include skips.

## [0.1.88] — 2026-10-28

Malformed integral packed-dimension declarations with a direct literal
initializer now follow the same compile-time rejection path as uninitialized
declarations. The initializer is recovered only from the declaration spelling
when pyslang has replaced it with `InvalidExpression`; calls and other
effectful initializers remain loud. The `invalid_packed_dimension_literal`
fixture and Lean receipt supply the `PASS` evidence. Differential coverage is
now **342 rows / 336 matches / 0 disagreements / 6 recorded refusals**;
grammar coverage remains **218 / 97 / 121**. The external census snapshot is
still unavailable in this checkout and remains **5,401 clean / 16,597 partial**
with 67 include skips.

## [0.1.87] — 2026-10-28

Declaration-only integral variables whose packed dimension is rejected during
elaboration now disappear as inert metadata. The narrow `ErrorType` slice
covers malformed ranges such as `bit [3:x]` and `bit [3]`; ordinary 2-state
variables, initialized malformed declarations, and invalid uses remain loud.
The `invalid_packed_dimension_decl` compile-error fixture and Lean receipt
supply the `PASS` evidence. Differential coverage is now **341 rows / 335
matches / 0 disagreements / 6 recorded refusals**; grammar coverage remains
**218 / 97 / 121**. The committed 22,065-file snapshot is externally
unavailable; its prior **5,401 clean / 16,597 partial** counts are unchanged
in this checkout, with 67 include skips.

## [0.1.86] — 2026-10-27

Declarations initialized by `new[0]` or an empty assignment pattern now lower
to inert metadata for both 2-state and 4-state dynamic arrays. Nonzero
allocations and later dynamic-array operations remain loud. Differential
coverage is **340 rows / 334 matches / 0 disagreements / 6 recorded refusals**;
grammar coverage remains **218 / 97 / 121**. The pinned 22,065-file census is
unchanged at **5,401 clean / 16,597 partial** with 67 include skips while the
external corpus checkout is unavailable.

## [0.1.85] — 2026-10-27

Exact whole-array blocking self-copies for one-dimensional fixed unpacked
integral arrays now lower to an `Empty` no-op. Sliced, overlapping, nonblocking,
timed, dynamic, aggregate, and effectful copies remain loud. The
`fixed_array_self_copy` fixture and Lean receipt supply `selfcopy 3 7`.
Differential coverage is now **339 rows / 333 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census remains **5,401 clean / 16,597 partial** with 67 include
skips while the external corpus checkout is unavailable.

## [0.1.84] — 2026-10-27

Whole assignments to a one-dimensional fixed unpacked integral array now admit
source-pure RHS patterns that read the destination itself. The extractor first
captures every RHS cell in local temporaries, then writes the flattened cells,
preserving the complete-RHS-before-store rule. Nested, dynamic, aggregate,
effectful, and width-mismatched aliasing remains loud. The existing
`assignment_patterns/self_alias.sv` fixture now supplies the `self 7 3`
receipt. Differential coverage is now **338 rows / 332 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**. The pinned 22,065-file census remains **5,401 clean / 16,597 partial**
with 67 include skips while the external corpus checkout is unavailable.

## [0.1.83] — 2026-10-27

Unreferenced package functions and tasks are now erased after the elaborated
call graph proves that no `CallExpression.subroutine` targets them. Calls from
modules, imports, other packages and recursive bodies retain the existing
`Package:Subroutine` boundary. The `package_unused_subroutines` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **337 rows /
331 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121**. The pinned 22,065-file census remains **5,401 clean
/ 16,597 partial** with 67 include skips while the external corpus checkout is
unavailable.

## [0.1.82] — 2026-10-27

Unreferenced module-scope functions and tasks are now erased as inert
declarations after the elaborated call graph proves no `CallExpression`
targets them. Referenced, recursive, receiver, DPI, and effectful-call
declarations remain loud because callable frames and external effects are not
represented. The `unused_subroutines` fixture supplies the `PASS` receipt.
Differential coverage is now **336 rows / 330 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census remains **5,401 clean / 16,597 partial** with 67 include
skips while the external corpus checkout is unavailable.

## [0.1.81] — 2026-10-27

Finite multidimensional unpacked integral arrays now admit `foreach` loops
when every dimension is explicitly bound. Dynamic reads and writes expand to
mutually exclusive conditions over the existing flat leaf cells; incomplete,
dynamic, queue, aggregate, and effectful forms remain loud. The
`foreach_nested` fixture supplies the `sum=21` differential receipt.
Differential coverage is now **335 rows / 329 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census is unchanged at **5,401 clean / 16,597 partial** with 67
include skips.

## [0.1.80] — 2026-10-27

One-dimensional fixed integral arrays now render as `%p` diagnostic arguments
through their existing flattened cells. Declared index order and signed
element rendering are preserved; nested, dynamic, effectful, and non-`%p`
aggregate values remain loud. The `array_named_display` fixture covers the
rendered transcript and the nested-array refusal. Differential coverage is now
**334 rows / 328 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census moves from **5,396 clean / 16,602 partial** to **5,401
clean / 16,597 partial** over 22,065 files, and
`NamedValueExpression:2state` falls **1,473 → 1,462**.

## [0.1.79] — 2026-10-27

Source-pure string equality and relational comparisons now fold for direct
ASCII literals and named strings with earlier unconditional blocking literal
writes. Equality, case equality, inequality, and the four ordered comparisons
produce exact one-bit literals; computed, control-dependent, timed,
nonblocking, dynamic, and non-ASCII histories remain loud. Differential
coverage is now **333 rows / 327 matches / 0 disagreements / 6 recorded
refusals**; the chapter-only census moves from **5,384 clean / 16,614 partial**
to **5,396 clean / 16,602 partial** over 22,065 files, and
`NamedValueExpression:2state` falls **1,488 → 1,473**.

## [0.1.78] — 2026-10-27

Explicit casts from a finite source-pure `real` or `shortreal` to an integral
type now round to the nearest integer, with ties away from zero, before the
ordinary target-width conversion. Direct literals and source-ordered direct
blocking literal histories are admitted; computed, control-dependent, timed,
non-finite, and dynamic real sources remain loud. Differential coverage is
now **332 rows / 326 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census moves from **5,359 clean / 16,639 partial** to **5,384
clean / 16,614 partial** over 22,065 files, and
`ConversionExpression:Explicit` falls **34 → 9**.

## [0.1.77] — 2026-10-27

Static locals now preserve source order within a procedural scope, allowing a
later closed pure initializer to read an earlier static declaration. Runtime,
effectful, random, environment, cross-scope, and pre-process ordering cases
remain loud. Differential coverage is now **331 rows / 325 matches / 0
disagreements / 6 recorded refusals**. The chapter-only census moves from
**5,331 clean / 16,667 partial** to **5,359 clean / 16,639 partial** over
22,065 files; `StaticLocal:initializer` falls **168 → 140**.

## [0.1.76] — 2026-10-27

Literal-return user functions now accept named integral arguments whose
declaration and earlier writes are direct blocking literals in the time-zero
initial history. Computed, control-dependent, timed, nonblocking, dynamic,
output, inout, and reference arguments remain loud. Differential coverage is
now **330 rows / 324 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census remains **5,331 clean / 16,667 partial** over 22,065 files.

## [0.1.75] — 2026-10-27

`$timeformat` now accepts a source-pure named integral history for its unit,
precision, and width arguments when no `%t` consumer exists. The call remains
an inert configuration operation in the self-check state; a `%t` consumer,
computed, control-dependent, timed, nonblocking, or dynamic argument remains
loud. Differential coverage grows to **329 rows / 323 matches / 0
disagreements / 6 recorded refusals**, with grammar coverage unchanged at
**218 / 97 / 121**. The root-level witness is outside the chapter walk, so the
census remains **5,331 clean / 16,667 partial** and the statement-call blocker
remains **2,718**.

## [0.1.74] — 2026-10-27

`$assertcontrol` now accepts named integral arguments when their declaration
and earlier blocking writes are direct literals in the time-zero initial
history. The self-check tier has no assertion-control register, so the
validated call remains an inert `Empty`; computed, control-dependent, timed,
nonblocking, and dynamic arguments remain loud. Differential coverage grows
to **328 rows / 322 matches / 0 disagreements / 6 recorded refusals**, with
grammar coverage unchanged at **218 / 97 / 121**. The root-level witness is
outside the chapter walk, so the census remains **5,331 clean / 16,667 partial**
and the statement-call blocker remains **2,718**.

## [0.1.73] — 2026-10-27

Discarded `$countbits`, `$countones`, `$onehot`, `$onehot0`, and
`$isunknown` calls now accept named integral operands whose declaration and
earlier blocking writes are direct literals in the time-zero initial history.
The result is unobserved, so the envelope erases the call after the shared
source-order check; computed, control-dependent, timed, nonblocking, and
dynamic histories remain loud. Differential coverage grows to **327 rows / 321
matches / 0 disagreements / 6 recorded refusals**, with grammar coverage at
**218 / 97 / 121**. The witness is outside the chapter-only corpus walk, so
its **5,331 clean / 16,667 partial** counts and the **2,718** statement-call
blocker are unchanged.

## [0.1.72] — 2026-10-27

The four timed sv-tests-2 `$q_exam` witnesses now lower through a
source-ordered literal-delay replay: codes 2, 4, 5, and 6 report exact tick
statistics for mean interarrival, shortest completed wait, longest current
wait, and average completed wait. The timed receipt drives the existing
`elabTimedDesign`/timer scheduler at 4 and 6 ticks; the time-zero differential
matrix remains 326 rows with 320 matches, no disagreements, and 6 recorded
refusals. The chapter-only census is now **5,331 clean / 16,667 partial** over
22,065 files (67 include skips), and `ExpressionStatement:CallExpression`
falls from 2,722 to 2,718. Dynamic delays, overflow, branches, extra initial
processes, and computed or aliased queue histories remain loud.

## [0.1.71] — 2026-10-27

The self-check surface now has 326 differential rows: 320 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
`CallExpression` falls from 2,655 to 2,648.
Untimed initial-block `$realtime` now feeds the exact `$rtoi`, `$realtobits`,
and `$shortrealtobits` conversion paths as zero; continuous, scheduled, and
elapsed-time forms remain loud.

## [0.1.70] — 2026-10-27

The self-check surface now has 325 differential rows: 319 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
The exact real-conversion slices now accept `$itor` over a source-pure named
integral history, while computed, control-dependent, timed, nonblocking,
dynamic, and standalone real-storage forms remain loud.

## [0.1.69] — 2026-10-27

The self-check surface now has 324 differential rows: 318 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
`$rtoi` now folds a finite named real or short-real after source order proves
only direct literal assignments, preserving exact decimal truncation toward
zero; computed, control-dependent, timed, nonblocking, dynamic, and
out-of-range histories remain loud.

## [0.1.68] — 2026-10-27

The self-check surface now has 323 differential rows: 317 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
chapter census moves to 5,327 clean files and 16,670 partial files with 67
include skips; `CallExpression` falls from 2,656 to 2,655. An untyped mailbox
with one scalar integral literal now admits `try_peek()` into a destination of
a non-equivalent type, returning the required negative status without
consuming or writing mailbox state; aliases, dynamic histories, equivalent
types, and other mailbox methods remain loud.

## [0.1.67] — 2026-10-27

The self-check surface now has 322 differential rows: 316 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
chapter census remains at 5,326 clean files and 16,671 partial files with 67
include skips; the new witness is root-level and outside that walk. Direct
blocking scalar `$dist_uniform(seed, low, high)` assignments now resolve
signed 32-bit bounds from one earlier literal assignment in the same initial
process; computed, reassigned, timed, nonblocking, and value-position forms
remain loud.

## [0.1.66] — 2026-10-27

The self-check surface now has 321 differential rows: 315 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
corpus census has 5,326 clean files and 16,671 partial files with 67 include
skips; `AssignmentExpression:target` falls from 2,844 to 2,842. A direct
scalar-literal queue copied to a differently sized fixed array now lowers the
IEEE 1800-2023 §7.6 run-time mismatch to an immediate `$finish`, preserving
earlier output and preventing a partial copy. Equal-size copies and dynamic,
aliased, or effectful queue histories remain loud.

## [0.1.65] — 2026-10-27

The self-check surface now has 320 differential rows: 314 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
snapshot remains at 5,304 clean files and 16,688 partial files with 67 include
skips. Source-ordered scalar-literal mailbox histories now admit `peek()` and
`try_peek()`: both copy the FIFO head without consuming it, and `try_peek()`
also reports the empty-queue result. Dynamic messages, aliases, branches,
empty blocking peeks, and width mismatches remain loud.

## [0.1.64] — 2026-10-27

The self-check surface now has 319 differential rows: 313 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,304 clean files and 16,688 partial files with 67 include skips;
`CallExpression` falls from 2,729 to 2,672. Fixed-size bitstream `$bits`
operands are now admitted from their elaborated type without evaluating the
source expression, including increments, assignments, calls, and selected
reads; initialized dynamic-size operands remain loud.

## [0.1.63] — 2026-10-27

The self-check surface now has 318 differential rows: 312 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
moves to 5,304 clean files and 16,688 partial files with 67 include skips;
`AssignmentExpression:target` falls from 2,845 to 2,844 files. A source-pure
scalar-literal queue can now copy into a same-count fixed unpacked integral
array left to right; mismatches, aliases, aggregate elements, and scheduled
forms remain loud.

## [0.1.62] — 2026-10-27

The self-check surface now has 317 differential rows: 311 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
moves to 5,303 clean files and 16,689 partial files with 67 include skips;
`CallExpression` falls from 2,731 to 2,729. A direct empty queue assignment
after a literal initializer now makes later `size()` queries exactly zero;
nonempty mutations and content reads remain loud.

## [0.1.61] — 2026-10-27

The self-check surface now has 316 differential rows: 310 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,301 clean files and 16,691 partial files with 67 include skips;
`VariableSymbol:2state` falls from 2,223 to 2,118 files. A 2-state queue
initialized only by scalar literals now answers `size()` exactly; queue
mutations, content reads, and dynamic initializers remain loud.

## [0.1.60] — 2026-10-27

The self-check surface now has 315 differential rows: 309 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,301 clean files and 16,691 partial files with 67 include skips.
The no-argument `$dumpportsflush()` task is admitted as an inert external VCD
flush; argumented port-dump operations remain loud.

## [0.1.59] — 2026-10-27

The self-check surface now has 312 differential rows: 307 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,298 clean files and 16,694 partial files with 67 include skips;
the `CaseStatement:Unique` wall falls from 45 to 41 files. A sound literal
subset of `unique case` is now admitted: duplicate-free integral patterns
with a default arm, or complete coverage of every value for subjects up to
8 bits on a two-state subject. Dynamic, duplicate, incomplete, wildcard,
four-state complete-without-default, `unique0`, and priority forms remain
loud.

## [0.1.58] — 2026-10-27

The self-check surface now has 311 differential rows: 306 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,294 clean files and 16,698 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,739. A finite
source-pure pair of literal `for` loops around scalar mailbox `put()`/`get()`
operations now replays exact FIFO history; dynamic bounds, aliases, branches,
timing, and other mailbox methods remain loud.

## [0.1.57] — 2026-10-27

The self-check surface now has 310 differential rows: 305 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,293 clean files and 16,699 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,740. Fixed
one-dimensional unpacked struct arrays now also admit a direct packed
two-field `sort` key such as `{x.blue, x.green}`; computed, dynamic, and
aggregate keys remain loud.

## [0.1.56] — 2026-10-27

The self-check surface now has 309 differential rows: 304 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,292 clean files and 16,700 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,741. Fixed
one-dimensional unpacked struct arrays now admit literal `sort`/`rsort` with
`(item.field)` ordering while computed and aggregate keys remain loud.

## [0.1.55] — 2026-10-27

The self-check surface now has 308 differential rows: 303 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. A named `string`
with source-pure blocking ASCII literal history is now admitted for `%s`/`%S`
`$sformatf`; dynamic and effectful histories remain loud.

## [0.1.54] — 2026-10-27

The self-check surface now has 307 differential rows: 302 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal ASCII string
operands are now admitted for `%s`/`%S` in `$sformatf`; dynamic string storage
and non-ASCII operands remain loud.

## [0.1.53] — 2026-10-27

The self-check surface now has 306 differential rows: 301 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal integral
`$sformatf` expressions now admit `%0b/%0h/%0o/%0d` and uppercase aliases via
the existing minimal-width renderers.

## [0.1.52] — 2026-10-27

The self-check surface now has 305 differential rows: 300 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal integral
`$sformatf` expressions now admit `%c`/`%C` through the low-byte ASCII renderer;
dynamic or nonintegral string formatting remains loud.

## [0.1.51] — 2026-10-27

The self-check surface now has 304 differential rows: 299 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. A discarded literal
integral `$sformatf` call now reuses the expression converter and lowers to an
inert statement; dynamic formats and unsupported operands remain loud.

## [0.1.50] — 2026-10-27

The self-check surface now has 303 differential rows: 298 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,746 while
`AssignmentExpression:target` remains 2,852. Literal zero-time queue
histories now lower `$q_exam` codes 2, 4, 5, and 6 to zero, and code 1
tracks current length through static removals; timed and computed histories
remain loud.

## [0.1.49] — 2026-10-27

The self-check surface now has 302 differential rows: 297 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,286 clean files and 16,706 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,747 while
`AssignmentExpression:target` remains 2,852. Literal FIFO/LIFO queue histories
now lower `$q_remove` payloads to scalar job, inform, and status writes;
dynamic, timed, empty, and other queue operations remain loud.

## [0.1.48] — 2026-10-27

The self-check surface now has 301 differential rows: 296 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,274 clean files and 16,718 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,759 and `CallExpression`
falls to 2,739. Literal one-integral-operand `$sformatf` expressions now
render `%b/%h/%o/%d` and their uppercase equivalents through the packed-string
evaluator; dynamic formats, other conversions, and nonintegral operands remain
loud.

## [0.1.47] — 2026-10-27

The self-check surface now has 300 differential rows: 295 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,273 clean files and 16,719 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,759. Queue status calls
now admit source-pure named operands after one prior literal assignment, which
unlocks the `$q_exam` statistic-code fixture; computed and stateful queue forms
remain loud.

## [0.1.46] — 2026-10-27

The self-check surface now has 299 differential rows: 294 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,272 clean files and 16,720 partial files; `CallExpression` falls
to 2,750. Value-position `$q_full` now follows source-pure literal queue
history when prior status checks precede the first query; later status reads
and queue payload operations remain loud.

## [0.1.45] — 2026-10-27

The self-check surface now has 298 differential rows: 293 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,270 clean files and 16,722 partial files; `CallExpression` falls
to 2,752. Direct blocking scalar assignments from `$dist_uniform` now accept
signed literal 32-bit bounds, including negative-only and zero-crossing
ranges, with explicit seed updates; computed and value-position forms remain
loud.

## [0.1.44] — 2026-10-27

The self-check surface now has 295 differential rows: 290 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 95 MATCH and 123 REFUSE. The 22,059-path corpus
moves to 5,254 clean files and 16,738 partial files, with
`AssignmentExpression:target` at 2,852. A bounded `$dist_uniform(seed, 0,
1000)` assignment now updates a 32-bit seed and one dynamic fixed-array cell;
other random calls, bounds, storage, and effectful selectors remain loud.

## [0.1.43] — 2026-10-27

The self-check surface now has 282 differential rows: 277 matches, zero
disagreements, and 5 recorded refusals. The grammar census has 218 pyslang
syntax witnesses: 95 MATCH and 123 REFUSE. The 22,059-path corpus remains at
5,240 clean files and 16,752 partial files, with `AssignmentExpression:target`
at 2,853 and `ExpressionStatement:CallExpression` at 2,775. The
discarded-result slice now covers numeric enum queries, fixed-array reductions
and locator queries (including source-pure `with` clauses), literal string
transformations, and empty queue/dynamic-array deletes; stateful and effectful
forms remain loud.

## [0.1.42] — 2026-10-26

The self-check surface now has 276 differential rows: 271 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`AssignmentExpression:target` at 2,853 and
`ExpressionStatement:CallExpression` at 2,775. The discarded-result slice
now covers zero-size queue/array/string queries, ASCII string queries and
`atoreal()`, pre-trigger `event.triggered()`, and enum `.name()` calls; each
reuses the value converter and leaves dynamic or stateful forms loud.

## [0.1.41] — 2026-10-26

The self-check surface now has 271 differential rows: 266 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`AssignmentExpression:target` at 2,853 and
`ExpressionStatement:CallExpression` at 2,775. Discarded statement calls now
cover integral signing casts, literal time-scale queries, invalid literal
`$fopen` modes, and empty associative-array count and endpoint queries; each
reuses the value-position proof and keeps dynamic or stateful forms loud.

## [0.1.40] — 2026-10-26

The self-check surface now has 266 differential rows: 261 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Admitted discarded `$clog2`
queries now erase their pure result after the existing operand checks; malformed
and effectful forms remain loud.

## [0.1.39] — 2026-10-26

The self-check surface now has 261 differential rows: 256 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Discarded literal
`$countbits`, `$countones`, `$onehot`, `$onehot0`, and `$isunknown` calls now
erase without represented state effects; dynamic operands remain loud.

## [0.1.38] — 2026-10-26

The self-check surface now has 260 differential rows: 255 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Discarded valid
`$bits(expr)` calls now erase without evaluating their expression, as required
by IEEE 1800; value-returning and malformed forms remain loud.

## [0.1.37] — 2026-10-26

The self-check surface now has 259 differential rows: 254 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. A discarded valid
`$typename(expr)` call now erases without evaluating its expression, as required
by IEEE 1800; value-returning and malformed forms remain loud.

## [0.1.36] — 2026-10-26

The self-check surface now has 258 differential rows: 253 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with `CallExpression`
at 2,771. The literal predefined-stdout `$ftell(32'h8000_0001)` error result
now lowers to signed `-1`; dynamic descriptors and file-position state remain
loud.

## [0.1.35] — 2026-10-26

The self-check surface now has 257 differential rows: 252 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
measures 5,240 clean files and 16,752 partial files, with `CallExpression`
falling from 2,772 to 2,771. The literal predefined-stdout
`$fseek(32'h8000_0001, 0, 0)` error result now lowers to signed `-1`; dynamic
descriptors, offsets, whence values, and other file operations remain loud.

## [0.1.34] — 2026-10-26

The self-check surface now has 256 differential rows: 251 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
measures 5,239 clean files and 16,753 partial files, with
`CallExpression` falling from 2,778 to 2,772. Literal-only
`$coverage_control`, `$coverage_get`, `$coverage_get_max`, `$coverage_merge`,
and `$coverage_save` calls return the standard `SV_COV_NOCOV` zero in the
empty self-check coverage database; dynamic scopes and coverage constructs
remain loud.

## [0.1.33] — 2026-10-26

The self-check surface now has 255 differential rows: 250 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
moves to 5,233 clean files and 16,758 partial files, with
`AssignmentExpression:target` falling to 2,853. Pure conditional net drivers
with literal arms and one direct literal source initialization now snapshot
before static per-bit resolution; changing, effectful, unknown, and
strength-sensitive drivers remain loud.

## [0.1.32] — 2026-10-26

The self-check surface now has 254 differential rows: 249 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
moves to 5,231 clean files and 16,760 partial files, with
`AssignmentExpression:target` falling to 2,855. Fixed packed-net windows fed
by one direct literal source initialization now snapshot before the existing
static per-bit resolver; dynamic, multiply-written, effectful, and
strength-sensitive drivers remain loud.

## [0.1.31] — 2026-10-26

The self-check surface now has 253 differential rows: 248 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic indexed slices over nested packed elements by scaling
the runtime outer label in whole inner-element chunks; effectful, aggregate,
and unsupported forms remain loud.

## [0.1.30] — 2026-10-26

The self-check surface now has 252 differential rows: 247 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic `+:` and `-:` reads and targets on noncanonical one-bit
packed vectors through normalized flat windows; simple dynamic ranges,
effectful, unsigned, aggregate, and unsupported forms remain loud; partial
reads retain the selected evaluator boundary.

## [0.1.29] — 2026-10-26

The self-check surface now has 251 differential rows: 246 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits pure signed dynamic targets on noncanonical one-bit packed
vectors by normalizing their declared labels; unsigned, effectful, aggregate,
and unsupported forms remain loud.

## [0.1.28] — 2026-10-26

The self-check surface now has 250 differential rows: 245 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic indexing of nested packed elements for reads and
blocking targets by scaling the runtime label by the element width; ascending,
descending, aggregate, effectful, and unsupported forms remain loud.

## [0.1.27] — 2026-10-26

The self-check surface now has 249 differential rows: 244 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits dynamic `+:` and `-:` slices inside descending multidimensional
packed cells of bounded fixed arrays, with runtime bases scaled to the flat
cell representation; ascending, aggregate, alias-sensitive, and effectful
forms remain loud.

## [0.1.26] — 2026-10-26

The self-check surface now has 248 differential rows: 243 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits one dynamic selector when reading a bounded multidimensional
integral subarray into a distinct flat row; multiple dynamic, aggregate,
aliased, shape-mismatched, and effectful forms remain loud.

## [0.1.25] — 2026-10-26

The self-check surface now has 247 differential rows: 242 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release extends finite multidimensional subarray copies to one dynamic selector
after a constant prefix; multiple dynamic, aggregate, aliased, and effectful
forms remain loud.

## [0.1.24] — 2026-10-26

The self-check surface now has 246 differential rows: 241 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits dynamic outer subarray copies into bounded multidimensional
integral arrays through guarded flat-cell expansion; multiple dynamic,
aggregate, aliased, and effectful forms remain loud.

## [0.1.23] — 2026-10-26

The self-check surface now has 238 differential rows: 233 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 90 MATCH and 127 REFUSE. The 22,056-path corpus
measures 5,207 clean files, 16,782 partial files, and 67 include skips. This
release adds continuous sources from finite literal bindings, disjoint fixed
array slice copies, unsized one-bit left streams, pure literal integral net
expressions, and one dynamic selector in any dimension of finite multidimensional
arrays. Dynamic, overlapping, aggregate, and otherwise stateful forms remain
loud.

## [0.1.22] — 2026-10-26

The self-check surface now has 232 differential rows: 227 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 90 MATCH and 127 REFUSE. The 22,056-path corpus
measures 5,207 clean files, 16,782 partial files, and 67 include skips. This
release admits exact IEEE-754 `$realtobits` and `$shortrealtobits` conversions
from finite literal-bound real and shortreal variables; dynamic and
control-dependent real storage remains loud.

## [0.1.21] — 2026-10-25

The self-check surface now has 165 differential rows: 161 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,050-path corpus
measures 4,912 clean files, 17,072 partial files, and 66 include skips. This
release admits exact literal dynamic-array `size()` queries, four-state-aware
literal string `atobin()`/`atooct()`/`atohex()` conversions, and default-zero
literal semaphore `try_get` sequences. Dynamic, aliased, invalid, and other
stateful forms remain loud.

## [0.1.20] — 2026-10-25

The self-check surface now has 161 differential rows: 157 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,050-path corpus
measures 4,888 clean files, 17,096 partial files, and 66 include skips. This
release extends source-pure literal string support with assignment-aware
`.len()`, `.atoi()`, `.compare()`, and `.icompare()` results, including exact
decimal scanning and normalized ordering. Dynamic, aliased, non-ASCII, and
stateful string operations remain loud.

## [0.1.19] — 2026-10-25

The self-check surface now has 158 differential rows: 154 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,856 clean files, 17,127 partial files, and 66 include skips. This
release admits the state-free zero-key `semaphore.try_get(0)` result, exact
counts for untouched constructed mailboxes, and source-pure literal puts with
their corresponding unbounded-mailbox `num()` counts. Dynamic, aliased,
bounded, and other stateful mailbox/semaphore operations remain loud.

## [0.1.18] — 2026-10-25

The self-check surface now has 155 differential rows: 151 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,855 clean files, 17,128 partial files, and 66 include skips. This
release extends shallow untagged unpacked-union support with whole-value copies,
equality, conditional selection, compound member updates, and ordinary `case`
subjects, all through the shared flat-cell representation. Tagged, mixed-width,
nested, scheduled, and other aggregate forms remain loud.

## [0.1.17] — 2026-10-24

The self-check surface now has 150 differential rows: 146 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,853 clean files, 17,130 partial files, and 66 include skips. This
release admits direct reads and blocking writes through equal-width integral
members of shallow untagged unpacked unions by flattening them to one aliased
vector cell. Tagged, mixed-width, nested, whole-union, and scheduled forms
remain loud.

## [0.1.16] — 2026-10-24

The self-check surface now has 145 differential rows: 141 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus
measures 4,843 clean files, 17,139 partial files, and 66 include skips. This
release admits source-pure real/time severity arguments and constant formatted
`$sformat`/`$swrite` writes to packed variables and selections; dynamic,
effectful, aggregate, and unsupported formatting forms remain loud.

## [0.1.15] — 2026-10-24

The self-check surface now has 140 differential rows: 136 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,841 clean files, 17,142 partial files, and 66 include skips. This
release admits literal-zero semaphore `get` and `put` calls after a proven
constructor assignment; dynamic and stateful semaphore methods remain loud.

## [0.1.14] — 2026-10-24

The self-check surface now has 135 differential rows: 131 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,833 clean files, 17,149 partial files, and 66 include skips. This release
adds discarded literal `$itor`, `$bitstoreal`, and `$bitstoshortreal` calls,
plus inert handling for the standard-invalid dynamic-array continuous target
and multiple continuous assignments to one variable. Dynamic, effectful, and
stateful forms remain loud.

## [0.1.13] — 2026-10-24

The self-check surface now has 130 differential rows: 126 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus remains
4,829 clean files, 17,153 partial files, and 66 include skips. This release
adds metadata-only `$bits(real)` and `$bits(shortreal)` queries plus exact
literal `$itor` nesting through `$rtoi`, `$realtobits`, and
`$shortrealtobits`. Named, computed, dynamic, and effectful forms remain
loud.

## [0.1.12] — 2026-10-24

The self-check surface now has 126 differential rows: 122 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,829 clean files, 17,153 partial files, and 66 include skips. This release
adds literal-input pure function calls, literal `$rtoi`, `$realtobits`, and
`$shortrealtobits` conversions, plus their discarded-result statement forms.
Dynamic, effectful, and stateful forms remain loud.

## [0.1.11] — 2026-10-24

The self-check surface now has 121 differential rows: 117 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,816 clean files, 17,166 partial files, and 66 include skips. This release
adds literal-strength continuous-driver slices, inert literal assertion-control
calls, and empty 2-state queue initializers. Dynamic, effectful, and
stateful forms remain loud.

## [0.1.10] — 2026-10-24

The self-check surface now has 114 differential rows: 110 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 213 pyslang
syntax witnesses: 82 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,810 clean files, 17,172 partial files, and 66 include skips. This release
adds literal continuous drivers for one-dimensional fixed-unpacked net-array
cells, reusing flat `Net` cells and the existing time-zero four-state
resolution path. Whole-array, dynamic, multidimensional, timed, and effectful
forms remain loud.

## [0.1.9] — 2026-10-24

The self-check surface now has 109 differential rows: 105 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 213 pyslang
syntax witnesses: 82 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,806 clean files, 17,176 partial files, and 66 include skips. This release
adds literal whole-net and selected packed continuous drivers, typed enum
defaults in packed-struct array patterns, and time-zero resolution for static
literal wire-driver sets. Dynamic, variable, selected-resolution, timed, and
effectful forms remain loud.

## [0.1.8] — 2026-10-24

The self-check surface now has 104 differential rows: 100 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 212 pyslang
syntax witnesses: 81 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,791 clean files, 17,191 partial files, and 66 include skips. This release
adds constant indexed streaming targets, discarded literal-return calls,
inert literal `$timeformat`, literal-initialized procedural floating
declarations, and exact `.len()` queries on unchanged literal strings.

## [0.1.7] — 2026-10-24

The self-check surface now has 99 differential rows: 95 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,783 clean files, 17,197 partial files, and 66 include skips.
This release adds zero-size queries after explicit empty writes and `new[0]`,
literal-return zero-argument functions, inert monitor toggles without a
registration, and stdout-directed `$fwrite` with its no-newline behavior.

## [0.1.6] — 2026-10-24

The self-check surface now has 94 differential rows: 90 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,766 clean files, 17,214 partial files, and 66 include skips.
This release adds pure real system-function writes, zero-time `$stime` and
integral `$realtime` queries, zero-size queue and dynamic-array queries, and
zero-length queries on inert strings.

## [0.1.5] — 2026-10-24

The self-check surface now has 89 differential rows: 85 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,752 clean files, 17,228 partial files, and 66 include skips. This
release adds opaque `process::self()` writes and direct null writes for opaque
handles, plus post-incremented fixed-array index writes with the required
write-before-update ordering.

## [0.1.4] — 2026-10-24

The self-check surface now has 84 differential rows: 80 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 211 pyslang
syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,747 clean files, 17,233 partial files, and 66 include skips. Recent admitted
forms include time-zero `$realtime` writes, literal-only string concatenation
and replication writes, and empty queue and dynamic-array literal writes.

## [0.1.3] — 2026-10-24

The self-check surface now has 76 differential rows: 72 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 209 pyslang
syntax witnesses: 78 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,745 clean files, 17,235 partial files, and 66 include skips. Recent admitted
forms include opaque class-handle declarations and null writes, empty
subroutine calls, pure floating literal writes, and default values from empty
functions.

## [0.1.2] — 2026-10-23

The self-check surface now has 71 differential rows: 67 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 206 pyslang
syntax witnesses: 75 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,689 clean files, 17,291 partial files, and 66 include skips. Recent admitted
forms include literal time-scale queries and inert literal `$sdf_annotate`
calls, alongside constant dynamic-array cells and deferred pure `$strobe`
arguments.

## [0.1.1] — 2026-10-23

The self-check surface now has 66 differential rows: 62 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 204 pyslang
syntax witnesses: 73 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,654 clean files, 17,326 partial files, and 66 include skips. Recent admitted
forms include elaboration-constant indexed packed targets, out-of-bounds
struct defaults, packed-struct streaming sources, and constant-range
streaming `with` targets.

## [0.1.0] — 2026-10-23

The first public SV self-check prerelease records the executable surface and
its measured coverage. The pinned differential corpus has 57 rows: 53 matches,
zero disagreements, and 4 recorded refusals. The grammar census has 202
pyslang syntax witnesses: 71 MATCH and 131 REFUSE. On the 22,046-file
sv-tests-2 snapshot, the extractor reports 4,617 clean files, 17,363 partial
files, and 66 include skips.

The self-check surface now includes integral unpacked-struct copies and
patterns, finite multidimensional array patterns and copies, packed windows in
selected array cells, recursive right-streaming unpack into fixed arrays, and
fixed-slice left-streaming targets. Unsupported aggregate, dynamic, timed, and
effectful forms continue to fail loudly with their construct name.
