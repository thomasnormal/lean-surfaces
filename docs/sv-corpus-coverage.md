# SV corpus coverage census — sv-tests-2 vs the M0 extractor

Axis-1/2 coverage of the M0 tier (`docs/sv-design-m0.md`, envelope schema
`sv-0.1`) measured on real code: every `.sv` file under
`<corpus>/tests/chapter-*/`
(the IEEE 1800-2023 conformance corpus, self-checking PASS/FAIL tests), run
through the `extractors/sv/extract.py` pipeline **in-process** by
`extractors/sv/census.py`.

Reproduce (from the repo root):

```
python3.12 extractors/sv/census.py --corpus /path/to/tests            # full census
python3.12 extractors/sv/census.py --corpus /path/to/tests --recheck  # determinism check
```

Machine-readable results: `harness/sv/conformance/census.json`
(per-file records + this document's aggregates). The current committed summary
is the **2026-10-28** snapshot below, measured with Python 3.12 and pyslang 11;
the dated sections retain their original measurement denominators.

The committed summary uses a portable corpus-layout placeholder, not a
host-local checkout path. Supply the actual test directory explicitly.

The executable self-check differential matrix and pyslang grammar census are
published separately in [`docs/sv-coverage.md`](sv-coverage.md).

## Multidimensional fixed-array self-copies — 2026-10-28

An exact blocking self-copy of a multidimensional fixed unpacked integral array
now erases through the existing flattened-cell representation. Nonblocking,
partial, dynamic, and effectful copies remain loud because they need a
publication or aggregate-store contract. The `fixed_array_nested_self_copy`
fixture supplies the differential row and Lean receipt. The external corpus
checkout is unavailable, so the committed snapshot remains **5,602 clean /
16,390 partial** over 22,059 paths with 67 include skips; differential coverage
grows **372/366/0/6 → 373/367/0/6**.

## Conditional fixed-array self-aliases — 2026-10-28

The legacy extractor now lowers a blocking whole-array conditional assignment
with a destination self-alias branch to one source-preserving ternary per
fixed-array cell. Nonblocking self-alias branches remain loud because
publication is scheduler-visible. The `fixed_array_conditional_self_alias`
fixture supplies the differential row and Lean receipt. The external corpus
checkout is unavailable, so the committed snapshot remains **5,602 clean /
16,390 partial** over 22,059 paths with 67 include skips; differential coverage
grows **371/365/0/6 → 372/366/0/6**.

## Conditional unpacked-struct self-aliases — 2026-10-28

The legacy extractor now lowers a blocking whole-struct conditional assignment
with a destination self-alias branch to one source-preserving ternary per
integral field. Nonblocking self-alias branches remain loud because
publication is scheduler-visible. The
`unpacked_struct_conditional_self_alias` fixture supplies the differential row
and Lean receipt. The external corpus checkout is unavailable, so the committed
snapshot remains **5,602 clean / 16,390 partial** over 22,059 paths with 67
include skips; differential coverage grows **370/364/0/6 → 371/365/0/6**.

## Unpacked-struct self-copies — 2026-10-28

The legacy extractor now erases an exact blocking self-copy of a flattened
integral unpacked struct. Nonblocking self-copies remain loud because
publication is scheduler-visible. The `unpacked_struct_self_copy` fixture
supplies the differential row and Lean receipt. The external corpus checkout
is unavailable, so the committed snapshot remains **5,602 clean / 16,390
partial** over 22,059 paths with 67 include skips; differential coverage grows
**369/363/0/6 → 370/364/0/6**.

## Fixed-array unpacked-struct self-copies — 2026-10-28

The legacy extractor now erases an exact blocking self-copy of a
one-dimensional fixed unpacked array whose leaves are integral unpacked
structs. Nonblocking self-copies remain loud because publication is
scheduler-visible. The `fixed_array_struct_self_copy` fixture supplies the
differential row and Lean receipt. The external corpus checkout is unavailable,
so the committed snapshot remains **5,602 clean / 16,390 partial** over 22,059
paths with 67 include skips; differential coverage grows **368/362/0/6 →
369/363/0/6**.

## Multiple integral `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays a `$sformatf` assignment containing at least
two integral conversions and only literal ASCII text. Dynamic or nested
operands, unsupported conversion markers, timed forms, and nonblocking writes
remain loud. The `string_sformatf_multiple_integral_assignment` fixture
supplies the differential row and Lean receipt. The fresh 22,059-path census
moves **5,601 → 5,602 clean / 16,391 → 16,390 partial** with 67 include skips
and `AssignmentExpression:target` falls **2,783 → 2,782**; differential
coverage grows **367/361/0/6 → 368/362/0/6**.

## Escaped-percent integral `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays a `$sformatf` assignment containing one
escaped percent (`%%`), one integral conversion, and literal ASCII text.
Multiple conversions or escaped percents, dynamic operands, timed forms, and
nonblocking writes remain loud. The
`string_sformatf_percent_literal_assignment` fixture supplies the differential
row and Lean receipt. The fresh 22,059-path census moves **5,600 → 5,601 clean
/ 16,392 → 16,391 partial** with 67 include skips and
`AssignmentExpression:target` falls **2,784 → 2,783**; differential coverage
grows **366/360/0/6 → 367/361/0/6**.

## Integral ASCII-code `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays `%s/%S` `$sformatf` assignments from known
integral literals as packed printable ASCII bytes when the width is a multiple
of eight. Unknown, non-byte-width, NUL/control, dynamic, timed, and nonblocking
forms remain loud. The `string_sformatf_ascii_codes_assignment` fixture
supplies the differential row and Lean receipt. The fresh 22,059-path census
moves **5,599 → 5,600 clean / 16,393 → 16,392 partial** with 67 include skips
and `AssignmentExpression:target` falls **2,785 → 2,784**; differential
coverage grows **365/359/0/6 → 366/360/0/6**.

## Literal-prefix/suffix integral `$sformatf` assignments — 2026-10-28

The legacy extractor now replays a `$sformatf` assignment containing one
integral conversion and only literal ASCII text around it. Decimal,
hexadecimal, binary, octal, and character forms are covered; dynamic
operands, multiple conversions, escaped-percent formats, timed forms, and
nonblocking writes remain loud. The
`string_sformatf_integral_wrapper_assignment` fixture supplies the differential
row and Lean receipt. The fresh 22,059-path census moves **5,597 → 5,599
clean / 16,395 → 16,393 partial** with 67 include skips and
`AssignmentExpression:target` falls **2,787 → 2,785**; differential coverage
grows **364/358/0/6 → 365/359/0/6**.

## Zero-width string `$sformatf` assignments — 2026-10-28

The legacy extractor now replays `%0s/%0S` `$sformatf` assignments into
strings for ASCII literals and source-pure string histories, retaining one
literal prefix and suffix around the conversion. Dynamic or non-ASCII
operands, additional conversions, timed forms, and nonblocking writes remain
loud. The `string_sformatf_zero_width_string_assignment` fixture supplies the
differential row and Lean receipt. The fresh 22,059-path census moves **5,596
→ 5,597 clean / 16,396 → 16,395 partial** with 67 include skips and
`AssignmentExpression:target` falls **2,788 → 2,787**; differential coverage
grows **363/357/0/6 → 364/358/0/6**.

## Zero-width binary and octal `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays `%0b/%0B` and `%0o/%0O` `$sformatf`
assignments into strings for known 0/1 integral literals, using minimal binary
and octal text. Unknown or dynamic operands, timed forms, and nonblocking writes
remain loud. The `string_sformatf_zero_width_assignment` fixture supplies the
differential row and Lean receipt. The committed census remains **5,584 clean /
16,414 partial** with 67 include skips and `AssignmentExpression:target` at
**2,810**; differential coverage grows **362/356/0/6 → 363/357/0/6**.

## Literal decimal `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays decimal `$sformatf` assignments (`%d`, `%D`,
`%0d`, and `%0D`) into strings for known integral literals. Unknown or dynamic
operands, timed forms, and nonblocking writes remain loud. The
`string_sformatf_decimal_assignment` fixture supplies the differential row and
Lean receipt. The committed census remains **5,584 clean / 16,414 partial**
with 67 include skips and `AssignmentExpression:target` at **2,810**;
differential coverage grows **361/355/0/6 → 362/356/0/6**.

## Literal octal `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays `$sformatf("%o", ...)` and
`$sformatf("%O", ...)` assignments into strings for known 0/1 integral
literals, retaining the exact lower-case octal text. Unknown or dynamic
operands, timed forms, and nonblocking writes remain loud. The
`string_sformatf_octal_assignment` fixture supplies the differential row and
Lean receipt. The committed census remains **5,584 clean / 16,414 partial**
with 67 include skips and `AssignmentExpression:target` at **2,810**;
differential coverage grows **360/354/0/6 → 361/355/0/6**.

## Literal binary `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays `$sformatf("%b", ...)` and
`$sformatf("%B", ...)` assignments into strings for known 0/1 integral
literals, retaining their packed width. Unknown or dynamic operands, timed
forms, and nonblocking writes remain loud. The
`string_sformatf_binary_assignment` fixture supplies the differential row and
Lean receipt. The committed census remains **5,584 clean / 16,414 partial**
with 67 include skips and `AssignmentExpression:target` at **2,810**;
differential coverage grows **359/353/0/6 → 360/354/0/6**.

## Literal character `$sformatf` string assignments — 2026-10-28

The legacy extractor now replays `$sformatf("%c", ...)` and
`$sformatf("%C", ...)` assignments into strings for known integral literals,
using the low-byte ASCII character. Unknown, zero, non-ASCII/control, dynamic,
timed, and nonblocking forms remain loud. The
`string_sformatf_char_assignment` fixture supplies the differential row and
Lean receipt. The committed census remains **5,584 clean / 16,414 partial**
with 67 include skips and `AssignmentExpression:target` at **2,810**;
differential coverage grows **358/352/0/6 → 359/353/0/6**.

## Source-pure string `$sformatf` assignments — 2026-10-28

The legacy extractor now replays `$sformatf("%s", ...)` and
`$sformatf("%S", ...)` assignments into strings for ASCII literals and
source-pure named-string histories. Dynamic operands, unsupported formats,
timed forms, and nonblocking writes remain loud. The
`string_sformatf_string_assignment` fixture supplies the differential row and
Lean receipt. The committed census remains **5,584 clean / 16,414 partial**
with 67 include skips and `AssignmentExpression:target` at **2,810**;
differential coverage grows **357/351/0/6 → 358/352/0/6**.

## Literal `$sformatf` string assignments — 2026-10-28

The existing literal formatter now supplies source-pure ASCII history for
blocking string assignments of `%h`/`%H` results from integral literals. Later
string comparisons and diagnostics observe the exact hexadecimal text;
dynamic operands, other formats, timed forms, and nonblocking writes remain
loud. The `string_sformatf_literal_assignment` fixture supplies the
differential row and Lean receipt.

The fresh 22,065-path census moves **5,582 → 5,584 clean / 16,416 → 16,414
partial** with 67 include skips; `AssignmentExpression:target` falls
**2,812 → 2,810**. Differential coverage grows **356/350/0/6 → 357/351/0/6**
with no disagreements; grammar coverage remains **218/97/121**.

## Literal string-index character assignments — 2026-10-28

The legacy extractor now replays a constant-index string-byte assignment from
a one-byte ASCII literal through the receiver's direct literal history. Later
comparisons and `%0s` diagnostics see the updated value; dynamic, out-of-range,
multi-byte, timed, and nonblocking forms remain loud. The
`string_index_literal_character` fixture supplies the differential row and
Lean receipt.

The fresh 22,065-path census moves **5,580 → 5,582 clean / 16,418 → 16,416
partial** with 67 include skips; `AssignmentExpression:target` falls
**2,814 → 2,812**. Differential coverage grows **355/349/0/6 → 356/350/0/6**
with no disagreements; grammar coverage remains **218/97/121**.

## NUL string-literal character assignments — 2026-10-28

The legacy extractor now erases a blocking assignment of the one-byte NUL
string literal (`"\\0"`) to a constant-indexed string byte, matching the
existing integral-zero rule in IEEE 1800-2023 §6.16. Dynamic indices, nonzero
bytes, timed forms, and nonblocking writes remain loud. The
`string_null_literal_character` fixture supplies the differential row and
Lean receipt.

The fresh 22,065-path census moves **5,579 → 5,580 clean / 16,419 → 16,418
partial** with 67 include skips; `AssignmentExpression:target` falls
**2,815 → 2,814**. Differential coverage grows **354/348/0/6 → 355/349/0/6**
with no disagreements; grammar coverage remains **218/97/121**.

## Literal queue write followed by empty concatenation — 2026-10-28

A blocking literal queue write followed by an empty queue concatenation is now
admitted when the only later observation is `.size()`. The earlier opaque
write is erased because the empty assignment replaces it before the query;
dynamic or nonliteral writes, element reads, pushes, and other observations
remain loud. The `queue_literal_then_empty_concat` fixture supplies the
differential row and Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**351/345/0/6 → 352/346/0/6**, while grammar coverage remains **218/97/121**.

## Source-pure string transformation assignments — 2026-10-28

Blocking `string.toupper()`, `string.tolower()`, and bounded `string.substr()`
assignments are now admitted from a direct ASCII literal history, with the
transformed value used by later string comparisons. Dynamic, aliased, timed,
nonblocking, and non-ASCII forms remain loud. The `string_case_assignment` and
`string_substr_assignment` fixtures supply differential rows and Lean receipts.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**352/346/0/6 → 354/348/0/6**, while grammar coverage remains **218/97/121**.

## Power self-check differential rows — 2026-10-28

The unsigned, signed, and zero-to-negative integral power fixtures are now
included in the executable differential matrix. Each matches its committed
`PASS` declaration. The zero-to-negative fixture retains the documented
IEEE 1800-2023 §11.4.3 Table 11-4 and Icarus all-x result, while the separate
reference run returns zero; this is recorded as a divergence rather than a
reference confirmation.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**348/342/0/6 → 351/345/0/6**, while grammar coverage remains **218/97/121**.

## Fixed-array subarray self-copies — 2026-10-28

An exact blocking self-copy of one constant subarray of a fixed
multidimensional integral array now lowers to `Empty`. Nonblocking,
overlapping, dynamic, timed, and nonintegral forms remain loud because their
publication or storage behavior is not erased. The
`fixed_array_subarray_self_copy` fixture supplies the differential row and
Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**347/341/0/6 → 348/342/0/6**, while grammar coverage remains **218/97/121**.

## Disjoint fixed-array subarray copies — 2026-10-28

A blocking copy between two constant subarrays of one fixed multidimensional
integral array is admitted when the flattened source and destination cell
sets are disjoint and have equal widths and lengths. The extractor lowers the
copy to cellwise writes while preserving the complete source snapshot;
overlapping, dynamic, timed, nonblocking, and nonintegral forms remain loud.
The `fixed_array_disjoint_subarray_copy` fixture supplies the differential
row and Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**346/340/0/6 → 347/341/0/6**, while grammar coverage remains **218/97/121**.

## Literal-return function operands in dynamic-array concatenations — 2026-10-28

An unpacked concatenation assigned to a scalar-integral dynamic array may now
contain a zero-argument function whose complete body assigns one integral
literal through the implicit function name. The call is materialized as one
sampled cell; state-dependent, effectful, and otherwise unsupported function
operands remain loud. The `dynamic_array_concat_literal_function` fixture
supplies the differential row and Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified census delta is claimed. Differential coverage grows
**345/339/0/6 → 346/340/0/6**, while grammar coverage remains **218/97/121**.

## Source-pure fixed-array continuous copies — 2026-10-28

The legacy extractor now lowers a whole-array continuous assignment from a
one-dimensional fixed-unpacked variable with a complete literal declaration
initializer and no later writes. It expands the source snapshot into the
existing flat destination cells, retaining ordinal correspondence across
opposite range directions. Mutable, net, sliced, dynamic, timed, and
nonblocking sources remain at the continuous-driver boundary. The
`static_fixed_array_continuous_copy` fixture supplies the differential row and
Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified corpus delta is claimed. Differential coverage grows
**342/336/0/6 → 343/337/0/6**, while grammar coverage remains **218/97/121**.

## Ignored string null-character assignments — 2026-10-28

The legacy extractor now lowers a blocking assignment of literal integral
zero to a constant-indexed string byte to `Empty`, matching IEEE 1800-2023
§6.16's rule that strings cannot contain the special null character. Dynamic
indices, nonzero values, timed forms, and nonblocking writes remain at
`AssignmentExpression:target`. The `string_null_character` fixture supplies
the differential row and Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified corpus delta is claimed. Differential coverage grows
**343/337/0/6 → 344/338/0/6**, while grammar coverage remains **218/97/121**.

## Source-pure string replication writes — 2026-10-28

Constant string replications and concatenations now resolve named-string
operands whose earlier history consists only of unconditional blocking ASCII
literal writes. The opaque string target is erased, and a matching `%s`
diagnostic receives the exact packed bytes. Uninitialized, computed,
control-dependent, timed, nonblocking, and non-ASCII histories remain loud.
The existing `replication/dynamic_string` fixture supplies the differential
row and Lean receipt.

The external sv-tests-2 checkout is unavailable, so the committed census
remains **5,401 clean / 16,597 partial** over 22,065 paths with 67 include
skips; no unverified corpus delta is claimed. Differential coverage grows
**344/338/0/6 → 345/339/0/6**, while grammar coverage remains **218/97/121**.

## One-dimensional fixed-array `%p` diagnostics — 2026-10-27

Direct one-dimensional fixed integral arrays can now be passed to `%p`
diagnostics. The extractor expands the value to the existing flattened cells
in declared index order, and the self-check renderer emits the aggregate text
without adding aggregate storage. Nested, dynamic, effectful, and other-format
aggregate values remain loud. The `array_named_display` fixture supplies the
differential row and Lean receipt.

The chapter-only census moves **5,396 clean / 16,602 partial → 5,401 clean /
16,597 partial** over **22,065** files with 67 include skips;
`NamedValueExpression:2state` falls **1,473 → 1,462**. Differential coverage
grows **333/327/0/6 → 334/328/0/6** with no disagreements; grammar coverage
remains **218/97/121**.

## Source-pure string equality and relational comparisons — 2026-10-27

String `==`, `!=`, `===`, `!==`, `<`, `<=`, `>`, and `>=` now lower to exact
one-bit literals when both operands are direct ASCII literals or named strings
whose earlier history contains only unconditional blocking ASCII literal
writes. Computed, control-dependent, timed, nonblocking, dynamic, and
non-ASCII histories remain loud. The `string_comparison_history` fixture
supplies the differential row and Lean receipt.

The chapter-only census moves **5,384 clean / 16,614 partial → 5,396 clean /
16,602 partial** over **22,065** files with 67 include skips;
`NamedValueExpression:2state` falls **1,488 → 1,473**, while the leading
blockers remain unchanged. Differential coverage grows **332/326/0/6 →
333/327/0/6** with no disagreements; grammar coverage remains **218/97/121**.

## Explicit source-pure real-to-integral casts — 2026-10-27

Explicit casts from a finite real or short-real source to an integral target
now lower to a nearest-integer literal, with ties away from zero, followed by
the existing target-width conversion. Direct real literals and source-ordered
direct blocking literal histories are admitted; computed, control-dependent,
timed, non-finite, and dynamic real sources remain loud. The
`real_integral_cast` fixture supplies the differential row and Lean receipt.

The chapter-only census moves **5,359 clean / 16,639 partial → 5,384 clean /
16,614 partial** over **22,065** files with 67 include skips;
`ConversionExpression:Explicit` falls **34 → 9**, while the leading blockers
remain unchanged. Differential coverage grows **331/325/0/6 → 332/326/0/6**
with no disagreements; grammar coverage remains **218/97/121**.

## Source-ordered pure static dependencies — 2026-10-27

Static locals now preserve declaration order within one procedural scope, so a
later closed pure initializer may read an earlier static declaration. The
`static_dependency_initializer` fixture supplies the differential row. The
chapter-only census moves **5,331 clean / 16,667 partial → 5,359 clean /
16,639 partial** over **22,065** files with 67 include skips;
`StaticLocal:initializer` falls **168 → 140** while the leading blockers stay
unchanged.

## Named literal-history literal-return functions — 2026-10-27

The self-check surface now accepts a named integral argument to a one-literal
return function after source order proves direct blocking literal history.
`literal_function_named_history` is a repository fixture outside the
chapter-only walk, so the pinned **22,065-file** census remains **5,331 clean /
16,667 partial** with 67 include skips and unchanged leading blockers.
Differential coverage grows **329/323/0/6 → 330/324/0/6**; grammar coverage
remains **218/97/121**.

## Named literal-history `$timeformat` — 2026-10-27

`$timeformat` now accepts named integral unit, precision, and width arguments
after source order proves direct blocking literal histories, provided the
source has no `%t` consumer. The self-check state has no time-format register,
so this validated configuration call is erased; `%t` consumers, computed,
control-dependent, timed, nonblocking, and dynamic forms remain loud. The
`timeformat_named_history` fixture supplies the differential row. This
root-level witness is outside the chapter-only census, which remains
**22,065 files, 5,331 clean / 16,667 partial** with 67 include skips and
`ExpressionStatement:CallExpression` at **2,718**. Differential coverage
grows **328/322/0/6 → 329/323/0/6**; grammar remains **218/97/121**.

## Named literal-history `$assertcontrol` — 2026-10-27

`$assertcontrol` now accepts integral arguments after source order proves that
their declarations and all earlier writes are direct blocking literals in the
time-zero initial history. The self-check envelope has no assertion-control
register, so the validated call is erased; computed, control-dependent, timed,
nonblocking, and dynamic arguments remain loud. The
`assertcontrol_named_history` fixture supplies the differential row. This
root-level witness is outside the chapter-only census, which remains
**22,065 files, 5,331 clean / 16,667 partial** with 67 include skips and
`ExpressionStatement:CallExpression` at **2,718**. Differential coverage
grows **327/321/0/6 → 328/322/0/6**; grammar remains **218/97/121**.

## Discarded bit queries over named literal history — 2026-10-27

The statement-position bit queries `$countbits`, `$countones`, `$onehot`,
`$onehot0`, and `$isunknown` now accept named integral operands after the
extractor proves a declaration and all earlier writes are direct blocking
literal assignments in the time-zero initial history. Their discarded results
are erased; computed, control-dependent, timed, nonblocking, and dynamic
histories remain loud. The `bit_query_named_history` fixture supplies the
differential row. The witness is outside the chapter-only corpus walk, so the
current **22,065-file** snapshot remains **5,331 clean / 16,667 partial** with
67 include skips and `ExpressionStatement:CallExpression` at **2,718**.
Differential coverage grows **326/320/0/6 → 327/321/0/6**; grammar coverage
remains **218/97/121**.

## Timed literal `$q_exam` statistics — 2026-10-27

The extractor now replays a single straight-line initial process with literal
queue operations and empty literal delays. Statistic codes 2, 4, 5, and 6 use
the resulting tick timeline for mean interarrival, shortest completed wait,
longest current wait, and average completed wait. The source must have one
initial process, literal queue IDs or one direct prior literal ID assignment,
successful scalar-literal additions, nonempty scalar removals, and direct
output lvalues; dynamic delays, overflow, branches, extra processes, and
computed or aliased histories remain loud.

The four timed sv-tests-2 witnesses move the statement-call blocker from
**2,722 to 2,718**. The current pinned chapter-only walk has **22,065** files:
**5,331 clean / 16,667 partial** with 67 include skips (the previous committed
snapshot had 22,064 files, so one upstream partial file also arrived). The
time-zero differential matrix is unchanged at **326 rows / 320 matches / 0
disagreements / 6 recorded refusals**; the timed fixture is checked by the
separate `q_exam_timed_statistics` receipt because the self-check runner is
time-zero-only. Grammar coverage remains **218 / 97 / 121**.

## Time-zero `$realtime` conversions — 2026-10-27

The exact real-conversion paths now fold `$rtoi($realtime)`,
`$realtobits($realtime)`, and `$shortrealtobits($realtime)` to zero in an
untimed `initial` process. Continuous, always, delayed/event/waiting, direct
real-storage, and other elapsed-time forms remain loud. The
`realtime_conversion_calls` fixture supplies the differential row and Lean
receipt.

The chapter-only census remains **5,327 clean / 16,670 partial** (67 include
skips), while `CallExpression` falls **2,655 → 2,648**. The witness itself is
outside the committed corpus walk.
Differential coverage grows **325/319/0/6 → 326/320/0/6** with no
disagreements; grammar remains **218/97/121**.

## Source-pure named-integral `$itor` — 2026-10-27

The exact real-conversion slices now accept `$itor(named_integral)` after a
declaration or earlier direct blocking literal assignment. `$rtoi`,
`$realtobits`, and `$shortrealtobits` consume the folded value without adding
real storage; computed, control-dependent, timed, nonblocking, dynamic, and
standalone real uses remain loud. The `itor_named_integral_history` fixture
supplies the differential row and Lean receipt.

The chapter-only census snapshot remains **5,327 clean / 16,670 partial** (67
include skips), because this witness is outside the committed corpus walk.
Differential coverage grows **324/318/0/6 → 325/319/0/6** with no
disagreements; grammar remains **218/97/121**.

## Source-pure named-real `$rtoi` — 2026-10-27

`$rtoi` now accepts a named real or short-real whose declaration and prior
direct blocking assignments are all finite literals. Decimal truncation toward
zero remains exact without modeling floating storage; computed, control-
dependent, timed, nonblocking, dynamic, and out-of-range histories remain
loud. The `rtoi_named_real_history` fixture supplies the differential row and
Lean receipt.

The chapter-only census snapshot remains **5,327 clean / 16,670 partial** (67
include skips), because this witness is outside the committed corpus walk.
Differential coverage grows **323/317/0/6 → 324/318/0/6** with no
disagreements; grammar remains **218/97/121**.

## Mailbox `try_peek()` type mismatch — 2026-10-27

An untyped mailbox with one scalar integral literal now admits
`try_peek(destination)` when the destination type is not equivalent to the
message type. IEEE 1800-2023 §15.4.8 makes the result negative without
consuming the mailbox or writing the destination, so this slice needs no
mailbox object or scheduler state. Aliases, dynamic or multiple histories,
equivalent types, and other mailbox methods remain loud. The
`mailbox_try_peek_type_mismatch` fixture supplies the differential row and
Lean receipt.

The 22,064-path census moves **5,326 → 5,327 clean / 16,671 → 16,670
partial** (67 include skips); `CallExpression` falls **2,656 → 2,655** while
`ExpressionStatement:CallExpression` remains **2,722**. Differential coverage
grows **322/316/0/6 → 323/317/0/6** with no disagreements; grammar remains
**218/97/121**.

## Source-pure variable bounds for `$dist_uniform` — 2026-10-27

The scalar seeded distribution lowering now resolves each 32-bit signed bound
from one earlier direct blocking literal assignment in the same initial
process. This admits the root-level §18.13.3 bounded-loop witness without
introducing mutable bound storage into the flat state. Computed, reassigned,
timed, nonblocking, non-32-bit, and value-position random forms remain loud.
The `dist_uniform_variable_bounds` fixture supplies the self-check and Lean
receipt.

The committed chapter-only 22,064-path census remains **5,326 clean / 16,671
partial** (67 include skips); the witness is outside `chapter-*`, so the
blocker counts remain `ExpressionStatement:CallExpression` **2,722** and
`CallExpression` **2,656**. Differential coverage grows **321/315/0/6 →
322/316/0/6** with no disagreements; grammar remains **218/97/121**.

## Literal queue-to-fixed-array size mismatch — 2026-10-27

A direct scalar-literal queue copied to a differently sized fixed unpacked
integral array now lowers the §7.6 run-time mismatch to an immediate `$finish`.
Earlier output remains visible and no partial aggregate copy is fabricated.
Equal-size copies, dynamic or effectful queue histories, aliases, mutations,
timed forms, and nonblocking assignments remain loud. The
`queue_fixed_size_mismatch` fixture supplies the differential row and Lean
receipt.

The current 22,064-path census moves **5,325 → 5,326 clean / 16,672 → 16,671
partial** (67 include skips); `AssignmentExpression:target` falls **2,844 →
2,842**. Differential coverage grows **320/314/0/6 → 321/315/0/6** with no
disagreements; grammar remains **218/97/121**.

## Fixed-size `$bits` operands — 2026-10-27

Fixed-size bitstream operands of `$bits(expr)` are now admitted from their
elaborated type without evaluating the source expression. The `bits_fixed_expr`
fixture covers a post-increment operand; initialized dynamic strings, queues,
associative arrays, and other runtime-sized or non-bitstream operands remain
loud.

The 22,059-path snapshot remains **5,304 clean / 16,688 partial** (67 include
skips), while `CallExpression` falls **2,729 → 2,672**. Differential coverage
grows **318/312/0/6 → 319/313/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal mailbox `peek()` and `try_peek()` — 2026-10-27

Source-ordered scalar-literal mailbox histories now admit `peek()` and
`try_peek()` without consuming the FIFO head. The latter also publishes its
success flag and copied output value. Empty blocking peeks, dynamic messages,
aliases, branches, and width mismatches remain loud because the flat
self-check state has no mailbox object. `mailbox_literal_peek` supplies the
differential row and Lean receipt.

The committed 22,059-path snapshot remains **5,304 clean / 16,688 partial**
(67 include skips). Differential coverage grows **319/313/0/6 → 320/314/0/6**
with no disagreements; grammar remains **218/97/121**.

## Literal queue initializer `.size()` — 2026-10-27

A 2-state queue initialized only by scalar literals now answers `.size()` with
its exact element count. Queue mutations, aliases, content reads, dynamic
initializers, and value-position aggregate operations remain loud because the
flat self-check state still carries no queue object. `queue_literal_size`
supplies the differential row and Lean receipt.

The 22,059-path snapshot remains **5,301 clean / 16,691 partial** (67 include
skips); `VariableSymbol:2state` falls **2,223 → 2,118**, while
`ExpressionStatement:CallExpression` remains **2,739**. Differential coverage
grows **315/309/0/6 → 316/310/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal queue empty reassignment `.size()` — 2026-10-27

A direct `q = {}` after a scalar-literal queue initializer now makes later
`q.size()` queries return exact zero. Other queue mutations, aliases, content
reads, dynamic or effectful assignments, and value-position aggregate
operations remain loud. `queue_literal_size_after_empty_write` supplies the
differential row and Lean receipt.

The 22,059-path snapshot moves **5,301 → 5,303 clean / 16,691 → 16,689
partial** (67 include skips); `CallExpression` falls **2,731 → 2,729** while
`ExpressionStatement:CallExpression` remains **2,739**. Differential coverage
grows **316/310/0/6 → 317/311/0/6** with no disagreements; grammar remains
**218/97/121**.

## Literal ASCII string `$sformatf` — 2026-10-27

An ASCII string literal is now admitted as the sole `%s`/`%S` operand of the
literal `$sformatf` slice. Its bytes flow through the existing packed string
renderer; dynamic strings, non-ASCII text, aggregates, and other storage stay
loud. `sformatf_string_literal` supplies the differential row and extractor
regression.

The 22,059-path snapshot remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**306/301/0/5 → 307/302/0/5** with no disagreements; grammar remains
**218/96/122**.

## Source-pure named ASCII string `$sformatf` — 2026-10-27

A named `string` is now accepted as a `%s`/`%S` operand when its declaration
and every source assignment are blocking ASCII literals. The latest proven
bytes reuse the packed renderer; dynamic, unassigned, nonblocking, timed,
non-ASCII, aggregate, and other histories remain loud.
`sformatf_string_history` supplies the differential row and extractor
regressions.

The 22,059-path snapshot remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**; the residual
`CallExpression:$sformatf:format` wall falls **6 → 4**. Differential coverage grows
**307/302/0/5 → 308/303/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal integral zero-width `$sformatf` — 2026-10-27

The literal integral `$sformatf` slice now accepts `%0b/%0h/%0o/%0d` and their
uppercase aliases. Existing minimal-width renderers produce the packed text;
dynamic formats, other field controls, and nonintegral operands remain loud.
`sformatf_zero_width` supplies the differential row and extractor regression.

The 22,059-path snapshot remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**305/300/0/5 → 306/301/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal integral character `$sformatf` — 2026-10-27

The literal integral `$sformatf` expression slice now includes `%c` and `%C`.
The formatter renders the low byte as an ASCII packed character, and the
result can flow through an existing `$display` argument. Unknown bits, dynamic
formats, string or aggregate operands, and other conversion forms remain
loud. `sformatf_char` supplies the differential row and extractor regression.

The 22,059-path snapshot remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`CallExpression` remains **2,739**. Differential coverage grows
**304/299/0/5 → 305/300/0/5** with no disagreements; grammar remains
**218/96/122**.

## Discarded literal `$sformatf` statements — 2026-10-27

Statement-position calls now erase a `$sformatf` result after the existing
converter proves one literal `%b/%h/%o/%d` format (including uppercase aliases)
and one pure integral operand. Dynamic formats, unsupported conversions, extra
arguments, real or aggregate operands, and other string state remain loud.
`sformatf_statement` supplies the differential row and extractor regression.

The 22,059-path snapshot remains **5,287 clean / 16,705 partial** (67 include
skips); `ExpressionStatement:CallExpression` remains **2,746** and
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
**303/298/0/5 → 304/299/0/5** with no disagreements; grammar remains
**218/96/122**.

## Literal integral `$sformatf` expressions — 2026-10-27

Expression-position `$sformatf` now admits one literal format and one pure
integral operand for the `%b`, `%h`, `%o`, and `%d` display conversions. The
uppercase `%B`, `%H`, `%O`, and `%D` spellings use the same renderer, as
required by IEEE 1800-2023 §21.2.1.1. The result is an ASCII packed value, so
ordinary string equality observes the exact formatted bytes without adding a
dynamic string store. Dynamic formats, multiple arguments, unsupported
conversion characters, aggregate or real operands, and other value contexts
remain loud. `sformatf_uppercase` supplies the differential row and the
extractor regression pins the refusal boundaries.

The 22,059-path snapshot moves **5,273 → 5,274 clean** and **16,719 → 16,718
partial** (67 include skips). `ExpressionStatement:CallExpression` remains
**2,759**, while `CallExpression` falls **2,750 → 2,739** as the literal
format family is admitted. Differential coverage grows **300/295/0/5 →
301/296/0/5** with no disagreements; grammar remains **218/96/122**.

## Literal FIFO/LIFO queue payload removal — 2026-10-27

One source-pure queue history may now contain a literal FIFO or LIFO
`$q_initialize`, literal `$q_add` entries, and nonempty `$q_remove` calls.
The extractor snapshots each removed pair and emits scalar assignments for the
job, inform, and status outputs, so the existing flat self-check state keeps
the exact observable values and ordering. Dynamic or computed payloads,
empty removals, timing, branches, other queue tasks, and value-position forms
remain loud. `q_remove_payload` supplies the differential row and Lean receipt.

The 22,059-path snapshot moves **5,274 → 5,286 clean** and **16,718 → 16,706
partial** (67 include skips). `ExpressionStatement:CallExpression` falls
**2,759 → 2,747**, while `AssignmentExpression:target` remains **2,852**.
Differential coverage grows **301/296/0/5 → 302/297/0/5** with no
disagreements; grammar remains **218/96/122**.

## Named literal queue history for `$q_exam` — 2026-10-27

The queue status recognizers now resolve one direct named operand from a prior
blocking literal assignment. The `q_exam_stat_codes` source uses that rule for
`q_id`, `job_id`, and `inform_id`, then admits statistic codes 1 and 3 with
source-ordered add history; unassigned or recomputed values and unsupported
queue operations remain loud.

The 22,059-path snapshot moves **5,272 → 5,273 clean** and **16,720 → 16,719
partial** (67 include skips). `ExpressionStatement:CallExpression` falls
**2,760 → 2,759**, `CallExpression` remains **2,750**, and differential
coverage grows **299/294/0/5 → 300/295/0/5** with grammar unchanged at
**218/96/122**.

## Bounded dynamic `$dist_uniform` fixed-array writes — 2026-10-27

The self-check surface now admits an assignment whose RHS is
`$dist_uniform(seed, 0, 1000)` and whose destination is a one-dimensional
finite fixed-unpacked integral array selected by a pure integral index. The
32-bit seed is updated and the selected flattened cell is written in the same
branch; repeated seeds therefore produce the same sequence while the update
remains explicit state rather than an invented random oracle. The admitted
slice requires a direct 32-bit variable seed, literal bounds `0` and `1000`,
and a 32-bit array element. Other bounds, seed expressions, aggregate or
dynamic storage, effectful selectors, and value-position random calls remain
loud.

`dist_uniform_array_target` supplies the repeatability fixture, extractor
regression, Lean receipt, and differential row. The 22,059-path census moves
**5,253 → 5,254 clean** and **16,739 → 16,738 partial** (67 include skips);
`AssignmentExpression:target` falls **2,853 → 2,852**. Differential coverage
grows **294/289/0/5 → 295/290/0/5** with no disagreements; grammar coverage
remains **218/95/123**.

## Seeded bounded `$dist_uniform` scalar assignments — 2026-10-27

Direct blocking assignments from `$dist_uniform(seed, 0, 1000)` now update
the 32-bit inout seed and one scalar 32-bit integral destination through an
explicit deterministic recurrence. The admitted slice requires a variable
seed and literal bounds; other bounds, seed expressions, nonblocking or timed
forms, non-32-bit targets, and value-position random calls remain loud. The
`dist_uniform_scalar` fixture and four chapter-20 witnesses provide the
repeatability and range checks.

The 22,059-path census moves **5,254 → 5,258 clean** and **16,738 → 16,734
partial** (67 include skips); `CallExpression` falls **2,768 → 2,764** while
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
by one matching row; grammar coverage is regenerated with the current witness
set.

## Nonnegative literal `$dist_uniform` scalar bounds — 2026-10-27

The direct scalar assignment rung now accepts any nonnegative literal
`$dist_uniform` start/end pair up to the signed 32-bit maximum. The existing
explicit recurrence supplies the inclusive result and seed update. Negative or
computed bounds, nonblocking or timed forms, non-32-bit targets, and
value-position calls remain loud. `dist_uniform_literal_bounds` supplies the
source-bound differential row; ten additional chapter-20 files become clean.

The 22,059-path census moves **5,258 → 5,268 clean** and **16,734 → 16,724
partial** (67 include skips); `CallExpression` falls **2,764 → 2,754** while
`AssignmentExpression:target` remains **2,852**. Differential coverage grows
**296/291/0/5 → 297/292/0/5**; grammar moves **218/95/123 → 218/96/122**.

## Signed literal `$dist_uniform` scalar bounds — 2026-10-27

Direct blocking assignments from `$dist_uniform` now accept signed literal
start/end pairs in the 32-bit integer range. Negative-only and zero-crossing
ranges update the seed and write a two's-complement result through the same
scalar state path; computed, reversed, out-of-range, timed, nonblocking, and
value-position forms remain loud. The `dist_uniform_signed_bounds` fixture
and extractor regression pin both signed ranges, while the two matching
chapter-20 witnesses become clean.

The committed **22,059-path** snapshot moves **5,268 → 5,270 clean** and
**16,724 → 16,722 partial** (67 include skips). `CallExpression` falls
**2,754 → 2,752**, and differential coverage grows **297/292/0/5 →
298/293/0/5** with grammar coverage unchanged at **218/96/122**.

## `$q_full` value calls after prior status checks — 2026-10-27

Value-position `$q_full` calls now use the source-pure literal queue history
when the status output has only been read before the first query. The existing
capacity counter supplies the query result; later status reads, symbolic IDs,
payload observations, removals, and other queue operations remain loud. The
`q_full_value_history` fixture and extractor regression pin the empty/full
sequence, and the two matching chapter-20 witnesses become clean.

The committed **22,059-path** snapshot moves **5,270 → 5,272 clean** and
**16,722 → 16,720 partial** (67 include skips). `CallExpression` falls
**2,752 → 2,750**, and differential coverage grows **298/293/0/5 →
299/294/0/5** with grammar coverage unchanged at **218/96/122**.

## Queue-removal status — 2026-10-27

Undefined literal queue IDs now lower `$q_remove` to status 2. A valid literal
FIFO/LIFO initialization followed by one removal from the still-empty queue
lowers the initialization to 0 and the removal to status 3. Named IDs require
one direct literal assignment, and job/inform outputs must remain unread;
populated, payload-observing, computed, and additional queue forms stay loud.
The `q_remove_status_2` and `q_remove_status_3` fixtures supply the PASS
transcripts and differential rows.

The committed **22,059-path** snapshot moves **5,241 → 5,243 clean** and
**16,751 → 16,749 partial** (67 include skips). The
`ExpressionStatement:CallExpression` wall falls **2,774 → 2,772** and
`AssignmentExpression:target` remains **2,853**. Differential coverage grows
**284/279/0/5 → 286/281/0/5** with no disagreements; grammar coverage is
regenerated with the current witness count.

## Queue-add status — 2026-10-27

Source-pure `$q_add` calls now retain their scalar status after a literal
FIFO/LIFO initialization. Successful literal additions report 0, and an
addition after the positive capacity reports 1. Queue ID, job, and inform
arguments must be integral literals; symbolic IDs, payload expressions,
additional queue operations, and value-position forms remain loud. The
`q_add_status_0` and `q_add_status_1_when_full` fixtures supply the PASS
transcripts and differential rows.

The committed **22,059-path** snapshot moves **5,243 → 5,245 clean** and
**16,749 → 16,747 partial** (67 include skips). The
`ExpressionStatement:CallExpression` wall falls **2,772 → 2,770** and
`AssignmentExpression:target` remains **2,853**. Differential coverage grows
**286/281/0/5 → 288/283/0/5** with no disagreements; grammar coverage remains
**218/95/123**.

## Queue-full status — 2026-10-27

Source-pure `$q_full` queries now lower against a literal queue initialization
and literal add history. The scalar result is 0 below capacity and 1 at or
above capacity. Direct status-output statements and value-position queries with
an unread status output are admitted; symbolic IDs, observed status effects,
other queue operations, and payload expressions remain loud. The
`q_full_status_0` and `q_full_status_1_when_full` fixtures supply the PASS
transcripts and differential rows.

The committed **22,059-path** snapshot moves **5,245 → 5,249 clean** and
**16,747 → 16,743 partial** (67 include skips). The
`ExpressionStatement:CallExpression` wall falls **2,770 → 2,764** and
`AssignmentExpression:target` remains **2,853**. Differential coverage grows
**288/283/0/5 → 290/285/0/5** with no disagreements; grammar coverage remains
**218/95/123**.

## Queue-exam length statistics — 2026-10-27

Source-pure `$q_exam` calls with literal statistic code 1 or 3 now lower after
one literal queue initialization and literal add history. The current or
maximum length is the successful-add count clamped at capacity, followed by
status 0. Removal, timing, symbolic IDs, other statistic codes, and
value-position forms remain loud. The four `q_exam_*` fixtures supply the
PASS transcripts and differential rows.

The committed **22,059-path** snapshot moves **5,249 → 5,253 clean** and
**16,743 → 16,739 partial** (67 include skips). The
`ExpressionStatement:CallExpression` wall falls **2,764 → 2,760** and
`AssignmentExpression:target` remains **2,853**. Differential coverage grows
**290/285/0/5 → 294/289/0/5** with no disagreements; grammar coverage remains
**218/95/123**.

## Duplicate queue-ID status — 2026-10-27

Two source-pure `$q_initialize` calls with the same literal FIFO/LIFO type and
positive capacity now lower to scalar status writes: the first reports 0 and
the duplicate reports 6. A named queue ID is admitted only after one direct
literal assignment; other queue operations and computed or reassigned IDs stay
loud. The `q_initialize_duplicate_status` fixture supplies the PASS transcript
and differential row.

The committed **22,059-path** snapshot moves **5,240 → 5,241 clean** and
**16,752 → 16,751 partial** (67 include skips). The
`ExpressionStatement:CallExpression` wall falls **2,775 → 2,774** and
`AssignmentExpression:target` remains **2,853**. Differential coverage grows
**283/278/0/5 → 284/279/0/5** with no disagreements; grammar coverage is
regenerated with the current witness count.

## Discarded invalid literal `$fopen` modes — 2026-10-26

An invalid literal mode in a discarded `$fopen(path, mode)` statement now
lowers through the existing deterministic zero-result converter. The mode is
validated before erasing the call, so valid modes, dynamic paths or modes,
and value-position calls remain on their existing file-state boundary. The
`fopen_invalid_mode_statement` fixture supplies the differential row and
Lean receipt; Icarus also emits the declared `PASS` transcript (with its
standard invalid-mode warning).

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **268/263/0/5 → 269/264/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded empty associative-array count queries — 2026-10-26

Discarded `num()` and `size()` calls on a proven untouched 2-state associative
array now erase their exact zero result through the existing empty-array
converter. Populated, aliased, initialized, dynamic, and value-position
queries remain loud because their count depends on runtime state. The
`assoc_empty_query_statement` fixture supplies the differential row and Lean
receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **269/264/0/5 → 270/265/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded empty associative-array endpoint queries — 2026-10-26

Discarded `first(index)` and `last(index)` calls on a proven untouched 2-state
associative array now erase their exact zero result through the existing empty
endpoint converter. The direct named index argument remains checked, while
populated, aliased, initialized, dynamic, and value-position queries stay
loud. The `assoc_empty_endpoint_statement` fixture supplies the differential
row and Lean receipt; the pinned self-check oracle agrees with its `PASS`
transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **270/265/0/5 → 271/266/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded zero-size queries — 2026-10-26

Discarded `size()` calls on untouched queues or dynamic arrays, and `len()` on
an untouched empty string, now erase their exact scalar zero through the
existing zero-size converter. Mutation, aliases, initialized nonempty values,
and value-position observations remain loud. The `zero_size_statement` fixture
supplies the differential row and Lean receipt; the pinned self-check oracle
agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **271/266/0/5 → 272/267/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded literal-string queries — 2026-10-26

Discarded `len`, `getc`, `atoi`, radix, `compare`, and `icompare` calls on
unchanged ASCII literal strings now erase their scalar result through the
existing source-history converters. Non-ASCII strings, dynamic or mutated
receivers, aliases, unsupported conversions, and value-position observations
remain loud. The `string_query_statement` fixture supplies the differential
row and Lean receipt; the pinned self-check oracle agrees with its `PASS`
transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **272/267/0/5 → 273/268/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded literal-string `atoreal()` conversions — 2026-10-26

A discarded `atoreal()` call on an unchanged ASCII literal string now erases
its opaque real result through the existing source-history converter. Dynamic
strings, nonliteral writes, and value-position real conversions remain loud.
The `string_atoreal_statement` fixture supplies the differential row and Lean
receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **273/268/0/5 → 274/269/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded pre-trigger `event.triggered()` queries — 2026-10-26

Discarded `event.triggered()` calls on untouched events now erase their exact
pre-trigger false result through the existing event-history converter.
Triggered, dynamic, and value-position queries remain loud. The
`event_triggered_statement` fixture supplies the differential row and Lean
receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **274/269/0/5 → 275/270/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded enum `.name()` queries — 2026-10-26

Discarded `enum.name()` calls now reuse the existing enum method converter and
erase the unobserved string result after receiver and declaration-order checks.
Numeric enum methods, effectful receivers, malformed calls, and value-position
queries remain loud. The `enum_name_statement` fixture supplies the differential
row and Lean receipt; the pinned self-check oracle agrees with its `PASS`
transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **275/270/0/5 → 276/271/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded numeric enum queries — 2026-10-26

Discarded numeric enum methods (`first`, `last`, `num`, `next`, and `prev`)
now reuse the existing pure enum converter and erase their unobserved scalar
results after receiver and step checks. Dynamic or effectful receivers,
malformed methods, and value-position calls remain loud. The
`enum_numeric_statement` fixture supplies the differential row and Lean
receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **276/271/0/5 → 277/272/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded literal-string transformations — 2026-10-26

Discarded `toupper()`, `tolower()`, and literal-bound `substr()` calls now
erase their fresh string result after the existing ASCII source-history check.
Dynamic, aliased, mutated, non-ASCII, symbolic, and value-position forms remain
loud. The `string_transform_statements` fixture supplies the differential row
and Lean receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **278/273/0/5 → 279/274/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded fixed-array locator queries — 2026-10-26

Discarded `min()`, `max()`, `unique()`, and `unique_index()` calls now erase
their unobserved queue result for named fixed-size arrays with integral leaves
when no `with` clause is present. Dynamic, queue, associative, aggregate,
`with`, symbolic, and value-position forms remain loud. The
`array_query_statements` fixture supplies the differential row and Lean receipt;
the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **279/274/0/5 → 280/275/0/5** with no disagreements, and grammar
coverage grows **217/92/125 → 218/93/125**.

## Discarded fixed-array locator `with` queries — 2026-10-26

The same discarded `min()`, `max()`, `unique()`, and `unique_index()` queries
now accept a source-pure integral `with` expression after the existing iterator
purity check. Effectful `with` clauses remain loud. The
`array_query_with_statements` fixture supplies the differential row and Lean
receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **280/275/0/5 → 281/276/0/5** with no disagreements, and grammar
coverage grows **218/93/125 → 218/95/123**.

## Discarded empty aggregate deletes — 2026-10-27

`delete()` on a source-pure empty queue or uninitialized dynamic array now
erases as an inert statement. Initialized, populated, aliased, effectful, and
symbolic aggregate forms remain loud. The `empty_aggregate_delete_statements`
fixture supplies the differential row and Lean receipt; the pinned self-check
oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **281/276/0/5 → 282/277/0/5** with no disagreements, and grammar
coverage remains **218/95/123**.

## Discarded empty associative-array deletes — 2026-10-27

An untouched 2-state associative array now erases discarded `delete()` calls
for the whole array or a source-pure integral/string key. Initialized,
four-state, effectful-key, aliased, and symbolic forms remain loud. The
`empty_associative_delete_statements` fixture supplies the differential row and
Lean receipt; the pinned self-check oracle agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **282/277/0/5 → 283/278/0/5** with no disagreements; grammar coverage
remains **218/95/123**.

## Discarded fixed-array reductions — 2026-10-26

Discarded fixed-array reductions (`sum`, `product`, `and`, `or`, and `xor`)
now reuse the balanced value lowering after storage-shape, width, iterator, and
purity checks. The existing empty-dynamic-array identity also permits discarded
`sum` and `product`; other dynamic storage, effectful `with` expressions, and
value-position reductions remain loud. The `array_reduction_statements` fixture
supplies the differential row and Lean receipt; the pinned self-check oracle
agrees with its `PASS` transcript.

The committed **22,059-path** snapshot remains **5,240 clean / 16,752
partial** (67 include skips), with `AssignmentExpression:target` at **2,853**
and `ExpressionStatement:CallExpression` at **2,775**. Differential coverage
grows **277/272/0/5 → 278/273/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Discarded time-scale metadata queries — 2026-10-26

Valid `$timeunit` and `$timeprecision` calls in statement position now erase
their discarded exponent after the existing converter accepts a literal
`` `timescale `` directive. Missing or malformed metadata and value uses remain
loud. The `time_scale_statements` fixture supplies the differential row and
Lean receipt; the pinned self-check oracle agrees with its PASS transcript.
The fresh census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**267/262/0/5 → 268/263/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded integral signing casts — 2026-10-26

Valid `$signed` and `$unsigned` calls in statement position now erase their
pure discarded result after the existing converter checks the operand. Real,
aggregate, malformed, and effectful forms remain loud. The
`signing_statement` fixture supplies the differential row and Lean receipt;
the pinned self-check oracle agrees with its PASS transcript. The fresh census
remains **5,240 clean / 16,752 partial** (67 include skips), with
`AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**266/261/0/5 → 267/262/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded constant `$clog2` queries — 2026-10-26

Admitted `$clog2` calls in statement position now erase their discarded
result after the existing converter accepts the operand. Unsupported or
effectful forms remain loud. The `clog2_statement` fixture supplies the
differential row and Lean receipt, and Icarus agrees with its PASS transcript.
The fresh census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**265/260/0/5 → 266/261/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded bounded `$isunbounded` queries — 2026-10-26

Literal and bounded-parameter `$isunbounded` calls in statement position now
erase their discarded result. The existing one-bit expression lowering proves
that these operands cannot be the special unbounded value; ordinary variables,
unbounded parameters, malformed calls, and value uses remain loud. The
`isunbounded_statement` fixture supplies the differential row and Lean receipt.
The fresh census remains **5,240 clean / 16,752 partial** (67 include skips),
with `AssignmentExpression:target` at **2,853** and
`ExpressionStatement:CallExpression` at **2,775**. Differential coverage grows
**264/259/0/5 → 265/260/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded time-zero realtime query — 2026-10-26

The zero-argument `$realtime` call now erases when its real result is discarded
at time zero. Argumented, delayed, and value-returning forms remain loud
because the tier has no general real-time state. The
`realtime_query_statements` fixture supplies the differential row and Lean
receipt. The fresh census remains **5,240 clean / 16,752 partial** (67 include
skips), with `AssignmentExpression:target` at **2,853**. Differential coverage
grows **263/258/0/5 → 264/259/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded time-zero integer queries — 2026-10-26

Zero-argument `$time` and `$stime` calls in statement position now erase their
discarded result using the existing exact time-zero literal rule. Argumented,
delayed, and value-returning forms remain loud. The `time_query_statements`
fixture supplies the differential row and Lean receipt. The fresh census
remains **5,240 clean / 16,752 partial** (67 include skips), with
`AssignmentExpression:target` at **2,853**. Differential coverage grows
**262/257/0/5 → 263/258/0/5** with no disagreements, and grammar coverage
remains **217/92/125**.

## Discarded fixed dimension queries — 2026-10-26

Valid fixed-type `$size`, `$high`, `$left`, `$right`, `$low`, `$increment`,
`$dimensions`, and `$unpacked_dimensions` calls in statement position now
erase their discarded result after the existing elaborated-metadata query
proves the shape. Dynamic arrays, dynamic selectors, effectful operands, and
value uses remain loud. The `dimension_query_statements` fixture supplies the
differential row and Lean receipt. The fresh census remains **5,240 clean /
16,752 partial** (67 include skips), with `AssignmentExpression:target` at
**2,853**. Differential coverage grows **261/256/0/5 → 262/257/0/5** with no
disagreements, and grammar coverage remains **217/92/125**.

## Discarded literal bit queries — 2026-10-26

Valid discarded literal-operand `$countbits`, `$countones`, `$onehot`,
`$onehot0`, and `$isunknown` calls now erase without a represented state
effect. Dynamic operands stay loud because these queries must evaluate them;
the `literal_bit_query_statements` fixture supplies the differential row and
Lean receipt. The fresh census remains **5,240 clean / 16,752 partial** (67
include skips), with `ExpressionStatement:CallExpression` at **2,775**.
Differential coverage grows **260/255/0/5 → 261/256/0/5** with no
disagreements, and grammar coverage remains **217/92/125**.

## Discarded `$bits` does not evaluate its expression — 2026-10-26

Valid one-argument `$bits(expr)` calls in statement position now erase without
evaluating `expr`, matching IEEE 1800-2023 §20.6.2. The `bits_discarded`
fixture supplies the differential row and Lean receipt; value-returning,
malformed, and stateful calls remain loud. The fresh census remains **5,240
clean / 16,752 partial** (67 include skips), with
`ExpressionStatement:CallExpression` at **2,775** because this standalone
shape is absent from sv-tests-2. Differential coverage grows **259/254/0/5 →
260/255/0/5** with no disagreements, and grammar coverage remains **217/92/125**.

## Discarded `$typename` does not evaluate its expression — 2026-10-26

Valid one-argument `$typename(expr)` calls in statement position now erase
without evaluating `expr`, matching IEEE 1800-2023 §20.6.1. The
`typename_discarded` fixture supplies the differential row and Lean receipt;
value-returning, malformed, and stateful calls remain loud. The fresh census
remains **5,240 clean / 16,752 partial** (67 include skips), with
`ExpressionStatement:CallExpression` at **2,775** because this standalone
shape is absent from sv-tests-2. Differential coverage grows **258/253/0/5 →
259/254/0/5** with no disagreements, and grammar coverage remains **217/92/125**.

## Literal predefined-stdout position errors — 2026-10-26

The exact `$ftell(32'h8000_0001)` query on the predefined stdout descriptor
now lowers to the standard signed 32-bit error result `-1`. Discarded calls are
inert because the self-check state has no seekable file object; dynamic
descriptors and file-position state remain loud. The `ftell_stdout_error`
fixture supplies the differential row and Lean receipt. The fresh census remains
**5,240 clean / 16,752 partial** (67 include skips), with `CallExpression` at
**2,771** because this exact shape is absent from sv-tests-2. Differential
coverage grows **257/252/0/5 → 258/253/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Literal predefined-stdout seek errors — 2026-10-26

The exact `$fseek(32'h8000_0001, 0, 0)` query on the predefined stdout
descriptor now lowers to the standard signed 32-bit error result `-1`.
Discarded calls are inert because the self-check state has no seekable file
object; dynamic descriptors, offsets, whence values, and other file operations
remain loud. The `fseek_stdout_error` fixture supplies the differential row and
Lean receipt. The fresh census moves **5,239 → 5,240 clean** and **16,753 →
16,752 partial** (67 include skips), with `CallExpression` falling **2,772 →
2,771**. Differential coverage grows **256/251/0/5 → 257/252/0/5** with no
disagreements, and grammar coverage remains **217/92/125**.

## Literal coverage queries in the empty database — 2026-10-26

Literal-only `$coverage_control`, `$coverage_get`, `$coverage_get_max`,
`$coverage_merge`, and `$coverage_save` calls now lower to the standard
`SV_COV_NOCOV` zero because the self-check state has no coverage database or
registered coverage objects. Dynamic scope/arguments and source coverage
constructs remain loud. The fresh census measures **5,239 clean / 16,753
partial** (67 include skips), with `CallExpression` falling **2,778 → 2,772**.
Differential coverage grows **255/250/0/5 → 256/251/0/5** with no
disagreements, and grammar coverage remains **217/92/125**.

## Pure conditional continuous drivers from literal source state — 2026-10-26

Whole packed-net drivers with literal arms and one direct literal
initialization for each condition now snapshot their selected arm before the
existing static per-bit resolver. This admits the all-high-impedance and
net-declaration driver witnesses without a live driver store; unknown,
changing, effectful, strength-sensitive, and scheduler-visible forms remain
loud. The fresh census moves **5,231 → 5,233 clean** and **16,760 → 16,758
partial** (67 include skips), with `AssignmentExpression:target` falling
**2,855 → 2,853**. Differential coverage grows **254/249/0/5 → 255/250/0/5**
with no disagreements, and grammar coverage remains **217/92/125**.

## Selected continuous windows from one literal source write — 2026-10-26

Fixed packed-net windows whose source variable has one direct literal
initialization now snapshot that source before the existing static per-bit
resolver. This admits the overlapping `scalared_net_allows_bitselect` witness
without introducing a live continuous-driver store; dynamic, multiply-written,
and effectful sources remain on the scheduler boundary. The fresh census moves
**5,230 → 5,231 clean** and **16,761 → 16,760 partial** (67 include skips),
with `AssignmentExpression:target` falling **2,856 → 2,855**. Differential
coverage grows **253/248/0/5 → 254/249/0/5** with no disagreements, and grammar
coverage remains **217/92/125**.

## Fresh extractor census — 2026-10-26

The chapter-scoped rerun covered **22,059** paths: **5,239 clean**,
**16,753 partial**, **67 include skips**, and **zero errors**. The adapter
walk found **24 unlockable** files, of which **17** are eligible for its
simulation tier. The leading refusal classes by file are
`AssignmentExpression:target` (2,853), `ExpressionStatement:CallExpression`
(2,775), `CallExpression` (2,772), `Hierarchy:ports` (2,400),
`VariableSymbol:2state` (2,223), `SubroutineSymbol:Subroutine` (1,634),
`NamedValueExpression:2state` (1,485), `ConcurrentAssertionStatement`
(1,359), `InvalidStatement` (1,330), and `ClassType` (1,330).

The per-chapter counts are retained in `docs/sv-construct-census.json` and
the per-file records in `harness/sv/conformance/census.json`; `--recheck`
matched all 200 fixed-seed sample classifications.

## Dynamic indexed slices over wide packed elements — 2026-10-26

Dynamic `+:` and `-:` slices over nested packed elements now normalize the
runtime outer label in whole inner-element chunks before using the existing
flat selected window. Ascending and descending declarations preserve their
source order and read/write aliasing; effectful bases and aggregate forms
remain loud. The `packed_array_dynamic_wide_slice` fixture supplies the
differential row and Lean receipt. The refreshed census remains **5,230 clean /
16,761 partial** (67 include skips), with `AssignmentExpression:target` at
**2,856**; differential coverage grows **252/247/0/5 → 253/248/0/5**, and
grammar remains **217/92/125**.

## Dynamic noncanonical packed indexed slices — 2026-10-26

Dynamic `+:` and `-:` part-select targets and reads on noncanonical one-bit
packed vectors now normalize their runtime base labels into the flat window
representation. Ascending ranges use increasing flat offsets and descending
ranges retain indexed direction; simple dynamic ranges, effectful, unsigned,
aggregate, and unsupported forms remain loud; partial reads retain the
selected evaluator boundary. The
`packed_array_dynamic_part_select` fixture supplies the differential row and
Lean receipt. The refreshed census remains **5,230 clean / 16,761 partial**
(67 include skips) with `AssignmentExpression:target` at **2,856**; differential
coverage grows **251/246/0/5 → 252/247/0/5**, and grammar remains **217/92/125**.

## Dynamic noncanonical packed-element targets — 2026-10-26

Blocking assignments to dynamic elements of noncanonical one-bit packed
vectors now reuse the existing declared-label offset normalizer. Ascending
ranges map the runtime index from the right label, so the write and subsequent
read address the same flat cell; the signed 32-bit index boundary and all
unsigned, effectful, aggregate, and unsupported forms remain loud. The
`packed_array_dynamic_target` fixture supplies the differential row and Lean
receipt. This shape is absent from the refreshed corpus, so its extractor
census remains **5,230 clean / 16,761 partial** (67 include skips) with
`AssignmentExpression:target` at **2,856**. Differential coverage grows
**250/245/0/5 → 251/246/0/5**; grammar coverage remains **217/92/125**.

## Dynamic nested packed-element indexing — 2026-10-26

A dynamic element select on a nested packed array with integral elements now
normalizes the declared label into the flat vector state by scaling the runtime
outer index by the element width. Reads and blocking targets share this
lowering, with ascending and descending declared ranges mapped from their
right-hand label. Out-of-range, aggregate, effectful, nonintegral, and
unsupported index forms remain loud. The `packed_array_dynamic_index` fixture
checks the read/write alias and its Lean receipt, while extractor regressions
cover the offset geometry.

The refreshed **22,058-path** census moves **5,227 → 5,230 clean** and
**16,764 → 16,761 partial** (67 include skips), with
`AssignmentExpression:target` falling **2,857 → 2,856** and
`ElementSelectExpression:source-type` **479 → 476**; `CallExpression` remains
**2,778**. Differential coverage grows **249/244/0/5 → 250/245/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic packed slices inside fixed-array cells — 2026-10-26

Dynamic `+:` and `-:` slices over a descending multidimensional packed cell
inside a bounded fixed unpacked array now reuse the flat selected-read and
selected-write representation. The extractor scales the runtime outer label
by the packed inner-element width and preserves the high-end position for
`-:`. Ascending ranges, dynamic widths, aggregate cells, and effectful bases
remain loud. The `fixed_array_dynamic_packed_slice` fixture supplies the
differential row and Lean receipt, with extractor regressions for both
directions and the ascending-range boundary.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857**.
Differential coverage grows **248/243/0/5 → 249/244/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic multidimensional subarray source reads — 2026-10-26

A single dynamic selector of a bounded multidimensional unpacked integral
array may now be read into a distinct flat fixed-array row. The extractor
expands the finite selector range into guarded branches and copies each
omitted suffix cell in declaration order, reusing the existing flat-cell
state. Multiple dynamic selectors, shape mismatches, aliases, aggregate
leaves, timed assignments, and effectful sources remain loud. The
`nested_fixed_array_dynamic_subarray_read_copy` fixture supplies the
differential row and Lean receipt, with extractor regressions for cell order
and the shape refusal.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857**.
Differential coverage grows **247/242/0/5 → 248/243/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Destructive finite dynamic-array reinitialization — 2026-10-26

Two plain positive constant allocations of one finite scalar dynamic array now
admit the IEEE destructive reinitialization rule. The second `new[N]` drops the
old cells and publishes fresh type-default cells, while resize-copy,
self-growth, zero-sized, dynamic-sized, and third allocations remain loud. The
`dynamic_array_reinitialization` fixture checks that old writes disappear and
that the new extent and defaults are observed.

The **22,056-path** census moves **5,209 → 5,210 clean** and **16,780 →
16,779 partial** (67 include skips). `AssignmentExpression:target` falls
**2,860 → 2,857** and `CallExpression` **2,780 → 2,778**. Differential
coverage grows **239/234/0/5 → 240/235/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Constant out-of-bounds unpacked-array reads — 2026-10-26

Constant reads beyond a finite unpacked integral array now lower to the IEEE
element default: all zeroes for a two-state element and all x for a four-state
element, including an enum's four-state base type. Dynamic indices, packed or
scalar diagnostics, aggregate leaves, and dynamic arrays remain loud. The
`array_oob_reads` fixture covers the two state kinds and enum result.

The **22,056-path** census moves **5,210 → 5,215 clean** and **16,779 →
16,774 partial** (67 include skips). `ElementSelectExpression:source-type`
falls **495 → 490**. Differential coverage grows **240/235/0/5 → 241/236/0/5**
with no disagreements; grammar coverage remains **217/90/127**.

## Direct indexing of literal ASCII strings — 2026-10-26

Constant indexing of a source-pure ASCII string now lowers to its byte value,
with the IEEE zero result for negative and out-of-range indices. Dynamic
indices, aliases, non-ASCII or nonliteral writes, and element writes remain
loud. The `string_index` fixture supplies the differential row and Lean
receipt; extractor tests cover literal history and each refusal boundary.

On the refreshed **22,056-path** census, clean files move **5,215 → 5,227**
and partial files **16,774 → 16,762** (67 include skips).
`ElementSelectExpression:source-type` falls **490 → 479**. Differential
coverage grows **241/236/0/5 → 242/237/0/5** with no disagreements; grammar
coverage remains **217/92/125**.

## Single literal initial-write continuous sources — 2026-10-26

A continuous scalar net driver may now fold a variable RHS when that variable
has exactly one direct blocking literal assignment in an `initial` block, with
no declaration initializer or other writes. This is lowered to the existing
time-zero literal driver, so the self-check observes the source value without
introducing a live scheduler driver. Dynamic, control-dependent, multiply
written, and nonliteral sources remain loud. The
`continuous_history_literal` fixture supplies the differential row and Lean
receipt, with extractor regressions for the one-write and multiple-write
boundaries.

On the refreshed **22,056-path** census, clean and partial counts remain
**5,227 / 16,762** (67 include skips), and `AssignmentExpression:target`
remains **2,857**. Differential coverage grows **242/237/0/5 → 243/238/0/5**
with no disagreements; grammar coverage remains **217/92/125**.

## Whole bounded multidimensional fixed-array copies — 2026-10-26

Assignments between distinct bounded multidimensional unpacked arrays with
integral leaves now expand in declaration order to the existing flat vector
cells. Equal ordinal shapes may use different declared index labels, matching
SystemVerilog's assignment-compatible unpacked arrays. Self-copies,
mismatched dimensions, dynamic or aggregate leaves, and effectful sources
remain loud. The `fixed_array_nested_copy` fixture supplies the differential
row and Lean receipt, with extractor regressions for ordinal mapping and the
refusal boundaries.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **243/238/0/5 → 244/239/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Constant multidimensional subarray copies — 2026-10-26

A constant prefix selection of a bounded multidimensional unpacked integral
array may now copy into a distinct flat fixed array in declaration order. The
existing cell expansion supplies the complete source row; dynamic selectors,
overlapping aliases, mismatched extents, aggregate leaves, and effectful
sources remain loud. The `fixed_array_subarray_copy` fixture supplies the
differential row and Lean receipt, with extractor regressions for the selected
row and refusal boundaries.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **244/239/0/5 → 245/240/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic outer multidimensional subarray copies — 2026-10-26

A single dynamic outer index of a bounded multidimensional unpacked integral
array now expands to guarded cellwise assignments from a distinct flat row.
The finite branch expansion preserves declaration order and leaves multiple
dynamic selectors, aliases, mismatched shapes, aggregate leaves, timed forms,
and effectful sources loud. The
`nested_fixed_array_dynamic_subarray_copy` fixture supplies the differential
row and Lean receipt, with extractor regression coverage for the lowering and
shape boundary.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **245/240/0/5 → 246/241/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Dynamic inner-prefix multidimensional subarray copies — 2026-10-26

One dynamic selector after a constant prefix of a bounded multidimensional
unpacked integral array now copies a distinct flat row through guarded,
cellwise branches. The lowering preserves suffix declaration order and leaves
multiple dynamic selectors, aliases, shape mismatches, aggregate leaves, timed
forms, and effectful sources loud. The
`nested_fixed_array_dynamic_inner_subarray_copy` fixture supplies the
differential row and Lean receipt, with extractor regression coverage for both
prefix positions.

The refreshed **22,058-path** census remains **5,227 clean / 16,764 partial**
(67 include skips), with `AssignmentExpression:target` at **2,857** because
the remaining corpus target rows require other aggregate or scheduler state.
Differential coverage grows **246/241/0/5 → 247/242/0/5** with no
disagreements; grammar coverage remains **217/92/125**.

## Finite literal dynamic-array reductions — 2026-10-26

Positional literal initializers for finite integral dynamic arrays now become
independent flat cells, so the existing `sum`, `product`, `and`, `or`, and
`xor` reduction lowering can evaluate them exactly. Later resize, uninitialized
or dynamic sources, keyed/default patterns, and nonintegral elements remain
outside the representation. The `dynamic_array_reductions` fixture covers the
five methods and their combined self-check output.

The **22,056-path** census moves **5,175 → 5,192 clean** and **16,813 →
16,797 partial** (67 include skips). `VariableSymbol:2state` falls **2,285 →
2,223** and `ExpressionStatement:CallExpression` falls **2,777 → 2,776**;
`AssignmentExpression:target` remains **2,861** and `CallExpression` remains
**2,801**. Differential coverage grows **225/220/0/5 → 226/221/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Nested finite fixed-array reductions — 2026-10-26

Pure nested reductions over finite two-dimensional unpacked arrays now lower
row-by-row through the existing flat cells. Both implicit `item.sum` and the
explicit `item.sum with (item)` form retain their iterator bindings; aggregate
results, effects, and non-finite storage remain loud. The `nested_2d_reductions`
fixture covers both forms.

The **22,056-path** census moves **5,192 → 5,195 clean** and **16,797 →
16,794 partial** (67 include skips); the leading blocker classes and the
grammar census are unchanged. Differential coverage is refreshed separately
in `docs/sv-coverage.md`.

## Empty dynamic-array reductions — 2026-10-26

Untouched default-empty dynamic arrays now lower `sum()` and `product()` to
their scalar zero identity. The source must have no resize, write, selection,
or effectful `with` use; other reduction methods remain loud.

The **22,056-path** census moves **5,195 → 5,197 clean** and **16,794 →
16,792 partial** (67 include skips). Differential coverage grows
**227/222/0/5 → 228/223/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Immutable literal variables as continuous net sources — 2026-10-26

The extractor now folds a whole net driven by an immutable declaration-
initialized integral literal variable into the existing time-zero literal
driver. Dynamic sources, rebinding, and multi-driver resolution remain loud.
The refreshed corpus counts are unchanged because the current sv-tests-2
snapshot has no sole witness for this narrow source-purity form.

## Disjoint fixed-array slice copies — 2026-10-26

Blocking assignment between non-overlapping constant slices of one finite
unpacked integral array now lowers cellwise. Overlapping slices, dynamic
selectors, and aggregate or effectful sources remain loud. The refreshed
corpus counts are unchanged because this narrow alias-safe shape has no sole
witness in the current sv-tests-2 snapshot.

## Unsized left streaming over one-bit leaves — 2026-10-26

Left-streaming assignment now uses the IEEE default one-bit chunk when every
direct target leaf is one bit. Wider unsized leaves, explicit dynamic forms,
nested streams, and aggregate targets remain loud. The refreshed corpus counts
are unchanged because this narrow one-bit shape has no sole witness in the
current sv-tests-2 snapshot.

## Single dynamic selectors in finite multidimensional arrays — 2026-10-26

Assignments and reads with exactly one dynamic selector in any unpacked
dimension of a finite multidimensional integral array now dispatch through flat
cells. Multiple dynamic selectors and aggregate leaves remain loud. The
refreshed corpus counts are unchanged because this narrow shape has no sole
witness in the current sv-tests-2 snapshot.

## Innermost dynamic selectors in finite multidimensional arrays — 2026-10-26

Assignments and reads with one dynamic selector in the innermost dimension of
a finite multidimensional integral array now dispatch through flat cells.
Outer dynamic selectors, multiple dynamic selectors, and aggregate leaves
remain loud. The refreshed corpus counts are unchanged because this narrow
shape has no sole witness in the current sv-tests-2 snapshot.

## Pure literal integral continuous expressions — 2026-10-26

Continuous assignment now folds an all-literal unsigned integral arithmetic or
bitwise expression into the existing time-zero driver. Variables, X/Z
operands, signed or dynamic expressions, and effectful calls remain outside
the fold. The refreshed corpus counts are unchanged because this narrow pure
expression shape has no sole witness in the current sv-tests-2 snapshot.

## Dynamic-array struct-field reductions — 2026-10-26

Finite dynamic arrays of untagged unpacked structs now admit a pure reduction
of one integral field through the existing flattened cells. Whole-struct and
aggregate-field reductions, and iterator-index expressions, remain outside
the representation.

The **22,056-path** census moves **5,197 → 5,198 clean** and **16,792 →
16,791 partial** (67 include skips). Differential coverage grows
**228/223/0/5 → 229/224/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Dynamic-array iterator-index reductions — 2026-10-26

The finite sampled dynamic-array reduction lowering now supplies the
zero-based cell position to a pure `item.index()` term. Dynamic or unrelated
iterator calls remain outside the representation.

The **22,056-path** census moves **5,198 → 5,199 clean** and **16,791 →
16,790 partial** (67 include skips). Differential coverage grows
**229/224/0/5 → 230/225/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Invalid literal `$fopen` modes — 2026-10-26

The extractor admits the deterministic IEEE case where `$fopen` receives a
literal path and an invalid literal mode, producing descriptor zero without
filesystem access. Valid or dynamic modes remain outside the surface.

The **22,056-path** census moves **5,199 → 5,200 clean** and **16,790 →
16,789 partial** (67 include skips); `CallExpression` falls **2,801 → 2,796**.
Differential coverage grows **230/225/0/5 → 231/226/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Packed-array packed-struct member windows — 2026-10-26

Constant element selections of packed arrays whose elements are untagged
packed structs or unions now compose the array element offset with the direct
field offset in the existing flat vector state. Dynamic selectors, tagged
aggregates, and nonintegral fields remain loud. The new
`packed_array_struct_member` fixture supplies the differential row and Lean
receipt, and extractor tests pin the dynamic boundary.

The refreshed **22,055-path** census moves **5,166 → 5,168 clean** and
**16,822 → 16,820 partial** (67 include skips). `AssignmentExpression:target`
falls **2,875 → 2,873** and `MemberAccessExpression` **1,019 → 1,018**;
`CallExpression` remains **2,801**. Differential coverage grows
**219/214/0/5 → 220/215/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Packed-union reshaped member windows — 2026-10-26

Constant element and part selections chained through an untagged packed-union
member now compose each fixed offset into the existing flat vector window.
Dynamic selectors, overlapping continuous drivers, tagged aggregates, and
nonintegral members remain loud. The `packed_union_reshaped_member` fixture
supplies the differential row and Lean receipt, and extractor tests retain the
dynamic and overlap boundaries.

The refreshed **22,055-path** census moves **5,168 → 5,169 clean** and
**16,820 → 16,819 partial** (67 include skips). `AssignmentExpression:target`
falls **2,873 → 2,872**; `CallExpression` remains **2,801**. Differential
coverage grows **220/215/0/5 → 221/216/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Literal wired-net resolution — 2026-10-26

Literal continuous drivers of `wand`, `wor`, `triand`, and `trior` nets now
resolve at time zero with the IEEE wired-AND and wired-OR four-state tables.
The extractor folds complete literal driver sets into one flat net write;
dynamic, strengthened, and mixed driver sets remain loud. The
`wired_net_resolution` fixture supplies the differential row and Lean receipt,
and extractor regressions cover vector resolution and dynamic-driver refusal.

The refreshed **22,055-path** census moves **5,132 → 5,166 clean** and
**16,856 → 16,822 partial** (67 include skips). `AssignmentExpression:target`
falls **2,905 → 2,875**; `CallExpression` remains **2,801** and
`ExpressionStatement:CallExpression` remains **2,778**. Differential coverage
grows **217/212/0/5 → 218/213/0/5** with no disagreements; grammar coverage
remains **217/90/127**.

## Static-scope `$sdf_annotate` calls — 2026-10-25

The self-check surface now erases `$sdf_annotate` when its SDF filename is a
literal and its optional module scope is a static elaborated scope. The
time-zero envelope has no timing-annotation state, so this form has no modeled
effect; dynamic filenames, nonstatic scopes, nonempty config files, and other
optional forms remain loud. The `sdf_static_scope` fixture supplies the
differential row and Lean receipt, and the SDF extractor regression pins the
static-scope boundary.

The refreshed **22,055-path** census moves **5,130 → 5,132 clean** and
**16,858 → 16,856 partial** (67 include skips). The
`ExpressionStatement:CallExpression` blocker falls **2,908 → 2,778** and is
overtaken by `AssignmentExpression:target` at **2,905**; 130 corpus call
sites match this static-scope form, and two of their files become clean.
Differential coverage grows **216/211/0/5 → 217/212/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Constant nested packed scalar selections — 2026-10-25

Constant element and part selections through two or more packed dimensions now
flatten to one offset in the root integral vector for both reads and writes.
Declared descending and ascending labels compose in source order; dynamic
labels and aggregate or member receivers remain loud. The
`packed_nested_scalar_select` fixture covers both range directions, scalar and
part selections, and four-state `x` preservation.

The refreshed **22,055-path** census moves **5,128 → 5,130 clean** and
**16,860 → 16,858 partial** (67 include skips). `AssignmentExpression:target`
falls **2,908 → 2,905**, while `ExpressionStatement:CallExpression` remains
**2,908**. Differential coverage grows **215/210/0/5 → 216/211/0/5** with no
disagreements; grammar coverage remains **217/90/127**.

## Nested multidimensional packed-array elements — 2026-10-25

Nested packed arrays now flatten to their contiguous integral vector for
constant element reads and writes. Canonical and upward ranges normalize their
declared labels, and packed enum leaves retain their element width. Dynamic
indices for elements wider than one bit remain loud because the runtime state
does not yet carry a symbolic slice stride. The `packed_array_multidim`
fixture supplies the differential row and Lean receipt; extractor regressions
cover canonical, upward, enum, and dynamic-index shapes.

The refreshed **22,055-path** census moves **5,084 → 5,126 clean** and
**16,904 → 16,862 partial** (67 include skips). `AssignmentExpression:target`
falls **2,937 → 2,908**, while `ExpressionStatement:CallExpression` remains
**2,910**. Differential coverage grows **212/207/0/5 → 213/208/0/5** with no
disagreements, and grammar coverage remains **217 witnesses, 90 MATCH, and
127 REFUSE**.

## Fixed-array `sort()` and `rsort()` after literal initialization — 2026-10-25

Fixed one-dimensional integral arrays now replay a complete blocking literal
pattern before `sort()` or `rsort()`, and repeated ordering calls consume the
previously sorted cell state. Signed values use their declared integral order;
unknown cells, aliases, dynamic or multidimensional arrays, and `with` clauses
remain loud. The `fixed_array_sort` fixture supplies both ascending and
descending checks with a Lean receipt; extractor regressions cover replay and
unknown-value refusal.

The refreshed **22,055-path** census moves **5,126 → 5,127 clean** and
**16,862 → 16,861 partial** (67 include skips). `ExpressionStatement:CallExpression`
falls **2,910 → 2,909** while `AssignmentExpression:target` remains **2,908**.
Differential coverage grows **213/208/0/5 → 214/209/0/5** with no
disagreements, and grammar coverage remains **217 witnesses, 90 MATCH, and
127 REFUSE**.

## Task-selected `$swriteb`/`$swriteo`/`$swriteh` packed writes — 2026-10-25

The self-check lowering now admits direct packed-integral destinations for the
IEEE 1800-2023 §21.3.3 task-selected binary, octal, and hexadecimal forms when
the source is an earlier blocking literal integral assignment. Four-state
groups retain their `x`/`z` spelling and the rendered bytes are right-aligned
in the packed destination. String targets, dynamic sources, timing controls,
and other task uses remain loud. The `swrite_default_radix` fixture supplies
the differential witness, generated envelope, and Lean receipt; extractor
tests cover the unknown-digit rendering and dynamic-source refusal.

The refreshed **22,055-path** census moves **5,127 → 5,128 clean** and
**16,861 → 16,860 partial** (67 include skips). The leading
`ExpressionStatement:CallExpression` blocker falls **2,909 → 2,908**; the
`AssignmentExpression:target` blocker remains **2,908**. Differential coverage
grows **214/209/0/5 → 215/210/0/5** with no disagreements, and grammar coverage
remains **217/90/127**.

## Enum `.name()` values — 2026-10-25

Enum `.name()` calls now lower to exact declaration-spelling string values in
the self-check embedding. The lookup is source-pure and returns the standard
empty string for a value outside the declaration; dynamic string operations and
array methods remain loud. The `enum_name_method` fixture covers both the
integral branch and the rendered name.

The refreshed **22,054-path** census moves **5,067 → 5,077 clean** and
**16,920 → 16,910 partial** (67 include skips); `CallExpression` falls
**2,827 → 2,799**. Differential coverage grows **210/205/0/5 → 211/206/0/5**
with no disagreements, and grammar coverage remains **217 witnesses, 90 MATCH,
and 127 REFUSE**.

## Finite integral-key associative-array cells — 2026-10-25

The extractor now represents a finite set of literal integral associative-array
keys as independent flat scalar cells when the values are scalar or packed
integral. Blocking reads and writes retain source order and four-state or
two-state value behavior. Dynamic keys, whole-array operations, methods, and
aggregate elements remain loud. The `assoc_integral_cells` fixture covers the
admitted path and its generated envelope and Lean receipt.

The refreshed **22,055-path** census moves **5,077 → 5,084 clean** and
**16,910 → 16,904 partial** (67 include skips); `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` moves
**2,909 → 2,910**. Differential coverage grows **211/206/0/5 → 212/207/0/5**
with no disagreements, and grammar coverage remains **217 witnesses, 90 MATCH,
and 127 REFUSE**.

## Discarded empty queue pops — 2026-10-25

Statement-position `void'(q.pop_front())` and `void'(q.pop_back())` now lower
to inert `Empty` statements when source-order analysis proves that the queue
is uninitialized or empty. The queue remains unchanged, matching IEEE
1800-2023 §§7.10.2.4–7.10.2.5. Nonempty or mutated queues, aliases, dynamic
receivers, and value-position pops retain their existing loud boundaries.

The refreshed **22,054-path** census moves **5,059 → 5,061 clean** and
**16,928 → 16,926 partial** (67 include skips); the two admitted witnesses
reduce `ExpressionStatement:CallExpression` **2,911 → 2,909**. Differential
coverage grows **205/200/0/5 → 206/201/0/5** with no disagreements, and the
grammar census is **217 witnesses, 90 MATCH, and 127 REFUSE**.

## Bounded `$isunbounded` queries — 2026-10-25

`$isunbounded(p)` now lowers to the exact one-bit zero when `p` is a known
bounded integral parameter (or a direct integral literal). Ordinary variables,
the special unbounded `$` parameter value, and non-parameter arguments remain
loud because their parameter binding is not represented in the self-check
state.

The refreshed **22,054-path** census moves **5,061 → 5,063 clean** and
**16,926 → 16,924 partial** (67 include skips); `CallExpression` falls
**2,833 → 2,831**. Differential coverage grows **206/201/0/5 → 207/202/0/5**
with no disagreements, and grammar coverage remains **217 witnesses, 90 MATCH,
and 127 REFUSE**.

## Fixed-width real conversion `$bits` queries — 2026-10-25

`$bits($realtobits(real_value))` and
`$bits($shortrealtobits(shortreal_value))` now fold their fixed 64- and 32-bit
results without observing opaque real storage. Direct `$bits` queries on named
real values, effectful conversion operands, and other real calls remain loud.
The `real_bits_query` fixture supplies the differential and Lean receipt.

The refreshed **22,054-path** census moves **5,063 → 5,064 clean** and
**16,924 → 16,923 partial** (67 include skips); `CallExpression` falls
**2,831 → 2,829**. Differential coverage grows **207/202/0/5 → 208/203/0/5**
with no disagreements, and grammar coverage remains **217 witnesses, 90 MATCH,
and 127 REFUSE**.

## Predefined string macro `.len()` queries — 2026-10-25

String variables assigned a predefined macro that elaborates to an ASCII
literal now expose the exact `.len()` result. The lowering uses the AST's
literal assignment and source order, so dynamic assignments and other string
methods remain loud. The `string_macro_len` fixture covers both a triple-quoted
macro and `` `__FILE__``.

The refreshed **22,054-path** census moves **5,064 → 5,066 clean** and
**16,923 → 16,921 partial** (67 include skips); `CallExpression` falls
**2,829 → 2,827**. Differential coverage grows **208/203/0/5 → 209/204/0/5**
with no disagreements, and grammar coverage remains **217 witnesses, 90 MATCH,
and 127 REFUSE**.

## Dynamic-array `.size` without parentheses — 2026-10-25

The constant dynamic-array allocation lowering now accepts the IEEE 1800-2023
§5.13 spelling `values.size` alongside `values.size()`. It still requires one
source-pure `new[N]` allocation and rejects later resizes, mutation, aliases,
and dynamic extents. The `dynamic_array_size_property` fixture supplies the
differential and Lean receipt.

The refreshed **22,054-path** census moves **5,066 → 5,067 clean** and
**16,921 → 16,920 partial** (67 include skips); `CallExpression` remains
**2,827**. Differential coverage grows **209/204/0/5 → 210/205/0/5** with no
disagreements, and grammar coverage remains **217 witnesses, 90 MATCH, and
127 REFUSE**.

The queue-declaration slice lowers an uninitialized 2-state queue to inert
metadata; queue initializers and all queue operations remain loud. The fresh
rerun keeps clean at **4,462** and partial at **17,507**, while
`VariableSymbol:2state` falls **3,989 → 3,839**. The differential matrix is
**32 rows, 28 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage is **200 witnesses, 68 MATCH, and 132 REFUSE**.

The dynamic-array declaration slice applies the same inert metadata rule to an
uninitialized 2-state dynamic array; allocation, initialization, and every
dynamic-array operation remain loud. Clean and partial totals stay **4,462 /
17,507**, while `VariableSymbol:2state` falls **3,839 → 3,691**. The
differential matrix is **33 rows, 29 matches, 0 disagreements, and 4 recorded
refusals**; grammar coverage remains **200 witnesses, 68 MATCH, and 132
REFUSE**.

The associative-array declaration slice applies the same inert metadata rule
to an uninitialized 2-state associative array; initializers, reads, writes,
and every 4-state associative array remain loud. The fresh rerun moves clean
files **4,505 → 4,506** and partial files **17,464 → 17,463** while
`VariableSymbol:2state` falls **3,691 → 3,501**. Differential coverage is
**37 rows, 33 matches, 0 disagreements, and 4 recorded refusals**; grammar
coverage remains **200 witnesses, 68 MATCH, and 132 REFUSE**.

## Literal-initialized procedural floating declarations — 2026-10-24

Pure numeric initializers on procedural `real` and `shortreal` declarations
are omitted from the flat self-check state, just like an uninitialized floating
declaration. Effectful initializers and all floating-point uses remain loud.
The current 22,048-path rerun keeps **4,784 clean** and moves **17,196 →
17,198 partial** with two additional corpus paths; `VariableSymbol:2state`
falls **2,376 → 2,351**. The `literal_real_decl` fixture supplies the
differential evidence.

## Literal string length queries — 2026-10-24

An unchanged pure string literal now exposes its exact `.len()` as an integral
literal while the string remains opaque. Writes, dynamic initializers,
non-ASCII contents, and other string methods remain loud. The 22,048-path
rerun moves **4,784 → 4,791 clean** and **17,198 → 17,191 partial**;
`CallExpression` falls **2,997 → 2,990**. The `literal_string_len` fixture
supplies the differential evidence.

Literal-only severity-task arguments now join the existing pure `$info` and
`$warning` slice: a literal format and literal values are erased, while
identifier or call arguments remain loud. The fresh rerun moves clean files
**4,462 → 4,467** and partial files **17,507 → 17,502**;
`ExpressionStatement:CallExpression` falls **3,764 → 3,759**. Differential
coverage is **34 rows, 30 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 68 MATCH, and 132 REFUSE**.

Literal `$error` calls now share the diagnostic-only lowering because IEEE
1800-2023 §20.10 requires simulation to continue after `$error`. The fresh
rerun moves clean files **4,467 → 4,476** and partial files **17,502 → 17,493**;
`ExpressionStatement:CallExpression` falls **3,759 → 3,749**. `$fatal` and
nonliteral `$error` arguments remain loud. Differential coverage is **35 rows,
31 matches, 0 disagreements, and 4 recorded refusals**.

Pure literal `$fatal` calls now lower to the existing whole-run halt, retaining
termination while omitting the unmodeled diagnostic stream. Dynamic finish
numbers and message arguments remain loud. The fresh rerun moves clean files
**4,476 → 4,505** and partial files **17,493 → 17,464**;
`ExpressionStatement:CallExpression` falls **3,749 → 3,602**. Differential
coverage is **36 rows, 32 matches, 0 disagreements, and 4 recorded refusals**.

The no-argument `$printtimescale` task now lowers to an inert diagnostic
statement; explicit scope arguments and all other time-format tasks remain
loud because hierarchy and time-scale state are not modeled. The fresh rerun
moves clean files **4,506 → 4,507** and partial files **17,463 → 17,462**;
`ExpressionStatement:CallExpression` falls **3,602 → 3,599**. Differential
coverage is **38 rows, 34 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage is **200 witnesses, 69 MATCH, and 131 REFUSE**.

The module-originating `$exit` task now lowers to an inert statement, matching
IEEE 1800-2023 §24.7's rule that `$exit` is ignored outside a program-originating
process. Program process control and other contexts remain loud. The fresh
rerun moves clean files **4,507 → 4,511** and partial files **17,462 → 17,458**;
`ExpressionStatement:CallExpression` falls **3,599 → 3,595**. Differential
coverage is **39 rows, 35 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

VCD setup tasks `$dumpfile` and `$dumpvars` now lower to inert statements.
They affect only external waveform output, which is outside the self-check
oracle; dynamic `$dumpfile` names remain loud. The fresh rerun moves clean files
**4,511 → 4,525** and partial files **17,458 → 17,444**;
`ExpressionStatement:CallExpression` falls **3,595 → 3,580**. Differential
coverage is **40 rows, 36 matches, 0 disagreements, and 4 recorded refusals**;
grammar coverage remains **200 witnesses, 69 MATCH, and 131 REFUSE**.

VCD control tasks `$dumpon`, `$dumpoff`, `$dumpall`, `$dumpflush`, and literal
`$dumplimit` now lower to inert statements. They affect only external waveform
recording, so the self-check observable state is unchanged; dynamic limits
remain loud. The fresh rerun moves clean files **4,525 → 4,540** and partial
files **17,444 → 17,429**; `ExpressionStatement:CallExpression` falls
**3,580 → 3,565**. Differential coverage is **41 rows, 37 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **200
witnesses, 69 MATCH, and 131 REFUSE**.

Whole copies of flattened integral unpacked structs now lower field by field,
sampling the source before destination writes; aggregate fields and self-copies
remain loud. The fresh rerun moves clean files **4,540 → 4,552** and partial
files **17,429 → 17,417**; `AssignmentExpression:target` falls **3,592 →
3,580**. Differential coverage is **42 rows, 38 matches, 0 disagreements, and
4 recorded refusals**; grammar coverage remains **200 witnesses, 69 MATCH, and
131 REFUSE**.

## Nested fixed two-state arrays — 2026-10-22

The legacy extractor now admits bounded fixed-size unpacked arrays with two
or more dimensions when their leaf type is integral and the declaration has
no aggregate initializer. Each finite leaf becomes an ordinary vector cell;
constant selections such as `matrix[1][2]` use that cell for reads and writes.
Dynamic arrays, queues, object/event/string/real leaves, effectful or
shape-mismatched patterns, and nonconstant selections remain loud. The new
`fixed_array_2state` differential row writes and reads a two-dimensional
`bit [3:0]` array and checks zero startup of an untouched cell;
`fixed_array_pattern_2state` checks nested replication; the
`fixed_array_packed_leaf_2state` row checks a multidimensional packed leaf.

Against the previous 22,045-path snapshot, clean files rise **4,326 → 4,345**
and partial files fall **17,653 → 17,634**. The `VariableSymbol:2state` wall
falls **5,744 → 5,666**; the related constant element-selection wall falls
**663 → 615**. The differential matrix is **14 rows, 10 matches, 0
disagreements, and 4 recorded refusals**.

The nested-pattern extension moves clean files **4,347 → 4,351** and partial
files **17,632 → 17,628**. `VariableSymbol:2state` falls **5,666 → 5,660**;
the differential matrix is now **16 rows, 12 matches, 0 disagreements, and 4
recorded refusals**.

The packed-leaf extension moves clean files **4,351 → 4,378** and partial
files **17,628 → 17,601**. `VariableSymbol:2state` falls **5,660 → 5,650**;
`AssignmentExpression:target` falls **3,980 → 3,961**. The differential
matrix is now **17 rows, 13 matches, 0 disagreements, and 4 recorded
refusals**.

## Shallow unpacked integral structs — 2026-10-22

An untagged, shallow unpacked `struct` whose fields are integral scalars or
packed vectors now lowers each field to its own ordinary vector cell. Direct
member reads, writes, and compound assignments use the flattened field name;
two-state fields retain zero startup and x/z-to-zero assignment conversion.
Whole-struct operations, nonintegral or array fields, initializers, dynamic
member forms, and tagged structs remain loud because the legacy state
has no aggregate slot. The `unpacked_struct_integral_fields` differential row
checks field updates and the resulting display.

The fresh census moves **4,378 → 4,409 clean** and **17,601 → 17,570
partial**, with zero extraction errors. `VariableSymbol:2state` falls
**5,650 → 5,556**, `AssignmentExpression:target` falls **3,961 → 3,922**,
and `MemberAccessExpression` falls **1,188 → 1,052**. The differential matrix
is **18 rows, 14 matches, 0 disagreements, and 4 recorded refusals**; the
grammar census remains **192 witnesses, 60 MATCH, and 132 REFUSE**.

## Unpacked struct aggregate initializers — 2026-10-22

Positional and complete keyed/default assignment patterns on shallow untagged
unpacked structs now lower to the existing field cells in declaration order.
Each field is converted at its own width and two-state boundary, so keyed
source order does not affect storage and `x`/`z` input is squashed for `bit`
fields. Partial, effectful, nested, and nonintegral aggregate forms remain
loud. The `unpacked_struct_initializers` fixture and differential row exercise
the admitted forms.

Clean files rise **4,409 → 4,413** and partial files fall **17,570 → 17,566**;
`VariableSymbol:2state` falls **5,556 → 5,551**. The differential matrix is
now **19 rows, 15 matches, 0 disagreements, and 4 recorded refusals**.

## Unpacked array concatenation initializers — 2026-10-22

The legacy cell representation now accepts a finite unpacked-array
declaration initializer whose concatenation mixes a constant source array,
integral elements, and an exact typed array pattern. Operands are flattened in
declared order and copied as already-sampled pure values; runtime source
arrays, self-aliases, width mismatches, and effectful forms remain loud. The
`unpacked_concat_initializer` row exercises the admitted shape.

Using the available 22,035-file snapshot, clean files rise **4,413 → 4,414**
and partial files fall **17,556 → 17,555**. `VariableSymbol:2state` falls
**5,548 → 5,547**; all other leading blocker counts are unchanged.

## Nested unpacked integral structs and arrays — 2026-10-22

Untagged unpacked structs now flatten recursively when every leaf is an
integral scalar or packed vector. Fixed unpacked arrays compose that lowering
at each constant position, so member reads and writes use names such as
`values[1].meta.count` while retaining ordinary two-state startup and
conversion. Whole struct values, aggregate array initializers, nonintegral
fields, and dynamic selections remain loud. The `unpacked_struct_array` row
exercises the nested array shape.

On the available 22,035-file snapshot, clean files rise **4,414 → 4,416** and
partial files fall **17,555 → 17,553**; `VariableSymbol:2state` falls
**5,532 → 5,521** and `MemberAccessExpression` **1,037 → 1,023**. The
differential matrix is **21 rows, 17 matches, 0 disagreements, and 4 recorded
refusals**; grammar coverage remains **192 witnesses, 60 MATCH, and 132
REFUSE**.

## Inert module event declarations — 2026-10-22

A module-scope named `event` declaration with no use in the time-zero
self-check path is now admitted as inert metadata. It does not enter the flat
vector state, while event waits, triggers, and other scheduler interactions
remain loud. The `event_declaration` differential row prints `PASS` and checks
the admitted declaration shape.

On the available 22,035-file snapshot, clean files rise **4,416 → 4,419** and
partial files fall **17,553 → 17,550**; `VariableSymbol:2state` falls
**5,521 → 5,276**. The differential matrix is **22 rows, 18 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage is **193 witnesses,
61 MATCH, and 132 REFUSE**.

## Inert module real declarations — 2026-10-22

A module-scope `real` or `shortreal` declaration with no use in the time-zero
self-check path is now admitted as inert metadata. It does not enter the flat
vector state; floating-point reads, writes, arithmetic, and formatting remain
loud. The `real_declaration` differential row prints `PASS` and checks the
declaration-only shape.

On the available 22,035-file snapshot, clean files rise **4,419 → 4,421** and
partial files fall **17,550 → 17,548**; `VariableSymbol:2state` falls
**5,276 → 4,990**. The differential matrix is **23 rows, 19 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage is **194 witnesses,
62 MATCH, and 132 REFUSE**.

## Inert chandle declarations — 2026-10-22

Module-scope and declaration-only local `chandle` variables are now admitted
as inert metadata on the time-zero self-check path. They do not enter the flat
vector state; handle reads, writes, and cross-type assignments remain loud. The
`chandle_declaration` differential row covers both scopes.

On the available 22,035-file snapshot, clean files rise **4,421 → 4,423** and
partial files fall **17,548 → 17,546**; `VariableSymbol:2state` falls
**4,990 → 4,954**. The differential matrix is **24 rows, 20 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage is **195 witnesses,
63 MATCH, and 132 REFUSE**.

## Null virtual-interface declarations — 2026-10-22

A module-scope virtual-interface variable initialized to `null` is now admitted
as inert metadata on the time-zero self-check path. It does not enter the flat
vector state; non-null interface handles, reads, writes, and interface
operations remain loud. The `virtual_interface_null_declaration` row covers the
admitted declaration.

On the available 22,035-file snapshot, clean files rise **4,423 → 4,424** and
partial files fall **17,546 → 17,545**; `VariableSymbol:2state` falls
**4,954 → 4,952**. The differential matrix is **25 rows, 21 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage is **199 witnesses,
67 MATCH, and 132 REFUSE**.

## Inert string declarations — 2026-10-22

Module-scope and declaration-only local `string` variables are now admitted as
inert metadata on the time-zero self-check path. They do not enter the flat
vector state; string reads, writes, concatenation, and formatting remain loud.
The `string_declaration` differential row covers both scopes.

On the available 22,035-file snapshot, clean files rise **4,424 → 4,427** and
partial files fall **17,545 → 17,542**; `VariableSymbol:2state` falls
**4,952 → 4,135**. The differential matrix is **26 rows, 22 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **199
witnesses, 67 MATCH, and 132 REFUSE**.

## Nested unpacked-struct initializers — 2026-10-23

Complete assignment patterns for unpacked struct trees now flatten recursively
into leaf cells. Positional, keyed, and default values are converted at each
leaf width with ordinary two-state squashing; partial, effectful, nonintegral,
and aggregate-array forms remain loud. The `nested_struct_initializers` row
covers nested defaults and keyed fields.

On the available 22,035-file snapshot, clean files rise **4,427 → 4,429** and
partial files fall **17,542 → 17,540**; `VariableSymbol:2state` falls
**4,135 → 4,133**. The differential matrix is **27 rows, 23 matches, 0
disagreements, and 4 recorded refusals**; grammar coverage remains **199
witnesses, 67 MATCH, and 132 REFUSE**.

## Constant out-of-bounds fixed-array writes — 2026-10-22

The target tier now handles the IEEE §7.4.5 rule that a fully constant
out-of-range index on a fixed unpacked array performs no update. The extractor
checks every fixed dimension and emits an `Empty` statement after requiring a
pure RHS; in-range and dynamic selections retain their existing target rules.
`fixed_array_oob` is the pinned differential witness.

Clean files rise **4,345 → 4,347** and partial files fall **17,634 → 17,632**.
The `AssignmentExpression:target` wall falls **3,982 → 3,980**; the other
blocker counts are unchanged.

## Assignment-target boundary — 2026-10-21

`AssignmentExpression:target` occurs in **4,030** files of the fresh
22,043-path census. It is the sole recorded refusal in **43** files and
co-occurs with another refusal in **3,987**. The target-only repricer finds
**79** instances: 27 whole aggregate/array targets, 32 dynamic element
targets, 14 packed or unpacked part-select targets, three concatenated or
streaming targets, two constant element/bit targets, and one keyed/default or
replicated pattern target. These shape counts are over the 43 sole-refusal
files and may overlap by file.

The existing target matrix already covers whole identifiers, fixed packed
windows, direct untagged packed-struct/union fields, expanded fixed-array
cells, and the tested pure concatenation/streaming leaves. The residual sole
files mix procedural aggregate/slice/stream forms with generated continuous
drivers; they need aggregate or runtime-index state, or the scheduler-owned
continuous-assignment path. The legacy loader has no such continuous-driver
rule, so this item adds no target lowering and introduces no aggregate store or
second scheduler. The complete boundary and reproduction command are in
[assignment targets](sv-assignment-targets.md).

## Statement-call boundary — 2026-10-21

`ExpressionStatement:CallExpression` occurs in **3,791** files of the fresh
22,043-path census. It is the sole refusal in **261** files and co-occurs in
**3,530**. The call-only repricer finds **498** unsupported statement-call
instances. The largest heads are `$fatal` (74), `$q_add` (46),
`$q_initialize` (34), `$dumpvars` (30), `$strobe` (29), `$dumpfile` (27),
`$monitor` (20), `$info` (19), `$q_remove` (19), and `$warning` (17).

The public statement-call matrix remains `$display`, `$write`, `$finish`, and
`$stop`, with the existing pure argument and output/halt rules. The residual
heads require diagnostic/status channels, Postponed scheduling, aggregate or
device state, external I/O, or an explicit random oracle. No call-only head
can be admitted independently without changing those representations. The
full boundary and repricing command are in [call statements](sv-call-statements.md).

## Call-expression boundary — 2026-10-21

`CallExpression` occurs in **3,291** files of the fresh 22,043-path census.
It is the sole refusal in **212** files and co-occurs in **3,079**. The
call-expression repricer finds **315** unsupported expression-call instances;
the largest heads are `$random` (30), `$dist_uniform` (23), `$urandom` (21),
`$stable` (19), `$rose` (18), `$changed` (15), `$past` (15), and
`std::randomize` (15).

The admitted expression-call surface remains fixed metadata queries, pure and
runtime `$clog2`, the time-zero `$time` literal, and dynamic integral `$cast`
through their existing contracts. Residual calls need an explicit random
oracle, sampled scheduler history, elapsed-time/unit state, external effects,
unsupported value types, or callable frames. No call-only head is admitted by
folding or discarding those effects. The complete boundary and reproduction
command are in [call expressions](sv-call-expressions.md).

## Procedural variable lifetimes — 2026-10-20

IEEE §6.21/§9.3 static scalar, packed and fixed-array procedural storage now
initializes once before process entry. Named-block references preserve bound
identity; declaration re-entry retains storage. Actual automatic scalars use
per-entry initialization and the existing retained continuation across waits.
Dependent/effectful static initialization, invalid source and the observed
implicit automatic-module lifetime disagreement remain explicit refusals.
See [the contract](sv-procedural-lifetimes.md).

The paired **22,035** paths gain **20 clean extractions** and withdraw **35**
prior admissions: **4,341 → 4,326 clean**, **17,628 → 17,643 partial**,
**66 include skips**, zero errors. Nineteen gained simulations and eight authored
programs match complete independent transcripts under both tested orders.
One gained compile-warning case remains horizon-limited; four authored programs
refuse. All 32 successful references are authenticated. The 1,141 changed prior
clean designs have identical paired model statuses/transcripts (1,116 completed,
17 runtime refusals, eight loader refusals); this is regression telemetry only.
Four source-bound kernel theorems cover initialization, entry retention and
retained modular increments. Extraction is distinct from execution conformance.

## Residual static initializers — 2026-10-22

`StaticLocal:initializer` remains the nonclosed static-initializer boundary.
The fresh **22,043**-path census records it in **167** files: **40** are
initializer-only and **127** co-occur with another wall. Repricing the sole
files finds **47** spans: **9** random or constrained-random calls, **13**
system-function calls, **3** macro expansions, **2** package/qualified reads,
**7** type or size casts, **6** real conversions, **5** shifts, **3** powers,
**5** bitwise expressions, **1** conditional, **1** aggregate assignment
pattern and **39** runtime-dependent reads (features overlap). Closed pure
values remain admitted; the envelope has no ordered pre-process evaluator,
random/environment oracle or general conversion context, so no initializer is
folded, dropped or run as a module process. See [the static-initializer
boundary](sv-static-initializers.md) and
`extractors/sv/static_initializer_reprice.py` for the reproducible scan.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 60 | 239 | 1 |
| 4 | 427 | 187 | 240 | 0 |
| 5 | 618 | 363 | 255 | 0 |
| 6 | 1185 | 428 | 757 | 0 |
| 7 | 796 | 118 | 678 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 114 | 475 | 0 |
| 10 | 657 | 248 | 409 | 0 |
| 11 | 1034 | 736 | 298 | 0 |
| 12 | 627 | 294 | 333 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 50 | 1493 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 212 | 613 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 383 | 161 | 28 |
| 23 | 851 | 174 | 677 | 0 |
| 24 | 355 | 2 | 353 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 165 | 400 | 0 |
| 27 | 354 | 177 | 177 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 124 | 103 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 137 | 280 | 0 |
| 38 | 340 | 211 | 129 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Let expressions — 2026-10-20

IEEE §11.12 templates now use the frontend's ordinary bound expressions,
with declaration-order validation and distinct lexical storage identities.
Module/generate/package/unit/procedural scopes compose. Nonmodule roots,
unsupported expanded operations and invalid source remain loud.
See [the contract](sv-let-expressions.md).

The paired **22,035** paths gain **33 clean extractions** and withdraw **12**
prior program admissions: **4,320 → 4,341 clean**, **17,649 → 17,628 partial**,
**66 include skips**, zero errors. Of the prior clean designs, 4,297 are identical,
11 receive corrected lexical storage names and all eleven match independent
execution under both tested region oracles. Twenty-nine gained files and seven
authored programs match complete transcripts under both orders. Two gained
files retain runtime refusals; two lack explicit-formal-type oracle support.
Three authored refusals and two authored oracle limitations remain separate.
Fifty-one successful final-source references were authenticated. Four kernel
theorems bind the actual parsed template/shadow/copyback fixture. These counts
measure extraction and selected execution coverage separately.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 55 | 244 | 1 |
| 4 | 427 | 187 | 240 | 0 |
| 5 | 618 | 368 | 250 | 0 |
| 6 | 1185 | 435 | 750 | 0 |
| 7 | 796 | 117 | 679 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 111 | 478 | 0 |
| 10 | 657 | 248 | 409 | 0 |
| 11 | 1034 | 747 | 287 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 50 | 1493 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 216 | 609 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 386 | 158 | 28 |
| 23 | 851 | 171 | 680 | 0 |
| 24 | 355 | 2 | 353 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 166 | 399 | 0 |
| 27 | 354 | 177 | 177 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 124 | 103 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 137 | 280 | 0 |
| 38 | 340 | 211 | 129 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Fixed-array reduction methods — 2026-10-20

IEEE §7.12/§7.12.3 array `sum`, `product`, `and`, `or` and `xor` now use
intrinsic element/`with` widths and symbol-bound iterator substitution through
the existing fixed-cell storage and integral operations. Pure nested reductions,
packed fields, hierarchy, automatic lifetimes and timing compose. Dynamic
storage, unsupported types/effects/iterator queries, invalid source and symbolic
mode remain loud. No evaluator or scheduler changes. See [the contract](sv-array-reductions.md).

The paired **22,035** paths gain **11 clean extractions**, no losses:
**4,309 → 4,320 clean**, **17,660 → 17,649 partial**, **66 include skips**,
zero errors. All 4,309 previously clean extracted designs remain identical.
All eleven gains and six authored programs match complete independent
transcripts under both tested region oracles. Two authored programs retain
explicit refusals; they are not execution agreements. Nineteen final independent
invocations were authenticated. Four source-bound kernel theorems cover live
reads, modular arithmetic, copyback and source preservation. Extraction is
distinct from runtime conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 54 | 245 | 1 |
| 4 | 427 | 187 | 240 | 0 |
| 5 | 618 | 368 | 250 | 0 |
| 6 | 1185 | 436 | 749 | 0 |
| 7 | 796 | 117 | 679 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 111 | 478 | 0 |
| 10 | 657 | 248 | 409 | 0 |
| 11 | 1034 | 722 | 312 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 50 | 1493 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 216 | 609 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 385 | 159 | 28 |
| 23 | 851 | 170 | 681 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 165 | 400 | 0 |
| 27 | 354 | 176 | 178 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 123 | 104 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 136 | 281 | 0 |
| 38 | 340 | 211 | 129 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Dynamic integral casts — 2026-10-20

IEEE §6.24.2/§20.5 dynamic integral casts now sample once, convert to the
destination width/state kind, and test an enum's exact bound member table.
Function failure returns zero without a destination write; success stores the
converted snapshot and returns one. Whole values, packed windows/members and
fixed cells use existing stores. The existing plusargs sequencer also sequences
casts, retaining logical short circuiting and refusing unordered dependencies.
Task success uses the same rule; invalid task diagnostics, unsupported types,
effects/contexts, invalid source and symbolic mode remain loud. No evaluator
or scheduler changes. See [the contract](sv-dynamic-cast.md).

The paired **22,035** paths gain **13 clean extractions**, no losses:
**4,296 → 4,309 clean**, **17,673 → 17,660 partial**, **66 include skips**,
zero errors. All 4,296 previously clean extracted designs remain identical.
Twelve gains match complete independent transcripts under both region oracles;
one retains the existing timed `$time` refusal. Six authored sources match
both orders, and four retain explicit boundaries. The invalid task reference
produces a runtime diagnostic and status one; it is not an agreement. Final
source/status/transcript/provenance authentication covers 22 successful
independent invocations plus that one diagnostic invocation. Six kernel
theorems bind the actual parsed source capture, membership guard and success
body. Extraction is distinct from whole-corpus runtime conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 54 | 245 | 1 |
| 4 | 427 | 187 | 240 | 0 |
| 5 | 618 | 368 | 250 | 0 |
| 6 | 1185 | 436 | 749 | 0 |
| 7 | 796 | 106 | 690 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 111 | 478 | 0 |
| 10 | 657 | 248 | 409 | 0 |
| 11 | 1034 | 722 | 312 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 50 | 1493 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 216 | 609 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 385 | 159 | 28 |
| 23 | 851 | 170 | 681 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 165 | 400 | 0 |
| 27 | 354 | 176 | 178 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 123 | 104 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 136 | 281 | 0 |
| 38 | 340 | 211 | 129 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Static portless module hierarchy — 2026-10-20

IEEE clauses 23/27 elaboration now flattens actual portless module instances,
including parameter overrides, generated instances, static instance arrays
and bound parent/child/sibling/upward references. Per-instance storage and
procedural locals remain distinct, including when the frontend shares a
canonical template. Package storage is shared once. Existing executors and
region oracles apply; ports, program/interface kinds, differing timescales,
new initializer-order dependence and unsupported active members remain loud.
See [the contract](sv-module-hierarchy.md).

## Connected child ports — 2026-10-21

`Hierarchy:ports` remains the explicit boundary for a module instance with a
declared port. The fresh **22,043**-path census records this wall in **2,397**
files: **1,186** port-only and **1,211** co-occurring. Frontend-instance
repricing of the port-only files finds **1,481** concrete child instances and
**3,593** declared ports. **1,423** instances have every port connected,
**43** have at least one empty/omitted connection, and **15** are entirely
unconnected. The connected cases include ordinary scalar links as well as
conversions, selections, concatenations and `inout`; all require a port map,
continuous propagation, and scheduler-owned update behavior. The omitted
cases retain default/`z` input rules. No safe subfamily is admitted by the
existing flat store. See [the boundary](sv-hierarchy-ports.md) and
`extractors/sv/hierarchy_reprice.py` for the reproducible measurement.

## Program and interface hierarchy — 2026-10-21

`Hierarchy:module-kind` remains the boundary for a concrete `program` or
`interface` instance. The fresh **22,043**-path census records this wall in
**1,248** files: **319** module-kind-only and **929** co-occurring. Repricing
the sole files finds **365** non-module instances: **330** programs and **35**
interfaces. The instances include **57** top-level programs, **273** nested
programs and **35** nested interfaces; **279** are portless and **86** have
ports. Program reactive/completion behavior and interface modport/clocking
and design-signal behavior cannot be represented by the ordinary module
executor, so no subfamily is admitted. See [the boundary](sv-hierarchy-kinds.md)
and `extractors/sv/hierarchy_kind_reprice.py` for the reproducible scan.

## Subroutines — 2026-10-21

`SubroutineSymbol:Subroutine` remains the callable declaration boundary. The
fresh **22,043**-path census records it in **1,714** files: **108**
subroutine-only and **1,606** co-occurring. Repricing the sole files finds
**126** declarations: **70** functions, **23** tasks and **33** DPI imports.
Function activation/return/local state, task blocking and argument copyback,
and DPI external effects have no representation in the current envelope or
executor. Constant-function candidates require a separate elaboration
evaluator. No subfamily is admitted by this item. See [the boundary](sv-subroutines.md)
and `extractors/sv/subroutine_reprice.py` for the reproducible scan.

## Primitive instances — 2026-10-21

`PrimitiveInstanceSymbol:PrimitiveInstance` remains the structural-driver
boundary. After the primitive-array extractor fix, the fresh **22,043**-path
census records it in **1,153** files: **583** primitive-only and **570**
co-occurring. Repricing the sole files finds **811** concrete instances:
**392** logic gates, **121** conditional gates, **146** MOS switches, **78**
tran switches and **74** pull sources. **120** carry delays and **691** do
not. Continuous drivers, four-state net resolution, strengths and delayed
publication are absent from the current store, so no primitive family is
admitted. See [the boundary](sv-primitives.md) and
`extractors/sv/primitive_reprice.py` for the reproducible scan.

## Concurrent assertions — 2026-10-21

`ConcurrentAssertionStatement` remains the sampled-property boundary. The
fresh **22,043**-path census records it in **1,358** files: **539**
assertion-only and **819** co-occurring. Repricing the sole files finds
**639** statements: **562** `assert property`, **37** `cover property`, **9**
`assume property`, **8** `cover sequence`, **21** `expect` and **2**
`restrict` forms. Preponed sampling, Observed evaluation, sequence-attempt
state and Reactive/coverage actions have no representation in the current
executor, so no flavor is admitted. See [the boundary](sv-concurrent-assertions.md)
and `extractors/sv/concurrent_assert_reprice.py` for the reproducible scan.

## Property declarations — 2026-10-21

`PropertySymbol:Property` remains the named concurrent-property declaration
boundary. The fresh **22,043**-path census records it in **471** files:
**10** property-only and **461** co-occurring. Repricing the sole files finds
**11** unsupported property spans. Overlapping source features include **6**
clocked spans, **4** implication spans, **3** formal-property-argument
spans, **2** with local variables, **2** with sampled functions, **1** with
abort/disable controls and **1** with an `endproperty` label. Formal
arguments, sampled history and sequence-attempt state have no representation
in the envelope, so no declaration shape is admitted. See [the property
boundary](sv-properties.md) and `extractors/sv/property_reprice.py` for the
reproducible scan.

## Covergroup declarations — 2026-10-21

`CovergroupType:CovergroupType` remains the verification-object boundary. The
fresh **22,043**-path census records it in **725** files: **8** covergroup-only
and **717** co-occurring. Repricing the sole files finds **9** unsupported
covergroup spans. Overlapping features include **9** coverpoints, **6** bin
declarations, **3** clocked samples, **3** sample-argument directions, **2**
options, **2** sample methods, **1** `with` expression and **1** cross.
Sampling events, bin databases and cross state have no representation in the
envelope, so no covergroup shape is admitted. See [the covergroup boundary](sv-covergroups.md)
and `extractors/sv/covergroup_reprice.py` for the reproducible scan.

## Compilation-unit covergroups — 2026-10-21

The separate `CovergroupType` marker covers a covergroup declared outside a
module. The fresh **22,043**-path census records it in **5** files: **3**
covergroup-only and **2** co-occurring. Repricing the sole files finds **3**
spans: **3** clocked, **3** `extends`, **4** coverpoint and **2** bin rows
(features overlap). Top-level inheritance errors retain the same coverage
object boundary; no compilation-unit covergroup is admitted. See
[the covergroup boundary](sv-covergroups.md) and
`extractors/sv/top_covergroup_reprice.py` for the reproducible scan.

## Parameterized class declarations — 2026-10-21

`GenericClassDefSymbol` remains the generic object/elaboration boundary. The
fresh **22,043**-path census records it in **146** files: **10**
generic-class-only and **136** co-occurring. Repricing the sole files finds
**10** parameterized class spans. Feature rows overlap: **9** value-parameter,
**5** type-parameter, **8** virtual-class, **7** typedef-member, **2**
static-method, **2** packed-aggregate-type and **1** local-parameter spans.
No default specialization is admitted. See [the generic-class boundary](sv-generic-classes.md)
and `extractors/sv/generic_class_reprice.py` for the reproducible scan.

## Generic class member and scope uses — 2026-10-21

`GenericClassDefSymbol:GenericClassDef` remains the member/scope elaboration
boundary for parameterized classes. The fresh **22,043**-path census records
it in **39** files: **2** generic-class-use-only and **37** co-occurring.
Repricing the sole files finds **2** spans, with one value-parameter member,
one type-parameter member, one local-parameter member and one class-scope
resolution row (features overlap). No parameter iteration or type-scope lookup
is admitted. See [the generic-class boundary](sv-generic-classes.md) and
`extractors/sv/generic_class_use_reprice.py` for the reproducible scan.

## Type parameters — 2026-10-21

`TypeParameterSymbol:TypeParameter` remains the type-binding boundary. The
fresh **22,043**-path census records it in **18** files: **8**
type-parameter-only and **10** co-occurring. Repricing the sole files finds
**9** spans: **3** empty frontend spans, **4** `type(...)` operator spans and
**2** typed-default spans (features overlap). No type override or dependent
declaration is reduced to a default. See [the type-parameter boundary](sv-type-parameters.md)
and `extractors/sv/type_parameter_reprice.py` for the reproducible scan.

## Final procedures — 2026-10-21

`ProceduralBlockSymbol:Final` remains the end-of-simulation shutdown boundary.
The fresh **22,043**-path census records it in **88** files: **39** are
final-only and **49** co-occurring. Repricing the sole files finds **45** final
spans. Their overlapping source features include **39** block bodies,
**33** assignments or increments, **38** `$display` calls, **4** `$finish`
calls, **2** assertion/`$fatal` sites, **3** delays, **1** `wait` and **1**
`$time` query. Final procedures run once at simulation completion in a
function-like shutdown context, after the finish condition and with distinct
ordering/completion rules; they are not `initial`, delayed, or independent
concurrent processes. The envelope has no final-invocation context or
end-of-simulation queue, so no final body is admitted by running it at time
zero or by inventing another scheduler. See [the final boundary](sv-final.md)
and `extractors/sv/final_reprice.py` for the reproducible scan.

## Implicit event controls — 2026-10-22

`TimedStatement:ImplicitEventControl` remains the inferred-sensitivity
boundary for `@*` and `@(*)`. The fresh **22,043**-path census records it in
**53** files: **38** are implicit-control-only and **15** co-occurring.
Repricing the sole files finds **38** spans: **29** bare `@*` and **9**
`@(*)`, with **25** block bodies, **14** case statements, **5** indexed
selects, **4** conditionals, **3** nested controls, **3** concatenations and
**1** system call (features overlap). The envelope has no inferred read-set or
rearming state, so no implicit control is admitted by guessing a sensitivity
list or executing it once. See [the implicit-event boundary](sv-implicit-events.md)
and `extractors/sv/implicit_event_reprice.py` for the reproducible scan.

## Unique case statements — 2026-10-22

`CaseStatement:Unique` remains the first-match plus diagnostic boundary. The
fresh **22,043**-path census records it in **45** files: **37** are unique-case
only and **8** co-occurring. Repricing the sole files finds **38** spans:
**20** have a `default` arm in **19** files, **9** use nonblocking updates,
**5** use indexed selects, **4** use multi-label items, **4** are `casez`, **1** is `casex`, **1**
uses `inside` and **1** has a nested block (features overlap). The envelope has
no unique-violation diagnostic channel or retained case-check state, so no
qualifier is erased and no fixed arm is selected. See [the unique-case
boundary](sv-unique-cases.md) and `extractors/sv/unique_case_reprice.py` for
the reproducible scan.

## Unique-if statements — 2026-10-22

`ConditionalStatement:Unique` remains the first-match plus all-condition
diagnostic boundary. The fresh **22,044**-path census records it in **20**
files: **16** are unique-if-only and **4** co-occurring. Repricing the sole
files finds **16** spans: **10** no-match paths without a final `else`, **6**
explicit `else` fallbacks, **4** potentially multiple-true chains, **3**
`always_comb` contexts, **2** reschedule-flush rows, one nested chain, one
`always` context, one Observed-region report, one event-resume flush, one loop
context and one invalid qualifier after `else` (features overlap). The
ordinary conditional envelope has no uniqueness status, all-condition
evaluation record or pending-report state, so no qualifier is erased and no
arm is selected. See [the unique-if boundary](sv-unique-if.md) and
`extractors/sv/unique_if_reprice.py` for the reproducible scan.

## Priority case statements — 2026-10-22

`CaseStatement:Priority` remains the first-match plus no-match diagnostic
boundary. The fresh **22,044**-path census records it in **12** files, all
priority-case-only. Repricing finds **13** spans: **6** without a `default`,
**7** with one, **5** indexed selects, **4** `casez`, **6** wildcard labels,
**3** `inside` cases, **4** multi-label items, **2** `always_comb` contexts
and one explicit no-match violation row (features overlap). The ordinary case chain lacks priority status and a no-match
diagnostic channel, so no qualifier is erased and no arm is selected. See
[the priority-case boundary](sv-priority-cases.md) and
`extractors/sv/priority_case_reprice.py` for the reproducible scan.

## Priority-if statements — 2026-10-22

`ConditionalStatement:Priority` remains the listed-order first-match plus
no-match diagnostic boundary. The fresh **22,044**-path census records it in
**9** files, all priority-if-only. Repricing finds **9** spans: **6** explicit
`else` fallbacks, **2** no-match paths without a final `else`, **4**
potentially multiple-true chains, **2** indexed selects, **2** `always_comb`
contexts, one explicit no-match violation and one invalid qualifier after
`else` (features overlap). The ordinary conditional chain lacks priority
status and a no-match diagnostic channel, so no qualifier is erased and no
branch is selected. See [the priority-if boundary](sv-priority-if.md) and
`extractors/sv/priority_if_reprice.py` for the reproducible scan.

## Unique0 case statements — 2026-10-22

`CaseStatement:Unique0` remains the first-match plus multiple-match
diagnostic boundary with an explicitly allowed no-match. The fresh **22,044**-
path census records it in **8** files, all unique0-case-only. Repricing finds
**10** spans: **10** no-match-allowed paths without a `default`, **9** no-match
rows without violation, **3** `casex`, **4** wildcard labels, **2** indexed
selects, **2** `inside` cases, one `casez` and one multiple-match violation
row (features overlap). The
ordinary case chain has no overlap status, so no qualifier is erased, no arm
is selected and no no-match behavior is invented. See [the unique0-case
boundary](sv-unique0-cases.md) and
`extractors/sv/unique0_case_reprice.py` for the reproducible scan.

## Randcase statements — 2026-10-22

`RandCaseStatement` remains the weighted-random branch boundary. The fresh
**22,043**-path census records it in **35** files: **31** are randcase-only and
**4** co-occurring. Repricing the sole files finds **33** spans: **3**
all-zero-weight cases, **12** with a zero-weight branch, **10** expression-
weight spans, **7** indexed targets, **21** increments and **1** branch block
(features overlap). The envelope has no random oracle, sampled weight vector
or weighted-selection trace, so no branch is chosen by a fixed seed or source
order. See [the randcase boundary](sv-randcase.md) and
`extractors/sv/randcase_reprice.py` for the reproducible scan.

## Disable statements — 2026-10-22

`DisableStatement` remains the named-scope cancellation boundary. The fresh
**22,043**-path census records it in **45** files: **28** are disable-only and
**17** co-occurring. Repricing the sole files finds **28** spans: **25** named
targets, **2** escaped targets and **1** statement label. A disable terminates
the selected named block or statement label, skips its remaining statements and
resumes after that scope; named forks and blocks can also cancel retained child
activity. The envelope has no target-scope identity, cancellation token or
retained continuation tree, so no target is guessed and no disable is lowered
to `break`, return or silent child cancellation. See [the disable boundary](sv-disable.md)
and `extractors/sv/disable_reprice.py` for the reproducible scan.

## Specify blocks — 2026-10-22

`SpecifyBlockSymbol:SpecifyBlock` remains the structural timing-model boundary.
The fresh **22,043**-path census records it in **54** files: **28** are
specify-only and **26** co-occurring. Repricing the sole files finds **28**
spans: **14** timing checks, **12** module paths, **14** edge-sensitive forms,
**10** scalar delays, **7** notifier references, **5** state-dependent paths,
**4** indexed terminals, **3** conditional paths, **3** polarity forms, **2**
tuple delays, **1** `ifnone` path, **1** illegal edge specification, **1**
invalid concurrent assertion and **1** invalid system task (features overlap).
The envelope has no path-delay graph, timing-check monitor, pulse state or
notifier publication, so no specify declaration is dropped or run as a
procedural block. See [the specify boundary](sv-specify.md) and
`extractors/sv/specify_reprice.py` for the reproducible scan.

## Net aliases — 2026-10-22

`NetAliasSymbol:NetAlias` remains the bidirectional net-topology boundary. The
fresh **22,043**-path census records it in **35** files: **25** are alias-only
and **10** co-occurring. Repricing the sole files finds **31** spans: **11**
indexed-select spans in **7** files, **4** chained aliases, **12** declarations
in **6** files with multiple alias statements, **4** alias spans in **3**
generated placements and **1** protected-region span (features overlap). The
envelope has no alias graph or resolved-driver topology, so no alias is erased,
made one-way or replaced by an initial assignment. See [the net-alias boundary](sv-net-alias.md)
and `extractors/sv/net_alias_reprice.py` for the reproducible scan.

## Package initializers — 2026-10-22

`Package:initializer` remains the package initialization-order boundary. The
fresh **22,043**-path census records it in **41** files: **25** are
initializer-only and **16** co-occurring. Repricing the sole files finds **35**
spans: all **35** contain a runtime variable reference, **14** use arithmetic
in **11** files, **6** contain multiple referenced identifiers, **1** uses a
qualified package reference, and **19** occur in **9** files with multiple
initializers (features overlap). Export contexts occur in **24** spans across
**17** files, including **9** wildcard-export spans in **5** files. The
envelope has no dependency graph or initialization phase for these reads, so no
initializer is folded to a constant, dropped or run as a module process. See
[the package-initializer boundary](sv-package-initializers.md) and
`extractors/sv/package_initializer_reprice.py` for the reproducible scan.

## Event lists — 2026-10-22

`TimedStatement:EventListControl` remains the multi-event wait boundary. The
fresh **22,043**-path census records it in **38** files: **24** are event-list-
only and **14** co-occurring. Repricing the sole files finds **25** spans:
**21** `or` lists, **6** comma lists, **10** edge events, **4** `iff` filters,
**3** lists with at least three events, **4** block bodies, **3** `always_ff`
controls, **1** parenthesized list, **1** indexed expression and **1**
procedural assign/deassign (features overlap). The envelope has no multi-event
registration, per-event guard or retained rearming state, so no list is reduced
to one signal or a fixed sequence. See [the event-list boundary](sv-event-lists.md)
and `extractors/sv/event_list_reprice.py` for the reproducible scan.

## Clocking blocks — 2026-10-22

`ClockingBlockSymbol:ClockingBlock` remains the scheduler-region synchronization
boundary. The fresh **22,043**-path census records it in **562** files: **24**
are clocking-only and **538** co-occurring. Repricing the sole files finds **24**
spans: **8** global declarations, **4** default declarations, **8** input
clockvar forms, **5** output clockvar forms, **4** sequence/property-containing
blocks, **5** nested event/control forms (including **1** nested clocking block),
**3** generated placements, **1** skew declaration, **1** end-label and **1**
unnamed clocking block (features overlap). The envelope has no clockvar
sample/drive queues, skew representation or region bridge, so no clocking block
is reduced to an ordinary event wait. See [the clocking-block boundary](sv-clocking-blocks.md)
and `extractors/sv/clocking_reprice.py` for the reproducible scan.

## Invalid package compilations — 2026-10-22

`Package:invalid-compilation` remains the package diagnostic boundary. The
fresh **22,043**-path census records it in **146** files: **24** are
invalid-package-only and **122** co-occurring. Repricing the sole files finds
**24** diagnostic spans: **3** repeated-timeunit declarations, **19** import
cases, **10** files with multiple imports, **9** wildcard imports, **8** export
cases, **6** combined import/export cases, **1** `export *::*` case and **2**
exports without a corresponding import (features overlap). The envelope keeps
the frontend rejection as a design-level marker; it does not salvage package
declarations or choose an import resolution. See [the invalid-package boundary](sv-package-invalid.md)
and `extractors/sv/package_invalid_reprice.py` for the reproducible scan.

## Procedural continuous assignments and force/release — 2026-10-22

`ProceduralAssignStatement` remains the retained-driver boundary. The fresh
**22,043**-path census records it in **112** files: **23** are
procedural-assign-only and **89** co-occurring. Repricing the sole files finds
**27** spans: **16** `assign` and **11** `force`, **13** nonliteral RHS
expressions, **6** explicit reevaluation/sensitivity scenarios, **7** priority
cases, **6** active-assignment replacements, **3** mixed-assignment
diagnostics, **3** net targets, **24** variable targets, **1** concatenation
LHS, **1** part-select LHS, **1** event-triggered process and **2** chapter-37
statement forms (features overlap). The envelope has no procedural-driver,
force-priority or release-restoration state, so these forms are not lowered to
ordinary assignments. See [the procedural assign boundary](sv-procedural-assign.md)
and `extractors/sv/procedural_assign_reprice.py` for the reproducible scan.

## Defparam overrides — 2026-10-22

`DefParamSymbol:DefParam` remains the hierarchy-elaboration override boundary.
The fresh **22,043**-path census records it in **49** files: **23** are
defparam-only and **26** co-occurring. Repricing the sole files finds **33**
spans: **33** hierarchical targets, **13** deep paths, **4** instance-array
elements, **9** last-wins cases, **6** multi-target statements, **2** RHS
parameter references, **1** RHS arithmetic form, **2** instance-precedence
cases, **1** generate-order case, **2** invalid cross-array diagnostics,
**1** dependent-parameter chain and **1** chapter-37 type form (features
overlap). The envelope has no hierarchy-wide parameter environment or
parameter-before-generate pass, so defparam is not rewritten as a local or
inline override. See [the defparam boundary](sv-defparam.md) and
`extractors/sv/defparam_reprice.py` for the reproducible scan.

## Net delays — 2026-10-22

`NetSymbol:delay` remains the delayed-net publication boundary. The fresh
**22,043**-path census records it in **27** files: **21** are net-delay-only
and **6** co-occurring. Repricing the sole files finds **22** spans: **8**
declaration-time continuous-assignment forms, **9** rise/fall forms, **2**
turn-off forms, **1** min:typ:max form, **3** vectors, **4** four-state
`z` transitions, **3** inertial cancellation/rescheduling cases, **5**
net-versus-continuous-assignment placement cases and **2** chapter-37 type
forms (features overlap). The envelope has no delayed-driver queue or
transition selector, so these delays are not replaced by immediate assignment.
See [the net-delay boundary](sv-net-delays.md) and
`extractors/sv/net_delay_reprice.py` for the reproducible scan.

## `trireg` charge-storage nets — 2026-10-22

`NetSymbol:TriReg` remains the capacitive-net boundary. The fresh **22,043**-
path census records it in **53** files: **17** are `TriReg`-only and **36**
co-occur with another wall. Repricing the sole files finds **21** concrete
declarations: **11** explicit charge-strength forms, **14** driver-release
forms, **9** retained-charge observations, **4** four-state `x` cases, **2**
undriven-startup cases, **2** capacitive-network declarations, **1**
charge-decay delay and **1** signed packed vector (features overlap). The
envelope has no charge state, driver-release transition or decay publication,
so `trireg` is not reduced to a wire or variable. See [the `trireg` boundary](sv-trireg.md)
and `extractors/sv/trireg_reprice.py` for the reproducible scan.

## `tri0` implicit pull nets — 2026-10-22

`NetSymbol:Tri0` remains the implicit-driver boundary. The fresh **22,043**-
path census records it in **22** files: **11** are `Tri0`-only and **11**
co-occur with another wall. Repricing the sole files finds **11** declarations:
all carry an implicit pull-0, **8** observe an undriven net, **3** have a
continuous driver, **1** uses explicit driver strength, **1** tests a strong
driver override and **1** tests an `x` driver (features overlap). The envelope
has no implicit pull driver or strength-resolved driver set, so `tri0` is not
reduced to a constant or ordinary wire. See [the `tri0` boundary](sv-tri0.md)
and `extractors/sv/net_pull_reprice.py` for the reproducible scan.

## `tri1` implicit pull nets — 2026-10-22

`NetSymbol:Tri1` remains the implicit-driver boundary. The fresh **22,043**-
path census records it in **20** files: **10** are `Tri1`-only and **10**
co-occur with another wall. Repricing the sole files finds **10** declarations:
all carry an implicit pull-1, **6** observe an undriven net, **4** have a
continuous driver, **3** test a strong-driver override, **1** tests a release
and **1** tests an `x` driver (features overlap). The envelope has no implicit
pull driver or strength-resolved driver set, so `tri1` is not reduced to a
constant or ordinary wire. See [the `tri1` boundary](sv-tri1.md) and
`extractors/sv/tri1_reprice.py` for the reproducible scan.

## `tri` resolved nets — 2026-10-22

`NetSymbol:Tri` remains the resolved-wire boundary. The fresh **22,043**-path
census records it in **66** files: **7** are `Tri`-only and **59** co-occur
with another wall. Repricing the sole files finds **7** declarations: **3**
continuous single-driver forms, **4** undriven observations, **2** wire/tri
equivalence comparisons, **2** invalid `tri reg` spellings and **1** floating
four-state observation (features overlap). The envelope has no general driver
set or strength-resolution state, so `tri` is not renamed to `wire` and no
invalid declaration is salvaged. See [the `tri` boundary](sv-tri.md) and
`extractors/sv/tri_reprice.py` for the reproducible scan.

## `interconnect` hierarchical nets — 2026-10-22

`NetSymbol:Interconnect` remains the hierarchical-connectivity boundary. The
fresh **22,043**-path census records it in **15** files: **8** are
Interconnect-only and **7** co-occur with another wall. Repricing the sole
files finds **10** declarations: **3** declaration initializers, **2** delay
specifications, **1** min:typ:max delay, **1** explicit data type, **1**
drive/charge strength, **2** packed dimensions, **2** unpacked dimensions and
**1** per-bit net-type resolution observation; **6** are compile-error
diagnostic shapes (features overlap). The envelope has no elaborated port
graph, bidirectional connection identity or per-bit net-type resolution, so
`interconnect` is not rewritten as a local wire and invalid declarations are
not salvaged. See [the `interconnect` boundary](sv-interconnect.md) and
`extractors/sv/interconnect_reprice.py` for the reproducible scan.

## Continuous-assignment delays — 2026-10-22

`ContinuousAssignSymbol:delay` remains the delayed continuous-driver boundary.
The fresh **22,043**-path census records it in **21** files: **13** are
continuous-assignment-delay-only and **8** co-occurring. Repricing the sole
files finds **13** spans: **6** rise/fall forms, **4** three-delay forms,
**4** vectors, **4** inertial cancellation/rescheduling cases, **2** four-state
`z` transitions, **3** initial-X settling cases, **1** strength-before-delay
case and **1** chapter-37 type form (features overlap). The envelope has no
delayed-driver queue or transition selector, so delayed continuous assignments
are not replaced by immediate assignments. See [the continuous-assignment
delay boundary](sv-continuous-assign-delays.md) and
`extractors/sv/continuous_assign_delay_reprice.py` for the reproducible scan.

## Dynamic delay expressions — 2026-10-22

`TimedStatement:DelayControl:expression` remains the runtime delay-expression
boundary. The fresh **22,043**-path census records it in **168** files:
**20** are delay-expression-only and **148** co-occurring. Repricing the sole
files finds **24** spans: **10** dynamic parameter/signal references, **10**
fixed-point forms, **9** unit-suffixed literals, **15** timeunit/timeprecision
or rounding contexts, **3** X/Z-to-zero cases, **4** delayed-assignment forms,
**3** arithmetic expressions and **4** time-query contexts (features overlap).
The envelope admits only fixed integral delays, so these expressions are not
folded to constants. See [the dynamic delay-expression boundary](sv-delay-expressions.md)
and `extractors/sv/delay_expression_reprice.py` for the reproducible scan.

## Event controls over expressions — 2026-10-22

`SignalEventControl:clock` remains the expression-sampling event boundary.
The fresh **22,035**-path census records it in **350** files: **20** are
event-expression-only and **330** co-occurring. Repricing the sole files
finds **20** spans: **4** multibit edge controls, **16** value-change controls,
**3** binary expressions, **1** concatenation, **1** conditional expression,
**3** reductions or unary expressions, **3** selected expressions, **4**
singular/aggregate cases, **11** result-change scenarios and **1**
scheduler-context row (features overlap). The envelope has no expression
sampler, dependency set or retained result, so no expression event is reduced
to one operand or a fixed bit. See [the event expression boundary](sv-event-expressions.md)
and `extractors/sv/event_expression_reprice.py` for the reproducible scan.

## Level-sensitive wait statements — 2026-10-22

`WaitStatement` remains the level-sensitive condition boundary. The fresh
**22,035**-path census records it in **65** files: **18** are wait-only and
**47** co-occurring. Repricing the sole files finds **18** spans: **6**
already-true/no-block cases, **3** negated conditions, **3** four-state
producer values, **2** trailing-delay releases, **1** conjunction, **1**
disjunction, **1** case equality, **1** same-time NBA condition and **1**
while-loop recheck (features overlap). The envelope has no level-wait sampler
or dependency registration, so no wait is reduced to an edge control or run
immediately. See [the wait-statement boundary](sv-wait-statements.md) and
`extractors/sv/wait_reprice.py` for the reproducible scan.

## Invalid statement markers — 2026-10-21

`InvalidStatement` is a frontend recovery marker, not a runtime statement
family. The fresh **22,043**-path census records it in **1,329** files:
**606** marker-only and **723** co-occurring. Repricing the sole files finds
**568** bad `begin`/block recovery spans, **31** VPI system-task tokens and
**7** empty frontend spans. These spans preserve bad-AST and diagnostic
boundaries; they cannot be admitted by dropping a wrapper or executing a
partial block. See [the boundary](sv-invalid-statements.md) and
`extractors/sv/invalid_stmt_reprice.py` for the reproducible scan.

## Configurations — 2026-10-21

`ConfigBlockSymbol` remains the elaboration-time design-selection boundary.
The fresh **22,043**-path census records it in **271** files: **148**
configuration-only and **123** co-occurring. Repricing the sole files finds
**166** configuration blocks across 148 files, with **17** files containing
more than one block. There are **159** design clauses naming **168** top cells,
**145** `default liblist` rules, **16** `cell liblist`, **7** `cell use`,
**23** `instance liblist`, **35** `instance use`, and **5** configuration
`localparam` declarations in four files. Clause rows overlap within a file.

The current envelope has no library namespace, configuration-rule precedence,
hierarchical binding or elaboration-time parameter environment. No config
shape is admitted by flattening it into a module; the complete boundary and
reproduction command are in [configurations](sv-configurations.md).

## Class declarations — 2026-10-21

`ClassType` remains the object-model boundary. The fresh **22,043**-path
census records it in **1,328** files: **109** class-only and **1,219**
co-occurring. Repricing the sole files finds **161** class spans: **95**
ordinary classes, **29** `extends` classes, **32** interface classes and **5**
virtual classes. Feature rows overlap: **100** spans contain methods, **44**
random fields, **29** constraints, **4** extern declarations and **3** typedef
members. The envelope has no object identity, allocation, inheritance,
method-frame, virtual-dispatch or constrained-random representation, so no
class shape is admitted by module rewriting. See [classes](sv-classes.md) for
the boundary and reproducible scan.

## Nested class declarations — 2026-10-21

`ClassType:ClassType` marks a class declaration nested in a module. The fresh
**22,043**-path census records it in **509** files: **49** class-use-only and
**460** co-occurring. Repricing the sole files finds **65** nested class
spans: **43** ordinary classes, **14** `extends` classes, **6** interface
classes and **2** virtual classes. Overlapping feature rows find **25**
method-bearing spans, **22** with constraints, **18** with random fields,
**16** with virtual/interface mentions, **17** with `extends` and **5** with
covergroups. These are source-span labels, not an admission claim; nested
classes still need the object model and are not flattened into their module.
See [classes](sv-classes.md) and
`extractors/sv/class_use_reprice.py` for the reproducible scan.

## Fork/join process control — 2026-10-21

The three `fork ... join*` markers remain a scheduler-owned process boundary.
The fresh **22,043**-path census records them in **571** files: **126**
fork/join-only and **445** co-occurring. Repricing the sole files finds **132**
join blocks: **90** `join`/JoinAll, **10** `join_any` and **32** `join_none`.
The existing envelope has no child-process identity, retained fork frame,
join barrier or detached-child lifetime, so no flavor is admitted by
serializing its body. See [fork/join](sv-fork-join.md) for the boundary and
reproducible scan.

The paired **22,035** paths gain **198 clean files**, no losses:
**4,098 → 4,296 clean**, **17,871 → 17,673 partial**, **66 include skips**,
zero extraction errors. All 4,098 previously clean extracted designs remain
identical. Of these gains, 193 follow instance lowering and five additionally
use bound hierarchical type queries. Extraction includes negative and compile-only
inputs and is not whole-corpus runtime conformance.

Of the 198 gains, 175 match complete independent transcripts under both
region oracles; nine match one tested legal order. Those nine contain
same-tick output ordering, early `$finish`, or an initial-write race; their
other traces are retained rather than counted as both-order matches. Eleven
retain runtime refusals: three continuous assignments, two procedural-edge
publication cases, two timed `$time` cases, two designs without procedural
processes, one zero-delay Inactive delivery and one run without `$finish`.
Two nested-module sources hit reference-compiler limitations, and one
multiple-top source has no usable single-top oracle. No successful reference
transcript falls outside both tested model traces. Eight authored/prior
fixtures match both orders; four explicit boundary fixtures remain refusals.
Final-source authentication covers 207 successful independent invocations
and two compiler refusals. Five kernel theorems certify the parsed
cross-instance storage and blocking/NBA statements.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 54 | 245 | 1 |
| 4 | 427 | 187 | 240 | 0 |
| 5 | 618 | 368 | 250 | 0 |
| 6 | 1185 | 425 | 760 | 0 |
| 7 | 796 | 106 | 690 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 111 | 478 | 0 |
| 10 | 657 | 248 | 409 | 0 |
| 11 | 1034 | 722 | 312 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 50 | 1493 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 214 | 611 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 385 | 159 | 28 |
| 23 | 851 | 170 | 681 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 165 | 400 | 0 |
| 27 | 354 | 176 | 178 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 123 | 104 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 136 | 281 | 0 |
| 38 | 340 | 211 | 129 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |


## Min typ max expressions — 2026-10-20

IEEE §11.11/§10.8 expressions select one complete bound arm globally at
elaboration, default typical, with an explicit recorded CLI choice. Only
that arm executes or enters admission analyses; widths, signs, conversions
and frontend validity are preserved. Existing evaluators/stores/timers apply.
Selected effects and unsupported types/calls/delays, nonconstant symbolic
forms and frontend-invalid contexts stay loud. Symbolic constant folding is
unchanged. See [the contract](sv-min-typ-max.md).

The paired **22,035** paths gain **15 clean files**, no losses:
**4,083 → 4,098 clean**, **17,886 → 17,871 partial**, **66 include skips**,
zero errors. **14 gains match complete independent transcripts under both
region oracles**; one retains the existing timed `$time` refusal. All 11
originally priced min/typ/max rows match. Of 4,083 previously clean designs,
one expands a folded constant into the selected tree; old and new executions
both match the same reference. Thirty authored mode/source pairs yield
20 complete both-oracle matches and 10 explicit refusals. Five kernel theorems
bind the actual selected RHS and blocking/NBA statements. These are extraction
and selected-execution counts, not whole-corpus runtime conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 46 | 253 | 1 |
| 4 | 427 | 186 | 241 | 0 |
| 5 | 618 | 362 | 256 | 0 |
| 6 | 1185 | 413 | 772 | 0 |
| 7 | 796 | 106 | 690 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 111 | 478 | 0 |
| 10 | 657 | 245 | 412 | 0 |
| 11 | 1034 | 721 | 313 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 48 | 1495 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 212 | 613 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 382 | 162 | 28 |
| 23 | 851 | 59 | 792 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 151 | 414 | 0 |
| 27 | 354 | 165 | 189 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 123 | 104 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 119 | 298 | 0 |
| 38 | 340 | 204 | 136 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Selected compound assignments — 2026-10-20

IEEE §10.4.1/§11.4.1 operator assignments now capture dynamic addresses once
and retain the complete bound RMW conversion tree over admitted variables,
packed selections/members and fixed unpacked cells. Array results are sampled
before copyback; bounded member vectors protect adjacent fields. Partial
packed ranges refuse explicitly after a measured simulator disagreement.
Effects and unsupported storage, symbolic and timing forms remain loud.
See [the contract](sv-compound-assignments.md).

The paired **22,035** paths gain **13 clean files** without losses:
**4,070 → 4,083 clean**, **17,899 → 17,886 partial**, **66 include skips**,
zero extraction errors. **All 13 gains match complete independent transcripts
under both region oracles**. All 4,070 previously clean extracted designs
remain identical. Seven authored complete transcripts match both oracles;
four further sources preserve refusals. Five source-bound kernel theorems
certify address capture, live RMW, blocking storage preserving NBA/output,
unknown no-store and partial-range refusal. Extraction counts include
negative and compile-only designs; they are not whole-corpus conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 46 | 253 | 1 |
| 4 | 427 | 186 | 241 | 0 |
| 5 | 618 | 362 | 256 | 0 |
| 6 | 1185 | 413 | 772 | 0 |
| 7 | 796 | 106 | 690 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 110 | 479 | 0 |
| 10 | 657 | 244 | 413 | 0 |
| 11 | 1034 | 708 | 326 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 48 | 1495 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 212 | 613 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 382 | 162 | 28 |
| 23 | 851 | 59 | 792 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 151 | 414 | 0 |
| 27 | 354 | 165 | 189 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 123 | 104 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 119 | 298 | 0 |
| 38 | 340 | 204 | 136 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Runtime integral `$clog2` — 2026-10-20

IEEE §20.8.1 calls now evaluate pure live integral operands at their own
width, interpreted as unsigned, through the existing ceiling-log2 helper.
The result is signed 32-bit; later assignment conversion is unchanged. Correct
constant literals and symbolic extraction remain. Runtime unknowns, effects,
unsupported types and invalid source stay loud; folds and elaboration cannot
replace unresolved calls with approximate frontend constants.
See [the contract](sv-runtime-clog2.md).

The paired **22,035** paths gain **13 clean files** without losses:
**4,057 → 4,070 clean**, **17,912 → 17,899 partial**, **66 include skips**,
zero extraction errors. **All 13 gains match complete independent transcripts
under both region oracles**. All 4,057 previously clean extracted designs
remain identical. Four authored complete transcripts match both oracles;
four further sources preserve refusals. Five source-bound kernel proofs
establish live reads, blocking storage, NBA capture, post-change visibility
and refusal before inventing unknown numeric results.

The table measures extraction, including negative and compile-only files,
rather than whole-corpus execution conformance.



## Integral replication — 2026-10-20

IEEE §11.4.12.1 pure integral replication now lowers self-determined groups
to existing concatenations. Nested groups, X/Z, string bytes, unsigned results,
later assignment resizing and legal zero members retain their source meaning.
Effects, unsupported operands/types, invalid compilation and expansion bounds
stay loud. The comparison also corrected §5.7.1 unsized based X/Z widening;
affected frontend elaboration constants refuse explicitly.
See [the contract](sv-replication.md).

The paired **22,035** paths gain **20 clean files** without losses:
**4,037 → 4,057 clean**, **17,932 → 17,912 partial**, **66 include skips**,
zero extraction errors. **All 20 gains match complete independent transcripts
under both region oracles**, including the initially divergent wide X/Z row.
All 4,037 previously clean extracted designs remain identical. Seven authored
complete transcripts match both oracles; three further sources preserve
refusals. Five source-bound kernel proofs establish live reads, blocking
stores, NBA capture, post-change commit visibility and zero-member identity.

These counts measure extraction, including negative and compile-only files.

## Integral assignment patterns — 2026-10-20

IEEE §10.9 positional, keyed/member/type/default and constant-replicated
patterns now lower into existing integral concatenation and storage rules.
Bound correspondence preserves widths, signedness and X/Z. Live reads, nested
structs, typed conditional operands, two-state conversion, whole-packed
self-swaps and NBA capture use the existing evaluator and scheduler. Keyed
numeric-index inventories map to declared order, including existing unpacked
cell paths. Effects, invalid source, unsupported storage/types, split-cell
self-aliases and expansion limits stay loud. Symbolic packed-pattern admission
is unchanged. See [the contract](sv-assignment-patterns.md).

The paired **22,035** paths gain **26 clean files** without losses:
**4,011 → 4,037 clean**, **17,958 → 17,932 partial**, **66 include skips**,
zero extraction errors. **Twenty-four gains match complete independent
transcripts under both region oracles**; two retain continuous-assignment
runtime refusals. All 26 independent runs succeed. There are no other
transcript differences, oracle failures or multi-top absences. A paired design
comparison finds no changes in the 69 previously clean pattern-bearing sources.

Five authored complete transcripts match both oracles; three more preserve
effect, storage and self-alias boundaries. Four source-bound kernel proofs
establish current reads, blocking stores, NBA capture and post-change commit
visibility.

## Elaborated generate scopes and integral parameters — 2026-10-20

IEEE clauses 6, 23 and 27 now lower live unconditional/if/case generate scopes
and elaborated loop entries into the existing module store and process runner.
Inactive branches and zero-count loops contribute no runtime work. Original
binding identity keeps sibling/nested variables, fixed arrays, procedural locals
and delayed captures distinct. Integral module/local/genvar parameters become
exact typed literals; bound hierarchical reads/stores reuse the original slots.
Symbolic extraction is unchanged. No scheduler changed. Active unsupported
members, instance storage, dependent static initialization, invalid source and
expansion limits stay loud. See [the contract](sv-elaborated-generate.md).

The paired **22,035** paths gain **345 clean files** without losses:
**3,666 → 4,011 clean**, **18,303 → 17,958 partial**, **66 include skips**,
zero extraction errors. Chapter 27 rises from 3 to 165 clean files; the other
gains include parameter-only sources.

Of the gains, **187 match complete independent transcripts under both region
oracles**. Three have legal time-zero races: one oracle matches the reference,
while reversing process order changes the output. Another 146 retain runtime
refusals (112 continuous assignments, 33 procedural edge-publication cases and
one time-zero-only clock); four have multiple top modules and remain loader
refusals. The reference compiler rejects five more sources: four constant
system-function contexts and one reset-protection pragma. None of those
refusals is counted as execution agreement. There are no other transcript
differences from both oracle traces.

Seven authored runnable sources match complete independent transcripts under
both region oracles; three more preserve active-member, instance-storage and
initialization-order boundaries. Three source-bound kernel proofs establish
current reads, distinct-scope storage and the selected blocking assignment.
The following table measures extraction, including negative and compile-only
paths; it is not whole-corpus execution conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 43 | 256 | 1 |
| 4 | 427 | 186 | 241 | 0 |
| 5 | 618 | 354 | 264 | 0 |
| 6 | 1185 | 412 | 773 | 0 |
| 7 | 796 | 106 | 690 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 110 | 479 | 0 |
| 10 | 657 | 226 | 431 | 0 |
| 11 | 1034 | 685 | 349 | 0 |
| 12 | 627 | 290 | 337 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 48 | 1495 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 196 | 629 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 382 | 162 | 28 |
| 23 | 851 | 59 | 792 | 0 |
| 24 | 355 | 12 | 343 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 151 | 414 | 0 |
| 27 | 354 | 165 | 189 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 120 | 107 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 119 | 298 | 0 |
| 38 | 340 | 204 | 136 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 40 | 47 | 0 |

## Package integral singleton storage — 2026-10-20

IEEE clause 26 source-defined packages now lower scalar/packed integral
variables into one shared vector store before module initialization. Qualified,
imported and reexported references bind the original declaration. Defaults,
closed pure initialization, integral parameters/enums and existing aliases use
the ordinary value rules. Unsupported members, dependent/effectful initializers,
unpacked/nonintegral storage, external packages and multiple-module storage
remain loud. Invalid import conflicts and unexported relay bindings have
explicit admission barriers. No scheduler changed. See [the contract](sv-package-storage.md).

The paired **22,035** paths gain **165 clean files** without losses:
**3,501 → 3,666 clean**, **18,468 → 18,303 partial**, **66 include skips**,
zero extraction errors. **All 165 gains match complete independent transcripts
under both region oracles.** Sixteen additional initially admitted sources
were independently rejected by the compiler; generic import-conflict/export
checks now retain all sixteen as partial. They are not counted as matches.

Four authored runnable sources match complete transcripts under both oracles;
three further sources preserve dependent-initialization, unpacked-storage and
subroutine boundaries. Four source-bound kernel proofs establish shared
reads, immediate blocking stores, NBA capture and visibility after commit.
The current chapter census is extraction coverage, including negative and
compile-only paths; it is not whole-corpus execution conformance.

| Chapter | Total | Clean | Partial | Include skips |
|---|---:|---:|---:|---:|
| 3 | 300 | 34 | 265 | 1 |
| 4 | 427 | 186 | 241 | 0 |
| 5 | 618 | 348 | 270 | 0 |
| 6 | 1185 | 389 | 796 | 0 |
| 7 | 796 | 105 | 691 | 0 |
| 8 | 843 | 0 | 842 | 1 |
| 9 | 589 | 107 | 482 | 0 |
| 10 | 657 | 225 | 432 | 0 |
| 11 | 1034 | 679 | 355 | 0 |
| 12 | 627 | 287 | 340 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1543 | 48 | 1495 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 171 | 654 | 0 |
| 21 | 900 | 84 | 816 | 0 |
| 22 | 572 | 379 | 165 | 28 |
| 23 | 851 | 34 | 817 | 0 |
| 24 | 355 | 10 | 345 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 140 | 425 | 0 |
| 27 | 354 | 3 | 351 | 0 |
| 28 | 737 | 3 | 734 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 103 | 124 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 111 | 306 | 0 |
| 38 | 340 | 194 | 146 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 10 | 77 | 0 |

## Simple immediate assertion actions — 2026-10-20

IEEE §16.3 simple immediate assert/assume/cover now retain source-kind
provenance while using the existing conditional executor. Conditions evaluate
once, and selected action continuations survive waits. Missing assert/assume
failure actions retain a loud implicit-diagnostic branch. Deferred/concurrent
checks, assertion controls, unsupported conditions/actions, symbolic mode,
invalid source and unvalidated null failure actions remain loud. No scheduler
changed. See [the contract](sv-immediate-assertions.md).

The paired **22,035**-path census gains **40 clean files** without losses:
**3,461 → 3,501 clean**, **18,508 → 18,468 partial**, **66 include skips**,
zero extraction errors. Thirty-five gains match complete configured independent
transcripts under both region oracles. Four gains retain runtime refusals:
procedural edge publication, time-zero-only clocks, scope-aware `%m` rendering
and `always_comb`. One runs the assertion actions but differs in the independent
`$finish(0)` source-location footer; it is not counted as agreement.

Four authored runnable sources match complete transcripts, including every
two-bit four-state condition, wide truthiness, nested/empty actions, successful
implicit checks and retained delayed selections. Three preserve the implicit
diagnostic, deferred-region and null-failure refusals. Independent action
checks explicitly enable all cover successes and disable extra assertion-engine
status messages; no additional transcript filtering is applied. Four kernel
theorems bind to actual compiled source subtrees.

## Implicit immediate-assertion diagnostics — 2026-10-22

`ImmediateAssertion:implicit-error` remains the omitted-failure-action
boundary. The fresh **22,043**-path census records it in **25** files: **22**
are implicit-error-only and **3** co-occur. Repricing the sole files finds
**24** branches: **17** `assert`, **7** `assume`, **12** omitted success
actions, **12** explicit success actions, **5** named assertions, **13** true
conditions, **1** false condition, **2** `always` contexts and **1**
`always_comb` context (features overlap). The branch remains an explicit
unsupported else node because the envelope has no portable diagnostic
text/status or coverage-observation contract. See the [immediate assertion
contract](sv-immediate-assertions.md) and
`extractors/sv/immediate_assert_error_reprice.py` for the reproducible scan.

## Deferred immediate assertions — 2026-10-22

`ImmediateAssertion:deferred` remains the scheduler-region assertion boundary.
The fresh **22,043**-path census records it in **52** files: **19** are
deferred-only and **33** co-occur. Repricing the sole files finds **27**
branches: **17** `assert`, **5** `assume`, **5** `cover`, **16** `#0`
Observed-region forms, **11** `final` Postponed-region forms, **15** single
system-call actions, **12** null actions, **1** block-action diagnostic, **4**
`always` contexts, **1** `always_comb` context and **1** protected-region form
(features overlap). The envelope has no deferred sampling/re-evaluation,
pending-report, action restriction or end-of-simulation ordering state, so no
branch is rewritten as an immediate conditional. See [the immediate assertion
contract](sv-immediate-assertions.md) and
`extractors/sv/immediate_assert_deferred_reprice.py` for the reproducible scan.

## Plain always source repetition — 2026-10-20

IEEE §9.2.2.1 plain `always` now retains its complete source body and compiles
to one ready process using the existing true-condition loop. Delays and
bare/negative-edge waits retain the unfinished body tail before the loop
boundary. Canonical positive-edge encoding is unchanged. The initial-only
runner still refuses `Always`; repeated scalar lifetimes, invalid source,
implicit/compound sensitivities, `iff`, level waits and symbolic-mode
repetition remain loud. No scheduler changed. See [the contract](sv-always.md).

The paired **22,035**-path census gains **90 clean files** without losses:
**3,371 → 3,461 clean**, **18,598 → 18,508 partial**, **66 include skips**,
zero extraction errors. Six gains match complete independent transcripts under
both region oracles. One more is race-sensitive: its observation and counter
update share time five; the independent simulator and reverse oracle print
`PASS`, while the source oracle prints `FAIL: fast_count=5 slow_count=2`.
The remaining 83 gains refuse at runtime: 75 require procedural edge
publication, six retain time-zero-only clock lowering, and two contain
continuous assignments. Two of those 75 are negative compilation fixtures
also rejected by the independent implementation; they are not runtime matches.

Four authored runnable sources match complete independent transcripts under
both oracles, including time-zero prefixes, retained tails, automatic array
reinitialization and an always-only design. A fifth source preserves the
internal edge-publication refusal. Four fixture-bound kernel theorems prove
the single-process compilation, delayed/event tails and event rearming.

## Case-inside membership selection — 2026-10-20

IEEE §12.5.4 unqualified integral `case … inside` now uses the existing
membership predicates and first-match case chain. Scalar labels use asymmetric
wildcard equality; colon ranges use inclusive signed/unsigned comparisons.
Only definite one selects an arm. Common-width fixed arrays/slices retain
source-order elements, and delayed selected arms retain their own continuation.
No evaluator, storage or scheduler changed. Effects, qualifiers, tolerance
syntax, unsupported types/storage, dollar case endpoints and array-element
widening remain loud. The symbolic structural case path is unchanged.
See [the contract](sv-case-inside.md).

The paired **22,035**-path census gains **21 clean files** without losses:
**3,350 → 3,371 clean**, **18,619 → 18,598 partial**, **66 include skips**,
zero extraction errors. All twenty-one gains match complete independent
transcripts under both source and reverse schedule oracles. Three authored
sources also match complete transcripts, including all 256 pairs of two-bit
four-state operands, type/range/array contexts and delayed live-value changes.
A fourth source explicitly preserves the case-array widening discrepancy as
a refusal; it is not a runtime match. Three fixture-bound kernel theorems prove
the scalar equality bridge, ambiguous-item skip with retained selected body,
and inclusive signed interval guard.

## Forever loops — 2026-10-20

IEEE §12.7.6 `forever` retains its body and compiles to the existing loop
control with a true one-bit condition and empty initializer/step lists.
Normal completion and `continue` start the next iteration; `break` exits
only the nearest loop. Delay/event waits retain the current body tail and
loop boundary. No evaluator or scheduler changed. See [the loop contract](sv-loops.md).
Unmodelled body lifetimes, named-block `disable`, procedural edge publication,
timed clocks, zero-delay Inactive delivery and symbolic-mode loops remain loud.

The paired **22,035**-path census gains **21 clean files** without losses:
**3,329 → 3,350 clean**, **18,640 → 18,619 partial**, **66 include skips**,
zero extraction errors. Ten gains match complete independent transcripts
under both source and reverse schedule oracles. Eleven gains remain runtime
refusals: seven require procedural edge publication and four retain the timed
`$time` boundary. Two additional candidates stay partial because their newly
visible bodies contain `disable`. Extraction gains are separate from runtime
agreement.

All three authored sources match complete independent transcripts, covering
nearest-loop transfers, nesting, automatic array reinitialization, termination,
live four-state values across delays and a permanently waiting event body.
Four fixture-bound kernel theorems establish event/delay retention, resumed
break and event rearming after body completion. Fuel exhaustion remains timeout.

## Symmetric wildcard case statements — 2026-10-20

IEEE §12.5.1 unqualified integral `casez` and `casex` now use the existing
first-match case control chain with a shared pure symmetric match predicate.
Z is ignored in either operand; `casex` additionally ignores X. Dynamic items
and masks retain their live values, whole-case width/sign conversions precede
matching, and selected bodies retain their continuation across waits. No
scheduler changed. Effects, qualifiers, unsupported types/storage and
symbolic-mode wildcard statements remain loud. See [the contract](sv-wildcard-cases.md).

The paired **22,035**-path census gains **30 clean files** without losses:
**3,299 → 3,329 clean**, **18,670 → 18,640 partial**, **66 include skips**,
zero extraction errors. Twenty-eight gains match complete independent
transcripts under both source and reverse schedule oracles. Two delayed
corpus files retain the timed `$time` boundary and are extraction gains only.
All three authored sources match complete transcripts, covering all 256
pairs of two-bit four-state values, signed/mixed/wide contexts, dynamic masks,
first/default/no-match, nesting and retained selected arms across delays.
Three fixture-bound kernel theorems prove the evaluator bridge, symmetric
matching and selected-arm continuation.

## Blocking intra-assignment timing — 2026-10-20

IEEE §10.4.1/§9.4.5 blocking controls now compile to capture, wait and
copyback using existing statements. RHS evaluation happens once at encounter;
destination selection happens after resumption. Packed concatenations,
state-kind conversion and repeated capture use existing assignment/storage
rules. Repeated events sample their count once through the existing loop
rule. No evaluator or scheduler changed. See [the contract](sv-intra-assignment.md).

The paired **22,035**-path census gains **15 clean files** without losses:
**3,284 → 3,299 clean**, **18,685 → 18,670 partial**, **66 include skips**,
zero extraction errors. Ten gains match complete independent transcripts
under both source and reverse schedule oracles. Two gains remain loud at
zero-delay Inactive delivery, and three retain the timed `$time` boundary.
Four dynamic unpacked destinations remain partial. Extraction gains are
separate from execution agreement.

Three authored acceptance sources match complete independent transcripts,
including resumed selection, X/Z neighbors, two-state concatenated copyback,
prior NBA work, repeated capture and retained event counts. Two additional
sources retain explicit zero-delay and procedural edge-publication refusals.
Three fixture-bound kernel theorems prove capture before wait, resumed-index
copyback and retained repeat control. Nonblocking controls, unsupported
effects/storage/delays and symbolic-mode controls remain loud.

## Nonblocking intra-assignment publication — 2026-10-21

`IntraAssignment:publication-or-context` remains the future-NBA boundary. The
fresh **22,043**-path census records it as the sole wall in **55** files and
the repricer finds **75** markers: **63** delayed controls, **2** event
controls, **1** explicit `#0`, and **9** repeat/context forms. The current
retained blocking path cannot represent a separate future publication queue
or same-time ordering, so no nonblocking shape is admitted. See
[intra-assignment publication](sv-intra-assignment.md) for the boundary and
reproduction command.

## Random sequence productions — 2026-10-21

`RandSequenceStatement` remains the constrained-random production boundary.
The fresh **22,043**-path census records it in **72** files: **53**
randsequence-only and **19** co-occurring. Repricing the sole files finds
**54** production blocks with overlapping features: **18** alternatives,
**15** conditional/case forms, **10** repeats, **10** weighted choices and
**54** action blocks. The current envelope has no production graph, random
state or generated action scope, so no feature is admitted by choosing a fixed
branch. See [randsequence](sv-randsequence.md) for the boundary and scan.

## Explicit command-line plusargs — 2026-10-20

The §21.6 family admits literal prefix queries and integral value queries
with an explicit ordered input environment. Immutable input specialization
compiles queries to existing expressions and packed copyback statements;
short-circuit lowering retains ordered dependent reads and skipped calls.
Ordinary loading refuses unspecified inputs. Existing retained continuations
handle selected writes across delays. See [the input contract](sv-plusargs.md).

The paired **22,035**-path census gains **31 clean files** without losses:
**3,253 → 3,284 clean**, **18,716 → 18,685 partial**, **66 include skips**,
zero extraction errors. Twenty-nine gains match complete independent
transcripts using each file's actual invocation metadata. One malformed
numeric input produces independent diagnostics and remains loud; one timed
file retains the existing `$time` boundary. They are extraction gains only.
Three authored sources separately match numeric, expression-order and timed
copyback observations; a fourth source records a diagnostic refusal.
Three kernel theorems bind first-match and copyback properties to the fixture.

## Fixed-dimension foreach — 2026-10-20

IEEE §12.7.3 fixed foreach loops compile to one ordinal `For` over the
existing bounded cell/vector storage. Declared bounds, rightmost-first index
variation, omitted dimensions, automatic signed-int iterator scope, live
reads, whole-loop break and tuple-advancing continue are preserved. Ordinary
timer continuation uses the existing retained body boundary. Pure signed-int
indices also gain widened noncanonical packed-read normalization. Other
runtime index types, unsupported aggregate storage, unresolved lifetimes,
dynamic collections and symbolic-mode loops remain loud. See
[the loop contract](sv-loops.md).

The paired **22,035**-path census gains **21 clean files** without losses:
**3,232 → 3,253 clean**, **18,737 → 18,716 partial**, **66 include skips**,
zero extraction errors. Nineteen gains match complete time-zero transcripts;
one more matches through the timed loader under both source and reverse
oracles. The remaining timed fixture is refused because its `$time` queries
carry time-zero-only provenance. A named-loop file remains partial because
lowering its foreach exposes the unsupported `disable` statement.

Three authored acceptance sources match complete independent transcripts,
including live four-state packed reads across delays under both oracles.
Fixture-bound kernel theorems establish ordinal offset evaluation, tuple
coordinate reconstruction and break without a cursor step. A fourth source
keeps wide unsigned negative-bound indexing loud: its observed behavior
disagrees with widened mathematical offsets, so no simulator agreement or
generic unsigned-index admission is claimed.

## Pre- and post-test procedural loops — 2026-10-20

Pure integral `while` and `do…while` now use the existing loop control,
with a body-first entry for `do…while`. Break, continue, nesting and retained
delay/event continuations preserve their proper test boundary. The general
completed-step correspondence includes the new entry. Effects, unsupported
conditions/storage, unresolved lifetimes and symbolic-mode loops remain loud.
No scheduler or queue changed.

The paired **22,035**-path census gains **46 clean files** without losses:
**3,186 → 3,232 clean**, **18,783 → 18,737 partial**, **66 include skips**,
zero extraction errors. Thirty-six gains match complete time-zero transcripts;
seven more match in the timed loader under source and reverse schedule
oracles. Two remain runtime refusals due to time-zero-only `$time` lowering.
One quiescent fixture differs only by an independent simulator warning;
the same warning appears in a no-loop control. The raw diagnostic difference
is retained and is not counted as a match.

The authored values and timer fixtures match complete independent output.
Four fixture-bound kernel proofs cover entry, assignment, break and first-wait
retention. A third fixture exposes missing procedural edge publication in the
kernel: its producer writes an internally watched signal. The timed loader
now refuses such designs, preserving the counterexample without silently
losing the waiter. External-stimulus edges retain their existing interface.

## Numeric enumeration methods — 2026-10-20

Pure integral `first`, `last`, `num`, `next` and `prev` calls now lower
through the bound declaration-order member table. Traversal uses exact case
equality, so named x/z members remain distinct. Unsigned two-state 32-bit
step conversion precedes modular wrapping; a nonmember returns the enum base
default even at step zero. Width, signedness and receiver storage reuse the
existing rules. Effects, string-valued `name()`, unsupported storage, invalid
frontend compilations and symbolic-mode methods remain loud. No evaluator or
scheduler changed.

The paired **22,035**-path census gains **24 clean files** without losses:
**3,162 → 3,186 clean**, **18,807 → 18,783 partial**, **66 include skips**,
zero extraction errors. Twenty-two gains match complete independent
transcripts. Two delay-bearing files remain runtime refusals, including in
the timed loader because their `$time` expressions use the time-zero-only
lowering. They are counted as extraction gains only. The authored fixture
also matches its complete independent transcript, and kernel proofs bound to
its extracted assignment establish nonmember defaults and declaration-order
succession.

## Integral formatted input — 2026-10-20

The legacy/self-check tier now admits direct blocking assignments of
`$sscanf` over pure packed input, literal formats and integral packed
outputs. The shared pure scanner supports `%b/%o/%h/%x/%d/%c/%s/%v`,
suppression, positive widths, whitespace, literals and `%%`. Input is
sampled once; successful outputs copy back left to right, later selectors
see earlier writes, unmatched destinations stay unchanged, and the return
count is assigned last. Existing packed-target rules retain neighboring
bits and two-state conversion. The timed stepper delegates the new leaf to
the same interpreter; no scheduler changes. General strings, real outputs,
other contexts/formats, excess arguments, effects and symbolic scanning
remain loud. Unknown packed input and diagnostic-bearing failures are
explicit runtime boundaries. Details: [formatted input](sv-formatted-input.md).

The paired **22,035**-path census gains **34 clean files** without losses:
**3,128 → 3,162 clean**, **18,841 → 18,807 partial**, **66 include skips**,
zero extraction errors. Thirty newly clean files execute and match complete
independent transcripts. Four remain runtime refusals: two unknown-input
diagnostics, one reduction over a selected slice, and one delay-bearing
copyback fixture. These four are extraction gains only. The authored
fixtures separately check ordered/partial copyback and integral conversion
edges, including sign/underscore field-width consumption and strength input.

## Pure logical implication — 2026-10-20

Pure integral `->` lowers to `!left || right`, preserving each operand's
self-determined width, four-state truth, one-bit unsigned results and the
frontend's associativity. Both symbolic compilers reuse the existing logical
operations. M0's logical conjunction/disjunction compilation now keeps
self-determined operands, matching the second compiler. Effects, unsupported
types, frontend errors and `<->` equivalence remain loud, including constant
contexts. No evaluator or scheduler changed.

The paired **22,035**-path census moves **3,121 → 3,128 clean** and
**18,848 → 18,841 partial**, with **66 include skips**, zero extraction errors,
7 gains and no losses. Six gains execute and match complete independent
transcripts. The seventh combines continuous assignment and delay, so the
existing runners refuse it; it is counted only as an extraction gain.
Fixture-bound symbolic proofs establish dominance rules for arbitrary source
widths. Both compiler paths match the observed 16-pair truth table at widths
1, 4 and 65; the values fixture also checks vector truth, result/arithmetic
context and associativity.

## Pure integral membership — 2026-10-20

Pure integral `inside` expressions lower to wildcard equality for scalar
items, inclusive comparisons for colon ranges, and three-valued logical
disjunction across the set. Common operand width/signedness precedes the
unsigned one-bit result. Single dollar endpoints use representation limits;
fixed one-dimensional arrays and constant slices reuse flattened cells.
Effects, tolerance syntax, nonintegral/unsupported storage, frontend errors
and symbolic-mode membership remain loud. No evaluator or scheduler changed.

The paired **22,035**-path census moves **3,083 → 3,121 clean** and
**18,886 → 18,848 partial**, with **66 include skips**, zero extraction errors,
38 gains and no losses. Every newly clean file executes and matches its
complete independent simulator transcript. Files whose names mention
tolerance ranges actually contain scalar wildcard comparisons; actual
tolerance syntax remains refused. The authored `inside` fixture covers
signed/mixed sizing, wildcard uncertainty, dollar/enum limits, reversed and
unknown ranges, arrays and nesting. Its symbolic kernel proofs check
definite-match dominance and arbitrary same-width all-wildcard membership.

## Local fixed-unpacked array declarations — 2026-10-20

One-dimensional fixed-unpacked arrays whose elements are integral scalars or
packed vectors now lower to independent vector cells. Static block-local cells
are hoisted into declaration state and keep their value across repeated block
entries; automatic cells remain local declarations and are initialized on each
entry. Declaration-specific storage names preserve distinct scopes. Pure closed
static initializers, positional/keyed/default patterns already admitted by the
cell lowering, copies, constant slices, streaming cells, and two-state
conversion reuse the existing vector operations. Effectful static initializers,
multidimensional or aggregate arrays, dynamic storage and unresolved lifetimes
remain loud.

The paired **22,035**-path census moves **3,054 → 3,083 clean** and
**18,915 → 18,886 partial**, with **66 include skips**, zero extraction errors,
29 gains and no losses. `VariableDeclStatement:2state` falls from 2,453 to
2,376. All 29 newly clean files execute through the self-check runner and
match complete independent simulator transcripts. The authored `local_arrays`
fixture exercises static persistence (`4, 5, 6`) beside automatic
reinitialization (`4, 4, 4`); its kernel proof checks both cell-level rules.
Array equality and inequality combine per-cell results with the corresponding
logical conjunction or disjunction, preserving the scalar four-state rules.

## Turn 1 inventory — 2026-10-19

A fresh extractor census over the chapter-scoped `sv-tests-2` corpus used
pyslang 11 on Linux with Python 3.9. It found **22,033** source paths:
**2,628 clean**, **19,339 partial**, **66 include skips**, and **0 extraction
errors**. The include-skipped paths are multi-file tests; no extractor crash
was observed. The adapter pass marked **4** paths unlockable (two simulation
rows). This is extractor coverage only: Lean ingestion and execution remain
separate gates.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 121 | 306 | 0 |
| 5 | 618 | 325 | 293 | 0 |
| 6 | 1,185 | 305 | 880 | 0 |
| 7 | 796 | 14 | 782 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 657 | 156 | 501 | 0 |
| 11 | 1,034 | 538 | 496 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 122 | 703 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 371 | 173 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 79 | 338 | 0 |
| 38 | 340 | 170 | 170 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,033** | **2,628** | **19,339** | **66** |

The leading extractor refusal classes are `AssignmentExpression:target`
(4,473 files), `CallExpression` (4,225), `InstanceSymbol:Instance` (3,838),
`ExpressionStatement:CallExpression` (3,717), `VariableSymbol:2state`
(3,716), `TimedStatement:DelayControl` (2,675),
`VariableDeclStatement:2state` (2,469), `SubroutineSymbol:Subroutine` (1,640),
`NamedValueExpression:2state` (1,504), `ClassType` (1,326),
`ProceduralBlockSymbol:NoEventControl` (1,307), and `InvalidStatement` (1,302).

## Fresh paired census — 2026-10-14

The October 14 summary in `docs/sv-construct-census.json` measured
**22,008** chapter-scoped paths with pyslang 11 on Linux. The older July
measurements retained after this section are historical. The current snapshot
is the October 19 comparison below.
Both sides of the integral-variable-port comparison use the same paths:
**2,572 → 2,573 clean**, **19,370 → 19,369 partial**, **66 includes skipped**,
**0 extraction errors**, **2 gains**, **1 loss**. Four paths change their
refusal sets. Both gains are chapter-23 predefined integer port declarations.
The loss is a negative fixture with a forbidden output-net port initializer
that the old extractor silently dropped. An extractor-clean classification
is not Lean admission or live execution.

The follow-up constant-`$clog2` admission uses the same paths and changes the
current snapshot to **2,580 clean** and **19,362 partial**: seven chapter-5/20
gains, no losses, and `CallExpression` falls from 4,351 to 4,328 files.

The fixed-dimension query follow-up changes the same snapshot to **2,588
clean** and **19,354 partial**: eight total chapter-20 gains from the
`$size`/`$high`/`$left`/`$right`/`$low`/`$increment` family and no losses;
`CallExpression` falls again to 4,233 files.

The scalar dimension-count follow-up adds `$dimensions` and
`$unpacked_dimensions` for the same fixed integral declarations. The fresh
census changes the snapshot to **2,596 clean** and **19,346 partial**: eight
additional gains (one in chapter 7 and seven in chapter 20), no losses, and
`CallExpression` falls to **4,207** files.

## Fixed array dimension selection — 2026-10-19

The corpus now contains **22,030** chapter-scoped paths. Both sides of a
fresh paired run use those same paths and pyslang 11 on Python 3.9. Fixed
packed/unpacked range metadata and optional static dimension operands remove
the dimension-arity refusal from **33** files; **67** files lose every
dimension-query refusal. Metadata-only type aliases also become admissible,
without admitting runtime array/aggregate storage, while erased aliases in
rejected compilations retain a diagnostic refusal. The resulting snapshot is
**2,596 clean → 2,599 clean**, **19,368 partial → 19,365 partial**,
**66 includes skipped**, **0 extraction errors**, three gains and no losses.
Two gains are chapter-20 type-operand queries; one is a chapter-6 fixture
whose unused packed-structure alias has no runtime effect. All three new
clean fixtures execute through Lean's self-check runner and agree with
independent source observations. The **22** extra paths
relative to October 14 are all partial on both sides, not regressions.

The same family corrects `$dimensions` of a plain scalar to zero while
preserving an implicit packed dimension for predefined integers, enums and
untagged packed aggregates. Dynamic storage, tagged unions, runtime dimension
selection and effects remain loud. Metadata admission is not simulator
agreement or live execution.

## Integral wildcard equality — 2026-10-19

A fresh paired run over the same **22,030** paths, with pyslang 11 on
Python 3.12, changes **2,599 → 2,628 clean** and **19,365 → 19,336 partial**,
with **66 include skips**, **zero errors**, **29 gains** and **no losses**.
All gains are in chapter 11. Thirty files lose their wildcard comparison
refusals; one remains partial because it also uses `$time`. Two gains
require both equality and inequality, beyond the 27 files with only one
of those refusal kinds. All 29 newly clean fixtures execute through Lean;
their complete outputs are checked against independent source runs.

`==?` and `!=?` share the four-state value rule documented in
[the operator contract](sv-wildcard-equality.md), including cared-left
unknowns, signed/mixed-width operands and one-bit result sizing. The
following chapter table is the current snapshot; earlier comparisons
remain historical. An extractor-clean result alone does not establish
execution or simulator agreement.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 121 | 306 | 0 |
| 5 | 618 | 325 | 293 | 0 |
| 6 | 1,185 | 305 | 880 | 0 |
| 7 | 796 | 14 | 782 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 656 | 156 | 500 | 0 |
| 11 | 1,034 | 538 | 496 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 122 | 703 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 371 | 173 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 478 | 8 | 470 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 79 | 338 | 0 |
| 38 | 340 | 170 | 170 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,030** | **2,628** | **19,336** | **66** |

The turn-one refusal sets counted assignment targets in 4,473 files,
expression calls in 4,225, instance hierarchy in 3,838, and two-state
declaration shapes in 3,716. The current 2026-10-19 snapshot is recorded
below; counts overlap because a file may have several walls.

## Unary arithmetic correction — 2026-10-19

A fresh 22,030-path census after retaining unary `+` as an arithmetic node
had **2,599 clean**, **19,365 partial**,
**66 include skips**, and **zero extraction errors**. This is a correction to
execution of admitted expressions: partially unknown operands now produce
all x under §11.4.3. The new source fixture covers scalar, signed, widened,
65-bit and nested arithmetic uses; extraction cleanliness alone does not
establish those runtime results. See [the operator contract](sv-unary-arithmetic.md).

## Constant fixed-unpacked element cells — 2026-10-19

The self-check extractor now lowers one-dimensional fixed-unpacked integral
array elements at constant in-range indices to independent vector cells. A
fresh chapter-scoped run over the same **22,033** paths reports **2,691 clean**
and **19,276 partial**, with **66 include skips** and **0 extraction errors**:
63 clean gains and no losses relative to the turn-one snapshot. The leading
`AssignmentExpression:target` refusal falls from **4,473 to 4,314 files**.
The remaining target class is heterogeneous; dynamic/out-of-range indices,
multidimensional and aggregate arrays, hierarchy, classes, strings and
floating values remain separate loud boundaries. The real fixture and Lean
proof are in `Examples/system-verilog/unpacked_cells`; this is an extractor
and self-check result, not a whole-corpus simulator-agreement claim.

| Chapter | Total | Clean | Partial | Include skip |
|---|---:|---:|---:|---:|
| 3 | 300 | 24 | 275 | 1 |
| 4 | 427 | 122 | 305 | 0 |
| 5 | 618 | 326 | 292 | 0 |
| 6 | 1,185 | 307 | 878 | 0 |
| 7 | 796 | 28 | 768 | 0 |
| 8 | 842 | 0 | 841 | 1 |
| 9 | 589 | 60 | 529 | 0 |
| 10 | 657 | 160 | 497 | 0 |
| 11 | 1,034 | 541 | 493 | 0 |
| 12 | 627 | 167 | 460 | 0 |
| 13 | 598 | 1 | 597 | 0 |
| 14 | 473 | 1 | 472 | 0 |
| 15 | 550 | 0 | 550 | 0 |
| 16 | 1,543 | 11 | 1,532 | 0 |
| 17 | 512 | 0 | 512 | 0 |
| 18 | 851 | 1 | 815 | 35 |
| 19 | 767 | 0 | 767 | 0 |
| 20 | 825 | 128 | 697 | 0 |
| 21 | 899 | 8 | 891 | 0 |
| 22 | 572 | 372 | 172 | 28 |
| 23 | 851 | 26 | 825 | 0 |
| 24 | 355 | 9 | 346 | 0 |
| 25 | 480 | 8 | 472 | 0 |
| 26 | 565 | 1 | 564 | 0 |
| 27 | 354 | 2 | 352 | 0 |
| 28 | 737 | 6 | 731 | 0 |
| 29 | 363 | 1 | 362 | 0 |
| 30 | 443 | 0 | 443 | 0 |
| 31 | 554 | 0 | 554 | 0 |
| 32 | 286 | 0 | 286 | 0 |
| 33 | 267 | 1 | 266 | 0 |
| 34 | 228 | 93 | 134 | 1 |
| 35 | 257 | 0 | 257 | 0 |
| 36 | 720 | 3 | 717 | 0 |
| 37 | 417 | 91 | 326 | 0 |
| 38 | 340 | 189 | 151 | 0 |
| 39 | 64 | 0 | 64 | 0 |
| 40 | 87 | 4 | 83 | 0 |
| **Total** | **22,033** | **2,691** | **19,276** | **66** |

## Whole-vector arbitrary packed ranges — 2026-10-19

The self-check extractor now admits whole-vector declarations and operations
over one-dimensional packed scalar ranges with arbitrary left/right bounds.
Selected reads and writes on noncanonical ranges remain loud because the
current evaluator still needs explicit bound mapping. The fresh run over the
same **22,033** paths reports **2,726 clean**, **19,241 partial**, **66 include
skips**, and **0 extraction errors**: 35 additional clean files with no
losses. `AssignmentExpression:target` falls from **4,314 to 4,224 files**;
`CallExpression` is now the leading refusal at **4,226**. The `packed_ranges`
fixture and proof run through the self-check surface; this is not a simulator
agreement claim for the corpus.

The chapter deltas from the preceding cell census are:

| Chapter | Clean | Partial | Include skip |
|---|---:|---:|---:|
| 6 | 310 | 875 | 0 |
| 7 | 33 | 763 | 0 |
| 10 | 165 | 492 | 0 |
| 11 | 550 | 484 | 0 |
| 20 | 140 | 685 | 0 |
| 38 | 190 | 150 | 0 |

## Time-zero `$time` queries — 2026-10-19

The self-check extractor folds zero-argument `$time` expressions to a 64-bit
zero literal with `time_zero` provenance. A fresh run over the same
**22,033** paths reports **2,789 clean**, **19,178 partial**, **66 include
skips**, and **0 extraction errors**: 63 additional clean files and no
losses. `CallExpression` falls from **4,226 to 3,565** files, while timed
processes still retain their delay/event refusals. The `time_zero` fixture and
Lean proof pass; this is not a whole-corpus simulator-agreement claim.

## Constant bit selects on arbitrary packed ranges — 2026-10-19

The self-check extractor now normalizes in-range constant bit selects on
one-dimensional noncanonical packed ranges to the existing LVec index
geometry. Dynamic/out-of-range indices and part-selects remain loud. The
fresh **22,033**-path run reports **2,795 clean**, **19,172 partial**, **66
include skips**, and **0 extraction errors**: 6 additional clean files with
no losses. `AssignmentExpression:target` falls from **4,224 to 4,223 files**.
The `packed_range_select` fixture and proof pass through Lean; this is not a
whole-corpus simulator-agreement claim.

## Positional fixed-unpacked initializers — 2026-10-19

Exact-length positional assignment patterns now populate the vector cells of
eligible one-dimensional fixed-unpacked integral declarations. Keyed/default,
wrong-length, effectful and aggregate initializers remain loud. The fresh
**22,033**-path run reports **2,798 clean**, **19,169 partial**, **66 include
skips**, and **0 extraction errors**: 3 additional clean files with no
losses. The `unpacked_init` fixture and Lean proof pass; this is not a
whole-corpus simulator-agreement claim.

## Direct packed-struct field windows — 2026-10-19

Direct fields of untagged packed structs and packed unions now lower to fixed
bit windows over their aggregate vector identifier. Nested/unpacked members,
classes, interfaces, tagged unions and nonintegral fields remain loud. The
fresh **22,033**-path run reports **2,886 clean**, **19,081 partial**, **66
include skips**, and **0 extraction errors**: 88 additional clean files with
no losses. `AssignmentExpression:target` falls **4,223 → 4,051** and
`MemberAccessExpression` falls **1,299 → 1,203**. The `packed_struct` fixture
and proof pass through Lean; this is not a whole-corpus simulator-agreement
claim.

## Whole-array positional assignment patterns — 2026-10-19

Whole assignments to eligible one-dimensional fixed-unpacked integral arrays
now admit an exact-length positional pattern. The extractor expands the
pattern into per-cell assignments over the same vector-cell state used for
constant element access and declaration initializers. Keyed/default,
wrong-length, dynamic, aggregate and destination-aliasing patterns remain
loud. A paired run over **22,029** chapter-scoped paths reports **2,889
clean**, **19,074 partial**, **66 include skips**, and **0 extraction errors**:
four clean gains and no losses on that checkout; the target wall falls by 23
files (**4,049 → 4,026**). The `unpacked_assign` fixture and Lean proof pass
through the self-check runner. This is not a whole-corpus simulator-agreement
claim.

## Assignment-target repricing — 2026-10-19

The paired target census leaves **87** files whose only recorded blocker is
`AssignmentExpression:target`, containing **117** target instances. The
remaining instances split by source shape as follows; a file may occur in more
than one row.

| residual target shape | instances | files |
|---|---:|---:|
| keyed/default/replicated or unpacked-array pattern RHS | 30 | 29 |
| dynamic element target | 21 | 17 |
| concatenated or streaming target | 16 | 15 |
| whole aggregate/array target | 18 | 13 |
| packed or unpacked part-select target | 13 | 9 |
| member target (nested packed, union or unsupported member) | 16 | 7 |
| constant element/bit target in a continuous or unsupported shape | 3 | 3 |

The next broad aggregate tier is not priced as a safe admission: dynamic and
unpacked aggregate targets require a runtime aggregate store, while the
continuous concatenation and part-select rows require continuous-assignment
scheduling. Nested/unpacked/class/interface member targets remain loud, and
the direct packed-struct window tier stays limited to untagged direct integral
fields. A future item must name one of those prerequisites and supply its
representation before lowering any wider target family.

Reproduce the table with
`python3.9 extractors/sv/target_reprice.py --corpus <corpus>/tests`; the
instrument reads the source in-process and writes no envelopes beside the
corpus.

## Bounded dynamic fixed-array cells — 2026-10-19

Pure integral dynamic accesses to one-dimensional fixed-unpacked arrays now
lower to finite conditional paths over the declaration's expanded vector
cells. Case-equality dispatch preserves x/z-index no-op writes and all-x
out-of-range reads. Dynamic/associative/queue storage, multidimensional arrays
and effectful indices remain loud. The paired **22,029**-path run reports
**2,906 clean**, **19,057 partial**, **66 include skips**, and **0 extraction
errors**: 17 clean gains and no losses; `AssignmentExpression:target` falls
**4,026 → 3,999**. The `unpacked_dynamic` fixture and proof pass through the
self-check runner. This is not a whole-corpus simulator-agreement claim.

## Equal-length fixed-array copies — 2026-10-19

Whole assignment between equal-length one-dimensional fixed-unpacked integral
arrays now pairs their already expanded cells in declaration order. Different
lengths, incompatible element widths, conditional aggregate expressions and
unsupported storage forms remain loud. The paired **22,029**-path run reports
**2,915 clean**, **19,048 partial**, **66 include skips**, and **0 extraction
errors**: nine additional clean files with no losses; the target wall falls
**3,999 → 3,978**. The `unpacked_copy` fixture and proof pass through the
self-check runner. This is not a whole-corpus simulator-agreement claim.

## Conditional fixed-array assignments — 2026-10-19

Pure one-condition ternaries over equal-length fixed-unpacked integral arrays
now lower cell by cell to existing `Ternary` values. An x condition therefore
keeps the per-bit conditional merge, while patterns, calls, unequal shapes and
unsupported aggregate storage remain loud. The paired **22,029**-path run
reports **2,918 clean**, **19,045 partial**, **66 include skips**, and **0
extraction errors**: three additional clean files with no losses; the target
wall falls **3,978 → 3,974**. The `unpacked_conditional` fixture and proof
pass through the self-check runner. This is not a whole-corpus simulator-
agreement claim.

## Constant fixed-array slice patterns — 2026-10-19

Simple in-range constant slices of eligible fixed-unpacked integral arrays now
accept exact-length positional patterns and lower to the selected cells in
source order. Dynamic/indexed/out-of-range slices and keyed/default patterns
remain loud. The paired **22,029**-path run reports **2,919 clean**, **19,044
partial**, **66 include skips**, and **0 extraction errors**: one additional
clean file with no losses; the target wall falls **3,974 → 3,972**. The
`unpacked_slice` fixture and proof pass through the self-check runner. This is
not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array patterns — 2026-10-19

Elaborated keyed/default patterns on eligible fixed-unpacked integral arrays
now lower their per-cell elements in declaration order. Constant replicated
patterns are admitted when the repetition count exactly equals the array
length. Wrong-length, dynamic, aggregate and destination-aliasing forms remain
loud. The `unpacked_patterns` fixture and proof pass through the self-check
runner. The external `sv-tests-2` checkout was unavailable for this turn, so
the committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array initializers — 2026-10-19

The same elaborated structured keyed/default and exact-length constant
replicated patterns now populate eligible fixed-unpacked declaration cells.
Wrong-length, effectful and aggregate initializers remain loud. The
`unpacked_init_patterns` fixture and proof pass through the self-check runner.
The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Constant part selects on arbitrary packed ranges — 2026-10-19

In-range constant simple part selects on one-dimensional noncanonical packed
scalar ranges now normalize their right bound to the existing LVec offset for
both reads and writes. Dynamic, out-of-range and indexed part-selects remain
loud. The `packed_range_part_select` fixture and proof pass through the
self-check runner. The external `sv-tests-2` checkout was unavailable for this
turn, so the committed census snapshot is unchanged and no fresh whole-corpus
gain is claimed. This is not a whole-corpus simulator-agreement claim.

## Constant fixed-array slice copies — 2026-10-19

Equal-length simple constant slices of eligible fixed-unpacked integral arrays
now pair their expanded cells for copies, including a whole-array source or
destination on either side. Overlapping self-copies, dynamic/indexed and
out-of-range slices remain loud because no temporary aggregate snapshot is
introduced. The `unpacked_slice_copy` fixture and proof pass through the
self-check runner. The external `sv-tests-2` checkout was unavailable for this
turn, so the committed census snapshot is unchanged and no fresh whole-corpus
gain is claimed. This is not a whole-corpus simulator-agreement claim.

## Structured and replicated fixed-array slice patterns — 2026-10-19

Elaborated keyed/default and exact-length constant replicated patterns now
populate simple constant fixed-array slices cellwise. Dynamic, indexed,
out-of-range and mismatched forms remain loud. The `unpacked_slice_patterns`
fixture and proof pass through the self-check runner. The external
`sv-tests-2` checkout was unavailable for this turn, so the committed census
snapshot is unchanged and no fresh whole-corpus gain is claimed. This is not a
whole-corpus simulator-agreement claim.

## Conditional fixed-array slice assignments — 2026-10-19

Equal-length simple constant slices on a fixed-array destination and both
branches of a pure ternary now lower cellwise to existing `Ternary` nodes.
Overlapping source/destination names, dynamic/indexed and out-of-range slices
remain loud. The `unpacked_slice_conditional` fixture and proof pass through
the self-check runner. The external `sv-tests-2` checkout was unavailable for
this turn, so the committed census snapshot is unchanged and no fresh
whole-corpus gain is claimed. This is not a whole-corpus simulator-agreement
claim.

## Fixed-array equality and inequality — 2026-10-19

Equal-length whole fixed-unpacked arrays and simple constant slices now compare
cellwise, joining the per-cell `==` or `!=` results with logical `&&`.
Unequal shapes and unsupported aggregate types remain loud. The
`unpacked_compare` fixture and proof pass through the self-check runner. The
external `sv-tests-2` checkout was unavailable for this turn, so the committed
census snapshot is unchanged and no fresh whole-corpus gain is claimed. This
is not a whole-corpus simulator-agreement claim.

## Fixed-array case equality and inequality — 2026-10-19

Equal-length whole arrays and simple constant slices now lower `===` and `!==`
to pairwise cell case comparisons joined by logical `&&`, preserving exact
x/z matching. Unequal shapes and unsupported aggregate types remain loud. The
`unpacked_compare` fixture and proof cover both ordinary and case comparisons.
The external `sv-tests-2` checkout was unavailable for this turn, so the
committed census snapshot is unchanged and no fresh whole-corpus gain is
claimed. This is not a whole-corpus simulator-agreement claim.

## Unpacked-array concatenation into fixed cells — 2026-10-19

Exact-length unpacked-array concatenations now flatten scalar and eligible
whole-array/simple-slice operands in source order and lower them to the
existing fixed-cell assignments. Destination aliases, dynamic or aggregate
operands and mismatched lengths remain loud. The `unpacked_concat` fixture and
proof pass through the self-check runner. The fresh **22,033**-path census
reports **2,952 clean**, **19,015 partial**, **66 include skips**, and **0
extraction errors**: nine additional clean files with no losses; the
`AssignmentExpression:target` wall falls **3,939 → 3,929**. This is not a
whole-corpus simulator-agreement claim.

## Unpacked assignment-pattern LHS — 2026-10-19

An exact positional unpacked pattern on the LHS now pairs its direct scalar
targets with cells from an eligible fixed-unpacked integral RHS, preserving
source-order sampling and destination width/state conversion. Nested,
effectful, duplicate or aliased targets and aggregate or dynamic RHS forms
remain loud. The `unpacked_pattern_lhs` fixture and Lean proof pass through the
self-check runner. The focused rerun cleans the corresponding §10.9.11 target
row; the committed machine census is unchanged because generated outputs are
not committed.

## Right-streaming unpack targets — 2026-10-19

Simple right-streaming unpack targets with no slice size and direct integral
identifier leaves now reuse the existing packed `ConcatTarget` executor. The
RHS is sampled once; a wider source contributes its leading target-width bits.
Left streaming, nested/effectful streams, unpacked aggregate leaves
and a narrower source remain loud. The `streaming_unpack`
fixture and Lean proof pass through the self-check runner. The next fresh
census reports **2,960 clean**, **19,007 partial**, **66 include skips** and
**zero extraction errors**: seven clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,928 → 3,920**. This is not a
simulator-agreement claim.

## Legacy streaming packed-member windows — 2026-10-20

The legacy right-streaming path now admits a constant member chain through an
untagged packed struct or union as one fixed `SelectTarget` leaf. The
`streaming_aggregate_member` fixture splits one sampled four-bit source into a
two-bit member and scalar output; nested packed-union alias leaves are pinned
by the focused extractor battery. Dynamic or effectful member indices, nested
streaming operators, left streaming and sized streams remain loud. No
aggregate runtime store or scheduler behavior was added, and the broad corpus
census was not regenerated for this focused rung.

## Whole packed values in right-streaming targets — 2026-10-20

Whole untagged packed structs/unions now lower to whole-vector streaming
leaves, including local typedef values and flattened fixed-array cells. The
`streaming_packed_value` fixture checks field order, union aliases, x/z and
leading-bit truncation against its extracted statements and a completed
simulator run. The newly admitted §11.4.14 corpus row also agrees on its full
transcript. The wider-source check corrected both extraction modes: streaming
unpack selects the source's leading bits rather than the low bits kept by an
ordinary packed resize.

A paired run over **22,035** paths reports **2,979 → 2,980 clean**,
**18,990 → 18,989 partial**, **66 include skips**, and **zero extraction
errors**: exactly one clean gain, no losses, and the
`AssignmentExpression:target` wall falls **3,942 → 3,941**. The committed
summary is regenerated from this run. The target-only repricing now leaves
**24 files / 31 instances**, with no concatenated/streaming target-only file;
the residual families still require runtime storage or driver-resolution work.
These counts establish extraction coverage only.

## Packed right-streaming sources — 2026-10-20

Pure packed integral right-streaming sources now reuse source-order `Concat`,
including optional slice sizes (ignored for `>>`). A wider destination adds
zeros at the right before destination two-state conversion. `streaming_pack`
and its symbolic theorem check the real extracted assignment;
`streaming_pack_fixed` exercises both symbolic assignment paths and process
orders. Completed simulator transcripts match both authored fixtures and all
18 newly clean corpus files. Smaller destinations, left/nested streams, `with`
selectors, unpacked
aggregate operands and symbolic parameter/generate families remain loud.

On the same **22,035** paths, **2,980 → 2,998 clean** and **18,989 → 18,971
partial**, with **66 include skips**, **zero extraction errors**, and no
clean losses. `ConversionExpression:StreamingConcat` falls **55 → 36** files;
one further partial file loses only that wall. The machine-readable summary
records this snapshot; these are extraction counts.

## Packed left-streaming sources — 2026-10-20

Packed left streams now lower through fixed selects and `Concat`: low chunks
first, original bit order inside each chunk, and no padding inside a final
short high chunk (§11.4.14.2). A wider destination receives trailing zeros
after reordering. `streaming_left` checks the extracted chunk expression with
a symbolic kernel theorem; `streaming_left_fixed` covers both symbolic process
orders. All 20 newly clean corpus files match their complete simulator output.
Nested/effectful streams, `with` selectors, unpacked aggregates, smaller
destinations and symbolic parameter/generate widths remain loud.

On the same **22,035** paths the pair reports **2,998 → 3,018 clean**,
**18,971 → 18,951 partial**, **66 include skips**, **zero extraction errors**
and no losses. `ConversionExpression:StreamingConcat` falls **36 → 16** files.
The committed summary records this extraction snapshot.

## Legacy continuous fixed-window targets — 2026-10-20

The legacy/self-check extractor now lowers constant packed bit/part selects,
fixed concatenation leaves, and direct untagged packed struct/union members on
continuous assignments to the existing `SelectTarget` windows. The focused
extractor tests cover member and vector writes, static overlap refusal, and
dynamic-index loudness. Tagged, effectful, dynamic fixed-array-cell and
unsupported net-resolution forms remain loud; a constant cell is an
ordinary flat identifier. The broad corpus census was not regenerated for this
focused rung.

## Legacy continuous nested packed-struct windows — 2026-10-20

The focused extractor battery now pins constant bit, simple part and indexed
selections through nested untagged packed-struct member chains as fixed vector
windows on continuous assignments, including flattened fixed-array aggregate
cells. Nested untagged packed unions use the same flat-vector alias windows;
dynamic and unpacked aggregate forms remain outside the tier. No broad census
or simulator-agreement claim is made for this focused boundary.

## Legacy continuous packed-union alias windows — 2026-10-20

Focused extraction now covers direct untagged packed-union members and their
constant indexed windows through the flat vector state. Alternate members
share the same static overlap guard, so conflicting continuous windows remain
loud. Nested untagged unions use the recursive window path below; tagged
unions, dynamic or effectful selections and unpacked storage stay outside this
focused rung. No broad census or simulator-agreement claim is made.

## Legacy continuous nested packed-union alias windows — 2026-10-20

Constant selections through nested untagged packed unions now accumulate fixed
outer offsets and flatten to the existing `SelectTarget` and `SelectRead`
windows. Alternate nested-union members alias one flat vector, while the
static overlap guard rejects conflicting continuous drivers before they could
imply resolution. Dynamic/effectful selections, tagged aggregates and unpacked
storage remain loud; no alias table, aggregate store or second scheduler is
introduced.

## Legacy continuous fixed-array cell windows — 2026-10-20

The legacy continuous-assignment path now has focused coverage for constant
packed bit/part and indexed selections inside flattened one-dimensional
fixed-unpacked cells. Canonical and noncanonical labels normalize to the
existing `SelectTarget`/`SelectRead` offsets, while static overlap is rejected
before it could imply driver resolution. Dynamic or effectful packed indices,
dynamic array indices, and aggregate storage remain loud. This is a focused
extractor boundary; the broad corpus census was not regenerated.

## Legacy continuous noncanonical indexed windows — 2026-10-20

Focused extraction now admits constant `+:` and `-:` selections on
noncanonical packed ranges for direct vectors, nested packed-struct members,
and flattened fixed-array cells. The indexed base is normalized to the
existing fixed-window offset and direction is retained; dynamic/effectful,
out-of-range, aggregate and unsupported net-resolution forms remain loud.
The new boundary tests are extractor-only and do not claim a broad census or
simulator agreement.

## Legacy continuous right-streaming cell windows — 2026-10-20

Simple right-streaming continuous targets now have focused coverage for direct
fixed-array cells, constant packed windows inside cells and direct packed
members of cells. The existing `ConcatTarget` split samples the RHS once;
left/sized/nested streams, dynamic or effectful leaves, aggregate storage and
overlapping windows remain loud. This focused extractor rung does not claim a
broad census or simulator agreement.

## Symbolic streaming targets over fixed cells — 2026-10-20

The symbolic `sv-0.2` procedural path now lowers simple right-streaming
assignments whose leaves are constant packed windows or constant cells of a
flattened fixed-unpacked integral array. `fixed_array_stream_target` samples a
five-bit RHS once, writes `arr[0]` and a scalar leaf in source order, and reads
the cell through the existing comb settle. Dynamic/effectful array indices,
dynamic packed bounds, left/sized/nested streams and aggregate leaves remain
loud. This semantic-only fixture does not change the legacy corpus census or
claim simulator agreement.

## Symbolic continuous streaming targets over fixed cells — 2026-10-20

Continuous right-streaming assignments now reuse the symbolic `ConcatTarget`
window path for constant packed leaves and constant flattened fixed-array cells.
`fixed_array_stream_continuous` samples a five-bit source once, writes `arr[0]`
and a scalar leaf in source order, and reads the cell through comb settle.
Dynamic/effectful leaves, left/sized/nested streams, aggregates and overlapping
windows remain loud. This semantic-only fixture does not change the legacy
corpus census or claim simulator agreement.

## Symbolic nested packed-union alias windows — 2026-10-20

Nested untagged packed-union member chains now accumulate fixed declaration
offsets and lower to `PartSel` windows over the outer vector. The focused
symbolic tests check alternate-field alias visibility and reject overlapping
constant drivers through the existing guard. Dynamic/effectful, tagged and
unpacked aggregate paths remain loud; no aggregate store, driver-resolution
rule or scheduler is added, and the legacy census is unchanged.

## Nested packed-struct field windows — 2026-10-19

Member reads and writes through a chain of untagged packed structs now flatten
the fixed declaration offsets into one `SelectRead`/`SelectTarget` window over
the outer vector. Nested unions, unpacked members, classes, interfaces and
tagged aggregates remain loud. The `packed_struct_nested` fixture and Lean
proof pass through the self-check runner. The fresh **22,033**-path census
reports **2,975 clean**, **18,992 partial**, **66 include skips** and **zero
extraction errors**: 15 clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,920 → 3,909**. This is not a
simulator-agreement claim.

## Typed assignment-pattern operands in unpacked concatenations — 2026-10-19

Unpacked-array concatenations now also flatten a typed simple assignment
pattern whose fixed-array elements are pure integral values at the destination
width. Replicated, nested or mismatched pattern operands remain loud. The
focused §10.10.1 rows now extract cleanly. The fresh **22,033**-path census
reports **2,979 clean**, **18,988 partial**, **66 include skips** and **zero
extraction errors**: four clean gains with no losses; the
`AssignmentExpression:target` wall falls **3,909 → 3,904**. This is not a
simulator-agreement claim beyond the fixture.

## Nested replicated assignment patterns — 2026-10-19

Fixed-array assignment-pattern replication now repeats an inner positional
element list when the constant repetition count times that list length equals
the destination length. Wrong-length, effectful and aggregate forms remain
loud. The §5.11 nested-replication row and a focused fixture pass through the
self-check runner; the fresh census below records the paired result.

The fresh **22,033**-path census reports **2,980 clean**, **18,987 partial**,
**66 include skips** and **zero extraction errors**: one clean gain with no
losses; the `AssignmentExpression:target` wall falls **3,904 → 3,902**. This
is not a simulator-agreement claim beyond the fixture.

## Historical method

* **Walk**: 21,336 `.sv` files in `tests/chapter-3` … `chapter-40` (445
  additional `.sv` files sit directly under `tests/` outside any chapter and
  are out of scope). Metadata (`:name:`/`:tags:`/`:type:`) parsed from each
  header; 1,366 files have no `:type:` line.
* **Pipeline**: the worker calls the same functions `extract.process_file`
  calls (`SyntaxTree.fromText` → `Compilation` → `convert_design`) without
  writing `.sv.json` files into the corpus. Cross-validated on 40 random
  files against the `extract.py` CLI: identical Unsupported sets.
* **Classes**:
  * `skip_include` — the file has a real `` `include `` directive
    (multi-file test; a single-file compile would classify a partial parse,
    so these are skipped with reason). 29 files, 27 of them in chapter-22.
  * `error` — the pipeline raised, or hit the 90 s per-file alarm.
  * `clean` — envelope has **zero** `Unsupported` nodes.
  * `partial` — envelope has `Unsupported` nodes; the distinct `sv_kind`
    values are recorded per file.
* **Determinism**: `--recheck` re-runs a seed-20260721 sample of 200 files
  and compares (status, kinds, adapter blockers, unlockable) — **200/200
  identical** on this census.
* **Runtime**: full census in **3.9 s** (32 workers, 96-core host) — far
  under the 15 min target; the corpus is many small files and pyslang's
  parser is C++.

## (a) Headline counts

| class | files | share |
|---|---:|---:|
| partial | 21,278 | 99.73% |
| clean | 29 | 0.14% |
| skip_include | 29 | 0.14% |
| **EXTRACT-ERROR** | **0** | 0% |
| total | 21,336 | |

Clean by `:type:` (clean / total of that type):

| :type: | clean / total | note |
|---|---:|---|
| simulation | 5 / 18,001 | all 5 are pragma/`protect` tests; 3 have **zero modules** (vacuously clean), none prints PASS via M0 constructs |
| compile_error | 18 / 1,747 | negative tests: *illegal* SV that happens to parse into M0 vocabulary — see robustness notes |
| shell / compile_warning / (none) | 6 / 1,435 | |

The corpus-wide truth: **no self-checking simulation test is runnable at
M0**, because self-checking requires `initial` + `$display`, both outside
the tier — exactly the Adapter phase's motivation.

## (b) Construct-frequency table — THE IMPLEMENTATION PRIORITY QUEUE

Number of `partial` files whose envelope contains each `sv_kind`
(a file counts once per distinct kind), top 60, sorted descending. **This
table is the implementation priority queue for growing the tier**: each row
is "how many corpus files stop being blocked-by-this if the construct is
implemented".

> Caveat: the extractor collapses whole out-of-tier *processes* into a
> single `Unsupported` node, so `ProceduralBlockSymbol:Initial` (row 1)
> hides everything inside `initial` bodies. Section (e) re-measures the
> queue with the adapter tier treated as supported — that residual table is
> the true post-Adapter queue.

| sv_kind | files blocked |
|---|---:|
| `ProceduralBlockSymbol:Initial` | 20569 |
| `VariableSymbol:2state` | 6911 |
| `InstanceSymbol:Instance` | 3658 |
| `ConversionExpression:width` | 3231 |
| `TimedStatement:DelayControl` | 2673 |
| `SubroutineSymbol:Subroutine` | 1414 |
| `ClassType` | 1289 |
| `ProceduralBlockSymbol:NoEventControl` | 1274 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 1016 |
| `VariableSymbol:signed` | 839 |
| `TypeAliasType:TypeAlias` | 799 |
| `PackageSymbol` | 735 |
| `VariableSymbol:type` | 709 |
| `CovergroupType:CovergroupType` | 652 |
| `CheckerSymbol` | 563 |
| `ClockingBlockSymbol:ClockingBlock` | 549 |
| `CheckerInstanceSymbol:CheckerInstance` | 534 |
| `ParameterSymbol:Parameter` | 518 |
| `ClassType:ClassType` | 503 |
| `PropertySymbol:Property` | 464 |
| `WildcardImportSymbol:WildcardImport` | 371 |
| `PrimitiveSymbol` | 371 |
| `ConfigBlockSymbol` | 271 |
| `SequenceSymbol:Sequence` | 261 |
| `GenerateBlockArraySymbol:GenerateBlockArray` | 258 |
| `GenerateBlockSymbol:GenerateBlock` | 250 |
| `TransparentMemberSymbol:TransparentMember` | 239 |
| `TypeAliasType` | 205 |
| `GenvarSymbol:Genvar` | 195 |
| `InstanceArraySymbol:InstanceArray` | 182 |
| `AssignmentExpression:target` | 180 |
| `SignalEventControl:None_` | 149 |
| `GenericClassDefSymbol` | 137 |
| `SubroutineSymbol` | 119 |
| `ExplicitImportSymbol:ExplicitImport` | 104 |
| `VariableSymbol:range` | 92 |
| `ExpressionStatement:UnaryExpression` | 90 |
| `ProceduralBlockSymbol:Final` | 83 |
| `VariableSymbol` | 76 |
| `NetSymbol:Tri` | 66 |
| `RangeSelectExpression` | 63 |
| `CallExpression` | 56 |
| `NetSymbol:Supply1` | 56 |
| `NetSymbol:WAnd` | 53 |
| `SignalEventControl:clock` | 53 |
| `NetSymbol:TriReg` | 53 |
| `NetSymbol:WOr` | 50 |
| `TransparentMemberSymbol` | 50 |
| `TimedStatement:ImplicitEventControl` | 49 |
| `SpecifyBlockSymbol:SpecifyBlock` | 49 |
| `EmptyMemberSymbol:EmptyMember` | 48 |
| `CaseStatement` | 48 |
| `NetSymbol:Supply0` | 47 |
| `PortSymbol:2state` | 42 |
| `GenericClassDefSymbol:GenericClassDef` | 39 |
| `NetSymbol:UserDefined` | 38 |
| `DefParamSymbol:DefParam` | 37 |
| `NetType` | 34 |
| `TimedStatement:EventListControl` | 33 |
| `LetDeclSymbol:LetDecl` | 33 |

## (c) Per-chapter coverage

| chapter | total | clean | partial | skip | clean % |
|---|---:|---:|---:|---:|---:|
| chapter-3 | 232 | 1 | 230 | 1 | 0.4% |
| chapter-4 | 424 | 0 | 424 | 0 | 0.0% |
| chapter-5 | 613 | 0 | 613 | 0 | 0.0% |
| chapter-6 | 1155 | 0 | 1155 | 0 | 0.0% |
| chapter-7 | 771 | 0 | 771 | 0 | 0.0% |
| chapter-8 | 805 | 0 | 805 | 0 | 0.0% |
| chapter-9 | 563 | 0 | 563 | 0 | 0.0% |
| chapter-10 | 629 | 3 | 626 | 0 | 0.5% |
| chapter-11 | 1014 | 0 | 1014 | 0 | 0.0% |
| chapter-12 | 596 | 0 | 596 | 0 | 0.0% |
| chapter-13 | 597 | 0 | 597 | 0 | 0.0% |
| chapter-14 | 464 | 0 | 464 | 0 | 0.0% |
| chapter-15 | 523 | 0 | 523 | 0 | 0.0% |
| chapter-16 | 1511 | 0 | 1511 | 0 | 0.0% |
| chapter-17 | 510 | 0 | 510 | 0 | 0.0% |
| chapter-18 | 816 | 0 | 816 | 0 | 0.0% |
| chapter-19 | 695 | 0 | 695 | 0 | 0.0% |
| chapter-20 | 782 | 0 | 782 | 0 | 0.0% |
| chapter-21 | 857 | 0 | 857 | 0 | 0.0% |
| chapter-22 | 567 | 4 | 536 | 27 | 0.7% |
| chapter-23 | 814 | 3 | 811 | 0 | 0.4% |
| chapter-24 | 347 | 4 | 343 | 0 | 1.2% |
| chapter-25 | 473 | 1 | 472 | 0 | 0.2% |
| chapter-26 | 562 | 0 | 562 | 0 | 0.0% |
| chapter-27 | 350 | 0 | 350 | 0 | 0.0% |
| chapter-28 | 721 | 0 | 721 | 0 | 0.0% |
| chapter-29 | 352 | 0 | 352 | 0 | 0.0% |
| chapter-30 | 427 | 0 | 427 | 0 | 0.0% |
| chapter-31 | 501 | 0 | 501 | 0 | 0.0% |
| chapter-32 | 286 | 0 | 286 | 0 | 0.0% |
| chapter-33 | 267 | 1 | 266 | 0 | 0.4% |
| chapter-34 | 228 | 12 | 215 | 1 | 5.3% |
| chapter-35 | 256 | 0 | 256 | 0 | 0.0% |
| chapter-36 | 720 | 0 | 720 | 0 | 0.0% |
| chapter-37 | 417 | 0 | 417 | 0 | 0.0% |
| chapter-38 | 340 | 0 | 340 | 0 | 0.0% |
| chapter-39 | 64 | 0 | 64 | 0 | 0.0% |
| chapter-40 | 87 | 0 | 87 | 0 | 0.0% |
| **total** | **21336** | **29** | **21278** | **29** | **0.14%** |

(Chapter-34 leads only because `pragma protect` envelopes elaborate to
empty/trivial designs; chapter-24's cleans are illegal-`program` negative
tests. No clean row represents a runnable self-checking test.)

## (d) M0-relevant deep-dive: chapters 4, 6, 11 — the unlockable set

**Definition (precise).** The Adapter phase's self-check tier extends M0
with exactly: `initial` blocks, `$display`/`$finish` calls, string
literals, and local variable declarations (M0-typed: unsigned 4-state
scalar or `[W-1:0]`, with M0/string initializers). A test is **unlockable**
iff it is `partial`, has ≥ 1 module, and re-walking its *elaborated AST*
with those four constructs treated as supported leaves zero blockers —
i.e. `initial` bodies are descended into (the envelope collapses them into
one `Unsupported` node, so envelope tags alone cannot decide this) and
everything inside must be M0 vocabulary (`begin/end`, `=`, `<=`, `if/else`,
M0 expressions) or the four constructs; `$display`/`$finish` arguments may
be string literals or M0 expressions; `$display` is likewise accepted
inside `always` bodies. Counts below are over `:type: simulation` tests.

| chapter | sim tests | clean | partial | **unlockable** | blocked by more |
|---|---:|---:|---:|---:|---:|
| chapter-4 | 420 | 0 | 420 | **0** | 420 |
| chapter-6 | 1011 | 0 | 1011 | **3** | 1008 |
| chapter-11 | 974 | 0 | 974 | **8** | 966 |

The 11 files are listed in `harness/sv/conformance/unlockable.txt`
(corpus-relative paths). Corpus-wide the same definition unlocks **265**
simulation tests (421 files counting non-simulation types).

**The four-construct tier is necessary but nowhere near sufficient for
these chapters.** What still blocks the rest (top residual blockers among
non-unlockable simulation tests, per chapter):

| chapter-4 | files | chapter-6 | files | chapter-11 | files |
|---|---:|---|---:|---|---:|
| `TimedStatement:DelayControl` | 346 | `AssignmentExpression:target` | 543 | `AssignmentExpression:target` | 549 |
| `ConversionExpression:width` | 202 | `VariableSymbol:2state` | 449 | `BinaryExpression:CaseEquality` | 383 |
| `VariableSymbol:2state` | 155 | `NamedValueExpression:2state` | 420 | `NamedValueExpression:2state` | 305 |
| `BinaryExpression:CaseEquality` | 143 | `BinaryExpression:LogicalAnd` | 314 | `VariableDeclStatement:2state` | 273 |
| `AssignmentExpression:target` | 140 | `VariableDeclStatement:2state` | 224 | `BinaryExpression:LogicalAnd` | 209 |
| `NamedValueExpression:2state` | 132 | `TypeAliasType:TypeAlias` | 216 | `BinaryExpression:CaseInequality` | 203 |
| `BinaryExpression:LogicalAnd` | 121 | `BinaryExpression:CaseEquality` | 215 | `VariableSymbol:2state` | 166 |
| `BinaryExpression:CaseInequality` | 69 | `CallExpression` | 198 | `ConversionExpression:width` | 119 |
| `InstanceSymbol:Instance` | 51 | `BinaryExpression:CaseInequality` | 187 | `NamedValueExpression:signed` | 101 |
| `TimedStatement:SignalEventControl` | 37 | `TimedStatement:DelayControl` | 169 | `VariableDeclStatement:signed` | 84 |

Chapter 4 (scheduling) is structurally about `#delay`/event control — its
unlockable set is empty because nearly every test *is about* timing.
Chapters 6/11 are dominated by 2-state types (`int`/`bit` locals and
module vars), `===`/`!==`, `&&`/`||`, and bit/part-select assignment
targets (`AssignmentExpression:target`).

Greedy increments — each row adds one construct to the adapter tier and
shows the cumulative unlockable count over ch. 4/6/11 simulation tests
(base 11):

| + construct | cumulative unlockable (ch 4/6/11) |
|---|---:|
| `BinaryExpression:CaseEquality` (`===`) | 71 |
| `BinaryExpression:CaseInequality` (`!==`) | 126 |
| `TimedStatement:DelayControl` (`#d`) | 167 |
| `ConversionExpression:width` (implicit resize) | 227 |
| `InstanceSymbol:Instance` (hierarchy) | 300 |
| `BinaryExpression:LogicalAnd` (`&&`) | 359 |
| `RangeSelectExpression` (`[a:b]`) | 378 |
| `ConversionExpression:StreamingConcat` | 397 |
| `BinaryExpression:LogicalOr` (`\|\|`) | 415 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 431 |

`===`/`!==` is the single cheapest high-yield add (the Lean value core
`LeanModels/Sv/Basic.lean` already has the case-equality ops — this is
extractor-vocabulary + envelope work only).

## (e) The post-Adapter priority queue (corpus-wide, simulation tests)

Residual blocker frequency over all non-unlockable `partial` simulation
tests with the adapter tier treated as supported — the *true* queue once
initial bodies are visible (top 30; `Call:<name>` = a call other than
`$display`/`$finish`):

| adapter-residual blocker | sim files blocked |
|---|---:|
| `AssignmentExpression:target` | 7498 |
| `TimedStatement:DelayControl` | 7343 |
| `NamedValueExpression:2state` | 6357 |
| `VariableSymbol:2state` | 6158 |
| `ConversionExpression:width` | 4746 |
| `BinaryExpression:LogicalAnd` | 4688 |
| `VariableDeclStatement:2state` | 3792 |
| `InstanceSymbol:Instance` | 3219 |
| `BinaryExpression:CaseEquality` | 3215 |
| `BinaryExpression:CaseInequality` | 2325 |
| `CallExpression` | 2235 |
| `RepeatLoopStatement` | 1214 |
| `SubroutineSymbol:Subroutine` | 1175 |
| `ClassType` | 1086 |
| `ProceduralBlockSymbol:NoEventControl` | 1068 |
| `TimedStatement:SignalEventControl` | 1031 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 921 |
| `NewClassExpression` | 857 |
| `MemberAccessExpression` | 830 |
| `InvalidStatement` | 797 |
| `VariableSymbol:signed` | 763 |
| `ElementSelectExpression` | 747 |
| `HierarchicalValueExpression` | 745 |
| `TypeAliasType:TypeAlias` | 696 |
| `NamedValueExpression:signed` | 640 |
| `VariableSymbol:type` | 634 |
| `PackageSymbol` | 597 |
| `CovergroupType:CovergroupType` | 558 |
| `ClockingBlockSymbol:ClockingBlock` | 450 |
| `BinaryExpression:LogicalOr` | 443 |

The corpus-wide greedy sequence (simulation, base 265):
`InvalidStatement`→578, `+InstanceSymbol:Instance`→887,
`+TimedStatement:DelayControl`→1014, `+BinaryExpression:CaseEquality`→1378,
`+ConversionExpression:width`→1909, `+BinaryExpression:CaseInequality`→2399,
`+PrimitiveInstance`→2842, `+PrimitiveSymbol`→3119. Headline: the
four-construct adapter tier + {`===`, `!==`, `#delay`, width-changing
implicit conversions, bit/part-select targets, 2-state locals} is the
shortest path to a four-digit conformance suite.

## Symbolic continuous concatenation targets — 2026-10-19

The fresh paired extractor census remains **2,980 clean / 18,987 partial / 66
include skips / 0 errors**; `AssignmentExpression:target` remains **3,902**
files because this item changes only the symbolic `sv-0.2` surface. The
target-only repricing is **18 files / 27 instances**, all continuous-assignment
shapes. The new semantic slice admits the direct nested-concatenation subset
through existing comb-settle windows and therefore makes no whole-corpus
clean-count claim. `sem2/concat_assign` exercises source-order flattening,
single-RHS sampling, and x-state propagation through the symbolic runner.

The follow-on `selected_assign` fixture exercises two disjoint constant
part-select continuous drivers through the same symbolic executor. It is a
semantic-tier acceptance case only: the legacy target-only census remains
unchanged because these corpus rows require the scheduler-facing continuous
assignment surface.

The `bit_select_assign` fixture adds the one-bit form: two disjoint constant
bit-select drivers, one fed by a selected source bit and one by a scalar input.
Its trace checks live updates, undriven x bits, and x propagation. This is
also a semantic-tier acceptance case only; the target-only census remains
unchanged for the same scheduler-facing reason.

The `packed_member_assign` fixture then checks direct members of an untagged
packed struct. Fixed field offsets become the same packed windows for writes
and reads, including an x-bearing source. This remains a semantic-tier
acceptance case; the legacy target-only census is unchanged.

The `packed_member_typedef` fixture covers the equivalent typedef spelling.
The alias is discarded as compile-time metadata while the canonical packed
width and member offsets remain in the emitted vector windows.

The `packed_member_nested` fixture checks a two-level untagged packed-struct
chain. Its inner fields flatten to the outer vector's fixed windows, with the
same four-state trace and no new aggregate store.

The `packed_union_assign` fixture checks direct untagged packed-union aliasing:
one field is driven, while a same-width alternate field and the whole union
read the same vector bits. Tagged unions remain outside this slice; nested
untagged union chains use the recursive alias-window slice below.

The `packed_union_typedef` fixture covers the same aliasing through an
untagged packed-union typedef; the alias is erased while the vector width is
retained.

The `indexed_part_assign` fixture covers literal indexed part-selects. Both
`+:` and `-:` forms normalize to the same fixed windows, while dynamic bases
remain loud; this is a semantic-tier fixture with no legacy census change.

The `noncanonical_part_assign` fixture covers simple constant parts on a
`[10:3]` packed range. Source and destination labels normalize to LVec offsets
before the existing window executor runs; this remains a symbolic-only result.

The `noncanonical_bit_assign` fixture applies the same normalization to
literal bit-selects and keeps dynamic noncanonical indices loud.

The symbolic extractor also rejects statically overlapping constant drivers
across separate assignments. The focused regression keeps the first driver
and makes the conflicting process loud; no driver-resolution rule is inferred.

The `packed_member_concat` fixture checks a sampled RHS split across two
disjoint packed-struct member windows, with the member outputs read back from
the same vector.

The `packed_member_subrange` fixture checks a constant `[1:0]` slice inside a
packed member, flattened to the corresponding outer-vector window with x
propagation. Dynamic nested selections remain loud.

The `packed_member_bit` fixture checks a literal bit-select inside a packed
member. Its one-bit write is flattened to the corresponding outer-vector
window and read back through the member, including x propagation; dynamic
nested selections remain loud.

The `packed_union_subrange` fixture applies the same constant-window lowering
to a direct member of an untagged packed union and reads the written bits
through its alternate field. The one-vector alias and x propagation are
preserved; tagged, nested and dynamic union paths remain loud.

The `packed_union_bit` fixture checks the one-bit form through the same union
alias. A literal bit write is visible through the alternate field with x
propagation; tagged, nested and dynamic union paths remain loud.

The `packed_member_indexed` fixture checks literal `+:` and `-:` slices inside
a direct packed-struct member. Both directions flatten to disjoint outer
windows and preserve x propagation; dynamic, parameter-dependent,
noncanonical and effectful nested selections remain loud.

The `packed_union_indexed` fixture checks both literal indexed directions on a
direct untagged packed-union member and reads the shared windows through the
alternate field. Alias visibility and x propagation are preserved; tagged,
nested, dynamic, parameter-dependent, noncanonical and effectful union paths
remain loud.

The `noncanonical_member_subrange` fixture checks a simple `[10:9]` slice of a
`[10:7]` packed-struct member. Declaration labels flatten to the corresponding
outer window with x propagation; direction-mismatched, dynamic, indexed and
effectful nested selections remain loud.

The `noncanonical_union_subrange` fixture applies the same `[10:9]` to `[10:7]`
label mapping to a direct packed-union member and reads the shared window
through its alternate field. Alias visibility and x propagation are preserved;
direction-mismatched, dynamic, indexed and effectful union paths remain loud.

The `noncanonical_member_bit` fixture checks a literal `[10]` select of a
`[10:7]` packed-struct member. The selected declaration label maps to the
outer one-bit window with x propagation; dynamic and effectful nested indices
remain loud.

The `noncanonical_union_bit` fixture applies the same `[10]` mapping to a
direct `[10:7]` packed-union member and reads the bit through its alternate
field. Alias visibility and x propagation are preserved; dynamic and effectful
union indices remain loud.

The `typedef_member_indexed` fixture checks a `+:` slice through an untagged
packed-struct typedef. The alias disappears while the field's fixed outer
window and x propagation remain; tagged, unresolved, dynamic and effectful
alias paths remain loud.

The `typedef_union_indexed` fixture checks the same `+:` slice through an
untagged packed-union typedef and reads it through the alternate field. Alias
visibility and x propagation remain; tagged, unresolved, dynamic and effectful
alias paths remain loud.

The `noncanonical_typedef_subrange` fixture checks a `[10:9]` slice through a
`[10:7]` packed-struct typedef. Alias erasure preserves declaration-label
offsets and x propagation; direction-mismatched, dynamic, indexed and
effectful alias paths remain loud.

The `noncanonical_typedef_union_subrange` fixture applies the same `[10:9]`
mapping through an untagged packed-union typedef and reads the shared bits
through its alternate field. Alias visibility and x propagation remain;
direction-mismatched, dynamic, indexed and effectful union aliases remain
loud.

The `noncanonical_typedef_bit` fixture checks a literal `[10]` select through a
`[10:7]` packed-struct typedef. Alias erasure preserves the one-bit outer
offset and x propagation; dynamic and effectful alias indices remain loud.

The `noncanonical_typedef_union_bit` fixture applies the same `[10]` mapping
through an untagged packed-union typedef and reads the bit through its alternate
field. Alias visibility and x propagation remain; dynamic and effectful union
aliases remain loud.

The `nested_member_indexed` fixture checks a `+:` slice of a member inside a
two-level untagged packed-struct chain. Recursive fixed offsets flatten to the
outer window with x propagation; nested unions, direction mismatches, dynamic
and effectful paths remain loud.

The `nested_member_bit` fixture checks a literal bit of the same nested member
chain. Recursive offsets flatten to the one-bit outer window with x
propagation; nested unions, dynamic and effectful paths remain loud.

The `nested_noncanonical_subrange` fixture checks `[10:9]` of a `[10:7]` final
member in the same nested chain. Recursive and local declaration offsets flatten
to the outer window with x propagation; direction mismatches, dynamic, indexed
and effectful paths remain loud.

The `nested_noncanonical_bit` fixture checks `[10]` of that `[10:7]` final
member. Recursive and local offsets flatten to the one-bit outer window with x
propagation; dynamic and effectful paths remain loud.

The `nested_member_concat` fixture checks one sampled RHS split across two
disjoint slices of nested members. Recursive windows receive the high and low
RHS pieces in source order with x propagation; dynamic, aliased, duplicate,
overlapping and effectful leaves remain loud.

The `typedef_nested_concat` fixture checks the same nested concatenation through
an untagged packed-struct typedef. Alias erasure preserves recursive windows,
source-order splitting and x propagation; tagged, unresolved, dynamic,
duplicate, overlapping and effectful alias leaves remain loud.

The `nested_noncanonical_concat` fixture checks one sampled RHS split across
`[10:9]` slices of two `[10:7]` final members in a nested chain. Recursive and
local declaration offsets preserve source-order splitting and x propagation;
direction-mismatched, dynamic, duplicate, overlapping and effectful leaves
remain loud.

The `fixed_array_element` fixture checks the symbolic one-dimensional
fixed-unpacked cell boundary. A no-initializer `logic [3:0] arr [0:1]`
declaration becomes the two vector cells `arr[0]` and `arr[1]`; a constant
element assignment and nested bit read use the existing symbolic identifiers,
while dynamic array indices remain loud. This is a semantic-only fixture: the
legacy corpus census and its target-only counts are unchanged, and no aggregate
storage or dynamic array executor is introduced.

The `typedef_fixed_array_element` fixture exercises the same boundary through
an untagged plain packed integral typedef. Alias metadata is erased and the
canonical `[3:0]` element range is retained on each emitted cell, so the
symbolic loader accepts the envelope and the constant write/read trace remains
`0`, `1`, `x`. Signed, 2-state, unresolved and aggregate aliases remain loud;
the legacy corpus census is unchanged.

The `enum_fixed_array_element` fixture carries the same flat-cell storage
through an ordinary four-state enum element type. Each cell keeps its `TypeRef`
metadata, while the constant enum-member write and cell read produce the
member's two-bit vector. Signed, 2-state and aggregate enum storage remain
loud; the legacy corpus census is unchanged.

The `packed_aggregate_array_member` fixture applies the same cell lowering to
untagged packed struct and union elements. Constant member writes and reads
reuse `PartSel` windows over `sa[0]` and `ua[0]`, including the union's alias
view. Tagged, nested-unpacked and dynamic aggregate paths remain loud; the
legacy corpus census is unchanged.

The `fixed_array_initializer` fixture exercises the declaration-time form of
the same flat storage. A pure positional assignment pattern populates `arr[0]`
and `arr[1]` before the continuous reads, producing `first=0001` and
`second=xxxx`; keyed/default and exact replicated patterns are covered by the
extractor tests. Wrong-length, effectful, nested and packed-aggregate
initializers remain loud, and the legacy corpus census is unchanged.

The `fixed_array_concat_target` fixture makes a cell one leaf of a symbolic
`ConcatTarget`. Source-order splitting writes the four-bit `arr[0]` cell and
the one-bit output from one sampled five-bit RHS; the second assignment reads
the same cell back, including x propagation. Dynamic, aliased and overlapping
array leaves remain loud, and the legacy corpus census is unchanged.

The `fixed_array_noncanonical_slice` fixture composes the two normalizations:
the constant cell `arr[0]` is emitted first, then its `[10:9]` element slice
maps to the cell offsets `[3:2]`. The runner observes `11xx` and `x0xx` on the
whole cell; dynamic packed bounds remain loud and no new storage is needed.

The `fixed_array_reverse_range` fixture checks a descending unpacked range
`[1:0]`. Declaration order remains `arr[1]`, `arr[0]`, but the literal `arr[0]`
write and read target the `arr[0]` cell and preserve the same `0`, `1`, `x`
trace. This keeps source labels visible instead of substituting ordinal
positions.

## Extractor robustness notes (observed, not fixed)

1. **Zero crashes.** 21,307 single-file compiles (including 1,747
   deliberately-illegal `compile_error` tests): 0 pipeline exceptions,
   0 `ExtractorInternal:*` nodes, 0 per-file timeouts. The "never fails on
   valid SV" guarantee empirically extends to invalid SV.
2. **`clean` does not imply valid SV.** `extract.py` never consults
   compilation diagnostics, so 18 of the 29 clean files are
   `:type: compile_error` negative tests (e.g.
   `chapter-10/10.3.2--variable-only-one-continuous-assignment-driver.sv`:
   two continuous assigns to one variable — illegal, but every node is M0
   vocabulary). Any conformance harness built on envelopes must gate on
   `:type:` (or on slang diagnostics) before trusting a clean envelope.
3. **Signedness is explicit in the M0 envelope.** Signed four-state ports,
   variables and nets retain `signed: true`; order comparisons whose two
   elaborated operands are signed are emitted as `s<`, `s<=`, `s>` or `s>=`.
   The M0 value core interprets those tags as two's-complement comparisons and
   still collapses any x/z operand to x. Unsigned comparisons keep their
   existing tags and behavior. This closes the former `type_width` refusal and
   the `-1 < 0` mis-evaluation boundary without inferring signedness from
   names at runtime.
4. **`InvalidStatement` clusters on unknown system calls**: 797 simulation
   files carry it, 313 of them as their *only* adapter-residual blocker —
   overwhelmingly slang marking statements bad around system functions it
   doesn't accept in that form (`$abs(-5)`, `$test$plusargs(vector)`, …).
   These are slang-frontend conformance gaps, not extractor bugs; they cap
   the reachable suite regardless of Lean-side work.
5. **Multi-file tests**: 29 files use real `` `include `` directives (27 in
   chapter-22). `extract.py` compiles single files with no include path, so
   the census skips them with reason rather than misclassifying a partial
   parse. Supporting them needs an include-dir argument in `extract.py`
   (one-line `SyntaxTree.fromText` change) — deferred.

## Artifacts

**CORRECTED 2026-08-23** (quality audit HIGH, `docs/quality-audit-2026-08-23.md`
§sv). This section previously named `harness/sv/conformance/census.json` as
"the summary block backing every table above" — a file that **`.gitignore`
line 5 excludes**, so it is absent from every checkout. A table whose backing
artifact cannot be obtained is a number about nothing, and the exclusion was
worse than an oversight because it looked deliberate.

* **`docs/sv-construct-census.json` — THE COMMITTED ARTIFACT, and what
  every table above should be read against.** Provenance + summary block,
  20 295 bytes, sorted and indent-stable so a double run is byte-identical.
  It carries the corpus name and path, file count, walk mode, frontend
  FAMILY (`pyslang-11`, never a point release), platform and python version,
  because a census that cannot say what it measured is not a measurement.
  `--compare` checks it against a fresh run and **exits non-zero on any
  drifting key**.
* `extractors/sv/census.py` — the census tool (python3.12 + pyslang 11.x;
  `--corpus-name`, `--corpus`, `--all-dirs`, `--recheck`, `--compare`,
  `--limit`, `--jobs`). Regenerate both artifacts with:

      python3.12 extractors/sv/census.py --corpus-name sv-tests-2

* `harness/sv/conformance/census.json` — the **per-file** records, ~11.9 MB
  over 21 186 files. **Deliberately not committed**: this repository's
  census artifacts run 6 KB–773 KB, so the per-file half stays
  regenerable-by-the-line-above while the half every claim actually cites is
  the committed summary. Its exclusion is now a stated policy rather than a
  silent `.gitignore` entry.
* `harness/sv/conformance/unlockable.txt` — **0 bytes on this host, and that
  is a measured finding rather than a missing file.** This document was
  written when it held 11 ch-4/6/11 paths. Re-measured 2026-08-22: **two of
  those eleven files no longer exist in the corpus; the other nine do and no
  longer classify as unlockable.** `classify()` was verified
  **byte-identical** to the committed version function-by-function, so this
  is a corpus-or-host difference and **not a regression** — the landed set
  was measured on Linux, this one on `darwin-arm64`. Recording it is the
  point: with no provenance stamp there was no way to tell those three
  causes apart, which is why the stamp now exists.

**One further staleness this correction exposes**: the counts above were
taken over **21 336** chapter files; the corpus today walks **21 186**. The
tables are therefore accurate as of their census date and not as of this
checkout — which is exactly what `--compare` is for, and why it now exits
non-zero rather than reporting agreement it cannot support.


### Type-directed packed selected reads — 2026-10-20

Supported two-state integral vectors and whole untagged packed structs/unions
now reuse the legacy selected-read operation. Invalid selected positions are
zero for a two-state whole source and x for a four-state whole source; partial
overlap retains valid bits. Mixed-field aggregates use their whole state kind.
The lowering applies two-state conversion to the result, preserving unsigned
selection and the existing constant-only noncanonical-range normalization.
Dynamic/effectful and unsupported aggregate shapes retain their prior limits;
the symbolic selected-read path is unchanged.

On the SAME **22,035** chapter paths, the paired census reports **3,018 → 3,054
clean**, **18,951 → 18,915 partial**, **66 include skips** and **zero extraction
errors**, with **37 gains** and **one loss**. The loss closes a prior false admission
of named string control escapes `\a`, `\v` and `\f`, whose decoded values
disagree with the simulator; those spellings now refuse before resize folding.
The authored `selected_types` fixture and 34 newly clean time-zero files match
complete simulator output in value-preserving mode. A further timed NBA-loop
file agrees through the existing scheduler. Two newly clean files remain loud
in the time-zero runner because they need delay or continuous-process support. Default-mode probes disagree on partial invalid reads,
so this comparison does not assert default-mode agreement there. Three
fixture-bound kernel theorems cover unknown-index zero fill and symbolic
partial overlap for both source state kinds. No evaluator or scheduler changed.


### Time-zero query boundary — 2026-10-20

A fresh paired **22,035**-path extraction census is unchanged: **3,054 clean**,
**18,915 partial**, **66 include skips**, zero errors and zero changed rows.
The runtime loader now preserves existing `time_zero` literal provenance as
design-level metadata and refuses it at the timed boundary. Time-zero
execution and ordinary literal timed execution remain available. The
previously extraction-clean delayed packed-struct corpus fixture continues
to refuse in the self-check runner and now also refuses explicitly in the
timed loader, closing its constant-zero `$time` leak. This is a corrected
admission boundary, not additional corpus runtime coverage.

## Invalid elaboration diagnostics — 2026-10-22

The fresh 22,043-path census records `Elaboration:invalid-compilation` in
**33** files, all sole refusals. The one-span-per-file repricing is split into
17 generate-scope name conflicts, four missing-delimiter spans, three nested
generate-region spans, three generate-port declarations, two nonconstant
generate schemes, four genvar-scope errors, one generate end-label mismatch
and one macro conditional-expression error. These feature counts overlap the
same 33 one-span files. The
frontend has rejected the elaborated design, so these rows remain diagnostic
boundaries rather than partial runtime programs. See
[invalid elaboration diagnostics](sv-elaboration-invalid.md) and the
read-only `extractors/sv/elaboration_invalid_reprice.py` instrument.

## `always_latch` inferred-sensitivity boundary — 2026-10-22

The fresh 22,043-path census records `ProceduralBlockSymbol:AlwaysLatch` in
**53** files: **13** are latch-only and 40 co-occur. Repricing the sole files
finds 13 spans: 12 infer sensitivity, six use nonblocking assignments, two
include mixed or timed companion processes, and one each exercises an explicit
timing-control diagnostic, a forbidden fork/join, multiple outputs, nested
enables and a protected region. Features overlap. The envelope does not carry
inferred wait registration or retained latch state, so all 13 remain loud. See
[`always_latch`](sv-always-latch.md) and
`extractors/sv/always_latch_reprice.py`.

## User-defined primitive boundary — 2026-10-22

The fresh 22,043-path census records `PrimitiveSymbol` in **382** files: **13**
are UDP-only and 369 co-occur. Repricing the sole files finds 13 UDP spans:
three port-shape diagnostics, one combinational current-state field, two all-X
input rows with non-X output/next-state, one duplicate-input row, three
multiple-transition rows, one missing input field, one `z` table symbol and
one invalid initial output value. UDP declarations and tables remain loud; the
legacy envelope has no truth-table state or transition matcher. See [the UDP
boundary](sv-udp.md) and `extractors/sv/udp_reprice.py`.

## Concurrent sequence declaration boundary — 2026-10-22

The fresh 22,043-path census records `SequenceSymbol:Sequence` in **284**
files: **12** are sequence-only and 272 co-occur. Repricing the sole files
finds **15** sequence spans: five local variables, four formal arguments,
seven multiclock rows, one `intersect`, nine temporal concatenations, two
matched endpoints, one end label, one event/local diagnostic, two
sequence-typed formals and two sampled-value functions. Features overlap across
spans. Sequence attempts and sampled history remain outside the envelope; see
[the sequence boundary](sv-sequences.md) and
`extractors/sv/sequence_reprice.py`.

## Residual module typedef boundary — 2026-10-22

The fresh 22,043-path census records `TypeAliasType:TypeAlias` in **299** files:
**12** are alias-only and 287 co-occur. Repricing the sole files finds 12
spans: eight `$bits` queries, nine aggregate typedefs, three enum typedefs,
two enum-member redefinitions, one nonpositive enum range and one
nonconstant member initializer. Features overlap. The residual aliases remain
loud; see [residual module typedefs](sv-type-alias-boundary.md) and
`extractors/sv/type_alias_reprice.py`.

## Compilation-unit aggregate typedef boundary — 2026-10-22

The fresh 22,043-path census records `TypeAliasType` in **116** files: **12**
are unit-alias-only and 104 co-occur. Repricing the sole files finds **13**
overlapping spans: seven nonintegral packed members, one packed-union width,
two packed-dimension qualifiers, one unpacked-struct-signing diagnostic, two
union-member defaults, one void-in-untagged-union diagnostic, two packed
tagged-union shapes, two tagged-union dynamic members and one untagged-union
dynamic member. The aliases remain loud; see [compilation-unit aggregate
typedefs](sv-unit-type-aliases.md) and
`extractors/sv/unit_type_alias_reprice.py`.

## Element-select source-type boundary — 2026-10-22

The fresh 22,043-path census records `ElementSelectExpression:source-type` in
**662** files: **11** are sole refusals and 651 co-occur. Repricing the sole
files finds **23** spans: one scalar source diagnostic, 17 nested packed-union
member selections, two two-state unpacked-array out-of-bounds reads, two
four-state out-of-bounds reads and one enum-array base-type result. The source
type remains loud; see [element-select source types](sv-element-select-source.md)
and `extractors/sv/element_select_source_reprice.py`.

## Package subroutine boundary — 2026-10-22

The fresh 22,043-path census records `Package:Subroutine` in **194** files:
**10** are sole refusals and 184 co-occur. Repricing the sole files finds
**12** spans: ten package function declarations, nine constant-function uses,
one nonconstant package function and two DPI imports. Features overlap. The
package callable boundary remains loud; see [package subroutines](sv-package-subroutines.md)
and `extractors/sv/package_subroutine_reprice.py`.

## Inout port boundary — 2026-10-22

The fresh 22,043-path census records `PortSymbol:InOut` in **10** files: **9**
are sole refusals and one co-occurs. Repricing the sole files finds **14**
spans: five generic-interface non-ANSI diagnostics, two unpacked-dimension
inheritance cases, two integer-to-signed resets, two packed-dimension-to-wire
resets, one inout initializer, one interconnect initializer and one signed
interconnect port. The bidirectional port remains loud; see [inout ports](sv-inout-ports.md)
and `extractors/sv/inout_port_reprice.py`.

## Variable type boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol:type` in **150** files:
**10** are sole refusals and 140 co-occur. Repricing the sole files finds
**10** spans: nine fixed unpacked-array storage declarations, seven of those
multidimensional, nine packed-plus-unpacked element types and one invalid
packed dimension on an aggregate. Features overlap. The variable type remains
loud; see [variable types](sv-variable-types.md) and
`extractors/sv/variable_type_reprice.py`.

## Compilation-unit variable boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol` in **76** files: **10**
are sole refusals and 66 co-occur. Repricing the sole files finds **10** spans:
nine compilation-unit variables, two multiple-top-level-module rows, one
enum-range declaration and one invalid packed dimension on `int`. Features
overlap. The residual variable boundary remains loud; see
[compilation-unit variables](sv-compilation-unit-variables.md) and
`extractors/sv/variable_symbol_reprice.py`.

## Case-subject boundary — 2026-10-22

The fresh 22,043-path census records `CaseStatement:subject` in **30** files:
**8** are sole refusals and 22 co-occur. Repricing the sole files finds **8**
spans: five `$time` subjects, one constant-expression subject, one packed-union
member subject and one packed-struct part-select subject. The subject remains
loud; see [case subjects](sv-case-subjects.md) and
`extractors/sv/case_subject_reprice.py`.

## Net type boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:type` in **24** files: **7**
are sole refusals and 17 co-occur. Repricing the sole files finds **7** spans:
four multidimensional net arrays, one generated net-array case, two packed-
struct nets and one typedef-struct net. Features overlap. The net type remains
loud; see [net types](sv-net-types.md) and
`extractors/sv/net_type_reprice.py`.

## `supply1` net boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:Supply1` in **56** files: **5**
are sole refusals and 51 co-occur. Repricing the sole files finds **5** spans;
all carry a supply-strength logic-one driver and one has a continuous-strength
context. The net remains loud; see [the `supply1` boundary](sv-supply1.md) and
`extractors/sv/supply1_reprice.py`.

## Variable packed-range boundary — 2026-10-22

The fresh 22,043-path census records `VariableSymbol:range` in **62** files:
**7** are sole refusals and 55 co-occur. Repricing the sole files finds **7**
unsupported range spans: four multidimensional packed ranges and three packed-
struct array ranges. The range remains loud; see [variable packed ranges](sv-variable-ranges.md)
and `extractors/sv/variable_range_reprice.py`.

## Explicit conversion boundary — 2026-10-22

The fresh 22,043-path census records `ConversionExpression:Explicit` in **37**
files: **7** are sole refusals and 30 co-occur. Repricing the sole files finds
21 real-to-integral rounding casts and one typed assignment-pattern cast. The
cast remains loud; see [explicit conversions](sv-explicit-casts.md) and
`extractors/sv/explicit_cast_reprice.py`.

## Invalid hierarchy boundary — 2026-10-22

The fresh 22,043-path census records `Hierarchy:invalid-compilation` in **329**
files: **7** are sole refusals and 322 co-occur. Repricing the sole files finds
seven rejected hierarchy spans across parameter assignment, port-list syntax,
localparam overrides and hierarchical `type()` references. The rejected
hierarchy remains loud; see [invalid hierarchies](sv-invalid-hierarchies.md)
and `extractors/sv/hierarchy_invalid_reprice.py`.

## Conditional event (`iff`) boundary — 2026-10-22

The fresh 22,043-path census records `SignalEventControl:iff` in **7** files;
all **7** are sole refusals. Repricing finds four procedural event guards,
two `always_ff` guards and one procedural `always` guard, with three edge and
four level-qualified forms. The guard remains loud; see [conditional events](sv-event-iff.md)
and `extractors/sv/event_iff_reprice.py`.

## Invalid static-local boundary — 2026-10-22

The fresh 22,043-path census records `StaticLocal:invalid-compilation` in
**241** files: **7** are sole refusals and 234 co-occur. Repricing the sole
files finds seven rejected static-local spans covering lexical errors,
declaration ordering and block-label syntax. The rejected block remains loud;
see [invalid static locals](sv-invalid-static-locals.md) and
`extractors/sv/static_invalid_reprice.py`.

## Invalid continuous-assignment boundary — 2026-10-22

The fresh 22,043-path census records `ContinuousAssignSymbol:InvalidExpression`
in **14** files: **6** are sole refusals and 8 co-occur. Repricing the sole
files finds seven rejected assignment spans involving `default_nettype none`,
invalid `supply0`/`supply1` directives and `undefineall` state. The rejected
assignment remains loud; see [invalid continuous assignments](sv-invalid-continuous-assignments.md)
and `extractors/sv/continuous_invalid_reprice.py`.

## Empty-member boundary — 2026-10-22

The fresh 22,043-path census records `EmptyMemberSymbol:EmptyMember` in **57**
files: **6** are sole refusals and 51 co-occur. Repricing the sole files finds
six empty-member spans covering soft-keyword mode, unnamed primitive arrays,
nested attributes and dollar-leading identifiers. The empty member remains
loud; see [empty members](sv-empty-members.md) and
`extractors/sv/empty_member_reprice.py`.

## Assignment-pattern boundary — 2026-10-22

The fresh 22,043-path census records `AssignmentPattern:integral-shape` in
**5** files, all sole refusals. Repricing finds **10** typed packed pattern
spans, each using a casted nested pattern in a concatenation. The pattern
remains loud; see [assignment patterns](sv-assignment-pattern-boundary.md) and
`extractors/sv/assignment_pattern_reprice.py`.

## Bitwise XNOR boundary — 2026-10-22

The fresh 22,043-path census records `BinaryExpression:BinaryXnor` in **7**
files: **5** are sole refusals and 2 co-occur. Repricing the sole files finds
**10** spans across the `~^` and `^~` spellings, with variable and literal
operands. XNOR remains loud; see [bitwise XNOR](sv-xnor.md) and
`extractors/sv/xnor_reprice.py`.

## Pattern-condition boundary — 2026-10-22

The fresh 22,043-path census records `ConditionalStatement:pattern` in **12**
files: **5** are sole refusals and 7 co-occur. Repricing the sole files finds
**9** spans covering constant integral, identifier-binding and structure member
or wildcard patterns. The pattern remains loud; see [pattern conditions](sv-pattern-conditions.md)
and `extractors/sv/pattern_condition_reprice.py`.

## Elaboration system-task boundary — 2026-10-22

The fresh 22,043-path census records `ElabSystemTaskSymbol:ElabSystemTask` in
**12** files: **5** are sole refusals and 7 co-occur. Repricing finds six
elaboration-task spans containing `$info` and `$warning`. The task remains
loud; see [elaboration system tasks](sv-elaboration-system-tasks.md) and
`extractors/sv/elab_task_reprice.py`.

## Hierarchy timescale boundary — 2026-10-22

The fresh 22,043-path census records `Hierarchy:timescale` in **27** files:
**5** are sole refusals and 22 co-occur. Repricing finds five hierarchy spans
with per-module directives and time observations or delays. The scale remains
loud; see [hierarchy timescales](sv-timescale.md) and
`extractors/sv/timescale_reprice.py`.

## `supply0` net boundary — 2026-10-22

The fresh 22,043-path census records `NetSymbol:Supply0` in **48** files:
**5** are sole refusals and 43 co-occur. Repricing finds five supply-strength
net spans, including one continuous-strength context. The net remains loud; see
[`supply0`](sv-supply0.md) and `extractors/sv/supply0_reprice.py`.

## System-call format boundary — 2026-10-22

The fresh 22,043-path census records `SysCall:format` in **6** files: **5**
are sole refusals and one co-occurs. Repricing finds five format spans, four
macro default/empty-argument cases and one runtime display format. The call
remains loud; see [system-call formatting](sv-syscall-format.md) and
`extractors/sv/syscall_format_reprice.py`.

## Compilation-unit parameter boundary — 2026-10-22

The fresh 22,043-path census records `ParameterSymbol` in **25** files: **5**
are sole refusals and 20 co-occur. Repricing finds five compilation-unit
parameter spans with `$unit::` references, module context and shadowing. The
parameter remains loud; see [parameter scope](sv-parameter-scope.md) and
`extractors/sv/parameter_scope_reprice.py`.

## Residual two-state named-value boundary — 2026-10-22

The fresh 22,043-path census records `NamedValueExpression:2state` in **1,482**
files: **5** are sole refusals and 1,477 co-occur. Repricing finds five fixed-
array named-value spans covering unpacked concatenation, indexed patterns,
array literals and descending `foreach`. The name remains loud; see
[residual two-state named values](sv-namedvalue-2state.md) and
`extractors/sv/namedvalue_2state_reprice.py`.

## Invalid enumeration boundary — 2026-10-22

The fresh 22,043-path census records `Enum:invalid-compilation` in **36**
files: **4** are sole refusals and 32 co-occur. Repricing finds four rejected
enum spans: three X/Z values on two-state bases and one duplicate value. The
enum remains loud; see [invalid enums](sv-invalid-enums.md) and
`extractors/sv/enum_invalid_reprice.py`.

## Large fixed-array sparse cells — 2026-10-23

The 2^24-element fixed unpacked array declaration is admitted when its
procedural uses are constant element selections. The extractor stores only
those observed cells, so the self-check interpreter can execute the standard's
boundary-access test without allocating millions of envelope declarations.
Dynamic and aggregate uses remain loud. The new differential fixture is
`Examples/system-verilog/large_fixed_array/large_fixed_array.sv`.

## Unused string literal initializers — 2026-10-23

Unused module and local `string` declarations with pure literal initializers
are admitted as inert metadata on the time-zero path. Reads, writes,
concatenation, formatting, and nonliteral initializers remain loud. The
`string_literal_decl` differential fixture covers this declaration-only slice.

## Pure string literal writes — 2026-10-23

Pure literal assignments to opaque strings are erased when they have no state
effect. Nonliteral writes and string reads remain loud. The
`do_while_string_literal` fixture supplies differential evidence.

## Literal string `getc` queries — 2026-10-24

The self-check extractor now lowers `.getc(index)` on an unchanged pure ASCII
literal string. It returns the literal byte for an in-range integral index and
zero for negative or out-of-range indices. Dynamic indices, writes, dynamic
initializers, non-ASCII strings, and other methods remain loud. The
`literal_string_getc` fixture supplies the differential row.

The 22,048-path census moves **4,791 → 4,797 clean** and **17,191 → 17,185
partial**; `CallExpression` falls **2,990 → 2,986**. Differential coverage
moves **104/100/0/4 → 105/101/0/4**.

## Single literal continuous net drivers — 2026-10-24

A single whole-net continuous assignment with a pure integral literal RHS now
lowers to the existing time-zero blocking assignment. This narrow case has no
future RHS change, driver conflict, selected target, or scheduler-visible
update; dynamic RHS expressions, variable or selected targets, and multiple
drivers remain loud. The `constant_net_driver` fixture supplies the differential
row and preserves the scheduler-owned boundary for all other continuous forms.

The 22,048-path corpus census is unchanged because its target-only continuous
driver witnesses require dynamic or multiple-driver behavior. Differential
coverage moves **105/101/0/4 → 106/102/0/4**; grammar coverage moves
**212/81/131 → 213/82/131** because the new fixture changes the retained
syntax-kind witness.

## Type-keyed enum defaults in packed-struct array targets — 2026-10-24

A whole fixed unpacked array of packed-struct elements now accepts one enum
type key together with a literal scalar default. The nested pattern is lowered
to the existing flat vector cells; dynamic or effectful keys/defaults and
other aggregate targets remain loud. The `typed_default_array_pattern` fixture
is the differential witness.

The 22,048-path census moves **4,797 → 4,798 clean** and **17,185 → 17,184
partial**; `AssignmentExpression:target` falls **3,046 → 3,045**. Differential
coverage moves **106/102/0/4 → 107/103/0/4**; grammar coverage remains
**213/82/131**.

## Single literal continuous packed-bit drivers — 2026-10-24

One constant packed bit or part-select with a pure integral literal continuous
driver now lowers to the existing time-zero selected assignment. Multiple
drivers, dynamic sources or selections, and aggregate/streaming targets remain
loud because they need the scheduler-owned driver and resolution path.

The 22,048-path census is unchanged at **4,798 clean / 17,184 partial / 66
include skips** with `AssignmentExpression:target` at **3,045 files**.
Differential coverage moves **107/103/0/4 → 108/104/0/4**; grammar coverage
remains **213/82/131**.

## Static literal wire-driver resolution — 2026-10-24

Multiple whole-net continuous drivers on a declared wire now resolve at time
zero when every source is an integral literal. The implementation applies the
IEEE per-bit table (`z` yields, equal values remain, conflicts and `x` produce
`x`) and emits one flat assignment. Dynamic/variable drivers, selected windows,
strengths, and future changes remain loud.

The 22,048-path census moves **4,798 → 4,806 clean** and **17,184 → 17,176
partial**; `AssignmentExpression:target` falls **3,045 → 3,037**. Differential
coverage moves **108/104/0/4 → 109/105/0/4**; grammar coverage remains
**213/82/131**.

## Literal continuous fixed-array variable cells — 2026-10-24

A pure integral literal continuous assignment to one constant cell of a
one-dimensional fixed-unpacked variable now lowers to the existing time-zero
blocking write for that expanded scalar cell. The source cell must occur once;
net arrays, dynamic or effectful indices, nonliteral sources, and multiple
drivers remain loud. `constant_array_cell_driver` supplies the differential
row and reuses the ordinary fixed-cell storage and interpreter path. The
22,048-path census is unchanged because its fixed-array continuous rows use
net-array types or dynamic drivers. Differential coverage moves
**109/105/0/4 → 110/106/0/4**; grammar coverage remains **213/82/131**.

## Literal continuous fixed-array net cells — 2026-10-24

A one-dimensional fixed-unpacked `wire` array with one pure integral literal
driver per constant cell is flattened into independent `Net` cells. The
existing time-zero assignment and four-state literal-driver resolution are
reused; whole-array, dynamic, multidimensional, non-integral, and effectful
forms remain loud. `constant_net_array_cell_driver` supplies the differential
witness.

The census moves **4,806 → 4,810 clean** and **17,176 → 17,172 partial**;
`AssignmentExpression:target` remains **3,037**. Differential coverage moves
**113/109/0/4 → 114/110/0/4**; grammar coverage remains **213/82/131**.

## Literal continuous packed-variable drivers — 2026-10-24

A pure integral literal continuous assignment to one whole packed variable or
one constant packed bit/part-select now lowers to the existing time-zero
blocking write. The source target must occur once; dynamic or effectful
sources/selections and multiple drivers remain loud. `constant_variable_driver`
supplies both target forms through the existing scalar and packed-target
interpreter operations. The 22,048-path census remains **4,806 clean / 17,176
partial / 66 include skips**, with `AssignmentExpression:target` at **3,037
files**. Differential coverage moves **110/106/0/4 → 111/107/0/4**; grammar
coverage remains **213/82/131**.

## Disjoint literal continuous packed-net windows — 2026-10-24

Multiple continuous assignments to disjoint constant bit/part-select windows
of one packed wire now lower independently to time-zero blocking writes when
all sources are pure integral literals. Overlapping windows and any dynamic
peer remain loud because they require per-bit net resolution and live driver
updates. `disjoint_literal_net_windows` supplies the differential row. The
22,048-path census remains **4,806 clean / 17,176 partial / 66 include skips**
with `AssignmentExpression:target` at **3,037 files**. Differential coverage
moves **111/107/0/4 → 112/108/0/4**; grammar coverage remains **213/82/131**.

## Static literal continuous packed-window resolution — 2026-10-24

The selected-window lowering now resolves overlapping literal drivers on one
packed wire per bit with the IEEE `z`/equal/conflict/`x` table. Dynamic peers,
out-of-range windows, strengths, and future source changes remain loud because
they need live driver and resolution state. `overlapping_literal_net_windows`
supplies the conflict and unchanged-bit witness. The 22,048-path census
remains **4,806 clean / 17,176 partial / 66 include skips**, with
`AssignmentExpression:target` at **3,037 files**. Differential coverage moves
**112/108/0/4 → 113/109/0/4**; grammar coverage remains **213/82/131**.

## Literal continuous `tri` drivers — 2026-10-24

A scalar or packed `tri` with only pure integral literal continuous drivers
uses the same fixed four-state result as a literal `wire`. The declaration
remains a net and the existing per-bit resolution handles `z`, equal values,
conflicts, and `x`; dynamic, effectful, strength, delayed, and future-update
forms remain loud. `constant_tri_driver` supplies the differential evidence.

The census remains **4,810 clean / 17,172 partial / 66 include skips** with
`AssignmentExpression:target` at **3,037 files**. Differential coverage moves
**114/110/0/4 → 115/111/0/4**; grammar coverage remains **213/82/131**.

## Explicit-strength literal continuous drivers — 2026-10-24

A single whole-net continuous driver with an explicit strength pair and a
pure integral literal source now lowers to the existing time-zero assignment.
Selected strength targets, multiple strength drivers, dynamic or effectful
sources, and multiple or mixed-strength `tri` drivers remain loud pending
per-driver strength representation. `constant_strength_driver` supplies the
differential evidence.

The corpus census remains **4,810 clean / 17,172 partial / 66 include skips**;
`AssignmentExpression:target` moves **3,037 → 3,036**. Differential coverage
moves **115/111/0/4 → 116/112/0/4**; grammar coverage moves
**213/82/131 → 214/83/131**.

## Single strengthened `tri` literal drivers — 2026-10-24

A `tri` with one explicitly strengthened whole-net driver and a pure integral
literal source now uses the existing fixed time-zero assignment. With no
competing driver, strength cannot affect the resolved value and no per-driver
state is needed. Selected targets, multiple or mixed-strength drivers,
dynamic/effectful sources, and delayed assignments remain loud.
`constant_tri_strength_driver` supplies the differential evidence.

The corpus census remains **4,810 clean / 17,172 partial / 66 include skips**;
`AssignmentExpression:target` remains **3,036 files**. Differential coverage
moves **116/112/0/4 → 117/113/0/4**; grammar coverage remains **214/83/131**.

## Single strengthened packed-select drivers — 2026-10-24

A single explicitly strengthened packed bit or constant part-select with a
pure integral literal source now lowers to the existing selected time-zero
write. Multiple strengthened selected drivers, dynamic/effectful sources, and
aggregate targets remain loud pending strength-aware selected-driver state.
`constant_strength_select_driver` supplies the differential evidence.

The corpus census remains **4,810 clean / 17,172 partial / 66 include skips**;
`AssignmentExpression:target` remains **3,036 files**. Differential coverage
moves **117/113/0/4 → 118/114/0/4**; grammar coverage remains **214/83/131**.

## Literal `$assertcontrol` calls — 2026-10-24

A one-argument `$assertcontrol` call with an integral literal now lowers to an
inert statement because assertion reporting controls are outside the
self-check state. Dynamic, multi-argument, and assertion-observable forms
remain loud. `assertcontrol_literal` supplies the differential evidence.

The corpus census remains **4,810 clean / 17,172 partial / 66 include skips**
with unchanged blocker counts. Differential coverage moves **118/114/0/4 →
119/115/0/4**; grammar coverage remains **214/83/131**.

## Literal `$assertcontrol` argument lists — 2026-10-24

`$assertcontrol` with one or more integral literal arguments now lowers to an
inert statement because assertion reporting controls are outside the
self-check state. Dynamic or hierarchical arguments remain loud.
`assertcontrol_literal_args` supplies the differential evidence.

The corpus census remains **4,810 clean / 17,172 partial / 66 include skips**
with unchanged blocker counts. Differential coverage moves **119/115/0/4 →
120/116/0/4**; grammar coverage remains **214/83/131**.

## Empty 2-state queue initializers — 2026-10-24

An empty queue initializer (`{}` or `'{}'`) on a 2-state queue is now omitted as
inert declaration metadata. Nonempty or effectful initializers and queue
operations remain loud because the flat self-check state has no queue object.
The `empty_queue_decl` fixture covers both empty initializer spellings. The
fresh chapter-scoped census moves **4,810 → 4,816 clean** and **17,172 →
17,166 partial** (66 include skips); `VariableSymbol:2state` falls **2,351 →
2,350**. Differential coverage moves **120/116/0/4 → 121/117/0/4**, and
grammar coverage remains **214/83/131**.

## Constant out-of-bounds writes to fixed-size dynamic arrays — 2026-10-24

The extractor now lowers a constant out-of-range write after one constant
`new[N]` allocation of an integral 2-state dynamic array to a no-op. The
dynamic-array cells are already flat, and IEEE 1800-2023 §7.4.5 specifies that
the invalid write performs no update. Dynamic indices, resizes, aggregate or
effectful values, and reads remain loud. The corpus has no exact instance of
this shape: **4,816 clean / 17,166 partial / 66 include skips** and
`AssignmentExpression:target` at **3,035 files** are unchanged. Differential
coverage moves **121/117/0/4 → 122/118/0/4**; grammar coverage remains
**214/83/131**.

## Dynamic-to-fixed size-mismatch assignments — 2026-10-24

IEEE 1800-2023 §7.6 requires a run-time error, with no copy, when a sampled
dynamic array is assigned to a fixed-size unpacked array of a different
length. The exact blocking form now lowers to an immediate `$finish` in the
self-check surface, preserving the observable halt without fabricating a
diagnostic channel or aggregate storage. Equal-size copies, nonblocking/timed
forms, effectful sources, and other dynamic-array operations remain loud.
`dynamic_fixed_size_mismatch` supplies the `BEFORE` transcript.

The fresh chapter-scoped census moves **4,841 → 4,842 clean** and **17,142 →
17,141 partial** (66 include skips); `AssignmentExpression:target` falls
**2,980 → 2,979**. Differential coverage moves **141/137/0/4 → 142/138/0/4**;
grammar coverage remains **214/83/131**.

## Literal `$sformat` writes to packed integrals — 2026-10-24

IEEE 1800-2023 §§5.9 and 21.3.3 assign a plain literal `$sformat` result to
the output integral in packed-byte order: right aligned, left padded, or
truncated. The exact two-argument form now lowers to an ordinary blocking
assignment; formatted, dynamic, selected, effectful, and string-output forms
remain loud. `sformat_literal_integral` supplies the `PASS` transcript.

The fresh chapter-scoped census moves **4,842 → 4,843 clean** and **17,141 →
17,140 partial** (66 include skips); `ExpressionStatement:CallExpression`
falls **2,984 → 2,983**. Differential coverage moves **142/138/0/4 →
143/139/0/4**; grammar coverage remains **214/83/131**.

## Source-pure real and time arguments in severity tasks — 2026-10-24

The quiet severity tasks now erase literal-format calls whose arguments are
source-pure integral reads, literal strings, real/shortreal reads or literals,
or zero-time `$time` / `$realtime` queries. The diagnostic stream and floating
storage remain outside the self-check state; function calls, mutable or
unsupported values, and nonliteral formats stay loud. `severity_opaque_args`
supplies the `PASS` transcript and the real/time argument witness.

The fresh chapter-scoped census moves **4,841 → 4,842 clean** and **17,141 →
17,140 partial** (66 include skips); `ExpressionStatement:CallExpression`
falls **2,983 → 2,982**. Differential coverage moves **143/139/0/4 →
144/140/0/4**; grammar coverage remains **214/83/131**.

## Constant formatted writes to packed selections — 2026-10-24

The exact constant `$sformat`/`$swrite` form now lowers to a blocking write
for integral packed variables and fixed packed selections. Literal formats and
literal integral/string arguments are rendered into the existing byte-aligned
bit vector; dynamic, unsupported, string-storage, aggregate, and effectful
forms stay loud. `sformat_constant_selected` supplies the `PASS` transcript.

The fresh chapter-scoped census remains **4,843 clean / 17,139 partial** (66
include skips); `ExpressionStatement:CallExpression` falls **2,982 → 2,981**.
Differential coverage moves **144/140/0/4 → 145/141/0/4**; grammar coverage
remains **214/83/131**.

## Literal fixed-array `reverse()` — 2026-10-24

IEEE 1800-2023 §7.12.2 reverses an unpacked array in place. Fixed unpacked
integral leaves are already represented as independent flat cells, so a
one-dimensional fixed array with a complete scalar literal initializer now
lowers `reverse()` to blocking writes of those cells in reverse order. Dynamic
arrays, queues, multidimensional arrays, nonliteral initializers, later writes,
and other array methods remain loud. The `array_reverse` fixture supplies the
`PASS` transcript and the extractor tests pin the refusal boundaries.

The fresh **22,049-path** census measures **4,846 clean / 17,137 partial** (66
include skips). Relative to the committed 22,048-path snapshot, the external
corpus gained one path; the call-statement wall falls **2,981 → 2,980**.
Differential coverage moves **145/141/0/4 → 146/142/0/4**; grammar coverage
remains **214/83/131**.

## Queue initialization status results — 2026-10-24

IEEE 1800-2023 §20.15.6 defines scalar status results for queue initialization.
With no other queue task in the source, a four-argument `$q_initialize` with
literal type and capacity now lowers to a blocking status write: valid FIFO or
LIFO creation reports 0, an unsupported type reports 4, and a nonpositive
capacity reports 5. Queue storage, duplicate IDs, and all subsequent queue
operations remain loud. The `q_initialize_status` fixture supplies the `PASS`
transcript and extractor tests pin the status and refusal boundaries.

The fresh **22,049-path** census moves **4,846 → 4,852 clean** and **17,137 →
17,131 partial** (66 include skips); `ExpressionStatement:CallExpression`
falls **2,980 → 2,974**, making `AssignmentExpression:target` the leading
blocker at **2,979**. Differential coverage moves **146/142/0/4 → 147/143/0/4**;
grammar coverage remains **214/83/131**.

## Explicit-slice right-streaming targets — 2026-10-24

IEEE 1800-2023 §11.4.14.3 permits a right-streaming concatenation with an
explicit integral slice type or size to unpack one sampled vector into equal
width scalar or fixed-cell targets. The extractor resolves numeric slices and
the built-in `byte`/`shortint`/`int`/`longint` spellings, then reuses the
existing `ConcatTarget` write path. `with` clauses, mixed-width leaves,
dynamic or nested targets, and non-integral slice types remain loud.
`streaming_slice_target` supplies the `PASS` differential witness.

The fresh **22,049-path** census remains **4,852 clean / 17,131 partial** (66
include skips); `AssignmentExpression:target` falls **2,979 → 2,978** as the
new lowering removes one target wall in the chapter snapshot. Differential
coverage moves **147/143/0/4 → 148/144/0/4**; grammar coverage remains
**214/83/131**.

## Named-type left-streaming targets — 2026-10-24

IEEE 1800-2023 §11.4.14.3 also permits a left-streaming target to spell its
positive slice as a built-in integral type. The extractor resolves the named
width and reuses the existing low-chunk-first `ConcatTarget` lowering for
equal-width scalar or fixed-cell leaves. Unsized streams, mixed-width leaves,
`with` clauses, and dynamic or nested targets remain loud.
`streaming_left_slice_target` supplies the `PASS` differential witness.

The fresh **22,049-path** census remains **4,852 clean / 17,131 partial** (66
include skips) with `AssignmentExpression:target` at **2,978**. Differential
coverage moves **148/144/0/4 → 149/145/0/4**; grammar coverage remains
**214/83/131**.

## Shallow unpacked-union member targets — 2026-10-24

Equal-width integral members of an untagged unpacked union now alias one flat
vector cell, so direct member reads and blocking writes use the existing
assignment target and expression paths. Tagged, unequal-width, mixed-state,
nested, whole-union, and scheduled forms remain loud. `unpacked_union_member`
is the differential witness.

The fresh **22,049-path** census moves **4,852 → 4,853 clean** and
**17,131 → 17,130 partial** (66 include skips); `AssignmentExpression:target`
falls **2,978 → 2,977**. Differential coverage moves **149/145/0/4 →
150/146/0/4**; grammar coverage remains **214/83/131**.

## Shallow unpacked-union whole copies — 2026-10-24

Blocking whole-value assignments between equal-width integral members of the
admitted shallow untagged unpacked-union shape now copy the shared flat vector
cell. `unpacked_union_copy` is the differential witness; tagged, mixed-width,
initialized, member-to-whole, nonblocking, and timed forms remain loud.

The fresh **22,049-path** census moves **4,853 → 4,855 clean** and
**17,130 → 17,128 partial** (66 include skips); `AssignmentExpression:target`
falls **2,977 → 2,975**. Differential coverage moves **150/146/0/4 →
151/147/0/4**; grammar coverage remains **214/83/131**.

## Shallow unpacked-union whole-value comparisons — 2026-10-24

Whole values of the admitted shallow untagged unpacked-union shape now read
from their shared flat cell for `==`, `!=`, `===`, and `!==`. The
`unpacked_union_equality` witness compares values written through alternate
members; union arithmetic and other aggregate operations remain loud.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **151/147/0/4 → 152/148/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union conditional values — 2026-10-25

A conditional expression between two equal-width integral values of the
admitted shallow untagged unpacked-union shape now selects their shared flat
cells through the ordinary `Ternary` path. Mixed shapes, aggregate arms,
union arithmetic, and scheduled forms remain loud.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **152/148/0/4 → 153/149/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union compound member updates — 2026-10-25

A blocking compound assignment through a direct member of the admitted shallow
untagged unpacked-union shape now performs its read-modify-write on the shared
flat cell. Nonblocking, timed, mixed-shape, and unsupported compound operators
remain loud.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial**
(66 include skips), with `AssignmentExpression:target` at **2,975**.
Differential coverage moves **153/149/0/4 → 154/150/0/4**; grammar coverage
remains **214/83/131**.

## Shallow unpacked-union case subjects — 2026-10-25

An ordinary `case` subject may now read a direct equal-width integral member of
the admitted shallow untagged unpacked-union shape. The subject reuses the
shared flat cell and the existing case lowering, so a write through one member
selects a matching item named through another. Tagged, unequal-width, nested,
effectful, and scheduled subjects remain loud. The
`unpacked_union_case_member` fixture supplies the differential witness.

The fresh **22,049-path** census remains **4,855 clean / 17,128 partial** (66
include skips), with `AssignmentExpression:target` at **2,975**. Differential
coverage moves **154/150/0/4 → 155/151/0/4**; grammar coverage remains
**214/83/131**.

## Zero-key semaphore `try_get` — 2026-10-25

IEEE 1800-2023 §15.3.4 defines `semaphore.try_get(0)` as an immediate
successful attempt returning a positive value; it consumes no keys. The
self-check surface represents that positive result as scalar `1` when the
receiver has a preceding literal `new(...)` constructor and the count is
exactly zero. Dynamic counts, unproven receivers, and nonzero or otherwise
stateful semaphore operations remain loud. The `semaphore_zero_try_get`
fixture supplies the differential witness.

The fresh **22,049-path** census moves **4,855 → 4,856 clean** and **17,128 →
17,127 partial** (66 include skips); `CallExpression` falls **2,973 → 2,972**
while `AssignmentExpression:target` remains **2,975**. Differential coverage
moves **155/151/0/4 → 156/152/0/4**; grammar coverage remains **214/83/131**.

## Empty mailbox `num()` queries — 2026-10-25

An untouched mailbox created by literal `new()` now answers `num()` with the
exact scalar value zero. The receiver must have a constructor witness and no
later mailbox operation; method calls that could observe queued messages remain
loud. The generic empty-function shortcut no longer fabricates a result for
mailbox `num()` calls, closing that wrong-answer path. The `mailbox_empty_num`
fixture supplies the differential witness.

The fresh **22,049-path** census remains **4,856 clean / 17,127 partial** (66
include skips). `CallExpression` is **3,026**, up from **2,972**, because
previously fabricated mailbox-method values are now explicit refusals;
`AssignmentExpression:target` remains **2,975**. Differential coverage moves
**156/152/0/4 → 157/153/0/4**; grammar coverage remains **214/83/131**.

## Literal unbounded mailbox puts and counts — 2026-10-25

An unbounded mailbox created by literal `new()` now admits source-pure literal
`put` calls and an exact `num()` count for the same direct handle. Aliases,
bounded constructors, other methods, dynamic arguments, and calls before
construction remain loud. The `mailbox_literal_put_num` fixture supplies the
differential witness while the flat self-check store retains no mailbox object.

The fresh **22,049-path** census remains **4,856 clean / 17,127 partial** (66
include skips), with `CallExpression` at **3,026** and
`AssignmentExpression:target` at **2,975**. Differential coverage moves
**157/153/0/4 → 158/154/0/4**; grammar coverage remains **214/83/131**.

## Literal string length after assignments — 2026-10-25

String `.len()` queries now follow source-pure literal assignment history and
use the most recent literal value for the receiver. Dynamic writes, aliases,
non-ASCII values, and other string operations remain loud. The
`string_len_assignment` fixture supplies the differential witness.

The fresh **22,049-path** census moves **4,856 → 4,865 clean** and **17,127 →
17,118 partial** (66 include skips); `CallExpression` falls **3,026 → 3,017**
while `AssignmentExpression:target` remains **2,975**. Differential coverage
moves **158/154/0/4 → 159/155/0/4**; grammar coverage remains **214/83/131**.

## Literal string `atoi()` conversions — 2026-10-25

String `.atoi()` calls now scan the latest source-pure ASCII literal value for
leading decimal digits and underscores, stop at the first other character, and
produce the exact signed 32-bit result. Dynamic writes, signs, base prefixes,
overflow, non-ASCII values, and other string methods remain loud. The
`string_atoi_literal` fixture supplies the differential witness.

The corpus snapshot now has **22,050 paths** after an upstream fixture update;
relative to the previous **22,049-path** measurement, this item moves clean
files **4,856 → 4,875** and partial files **17,127 → 17,109** (66 include
skips), with `CallExpression` falling **3,017 → 3,007**. Differential coverage
moves **159/155/0/4 → 160/156/0/4**; grammar coverage remains **214/83/131**.

## Literal string `compare()` and `icompare()` — 2026-10-25

Source-pure ASCII string comparisons now return normalized `-1`, `0`, or `1`
ordering results; `icompare()` folds ASCII case first. Dynamic writes,
non-ASCII values, unsupported methods, and other effects remain loud. The
`string_compare_literal` fixture supplies the differential witness.

The 22,050-path census moves **4,875 → 4,888 clean** and **17,109 → 17,096
partial** (66 include skips); `CallExpression` falls **3,007 → 2,994** while
`AssignmentExpression:target` remains **2,975**. Differential coverage moves
**160/156/0/4 → 161/157/0/4**; grammar coverage remains **214/83/131**.
## Literal semaphore `try_get` state sequences — 2026-10-25

IEEE 1800-2023 §15.3.4 makes `try_get` nonblocking: a literal request no
larger than the available count consumes those keys and returns a positive
integer; an excessive request returns zero and leaves the count unchanged.
The self-check tier represents the positive result as `1` and tracks the
remaining count only for a direct literal semaphore constructor followed by
literal `try_get` calls. Dynamic, negative, aliased, reassigned, and mixed
semaphore operations remain loud. The `semaphore_literal_try_get` fixture
and differential row exercise the admitted sequence.

The fresh 22,050-path census moves 4,888 → 4,901 clean and 17,096 → 17,083
partial (66 include skips); `CallExpression` falls 2,994 → 2,982 and
`ExpressionStatement:CallExpression` falls 2,974 → 2,973. The differential
table moves 161/157/0/4 → 162/158/0/4, with grammar coverage unchanged at
214/83/131.

## Literal dynamic-array `size()` after allocation — 2026-10-25

After a positive literal `new[N]` allocation, IEEE 1800-2023 dynamic-array
`size()` returns the sampled extent. The self-check tier admits this exact
scalar query while retaining loud boundaries for resize, delete, aliases,
dynamic bounds, and other methods. The `dynamic_array_literal_size` fixture
and differential row exercise the admitted form.

The fresh 22,050-path census moves 4,901 → 4,906 clean and 17,083 → 17,078
partial (66 include skips). `CallExpression` falls 2,982 → 2,965; the
differential table moves 162/158/0/4 → 163/159/0/4, with grammar coverage
unchanged at 214/83/131.
## Literal string radix conversions — 2026-10-25

Source-pure literal strings now convert through `atobin()`, `atooct()`, and
`atohex()` into exact 32-bit values. The admitted conversion preserves
SystemVerilog four-state `x`, `z`, and `?` radix digits; dynamic strings,
invalid digits, and other string methods remain loud. The
`string_radix_literal` fixture exercises all three methods.

The fresh 22,050-path census moves 4,906 → 4,910 clean and 17,078 → 17,074
partial (66 include skips); `CallExpression` falls 2,965 → 2,958. The
differential table moves 163/159/0/4 → 164/160/0/4, with grammar coverage
unchanged at 214/83/131.
## Default-zero literal semaphore `try_get` — 2026-10-25

The default `semaphore new()` constructor creates zero available keys. The
self-check tier now admits a direct literal `try_get(k)` after that
constructor and returns exact scalar zero, while preserving loud boundaries
for aliases, dynamic counts, reassignment, and other semaphore methods. The
`semaphore_default_try_get` fixture exercises the form.

The fresh 22,050-path census moves 4,910 → 4,912 clean and 17,074 → 17,072
partial (66 include skips); `CallExpression` falls 2,958 → 2,956. The
differential table moves 164/160/0/4 → 165/161/0/4, with grammar coverage
unchanged at 214/83/131.
## Empty mailbox `try_get` and `try_peek` — 2026-10-25

The self-check tier admits immediate zero results for `try_get(output)` and
`try_peek(output)` on a direct empty unbounded mailbox. Other mailbox methods,
aliases, bounded or nonempty states, and dynamic forms remain loud. The
`mailbox_empty_try` fixture exercises both nonblocking methods.

The fresh 22,050-path census moves 4,912 → 4,917 clean and 17,072 → 17,067
partial (66 include skips); `CallExpression` falls 2,956 → 2,951. The
differential table moves 165/161/0/4 → 166/162/0/4, with grammar coverage
unchanged at 214/83/131.
## Untriggered and null event status — 2026-10-25

The self-check tier admits `event.triggered()` as exact one-bit zero for an
uninitialized event or an event explicitly assigned `null`, provided no event
trigger or other event operation occurs. Triggering, waiting, aliases, and
dynamic event state remain loud. The `event_triggered_false` fixture exercises
both cases.

The fresh 22,050-path census moves 4,917 → 4,921 clean and 17,067 → 17,063
partial (66 include skips); `CallExpression` falls 2,951 → 2,947. The
differential table moves 166/162/0/4 → 167/163/0/4, with grammar coverage
unchanged at 214/83/131.

## Procedural fixed-array `reverse()` — 2026-10-25

A one-dimensional fixed unpacked integral array now admits `reverse()` after a
complete blocking assignment-pattern initialization, a copy from another finite
fixed array, and repeated calls in one linear process. The extractor replays
source-ordered cell writes and prior reversals while preserving four-state
values and independent copies. Branches, loops, direct element writes,
dynamic or multidimensional arrays, nonliteral aggregate values, and other
array methods remain loud. The `array_reverse_procedural` fixture supplies the
`PASS` differential row and Lean receipt; extractor tests cover the refusal
boundaries.

The fresh 22,053-path census remains **4,979 clean / 17,007 partial** (67
include skips), with `ExpressionStatement:CallExpression` at **2,942**. The
corpus clean count is unchanged because the main external witness still has
unsupported `sort()` calls; differential coverage moves **186/181/0/5 →
187/182/0/5**, and grammar coverage remains **214/86/128**.

## Literal scalar mailbox FIFO `put()`/`get()` — 2026-10-25

A direct unbounded mailbox with a linear sequence of literal integral `put()`
calls now lowers FIFO scalar `get()` calls to blocking assignments, and `num()`
remains exact after the queue is consumed. Bounded or aliased handles, dynamic
messages, empty or width-mismatched gets, branching or looped sequences, and
other methods remain loud. The `mailbox_literal_fifo` fixture supplies the
`PASS` row and Lean receipt; extractor tests cover the refusal boundaries.

The fresh 22,053-path census moves **4,979 → 4,990 clean** and **17,007 →
16,996 partial** (67 include skips). `ExpressionStatement:CallExpression`
falls **2,942 → 2,926**; `AssignmentExpression:target` is now the leading
blocker at **2,940**. Differential coverage moves **187/182/0/5 → 188/183/0/5**,
and grammar coverage remains **214/86/128**.

## String `getc()` after a literal assignment — 2026-10-25

`string.getc(index)` now replays a direct blocking ASCII literal assignment
before the query and selects the latest assigned value. Negative and
out-of-range indices return the IEEE-mandated zero byte; dynamic strings,
aliases, non-ASCII writes, nonliteral indices, and other string operations
remain loud. The `string_getc_assignment` fixture supplies the differential
row and Lean receipt, while extractor regressions cover the latest-value and
dynamic-write boundaries.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,024 → 5,031** and partial files **16,962 → 16,955** (67 include skips).
`CallExpression` falls **2,866 → 2,859** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **201/196/0/5 → 202/197/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## String literal queries across comments and escaped line continuations — 2026-10-25

The source-order history shared by literal string queries now scans a masked
code view: comments and quoted-string contents are blanked while offsets stay
stable. This keeps prose mentions of a receiver from becoming false runtime
uses and admits the standard combination of `.len()` and `.getc(index)` on a
proven ASCII literal, including a `\n` escape followed by a consumed
backslash-newline continuation. Dynamic writes, aliases, non-ASCII values,
unsupported methods, and other nonliteral observations remain loud. The
`string_query_lexing` fixture and extractor regressions cover the masking and
the exact six-character escaped value.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,031 → 5,057** and partial files **16,955 → 16,929** (67 include skips).
`CallExpression` falls **2,859 → 2,833** while `AssignmentExpression:target`
remains **2,937** and `ExpressionStatement:CallExpression` remains **2,911**.
Differential coverage grows **202/197/0/5 → 203/198/0/5** with no
disagreements; grammar coverage remains **216/89/127**.

## Empty queue pops into integral unpacked structs — 2026-10-25

An empty queue pop now lowers the default of an untagged unpacked struct with
only scalar or packed integral leaves into the existing flattened field cells.
The `queue_empty_pop_struct_default` fixture supplies the self-check and Lean
receipt; queue mutation, aliases, nonempty queues, aggregate fields, and
scheduled forms remain outside the admitted representation.

On the refreshed **22,053-path** sv-tests-2 snapshot, clean files move
**5,057 → 5,058** and partial files **16,929 → 16,928** (67 include skips).
`AssignmentExpression:target` falls **2,937 → 2,936** while
`ExpressionStatement:CallExpression` remains **2,911**. Differential coverage
grows **203/198/0/5 → 204/199/0/5** with no disagreements; grammar coverage
remains **216/89/127**.

## Module-scope unbounded mailbox initializers — 2026-10-25

An unbounded `mailbox mbx = new()` declaration at module scope is retained as
metadata and then consumed by the existing literal FIFO operation lowering.
Bounded constructors, aliases, dynamic messages, blocking or scheduled calls,
and other initialized class handles remain loud. The `mailbox_module_init`
fixture supplies the self-check and Lean receipt.

On the refreshed **22,054-path** sv-tests-2 snapshot, clean files move
**5,058 → 5,059** and partial files remain **16,928** (67 include skips).
`VariableSymbol:2state` falls **2,313 → 2,302** while
`AssignmentExpression:target` is **2,937**. Differential coverage grows
**204/199/0/5 → 205/200/0/5** with no disagreements; grammar coverage remains
**216/89/127**.

## Literal-bound real-to-bits conversions — 2026-10-26

The extractor now lowers `$realtobits` and `$shortrealtobits` when a named
real value is proven from a finite literal initializer or earlier direct
blocking assignment. Dynamic and control-dependent real storage remains loud;
the corpus and differential deltas are recorded below.

On the refreshed **22,056-path** sv-tests-2 snapshot, clean files move
**5,200 → 5,207** and partial files **16,789 → 16,782** (67 include skips).
`CallExpression` falls **2,796 → 2,780**. Differential coverage grows
**231/226/0/5 → 232/227/0/5** with no disagreements; grammar coverage remains
**217/90/127**.

## Whole fixed-array copies from wire arrays — 2026-10-26

Equal-length finite unpacked integral wire-array sources now lower to
cellwise blocking assignments. Dynamic or mismatched arrays and aggregate
forms remain loud. The refreshed **22,056-path** census moves **5,207 → 5,209
clean** and **16,782 → 16,780 partial** (67 include skips); the
`AssignmentExpression:target` blocker falls **2,861 → 2,860**. Differential
coverage grows **238/233/0/5 → 239/234/0/5** with no disagreements; grammar
coverage remains **217/90/127**.

## Literal queue to fixed-array copies — 2026-10-27

A blocking assignment from an exact scalar-literal queue to a same-count
fixed unpacked integral array now expands queue elements into the destination
cells in left-to-right order. Size mismatches, later queue uses, aliases,
aggregate elements, timed forms, and nonblocking assignments remain loud.
The `queue_fixed_array_copy` fixture supplies the differential row and Lean
receipt.

On the refreshed **22,059-path** census, clean files move **5,303 → 5,304**
and partial files **16,689 → 16,688** (67 include skips). The
`AssignmentExpression:target` blocker falls **2,845 → 2,844**. Differential
coverage moves **317/311/0/6 → 318/312/0/6** with no disagreements; grammar
coverage remains **218/97/121**.
