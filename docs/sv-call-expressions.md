# Call expressions — admitted boundary

Expression-position calls either compute a value or carry an effect through a
value context. The public tier admits only calls whose value and effects are
already represented by the scalar/packed evaluator, fixed metadata, or an
explicit time-zero rule. Everything else remains an `Unsupported` expression;
the statement-call contract is separate in [call statements](sv-call-statements.md).

## Admitted calls

### Literal integral character `$sformatf` — 2026-10-27

Literal one-integral-operand `$sformatf` now also admits `%c` and `%C`, using
the low byte as the ASCII character through the existing packed renderer.
Unknown bits, dynamic formats, string or aggregate operands, and other
conversion forms remain loud. The `sformatf_char` fixture checks the rendered
character in a `$display` argument.

Literal one-integral-operand `$sformatf` expressions now lower to an ASCII
packed value for `%b`, `%h`, `%o`, `%d`, and `%c`; `%B`, `%H`, `%O`, `%D`, and
`%C` are their uppercase aliases. The renderer retains four-state unknown summaries and
the operand's signedness for decimal output. Dynamic formats, multiple
arguments, unsupported conversions, aggregate or real operands, and dynamic
string storage remain loud.

Fixed `$bits`, `$high`, `$left`, `$right`, `$low`, `$increment`, `$size`,
`$dimensions`, and `$unpacked_dimensions` queries fold from elaborated type
metadata. `$bits(real)` and `$bits(shortreal)` now use the same metadata-only
path for their fixed 64- and 32-bit type widths; a named real value remains
loud. The fixed-width results of `$realtobits(real_value)` and
`$shortrealtobits(shortreal_value)` are also valid `$bits` operands, so nested
queries return 64 and 32 without reading opaque real storage. Pure `$clog2` constants fold to the existing signed 32-bit literal;
runtime integral `$clog2` uses the shared expression evaluator. A zero-argument
`$time` in the time-zero self-check slice is the existing 64-bit zero literal
with time-zero provenance. A `$rtoi` with one finite real literal now lowers
to the signed 32-bit literal obtained by truncating toward zero; the same
conversion is inert when its result is discarded as a statement. Dynamic real
reads, out-of-range results, and other argument shapes remain loud. A direct
finite real literal passed to `$realtobits` lowers to its exact 64-bit IEEE-754
encoding; an exact `$itor` conversion of one integral literal is admitted by
the same path, while dynamic storage and explicit conversion shells remain
loud. The
matching `$shortrealtobits` slice accepts only its implicit conversion shell
around a direct literal and lowers to the exact 32-bit IEEE-754 single pattern;
the same shell around an exact literal `$itor` result is admitted, while
explicit casts and overflow remain loud. Dynamic integral `$cast` has its own
capture and copyback contract. `$rtoi($itor(I))` also lowers when `I` is one
direct finite integral literal, because the integer-to-real conversion is exact;
a named or computed integer operand remains loud. These paths are not generic
callable frames and do not make arbitrary calls live. A scalar `.len()` query
on a string assigned a proven ASCII literal also folds, including a predefined
string macro whose AST value is a literal; dynamic assignments and other string
methods remain loud. Built-in dynamic-array `.size` accepts the IEEE 5.13
omission of empty parentheses when one constant `new[N]` allocation is already
sampled; later resizes and other array operations remain loud.
Enum `.name()` is also admitted as an exact declaration-spelling string value;
unknown enum values return the standard empty string. Enum traversal remains
integral, while string comparisons and dynamic string storage remain loud.

## Seeded bounded `$dist_uniform` scalar assignments — 2026-10-27

A direct blocking assignment from `$dist_uniform(seed, 0, 1000)` now updates
the 32-bit inout seed and the scalar 32-bit integral destination together.
The explicit recurrence makes equal seeds repeatable without introducing an
implicit random oracle. Direct variable seeds and literal bounds are required;
nonblocking or timed forms, other bounds, computed seeds, non-32-bit targets,
and value-position random calls remain loud. The `dist_uniform_scalar` fixture
and the four chapter-20 repeatability/range witnesses cover this slice.

## Nonnegative literal `$dist_uniform` scalar bounds — 2026-10-27

The scalar assignment slice now accepts any nonnegative literal start/end pair
within the signed 32-bit range, preserving the same inclusive scaling and
inout-seed update. Negative or computed bounds, nonblocking or timed forms,
non-32-bit targets, and value-position calls remain loud. The
`dist_uniform_literal_bounds` fixture covers the generalized range; ten more
chapter-20 `$dist_uniform` files become clean while the negative-range witness
stays outside this rung.

## Signed literal `$dist_uniform` scalar bounds — 2026-10-27

Direct scalar assignments now accept signed literal start/end pairs in the
32-bit integer range, including negative-only and zero-crossing ranges. The
seed recurrence is unchanged; the sampled integer is wrapped into a 32-bit
two's-complement vector so the existing signed evaluator sees the correct
value. Computed, reversed, or out-of-range bounds, nonblocking or timed forms,
non-32-bit targets, and value-position calls remain loud. The
`dist_uniform_signed_bounds` fixture checks both admitted ranges, and the two
chapter-20 negative-bound witnesses become clean.

## `$q_full` value calls after prior status checks — 2026-10-27

Value-position `$q_full` calls now remain admitted when a literal queue was
initialized and any status read occurred before the first query. The query
value follows the existing literal capacity/add history, and the status output
is left unobserved after that point. A later status read, symbolic queue ID,
payload observation, removal, or other queue operation remains loud. The
`q_full_value_history` fixture covers the empty and full results plus the
source-ordered initialization check; two chapter-20 value-query witnesses
become clean.

## Refusal boundary

The residual expression calls need state or effects absent from that surface:

* `$random`, `$urandom`, `$urandom_range`, and distribution calls outside the
  admitted seeded `$dist_uniform(seed, 0, 1000)` assignment slice mutate a
  seed and require an explicit random oracle;
* `$rose`, `$fell`, `$stable`, `$changed`, `$past`, and `$sampled` read sampled
  values and scheduler history;
* `std::randomize` and unqualified `randomize` need constraint solving and a
  random oracle;
* `$stime`, `$realtime`, `$timeunit`, and `$timeprecision` need an elapsed-time
  and unit environment beyond the time-zero `$time` rule;
* other real conversions, string formatting, file/system/coverage calls, and
  array methods require unsupported value types or external state; and
* user functions, scope calls, and receiver methods need callable frames,
  hierarchy, or object/aggregate storage.

No call is admitted by folding a random or sampled result to a constant, by
discarding a seed update, or by treating a method as a pure identifier. Those
shortcuts would fabricate values and make differential agreement meaningless.

## 2026-10-21 census and decision

The fresh 22,043-path census records `CallExpression` in **3,291** files:
**212** are call-only and **3,079** co-occur with another refusal. The
call-expression repricer finds **315** unsupported expression-call instances
in those 212 files. The largest heads are:

| source head | instances | files |
|---|---:|---:|
| `$random` | 30 | 22 |
| `$dist_uniform` | 23 | 17 |
| `$urandom` | 21 | 10 |
| `$stable` | 19 | 17 |
| `$rose` | 18 | 16 |
| `$changed` | 15 | 13 |
| `$past` | 15 | 13 |
| `std::randomize` | 15 | 12 |
| `$fell` | 13 | 12 |
| `$stime` | 13 | 9 |
| `$urandom_range` | 12 | 7 |
| `$dist_normal` | 11 | 6 |
| `$dist_t` | 11 | 6 |
| `$rtoi` | 11 | 6 |
| member method call | 11 | 10 |

The remaining 77 instances are a long tail of other distributions, sampled
queries, time/real conversions, file/system/coverage calls, and methods. The
literal `$rtoi` slice is now admitted: six corpus files that use one finite
literal conversion become clean, while dynamic and out-of-range calls remain
in the residual refusal set. Every remaining call-only head needs a random
oracle, scheduler history, time/unit state, external effect, unsupported value
type, or callable frame. Existing metadata-query, `$clog2`, `$time`, cast,
literal-`$rtoi`, literal-`$realtobits`, and literal-`$shortrealtobits` fixtures
pin the accepted boundary.

Reproduce the call-only table with
`python3.9 extractors/sv/call_expr_reprice.py --corpus <corpus>/tests`; the
tool reads sources in process and writes no envelopes beside the corpus.
