# Call expressions — admitted boundary

Expression-position calls either compute a value or carry an effect through a
value context. The public tier admits only calls whose value and effects are
already represented by the scalar/packed evaluator, fixed metadata, or an
explicit time-zero rule. Everything else remains an `Unsupported` expression;
the statement-call contract is separate in [call statements](sv-call-statements.md).

## Admitted calls

Fixed `$bits`, `$high`, `$left`, `$right`, `$low`, `$increment`, `$size`,
`$dimensions`, and `$unpacked_dimensions` queries fold from elaborated type
metadata. Pure `$clog2` constants fold to the existing signed 32-bit literal;
runtime integral `$clog2` uses the shared expression evaluator. A zero-argument
`$time` in the time-zero self-check slice is the existing 64-bit zero literal
with time-zero provenance. A `$rtoi` with one finite real literal now lowers
to the signed 32-bit literal obtained by truncating toward zero; the same
conversion is inert when its result is discarded as a statement. Dynamic real
reads, out-of-range results, and other argument shapes remain loud. A direct
finite real literal passed to `$realtobits` lowers to its exact 64-bit IEEE-754
encoding; dynamic storage and explicit conversion shells remain loud. The
matching `$shortrealtobits` slice accepts only its implicit conversion shell
around a direct literal and lowers to the exact 32-bit IEEE-754 single pattern;
explicit casts and overflow remain loud. Dynamic integral `$cast` has its own
capture and copyback contract. These paths are not generic callable frames and
do not make arbitrary calls live.

## Refusal boundary

The residual expression calls need state or effects absent from that surface:

* `$random`, `$urandom`, `$urandom_range`, and the distribution calls mutate a
  seed and require an explicit random oracle;
* `$rose`, `$fell`, `$stable`, `$changed`, `$past`, and `$sampled` read sampled
  values and scheduler history;
* `std::randomize` and unqualified `randomize` need constraint solving and a
  random oracle;
* `$stime`, `$realtime`, `$timeunit`, and `$timeprecision` need an elapsed-time
  and unit environment beyond the time-zero `$time` rule;
* other real conversions, string formatting, file/system/coverage calls, and
  enum/array methods require unsupported value types or external state; and
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
