# SystemVerilog tier changelog

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
