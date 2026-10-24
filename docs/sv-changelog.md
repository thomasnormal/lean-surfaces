# SystemVerilog tier changelog

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
