# Python binary64 floats and true division

Implementation tracking: issue #10. Float literals, addition, subtraction,
multiplication, `float(...)` and integer/bool, float and mixed true division connect
to the same kernel-reducible binary64 core on both interpreter surfaces.
The `float_lab` real extracted artifact has kernel proofs, differential rows
and script transcripts. This is not complete float-language support:
remaining operators, constructor protocols, NaN payload propagation,
hashing and identity are still language-coverage work.

## Representation and specification

`LeanModels.Python.Float64` stores a 64-bit word, not Lean's native `Float`.
Classification, exact rational decoding, nearest-even rational rounding and
decimal rendering use kernel-reducible integer operations. The source oracle
is CPython 3.9 on the binary64 platforms used by the regression suite.

Rounding keeps the sign separate from the nonnegative numerator and positive
denominator. It selects the binary scale from the exact ratio, clamps the
smallest unit to 2^-1074, rounds the significand to nearest with even ties, and
handles carry into the next exponent. This preserves negative zero at zero
and underflow, and distinguishes the largest finite value from overflow.

Integer true division rounds the ratio directly. It must not first convert
both operands to floats: `10**400 / 10**400` is 1.0 in CPython even though
converting either operand alone overflows. `Float64.divideInt` distinguishes
division by zero from a ratio whose rounded result overflows. Interpreter
adapters must retain their distinct Python exception classes and messages.

Mixed integer/float division is different: CPython first converts the integer,
then divides the two floats. `10**400 / 0.0` therefore raises the conversion
`OverflowError`, not `ZeroDivisionError`. The core provides conversion plus
float division separately, and retains that evaluation order. A
finite float quotient can overflow to infinity without raising the integer
division overflow exception. A nonzero finite denominator and infinite
numerator produce signed infinity; a finite numerator and infinite denominator
produce signed zero. Both signs use the operands' sign XOR, including signed
zero and subnormal inputs. A zero denominator raises `ZeroDivisionError` even
when the numerator is infinite or NaN. Mixed integer conversion still happens
first, including overflow with an infinite or NaN operand. NaN inputs and
infinity divided by infinity return an unresolved NaN-payload marker, after
these exception checks. The adapter must refuse that marker loudly, never
invent a Python exception or a portable NaN word. The legacy
`Float64.divideFinite` helper name is retained; its shared dispatch now also
admits the determined infinity cases without a second interpreter path.

Addition, subtraction and multiplication compute with exact rational operands
and round once to nearest-even binary64. Mixed integer/Boolean operands are
converted to binary64 first, including their conversion overflow; consequently
`9007199254740993 + 1.0` is 9007199254740992.0 and `10**400 * 0.0` raises
`OverflowError` rather than returning zero. Cancellation returns positive
zero, except that the IEEE same-sign zero rules preserve negative zero in
`-0.0 + -0.0` and `-0.0 - 0.0`. Multiplication preserves the sign XOR through
zero and underflow. Float overflow produces signed infinity. Nonindeterminate
infinity operations are admitted, while NaN inputs and indeterminate infinity
operations refuse rather than invent a platform-dependent payload/sign word.
That refusal records unfinished oracle/model work, not a scope exclusion.

Float ordering and mixed float/integer comparison use the exact decoded value.
They do not round the integer: 9007199254740992.0 is strictly less than
9007199254740993 even though converting that integer to binary64 loses the
distinction. Numerical NaN comparisons are false. Integer conversion truncates
toward zero, while exact-integral conversion is available for future dictionary
key normalization; neither conversion claims an answer for an infinity or NaN.

Decimal rendering computes the exact midpoints to the adjacent binary64
values, including the narrower lower interval at powers of two and the
virtual finite successor of the largest finite value. Endpoint inclusion
follows the significand's parity. It searches up to 17 significant digits,
chooses the closest admissible decimal with even ties, and selects fixed or
scientific notation from the resulting decimal exponent. Signed zero,
infinities and NaNs have separate representations.

The reference describes binary64 representation and shortest round-trip
display in the [CPython 3.9 floating-point tutorial](https://github.com/python/cpython/blob/v3.9.0/Doc/tutorial/floatingpoint.rst).
The implementation is checked against the actual pinned interpreter, not
just a reading of that explanation.

## Interpreter integration

The extractor records a float literal/default as an unsigned decimal binary64
word using `struct.pack`, without evaluating a program expression. Ingestion
validates `0 <= bits < 2^64`; boundary JSON uses
`{"t":"float","bits":"<unsigned decimal word>"}` and rejects an invalid
word rather than truncating it. `Const.float`, `Val.float` and `RVal.float`
preserve the word through reflection, thaw/freeze and heap-boundary proofs.
The typed proof surface supplies `PyFloat` (definitionally `Float64`) and exact
`ToVal` marshalling, so artifact theorem statements need not expose `Val`.

Both interpreters share the numeric adapters in `Semantics.lean`. Truthiness,
unary signs, `abs`, `int`, scalar/container rendering, bare `%s`/`%r`/finite
`%d`, f-string conversions and exact mixed comparisons are wired. `int(nan)`
and `int(inf)` retain their distinct exception classes/messages. Integer true
division and float division have distinct zero-division messages, and the
`ArithmeticError` handler relation covers both plus `OverflowError`.

Finite numeric `sorted`/`max`/`min` use the shared exact order. NaN comparisons
with `<`/`<=`/`>`/`>=` are false, but ordering NaNs inside containers refuses:
the insertion-sort implementation cannot claim CPython's results for a
non-total order. NaN equality and float dictionary/set keys (including nested
tuple keys) also refuse. Existing float attributes remain loud rather than
fabricating missing-attribute exceptions. Other float arithmetic must not fall
into an integer-only `TypeError`.

The `itertools.count` frame currently supports integer stepping. Valid float
starts/steps therefore refuse at admission rather than fabricating the
nonnumeric `TypeError`. Boolean starts with a non-unit step also refuse:
CPython preserves the initial Boolean in that case, unlike its unit-step
integer path. Invalid nonnumeric arguments and excessive positional arity
retain their faithful exceptions. These counter-frame limitations remain
unfinished work, not scope exclusions.

The new value forms add scalar proof cases without changing existing theorem
statements. `float_lab` proves concrete results against its extracted Python
file by kernel reduction, including augmented assignment and mixed rounding.
It also proves cancellation for every finite binary64 input via the shared
arithmetic lemma. This does not claim general symbolic float automation;
the global walker has no numeric-literal shortcuts.

NaN introduces an additional object-identity issue: its numerical comparison
is false, but container element comparison can shortcut on object identity.
An immediate value representation must not fabricate the answer when that
identity is unavailable. Dictionary key normalization also must preserve the
equality of finite floats with equal integers and signed zeros. These cases
remain in scope; refusing an unresolved case is not an exclusion or a reason
to weaken an existing theorem.

Broader float arithmetic, remaining constructor protocols, formatting specifications, methods,
hashing and identity remain language-coverage work. Undefined or
platform-dependent numerical details require an explicit model/oracle
parameter when they cannot be decided from the admitted state.

## Constructor contract

`float()` returns positive zero. One positional argument preserves an existing
binary64 word, converts an integer or Boolean with nearest-even rounding (and
the integer-conversion overflow exception), or parses a decimal string.
Decimal strings admit signs, a decimal point, signed exponents and underscores
strictly between digits. Unicode decimal digits and surrounding whitespace
use the pinned CPython 3.9 Unicode 13.0.0 inventory; ASCII control characters
are not broadened to Unicode `isspace`. `inf` and `infinity` are case-insensitive.
Decimal overflow produces signed infinity, underflow produces signed zero,
and finite results use the same exact rational rounding as arithmetic.

Malformed strings raise the repr-rendered `ValueError` when the shared
string renderer can decide its message exactly. Quote selection traverses
the structural code-point list, keeping error rendering kernel-reducible.
Unresolved Unicode repr,
textual NaN payloads, bytes-like inputs and object conversion protocols remain
explicit unfinished work. Existing NaN words are preserved without selecting
a new payload. Positional arity and immediate nonnumeric type errors retain
CPython's exception classes and messages; keyword construction stays loud
until its evaluation and positional-only protocol are modeled.

## Core validation

`lake build LeanModels.Python.Float64Tests` checks closed kernel proofs for
rounding, signed zero, subnormal ties, numerical equality, conversions,
division, arithmetic and decimal parsing. The closed numeric-arithmetic
checks have empty axiom reports; native execution is not a proof tactic.
Text parsing, the general finite-cancellation lemma and artifact proofs use
only Lean's standard `propext`, `Classical.choice` and `Quot.sound`, not native
computation or new axioms.

`python3.9 harness/float64_test.py` compares the core against CPython's bit
patterns, `repr`, integer and float division, addition/subtraction/
multiplication, unary negation, mixed comparisons, conversions and exception
messages in a single Lean
process. Decimal parsing tests also compare the complete Unicode decimal-zero
inventory against the pinned `unicodedata`, every decimal digit block,
Unicode whitespace, malformed syntax, extreme exponents and rounding ties.
It covers every finite exponent field at selected fraction
boundaries, both signs, arbitrary-size integer ratios, subnormal and overflow
ties, non-finite bit patterns and deterministic random samples. This is a
numeric-core test, not the language-level differential harness. NaN-payload
refusals are counted separately from successful numerical matches.
