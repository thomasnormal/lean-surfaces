# Python binary64 floats and true division

Implementation tracking: issue #10. This work remains unfinished. The binary64
core is not yet connected to the Python AST or either interpreter; the current
coverage page still correctly records float constants and true division as
refused. A successful core test is not evidence that a Python program runs.

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
finite-operand division separately, and retains that evaluation order. A
finite float quotient can overflow to infinity without raising the integer
division overflow exception. Non-finite division currently returns a distinct
unmodelled-result marker, except when a zero denominator already decides the
faithful exception. That marker must become a loud interpreter refusal, never
a Python exception invented by the adapter.

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

## Integration requirements

The following are required before this item is complete:

- Extract float constants as their exact bit pattern without evaluating any
  program expression; validate the full bit width on ingestion.
- Add literal, runtime and boundary value forms, and a true-division operator,
  with coherent thaw/freeze, JSON transport and elaborator reflection.
- Connect both the executable and proof interpreters to the same numeric core.
- Implement truthiness, unary signs, rendering, mixed numeric comparisons and
  division error ordering; audit every fallback for fabricated exceptions.
- Keep currently unmodelled float operations loud. In particular, a known
  numeric operation must not fall into an integer-only `TypeError`, and an
  existing float attribute must not be reported as missing.
- Preserve the existing theorem statements, frame invariants, fuel monotonicity
  and clock-erasure results; add kernel proofs against an extracted Python file.
- Extend the existing differential and grammar corpora, classify remaining
  refusals, regenerate coverage, and pass the full repository landing gates.

NaN introduces an additional object-identity issue: its numerical comparison
is false, but container element comparison can shortcut on object identity.
An immediate value representation must not fabricate the answer when that
identity is unavailable. Dictionary key normalization also must preserve the
equality of finite floats with equal integers and signed zeros. These cases
remain in scope; refusing an unresolved case is not an exclusion or a reason
to weaken an existing theorem.

Broader float arithmetic, constructors, formatting specifications, methods,
hashing and identity remain language-coverage work. Undefined or
platform-dependent numerical details require an explicit model/oracle
parameter when they cannot be decided from the admitted state.

## Core validation

`lake build LeanModels.Python.Float64Tests` checks closed kernel proofs for
rounding, signed zero, subnormal ties, numerical equality, conversions and
division. General kernel proofs also establish non-NaN equality reflexivity
and that a zero denominator is the only reason rational rounding returns none.
The axioms reports must remain empty; native execution is not a proof tactic.

`python3.9 harness/float64_test.py` compares the core against CPython's bit
patterns, `repr`, integer and finite float division, mixed comparisons,
conversions and exception messages in a single Lean
process. It covers every finite exponent field at selected fraction
boundaries, both signs, arbitrary-size integer ratios, subnormal and overflow
ties, non-finite bit patterns and deterministic random samples. This is a
numeric-core test, not the language-level differential harness.
