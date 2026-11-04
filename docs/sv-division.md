# Integral division

This extends the integral operator contract with `/` and plain scalar
`/=` (IEEE 1800-2023, 11.4.3, 11.8.2 and 10.4.1). It uses the existing
evaluation and assignment executors, without adding a scheduling rule.

## Value rule

Unsigned known operands produce their natural-number quotient. Signed
known operands produce their quotient truncated toward zero, represented
at the common width; the minimum signed value divided by minus one wraps
at that width. Any x/z bit in either operand makes every result bit x.
A known zero divisor also produces all x, including zero divided by zero.
Two-state destinations apply the existing unknown-to-zero conversion.

## Sizing and signedness

The frontend elaborates both operands at a common width before division.
The enclosing destination may widen that width; narrower destinations
truncate afterward. The signed operator applies only when both elaborated
operands are signed. Mixed-sign operands use unsigned division, including
a signed left operand divided by an unsigned right operand.

The envelope retains this distinction as `Binary` operators `u/` and
`s/`. They lower to M0 `BinOp.div` and `BinOp.sdiv`, respectively, and are
shared by self-check execution and Design2. A plain scalar `/=` reads its
original target once through the existing compound-assignment lowering.
Selected compound targets remain loud.
The symbolic extractor retains its existing refusal of all compound
assignment statements; scalar `/=` admission is on the legacy path.

## Symbolic compilation

Constant-expression positions keep their existing `/` integer-elaboration
path. Runtime positions use the explicit vector-operator tags above;
their operands must not be folded as unbounded signed integers. This
distinction matters for unsigned interpretation of negative bit patterns.
Older untyped `/` nodes do not gain runtime admission: without operand
signedness, a failed integer fold still refuses instead of guessing an
unsigned quotient.
Both symbolic instantiation paths preserve common/context operand sizing.
Runtime operand conversions remain structural, even when their default
elaboration is constant. This is necessary because signed negation and
unsigned division do not commute with changing the vector width.
Comparisons, logical operands and ternary conditions retain their own
self-determined widths; the enclosing division's context widens only their
results, not their internal arithmetic.
Legacy product-containing compilation backstops remain unchanged, and
admitted division adds its own invalid-compilation backstop at both
extraction modes.

Real arithmetic, remainder and expression-valued or selected compound
assignments remain outside this extension.

`Examples/system-verilog/division/proof.lean` proves unsigned and signed
width-parametric `BitVec` bridges against extracted divider modules, with a
nonzero-divisor hypothesis because SystemVerilog's zero case is four-state.
Two extracted context families, defaulted to widths 8 and 16, check both
widening and shrinking the parameters, including negation, signed constants,
equality, signed order, logical operations and ternary conditions. Four
self-check fixtures exercise ordinary execution and unknown results.
An additional extracted family checks concatenation, replication, reduction
and signed/unsigned cast boundaries at widths 4, 8 and 16.
The symbolic tiers retain their existing signed-declaration and
two-state-squash boundaries. The signed bridge consumes the extracted
expression, not a successful whole-module symbolic instantiation. M0
retains its selected-expression and unsigned-narrowing boundaries.
