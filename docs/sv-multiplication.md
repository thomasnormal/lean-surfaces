# Integral multiplication

This extends the M0 operator contract with integral `*` and plain scalar
`*=` (IEEE 1800-2023, 11.4.3, 11.8.2 and 10.4.1). It adds no scheduling
rule: evaluation and assignment use the existing core executors.

## Value rule

For known operands at common width `w`, the result is their product modulo
`2^w`. If either operand contains any x/z bit, every result bit is x,
including when the other operand is zero. `LVec.mul` is the shared value
authority for M0, Design2 and self-check execution.

## Sizing and assignment

The extractor retains slang's elaborated operand conversions. A wider
assignment destination propagates its width into the product before
evaluation. A narrower destination truncates afterward, rather than
shrinking the operands first. Signed operands sign-extend in a signed
context; mixed-sign operands zero-extend. Two-state assignment destinations
apply the existing unknown-to-zero conversion after multiplication.

A plain scalar `target *= factor` lowers to the ordinary assignment of a
product that reads the original target once. Selected compound targets
remain loud; this extension does not admit division, remainder, power,
shifts, real arithmetic or expression-valued assignments.

## Symbolic compilation

Successful constant integer elaboration keeps its existing literal shape.
When constant elaboration fails on runtime operands, symbolic `*` lowers
to the runtime product at the maximum operand/context width. Design2's
existing `fitExpr2` supplies explicit operand resizes. Other operators
retain their prior refusal behavior. Frontend errors in a legacy module
containing admitted products add `Multiplication:invalid-compilation`.

## Evidence

Four public self-check fixtures under `harness/sv/multiplication` cover
modular overflow, wider destinations, precedence, signed and mixed-sign
contexts, x/z collapse, two-state conversion and compound assignment.
Each carries independently checked output provenance.

`Examples/system-verilog/multiplication/spec.lean` proves a width-parametric
modular-product theorem over the expression extracted from the real
parameterized `multiplier.sv`. Its proof also pins that expression to the
assignment in the real runtime fixture, checks both symbolic runtime
instantiation paths and preserves constant elaboration. The proof is
symbolic, not a finite enumeration of input values.
