# Integral wildcard equality

IEEE 1800-2023 §11.4.6 and Table 11-10 define `==?` and `!=?`.
An x/z bit in the right operand matches any corresponding left bit.
At the remaining positions, a known mismatch makes equality false. If
there is no known mismatch, a cared left x/z makes the result unknown;
otherwise equality is true. Inequality is its three-valued complement.

Both operands receive the common equality width and their elaborated
signed or unsigned extension. The result is unsigned, one-bit and
self-determined. A surrounding assignment or arithmetic expression sizes
that result after the comparison, preserving the operands' own boundary.

`LVec.eqWildcard` and `LVec.neWildcard` provide one shared value rule.
Both envelope schemas, both symbolic compilers, M0, Design2 and the
self-check evaluator retain the operators. Their arithmetic-operand
walkers preserve the comparison boundary. The existing Boolean
`case inside` selector tests whether this same equality rule returns one.
This adds no scheduler rule. Nonintegral operands and unsupported value
or storage types keep their existing refusals. Integral membership
expressions require their own embedding and lowering and remain loud.

The real module in `Examples/system-verilog/wildcard_equality/` has
both assignments. Its proof file identifies their actual extracted AST,
checks symbolic instantiation independently of a wider result context,
and proves that an entirely wildcard right operand makes equality true
and inequality false for arbitrary left vectors at the same width.
Concrete checks cover both symbolic compilers' nested arithmetic paths.

## Oracle

The `wildcard-equality-values` group in `values.sv` derives its assertions
from §11.4.6 and is confirmed by the source observation recorded beside
that fixture. The source digest binds the file before its trailing
provenance comment; the executable statements are identical. No observed
values are rescaled or projected. Every assertion has an explicit expected
width, and the complete expected output is exactly `PASS`.

The fixture covers both operators on all 16 scalar pairs, asymmetric
right-hand wildcards, cared left x/z, a known mismatch beside an unknown,
unsigned result extension, signed and mixed-width operand extension,
65-bit vectors, and signed comparisons nested inside division.

The fresh paired census has 29 newly clean chapter-11 fixtures. All 29
execute through Lean's self-check evaluator; qualification compares their
complete output with independent runs of the same source files. Extraction
cleanliness and successful execution are separate measurements.
