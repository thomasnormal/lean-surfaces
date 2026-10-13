# Integral shifts

This item covers IEEE 1800-2023 §11.4.10 integral `<<`, `>>`, `<<<` and
`>>>` in the legacy/self-check and symbolic value paths. It adds no scheduler
rule: the existing expression evaluators and assignment machinery remain the
authority.

## Value rule

The right operand is self-determined and converted to an unsigned shift
amount. An x/z bit in that amount produces an all-x result. A shift amount at
least as large as the left operand width produces zeros for left and logical
right shifts; signed arithmetic right shift fills with the left operand's
sign bit, including x/z. Otherwise the left operand's four-state bits are
moved without collapsing unknown bits.

The result width is the left operand width. A destination context can widen
the left operand before the operation and narrows only after the operation.
The extractor records `u<<`/`s<<`, `u>>`/`s>>`, `u<<<`/`s<<<` and `u>>>`/`s>>>`.
The signedness tag is determined by the left operand, not by the shift amount.

## Evidence

`LVec.shl`, `LVec.shr`, `LVec.ashl` and `LVec.ashr` are shared by the M0
evaluator, self-check executor and both symbolic instantiation paths.
`Examples/system-verilog/shifts/proof.lean` anchors all four operators to the
generated envelope and proves the known-amount bit rules and unknown-amount
collapse without new axioms.

The focused extractor battery has 14 passing tests. The public self-check
fixture `harness/sv/shifts/shifts.sv` passes the independent simulator and
the Lean conformance runner, covering zero and oversized amounts, x/z amounts,
unknown data bits, signed sign fill, assignment widening, destination
narrowing, two-state conversion and scalar compound shifts. The paired corpus
census covers 21,952 files: clean extraction rises from 2,383 to 2,448
(65 gains, zero losses), and all 65 newly clean rows match both executable
paths used for the measurement.

Constant-position shifts retain the symbolic integer-elaboration path. Real,
selected-target and invalid-compilation boundaries remain loud.
