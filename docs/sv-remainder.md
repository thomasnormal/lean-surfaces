# Integral remainder (IEEE 1800-2023 §§11.4.3, 11.8.2)

The surface admits runtime integral `%` in the legacy/self-check and symbolic
value paths. The extractor records `u%` when at least one operand is unsigned
and `s%` when both operands are signed. Constant-position `%` remains the
integer elaboration operator in `sv-0.2`.

Both operands are converted to the common arithmetic width before evaluation.
Unsigned remainder uses the natural-number remainder. Signed remainder is the
remainder paired with truncation-toward-zero division, so its sign follows the
dividend. A zero divisor, or any `x`/`z` bit in either operand, yields an
all-`x` vector. A destination conversion is applied only after the operation.
Scalar `%=` lowers to the same typed binary node and reads the original target.

The public value core is `LVec.rem`/`LVec.srem`; the evaluator and both
symbolic instantiators dispatch to those functions rather than maintaining a
second operator table. `Examples/system-verilog/remainder/proof.lean` proves
width-parametric unsigned and signed bridges for nonzero `BitVec` divisors.
`harness/sv/remainder/remainder.sv` is covered by the directed Icarus case
`remainder_directed`.

Real operands, selected compound targets, and unresolved frontend
compilations remain loud. Unknown and zero-divisor behavior is intentionally
checked as all-`x`, not approximated by a two-state result.
