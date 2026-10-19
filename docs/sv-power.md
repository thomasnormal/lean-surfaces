# Integral power

IEEE 1800-2023 §11.4.3, Table 11-4 defines integral `**`.
The base takes the expression/assignment context width; the exponent is
self-determined in both width and signedness (§11.6 and §11.8.1–11.8.2).
Result width is the base width, never the maximum operand width.

For fully known nonnegative exponents the value is the power modulo the
result width. Zero exponents yield one, including `0 ** 0`. For negative
signed exponents, zero bases yield all x, bases one yield one, signed bases
minus one yield minus one for odd exponents and one for even exponents,
and every other base yields zero. Any x/z bit in either operand yields
an all-x result, including an unknown base raised to zero.

The runtime operators `u**u`, `u**s`, `s**u`, and `s**s` record base and
exponent signedness separately. They use the shared `LVec.pow` value rule
through the existing executors. Positive powers use structurally bounded
modular repeated squaring; they do not construct an enormous integer power.
The old `**` spelling remains constant-only integer elaboration and refuses
failed folds rather than guessing runtime types.

Real power and the existing whole-module signed declaration boundaries
remain loud. This family does not change scheduling or admission of
symbolic signed ports.

## Oracle record for zero-to-negative power

The three zero-base, negative-integral-exponent rows in
`harness/sv/power/zero_negative.sv` are a documented reference divergence,
not reference confirmations. IEEE 1800-2023 §11.4.3, Table 11-4 requires an
all-x result for integral `0 ** negative`; Icarus Verilog produces the same
all-x result. The separate reference run returns zero for these rows, so the
fixture deliberately checks the standard result and records the disagreement
instead of treating it as an oracle match. Reference cache
`c6e89990f6b74c057dad284b` (xrun 24.03-s004, 2026-10-12) records `FAIL` for
each of the three rows followed by `PASS`; the positive, zero-exponent and
nonzero-base rows remain subject to ordinary reference confirmation.
