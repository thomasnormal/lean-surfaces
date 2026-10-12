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
