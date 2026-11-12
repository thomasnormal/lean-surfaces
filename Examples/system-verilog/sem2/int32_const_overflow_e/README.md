# Exact-width `int` constant arithmetic

This clean-room fixture covers four independent IEEE 1800-2023 constant
expression cases: multiplication followed by division, a left shift followed
by a right shift, addition followed by remainder, and unary negation of the
most-negative signed value. The `int` expression width is 32 bits at every
intermediate node (§11.4, §11.6.1 and §11.8.1), including parameter `N` at
both the default point (`10000`) and an override (`8`).

Regenerate the envelope and run the receipt with:

```sh
python3 extractors/sv/extract.py --top int32_const_overflow_e \
  -o Examples/system-verilog/sem2/int32_const_overflow_e/int32_const_overflow_e.sv.json \
  Examples/system-verilog/sem2/int32_const_overflow_e/int32_const_overflow_e.sv
python3 Examples/system-verilog/sem2/int32_const_overflow_e/check.py
```

The receipt runs the Lean guards, Icarus Verilog 13.0 and the readiness-gated
Xcelium 24.03-s004. Negative shift amounts and right shift of a negative
constant remain loud follow-up cases. The comb tactic `/` and `%` readers
still need the same exact-width alignment; this item does not change those
proof-side readers.
