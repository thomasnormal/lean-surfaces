# E combinational row probe

This is the first S1 Step 4 probe after the frozen S0.e baseline.  It runs
the E-core-0 backend from the committed envelopes and compares both pinned
simulators, Icarus Verilog 13.0 and Xcelium 24.03-s004.  The probe is a small
representative slice; it does not change the frozen 547/684 migration number.

The three ordinary combinational rows all match both simulators:

| row | shape | cycles | result |
| --- | --- | ---: | --- |
| `xnor_n` | parameterized continuous combinational logic | 6 | E-MATCH |
| `fa_comb_proc` | `always_comb` full-adder process | 12 | E-MATCH |
| `addsub_comb` | parameterized add/subtract combinational process | 15 | E-MATCH |

The next source-shaped temporary-variable slice, `acg_temp_all`, also matches
Icarus Verilog 13.0 and Xcelium 24.03-s004 for all 6 cycles.  It is an
E-MATCH and does not change the frozen migration count.

The two-temporary slice, `acg_two_temps`, likewise runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 5 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The bit-granular temporary slice, `acg_bits_ok`, also runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 5 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The constant part-select slice, `acg_part_ok`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 4 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The source-shaped case slice, `acg_case_ok`, runs from its committed envelope
and matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for all 6 cycles.  It is
an E-MATCH and does not change the frozen migration count.

The conditional-expression slice, `acg_cond_ok`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 6 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The latch and self-read boundaries are explicit.  `latch_comb` also matches
both simulators in 8 cycles.  `rbw_comb` remains a loud
`AlwaysComb:self-read` refusal, so it has no E verdict and is not counted as a
match.  The next dynamic-index boundary, `t2_combw`, is a loud
`10.4.1: blocking assignment target is not a static in-range window` refusal;
the fresh Icarus Verilog 13.0 receipt is
`00001111,01001111,00001111,10100101,00000000,11111110`.  Xcelium was not
available in this run, so no Xcelium result is claimed for that refusal.  There
are no simulator disagreements in the admitted rows and no row flipped
relative to the frozen baseline.

The receipts were produced with:

```text
python3 harness/sv/diff_test2.py --backend e0 --sim both --no-xcheck --case <row>
```

The next Step 4 slice is the remaining ordinary `always_comb` rows ranked by
their first missing E construct; self-read and latch behavior stay in the
explicit boundary list until the corresponding E refinement is written.
