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

The one-bit parameter point, `addsub_comb_n1`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 9 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The eight-bit parameter point, `addsub_comb_n8`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 14 cycles.  It is an E-MATCH and does not change the frozen migration
count.

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

The nested conditional/case slice, `acg_nested_ok`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 6 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The latch-read slice, `acg_latch_read`, runs from its committed source-shaped
envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for all 8
cycles.  It is an E-MATCH and does not change the frozen migration count.

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

The dynamic-index slice, `acg_dyn_ok`, reaches the same E admission boundary
and is recorded as a loud refusal with that exact message. Its source-shaped
legacy receipt matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for all 6
cycles; no E verdict is claimed and the row does not change the frozen count.

The bit-sensitivity row, `acg_xproc_bits`, runs in E for all 7 cycles.  Its
Xcelium 24.03-s004 trace agrees with E; Icarus Verilog 13.0 is the declared
`iverilog-comb-bit-split-sensitivity` disagreement described in
`docs/sv-oracle-disagreements.md`.  It is therefore recorded as a declared
simulator disagreement rather than an E-MATCH, and does not change the frozen
count.

The alias-safe bit slice, `acg_alias_bits_ok`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 8 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The overlapping bit-copy alias row, `acg_alias_bits`, is refused by E as
`AlwaysComb:alias-read`.  This preserves the source-shaped guard at the
bit-level alias boundary; no E verdict or migration-count change is claimed.

The E runner now applies the same source-shaped alias admission guard as the
ordinary loader.  `acg_alias_assign` is therefore a loud
`AlwaysComb:alias-read` refusal, matching the pinned legacy refusal and the
IEEE 1800-2023 §§4.7–4.8 boundary; it is not executed as an E result.

The transitive port-copy row, `acg_alias_port`, is likewise a loud
`AlwaysComb:alias-read` refusal from the E runner.  Its pinned legacy receipt
has the same refusal boundary, so no E verdict or migration-count change is
claimed.

The multi-assignment copy chain, `acg_alias_chain`, is also refused by E as
`AlwaysComb:alias-read`.  The refusal is source-shaped and agrees with the
legacy boundary; no E verdict or migration-count change is claimed.

The inverted-copy alias row, `acg_alias_not`, is likewise refused by E as
`AlwaysComb:alias-read`.  Its source-shaped guard result agrees with the
legacy boundary; no E verdict or migration-count change is claimed.

The net-copy alias row, `acg_alias_wire`, is refused by E as
`AlwaysComb:alias-read`; this preserves the same source-shaped refusal at the
wire boundary and adds no E verdict or migration-count change.

The hierarchical alias row, `acg_alias_hier`, is refused by E as
`AlwaysComb:alias-read` after flattening the source-shaped instance path.  It
matches the legacy refusal boundary and adds no E verdict or migration-count
change.

The child-port alias row, `acg_alias_thru`, is refused by E as
`AlwaysComb:alias-read` after the source-shaped port path is followed.  It
matches the legacy refusal boundary and adds no E verdict or migration-count
change.

The write-safe alias row, `acg_alias_wr`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 8 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The copy-safe alias row, `acg_alias_copy`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 8 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The far-copy alias row, `acg_alias_far`, runs from its committed source-shaped
envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for all 8
cycles.  It is an E-MATCH and does not change the frozen migration count.

The hierarchy-safe alias row, `acg_alias_hier_ok`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 8 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The port-write-safe alias row, `acg_alias_port_wr`, runs from its committed
source-shaped envelope and matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all 8 cycles.  It is an E-MATCH and does not change the frozen migration
count.

The receipts were produced with:

```text
python3 harness/sv/diff_test2.py --backend e0 --sim both --no-xcheck --case <row>
```

The next Step 4 slice is the remaining ordinary `always_comb` rows ranked by
their first missing E construct; self-read and latch behavior stay in the
explicit boundary list until the corresponding E refinement is written.

The mixed clocked/comb probe `t2_case` is outside E-core-0: its source-shaped
envelope contains an edge/timed process, so the E runner refuses before
execution.  The legacy route independently refuses its `unique` case as
`CaseCheck:unique`; no simulator result is claimed for this row.

The pure combinational probe `t2_ci` runs from its source-shaped envelope and
matches Xcelium 24.03-s004 for all 7 cycles.  It is marked Xcelium-only in the
corpus because Icarus cannot parse this source form; no Icarus result is
claimed.  This is an E-MATCH against the available pinned oracle and does not
change the frozen migration count.
