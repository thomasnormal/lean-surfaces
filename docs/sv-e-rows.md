# E row baseline

This is the first frozen baseline for the exact-semantics E executor.  The
source is the committed `harness/sv/cases2.json` at the S0.e measurement.  Of
the 704 rows with simulator oracles, the 20 marked `verilator_only` are
two-state host-only rows and are reported outside this denominator.  The
remaining 684 row names, in cases-file order, have SHA-256
`a706825b8d8667675f6076fa4916d71d54b4041d6eaca53960a289c9cd25b4d1`.

The baseline used backend `e0`, the committed envelopes, Icarus Verilog 13.0
for ordinary rows, and Xcelium 24.03-s004 for the two `xrun_only` rows.  Each
row ran independently with a 120-second wall limit, eight workers, and no
multi-point cross-check.  The row's source and envelope were unchanged.

| outcome | rows | first examples or boundary |
| --- | ---: | --- |
| E-MATCH | 547 | `acg_alias_bits_ok`, `xnor_bin` |
| loud E refusal: edge/timed process outside E-core-0 | 57 | `alu_div_w32`, `always_ff_loop` |
| loud E refusal: generate guard is not an integer guard | 17 | `const_wrap_k0_u1`, `fold_lpshr` |
| loud E refusal: dynamic assignment target is not a static window | 8 | `acg_dyn_ok`, `proc_compound` |
| loud E refusal: retained `casez` is outside E-core-0 | 1 | `symbolic_casez_casex` |
| loud envelope refusal: old sv-0.1 envelope | 1 | `net_decl_driver` |
| declared simulator divergence | 16 | `acg_xproc_bits`, `array_oob_asc` |
| measured E/simulator divergence | 3 | `dyn32`, `fold_cgrow_n33` |
| simulator-side error, no E verdict | 18 | `nested_member_indexed`, `packed_member_indexed` |
| E-core-0 memory route not present | 9 | `async_mem_fifo`, `readmemh_rom_memory` |
| oracle unavailable | 5 | `fixed_array_stream_continuous`, `streaming_left_fixed` |
| per-row timeout | 2 | `proc_local`, `symbolic_parameter_for_large` |

Thus the initial migration number is **547 E-MATCH rows out of 684**.  The
three measured divergences and the 16 declared divergences remain separate
from E-MATCH; no row is silently counted as agreement.

The frozen S0 number above is historical.  The 2026-11-12 triage closed the
two `fold_cgrow` rows (`fold_cgrow_n33` and `fold_cgrow_n40`) by evaluating
typed generate guards at their own widths, so the current E count is
**549/684**.  `dyn32` now follows the unsigned 32-bit base rule and its only
remaining difference is the declared Xcelium partial-overhang behavior; it is
not counted as an E-MATCH.
