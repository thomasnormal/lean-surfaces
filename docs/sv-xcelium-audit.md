# Xcelium audit of the ls-sv differential corpus

Status: measured, 2026-10-29. Reference: Xcelium `xrun(64) 24.03-s004` (the line
`refsim -version` prints on vip-ng is `TOOL: xrun(64) 24.03-s004`), pinned in
`harness/sv/xcelium_golden.json`; procedure and rule in
[sv-xcelium-reference.md](sv-xcelium-reference.md). Under the 2026-10-29 rule
(Xcelium is the reference; when it differs the model is suspect; Icarus, Verilator
and mox are witnesses) every difference below is an open question about the MODEL.
This page finds and classifies. It does not fix the model and it takes no position
on what IEEE 1800 requires.

Reproduce every number here without Xcelium:

```
python3 harness/sv/xcelium_batch.py prepare --workdir W [--lean-wrapper CMD]   # model traces, once
python3 harness/sv/xcelium_compare.py --workdir W --json out.json --markdown out.md
python3 harness/sv/test_xcelium_compare.py                                      # offline unit tests
```

`xcelium_compare.py` reads the model traces from `W/prep/`, the Xcelium traces from the
golden file (a row whose content hash no longer matches is reported stale and gets no
verdict) and runs Icarus 12.0 locally. It needs `iverilog`, nothing else.

## 1. Totals

| accounting | rows |
|---|---|
| rows in `harness/sv/cases2.json` | 626 |
| loud-refusal rows (no simulator runs; not compared here) | 198 |
| simulated rows | **428** |
| simulated rows run on Xcelium | 428 (all `ok`) |
| Xcelium failures: compile error / runtime error / timeout / not pinned / stale pin | 0 / 0 / 0 / 0 / 0 |
| Icarus 12.0 (fresh local run): trace obtained | 404 |
| Icarus 12.0: no trace (14 compile failures, 10 run failures) | 24 = the 23 `icarus_unavailable` rows + `t2_ci` (`xrun_only`) |

Class of each simulated row (model vs Xcelium first, then Icarus):

| class | rows |
|---|---|
| model == Xcelium, Icarus agrees | 352 |
| model == Xcelium, Icarus differs, declared (`oracle_disagreement`) | 16 |
| model == Xcelium, Icarus differs, undeclared | 0 |
| model == Xcelium, no Icarus trace | 24 |
| **model != Xcelium, Icarus == model** (Xcelium departs from both) | **31** |
| **model != Xcelium, Icarus == Xcelium** (the model departs from both) | **2** |
| **model != Xcelium, three-way split** | **3** |
| model != Xcelium, no Icarus trace | 0 |
| Xcelium could not run the row | 0 |

The three pairwise relations side by side (428 rows):

| model vs Xcelium | model vs Icarus | Xcelium vs Icarus | rows |
|---|---|---|---|
| equal | equal | equal | 352 |
| equal | differ | differ | 16 |
| equal | no trace | no trace | 24 |
| differ | equal | differ | 31 |
| differ | differ | equal | 2 |
| differ | differ | differ | 3 |

The equivalences, applied and reported separately (never merged):

| layer | rows |
|---|---|
| equal, **exact** (the trace lines of the row's first accepted schedule are identical to the pinned Xcelium trace) | 392 |
| equal **only up to the accepted schedules** (identical to a later schedule of `accept_sigmas`, not the first) | 0 (no row of `cases2.json` sets `accept_sigmas`, so the layer is empty by construction) |
| equal **only up to x-versus-known in cycle 0** (the traces differ in cycle 0 alone and there only where one side has x/z and the other a known bit) | 0 |
| differ | 36 |
| &nbsp;&nbsp;of which differ in cycle 0 alone | 0 |
| &nbsp;&nbsp;of which differ in two or more cycles (persist after time zero) | 36 |
| &nbsp;&nbsp;of which differ only where one side is x/z (no known-value disagreement) | 30 |
| &nbsp;&nbsp;&nbsp;&nbsp;Xcelium x/z where the model has a known bit (Xcelium more pessimistic) | 19 |
| &nbsp;&nbsp;&nbsp;&nbsp;the model x/z where Xcelium has a known bit (the model more pessimistic) | 1 (`fold_pcase_wide`) |
| &nbsp;&nbsp;&nbsp;&nbsp;x versus z (a z read through an in-range bit; Xcelium shows x) mixed with the above | 10 |
| &nbsp;&nbsp;of which differ in a known value | 6 (the overhanging writes, cluster P3) |

The time-zero class is EMPTY. `diff_test2` drives the inputs at time 0 and samples at the
first negedge (time 2), so cycle 0 is not a time-zero sample, and no row differs in cycle 0
alone. All 36 differing rows differ in cycle 0 AND in at least one later cycle (in 33 of
them in every cycle), so none of them is an artefact of a scheduling race at the start. The
only recorded cycle-0 ordering split between Icarus and Xcelium in the corpus is the nine
`rbw_*` refusal rows (their `measured` text: "at cycle 0 the two simulators order the
block's time-zero run against the first stimulus differently"); they run no simulator in
this harness and are outside the 428.

Agreement count asked for: **392 of 428 simulated rows have model == Xcelium** (exact); of
those **352 also have Icarus equal**, 16 are declared Icarus departures, 24 have no Icarus
trace. **0 rows pass only up to an equivalence** (schedule or time-zero x-versus-known).

## 2. Clusters

A differing row is attributed cell by cell: every differing (cycle, signal) is routed by
(DUT file, signal) to the construct that produces it (`SIGNAL_CAUSES` in
`harness/sv/xcelium_compare.py`, written by reading the DUTs); a cell no entry claims is
reported UNCLUSTERED, and there is none. A row with several causes is a member of several
clusters, so the cluster sizes add up to more than 36 rows. "First difference" is the first
differing signal of the first differing cycle: stimulus, model, Xcelium, Icarus.

| cluster | kind | rows | cause | first difference |
|---|---|---|---|---|
| P1 | model_ne_xcelium | 30 | partly out-of-range part-select READ, constant base | `partsel` cycle 0, `ov_hi`: `a=101101110001` (N=4, W=3, `ov_hi = a[10 +: 4]`); model `xx10`, Xcelium `xxxx`, Icarus `xx10` |
| P2 | model_ne_xcelium | 6 | partly out-of-range part-select READ, run-time base | `dyn32` cycle 2, `d32 = v[b32 -: 4]`: `v=10110111`, `b32=...1001` (9); model `xx10`, Xcelium `xxxx`, Icarus `xx10` |
| P3 | model_ne_xcelium | 6 | partly out-of-range part-select WRITE (procedural) | `partsel` cycle 0, `w_hi`: `b=1011` (`w_hi[7 +: 4] = b`); model `10000000`, Xcelium `00000000`, Icarus `10000000` |
| H1 | model_ne_xcelium | 3 | narrower plain-signal actual into a wider input port | `hier_width` cycle 0, `in_narrow`: `s=00` into the 6-bit port of `u4`; model `111111`, Xcelium `xxxx11`, Icarus `111111` |
| T1 | declared_departure_contradicted | 1 | run-time bit-select index wider than 32 bits | `fold_pcase_wide` cycle 0, `o3 = v[a - P]`: `a` = 42 ones, `v=10110101`; model `x`, Xcelium `1`, Icarus `1` |
| DX1 | declared_departure_contradicted | 3 | declared Icarus departure, Xcelium equals neither Icarus nor the model | `array_oob_part` cycle 0, `d_hi`: `src=10110110`; model `xx0`, Xcelium `xxx`, Icarus `110` |
| DX2 | declared_departure_contradicted | 1 | declared Icarus departure, Xcelium equals Icarus, but only through P1 | `array_param_labels_l7` cycle 0, `w`: `x=10110100`, `u=1`; model `x1`, Xcelium `xx`, Icarus `xx` |
| D1 | icarus_ne_xcelium_model_agrees_xcelium | 11 | Icarus reads untouched bits of a partly driven variable as z | `bit_select_assign` cycle 0, `value`: `source=0000`; model `x0xxxx0x`, Xcelium `x0xxxx0x`, Icarus `z0zzzz0z` |
| D2 | icarus_ne_xcelium_model_agrees_xcelium | 1 | Icarus linearizes an out-of-range INNER packed-array index | `array_oob_inner` cycle 0, `w_flat`: `a=0110`; model `00000000`, Xcelium `00000000`, Icarus `00100000` |
| D3 | icarus_ne_xcelium_model_agrees_xcelium | 1 | Icarus pads a nested unbased-unsized fill in a port actual | `hier_fill_ctx` cycle 0, `xor1`: `a=00,b=00,s=0`; model `1111`, Xcelium `1111`, Icarus `0011` |
| D4 | icarus_ne_xcelium_model_agrees_xcelium | 3 | Icarus `always_comb` is not re-run after a copy/port/bit-split update (LRM-permitted split) | `acg_alias_assign` cycle 1, `y`: `a=10`; model `10`, Xcelium `10`, Icarus `11` |
| U1 | other | 24 | rows Icarus 12 cannot simulate, simulated by Xcelium | `packed_member_indexed` cycle 0, `out`: `low=01,high=10`; model `1001`, Xcelium `1001`, Icarus: compile failure (`elab_net.cc:668` assertion) |

The 36 differing rows are the union of the clusters P1 (30 rows), P2 (the five `partsel*` rows
are already in P1; `dyn32` is the sixth and is in no other), P3 (five of its six rows are already in
P1; `array_oob_lsbwrite` is in no other), H1 (3) and T1 (1): 30 + 1 + 1 + 3 + 1 = 36. DX1 and DX2
are views on rows that are already in P1 or P3 (or both); D1 to D4 and U1 hold rows on which the
model equals Xcelium. There are no rows of kind `xcelium_error_or_time_zero_race`: Xcelium
accepted and finished every row, and the time-zero class is empty (section 1).

### P1. Partly out-of-range part-select read, constant base (30 rows)

Rows: `array_oob`, `array_oob_part`, `partsel`, `partsel_n2_w5`, `partsel_n6_w2`,
`partsel_n5_w1`, `partsel_n1_w4`, `const_wrap`, `const_wrap_k1_u15`, `const_wrap_k6_u8`,
`const_wrap_k7_u0`, `param_types`, `param_types_p5`, `param_types_p0_v3`, `param_types_v25`,
`param_types_signed`, `param_types_s4n`, `param_types_u32`, `param_types_u32_3`,
`array_param_labels_l7`, `label_n0_n2`, `label_param_n4_p3`, `label_param_n6_p5`,
`bits_labels_n9`, `label_kminus_w4`, `label_kminus_w3`, `label_kminus_w1`, `label_kminus_w0`,
`label_kminus_wm1`, `label_kminus_w5`.

The model (and Icarus) return the in-range bits of a select that overhangs the vector and x
only for the out-of-range ones; Xcelium returns **all x for the whole select**. The select
forms are `[b +: w]`, `[b -: w]` and `[msb:lsb]`, over ascending, descending and single-element
ranges, with labels built from parameters, `$bits`, narrow wrapped arithmetic and `localparam`
chains. Measured: 286 differing cells, **286 of 286 have an all-x Xcelium value**; Icarus equals
the model on 27 of the 30 rows (the other three are declared rows, DX1 and DX2). All 30 rows
carry Xcelium's own warning `BNDWRN` (bit-select or part-select index out of declared bounds).

Where it does NOT differ (14 other rows carry `BNDWRN` and match): `array_oob_inner`,
`const_wrap_k4_u3`, `ctx_width_8`, `ctx_width_n2_8`, `fold_vsel_n1`, `label_k0_n2`..`n5`,
`label_n0_n0`, `label_n0_n1`, `label_n0_nm1`, `label_param_n0_p1`, `label_param_n4_p0`. Each was
read: they contain only single-bit selects, part-selects that lie wholly outside the vector
(all x in both), writes of a single out-of-range bit (dropped in both), or a partly
out-of-range select whose x collapses an arithmetic result to all x in the model too
(`ctx_width_8`'s `v[1 +: 8] + 4'd9`). So the 14 are not counterexamples: in the whole corpus
there is no row where Xcelium returns in-range bits of a partly out-of-range part-select. The
rule that fits all 44 rows is "a part-select with at least one in-range and at least one
out-of-range bit reads all x"; it is a fit to this corpus, not a tested universal.

### P2. Partly out-of-range part-select read, run-time base (6 rows)

Rows: `partsel`, `partsel_n2_w5`, `partsel_n6_w2`, `partsel_n5_w1`, `partsel_n1_w4`
(`dyn_up = v[sel +: 4]`, `dyn_dn = v[sel -: 4]`), `dyn32` (`v[s - 2 +: 4]`, `v[b32 -: 4]`, ...).

The same all-x result for a signal-valued base: 52 differing cells, **52 of 52 all-x** in
Xcelium. `dyn32` raises no Xcelium warning at all, so `BNDWRN` is not a complete predictor.
Cycle 2 of `dyn32` is the clean case (a positive base of 9, no sign question): model `xx10`,
Xcelium `xxxx`. Open point the traces cannot settle: for the 32-bit unsigned bases
(`s - 2` at `s = 0..1`, `b32 = 0xFFFFFFFE`) an unsigned reading makes the whole select
out of range, which is also all x; the model, Icarus and Yosys read a 32-bit index as
two's complement. No `dyn32` cell separates "Xcelium reads the base as unsigned" from P2.

### P3. Partly out-of-range part-select write (6 rows)

Rows: `partsel`, `partsel_n2_w5`, `partsel_n5_w1`, `array_oob`, `array_oob_part`,
`array_oob_lsbwrite`.

A procedural write whose target overhangs the vector (msb or lsb end; `[b +: w]`, `[b -: w]`
and `[msb:lsb]` forms; a 1-D vector or an inner packed dimension): the model writes the
in-range bits, Xcelium **drops the whole write**. Measured cell by cell: in `partsel`,
`partsel_n2_w5`, `partsel_n5_w1`, `array_oob_part` and `array_oob_lsbwrite` the overhung
target holds its baseline (`'0` or `8'h00`) in every cycle of Xcelium's trace; in `array_oob`
`m_flat` equals "`m[1][3:2]` never written" in all four cycles (`a=0110`: `00010110`, model
`01010110`). In the same DUTs the targets that do NOT overhang (`partsel_n6_w2.w_lo`,
`partsel_n1_w4.w_hi`) are written normally in Xcelium, so it is the partial overhang, not
the select form. Icarus equals the model on the 1-D rows and on `array_oob`; on the inner
dimension of `array_oob_part` and `array_oob_lsbwrite` it linearizes (declared, see section 3)
and Xcelium agrees with neither. All 6 rows carry `BNDWRN`.

### H1. Narrower plain-signal actual into a wider input port (3 rows)

Rows: `hier_width`, `hier_width_n2`, `hier_width_n6`: `hw_pass #(.W(N+2)) u4 (.i(s), .o(in_narrow))`
with a 2-bit `s`, so `in_narrow = ~i`. The model zero-extends the actual (a port connection is
a continuous assignment); in Xcelium the formal's high bits are unknown. All 42 differing cells
have the shape "the high N bits are x in Xcelium and the low two bits equal the model"
(42 of 42), in every cycle (14 of 14). All 3 rows carry `CUVMPW` ("port sizes differ in port
connection"). The outputs of the other four instances of the same DUT (`out_wide`, `out_narrow`, `in_wide`,
`in_safe`) match, and so do the 7 other rows that raise `CUVMPW` (`hier_fill`, `hier_fill_ctx`,
`hier_intact*`): their narrower actuals are expressions or constants, and Xcelium's result equals
the model's there.
What the pin cannot say: whether the high bits of the formal are z or x (the observed signal is
`~i`, which is x for both), and whether a narrower plain signal that is a variable or a
part-select behaves the same.

### T1. Run-time bit-select index wider than 32 bits (1 row)

`fold_pcase_wide` (`N=40`, `o3 = v[a - P]` over a 42-bit `a`, `P = -3`): the model reads the
42-bit index as out of range (`x`); Xcelium reads defined bits, equal to Icarus in all 3
differing cells (cycles 0, 1, 3: `1`, `1`, `0`), and prints its own `BIGWBS` ("bit-select
index truncation"). So Xcelium truncates the index to its low 32 bits, exactly as the
declaration says Icarus (and Verilator on a plain `v[a]`) do. The 5 other `BIGWBS` rows
match. Kind `declared_departure_contradicted`: this is the one declaration whose claim
about the LRM reading is not supported by the reference.

### DX1 and DX2. Declared rows whose trace fits neither side

* **DX1, Xcelium equals neither Icarus nor the model** (3 rows): `array_oob_part`,
  `array_oob_lsbwrite`, `label_kminus_w1`. The differences from the model are P1 (`d_hi`, `r_lo`,
  `r_hi`; `label_kminus_w1.p`) and P3 (`w_flat`, `v`). The Icarus-specific content of the three
  declarations is nevertheless NOT reproduced by Xcelium: where Icarus linearizes
  (`array_oob_part.d_hi` `110`, `w_flat` `00111100`; `array_oob_lsbwrite.w_flat` `00011000`)
  or reads the whole ascending vector (`label_kminus_w1.p` `10`, `01`, `11`, `0x`, `z0`),
  Xcelium shows `xxx`, `00000000`, `00000000` and `xx`. The verdict "CONTRADICTED" is
  therefore about the model's expected trace, not about Icarus's departure.
* **DX2, Xcelium equals Icarus through P1 only** (1 row): `array_param_labels_l7`
  (`w = u[L+1 -: 2]` over `[7:7]`): model `x1`/`x0`/`xz`, Icarus and Xcelium `xx` in all 3
  differing cells. The Xcelium trace is exactly the model trace with the partly
  out-of-range select forced to all x, so the row cannot tell "Xcelium reads `-:` as `+:`" from
  P1. Strictly the trace equals Icarus's, so the declaration is contradicted; whether the
  Icarus lowering it describes is corroborated is undecided by this pin.

### D1 to D4. Confirmed declared departures (16 rows, Icarus is the outlier)

* **D1** (11 rows): `bit_select_assign`, `noncanonical_bit_assign`, `packed_member_subrange`,
  `packed_member_bit`, `packed_union_subrange`, `packed_union_bit`, `nested_member_bit`,
  `nested_member_concat`, `typedef_nested_concat`, `fixed_array_noncanonical_slice`,
  `concat_undriven`. Icarus lowers a partly driven variable to a net and reads the untouched
  bits as z; the model and Xcelium keep the variable's initial x. All 11 declarations say "no
  licensed-simulator confirmation is claimed"; the pin now supplies it.
* **D2** `array_oob_inner`: Xcelium checks each packed dimension on its own, like the model
  (`w_flat = 00000000`, `z = x`); Icarus lands the write in `w[1][1]`. Carries `BNDWRN`.
* **D3** `hier_fill_ctx`: a fill nested under an operator in a port actual takes the port
  width in Xcelium and the model (`xor1 = 1111`); Icarus zero-pads (`0011`).
* **D4** `acg_alias_assign`, `acg_alias_port`, `acg_xproc_bits`: the three whose text already
  says "Xcelium 24.03 gives exactly the model's trace"; the golden confirms it on all 8, 8 and 7
  cycles. Icarus is stale from cycle 1.

### U1. Rows Icarus cannot simulate (24 rows)

The 23 rows declared `icarus_unavailable` (compiler assertion or vvp abort on packed-member,
noncanonical-slice, fixed-array stream and similar forms) plus the `xrun_only` row `t2_ci`
(`case ... inside`). All 24 run on Xcelium and equal the model, with no Xcelium warning. They
were unverifiable against Icarus; against Xcelium they now are verified.

## 3. Declarations

### 3.1 The 21 `oracle_disagreement` declarations

Verdict rule (the task's, applied to the pinned trace): CONFIRMED when Xcelium equals the
model's trace (Icarus is the outlier); CONTRADICTED when Xcelium equals the declaration's Icarus
trace, or equals neither. In addition the script checked that each declaration's recorded
`sim_trace` equals a fresh local Icarus run and its `lean_trace` equals the model trace: all 21
do. Of the 21 declarations 3 name Xcelium in their text (all confirmed) and 18 disclaim
licensed-simulator confirmation (13 now confirmed, 5 contradicted).

| row | declaration id | verdict | cluster | what Xcelium shows |
|---|---|---|---|---|
| `bit_select_assign` | iverilog-partial-variable-init | CONFIRMED | D1 | `x` kept |
| `noncanonical_bit_assign` | iverilog-noncanonical-variable-init | CONFIRMED | D1 | `x` kept |
| `packed_member_subrange` | iverilog-packed-member-subrange-init | CONFIRMED | D1 | `x` kept |
| `packed_member_bit` | iverilog-packed-member-bit-init | CONFIRMED | D1 | `x` kept |
| `packed_union_subrange` | iverilog-packed-union-subrange-init | CONFIRMED | D1 | `x` kept |
| `packed_union_bit` | iverilog-packed-union-bit-init | CONFIRMED | D1 | `x` kept |
| `nested_member_bit` | iverilog-nested-member-bit-init | CONFIRMED | D1 | `x` kept |
| `nested_member_concat` | iverilog-nested-member-concat-init | CONFIRMED | D1 | `x` kept |
| `typedef_nested_concat` | iverilog-typedef-nested-concat-init | CONFIRMED | D1 | `x` kept |
| `fixed_array_noncanonical_slice` | iverilog-fixed-array-noncanonical-slice-init | CONFIRMED | D1 | `x` kept |
| `concat_undriven` | iverilog-concat-target-undriven-init | CONFIRMED | D1 | `x` kept |
| `array_oob_inner` | iverilog-packed-inner-index-linearized | CONFIRMED | D2 | per-dimension, no landing |
| `hier_fill_ctx` | iverilog-port-fill-self-determined | CONFIRMED | D3 | context width |
| `acg_alias_assign` | iverilog-comb-assign-alias-sensitivity | CONFIRMED | D4 | settled value (text already claimed it) |
| `acg_alias_port` | iverilog-comb-port-loop-sensitivity | CONFIRMED | D4 | settled value (text already claimed it) |
| `acg_xproc_bits` | iverilog-comb-bit-split-sensitivity | CONFIRMED | D4 | settled value (text already claimed it) |
| `array_oob_part` | iverilog-packed-inner-part-linearized | **CONTRADICTED: Xcelium equals neither** | DX1 (+P1, P3) | `d_hi xxx`, `r_lo xxx`, `r_hi xx`, `w_flat 00000000`: no linearization, but not the model's `xx0`, `11x`, `x0`, `00001100` either |
| `array_oob_lsbwrite` | iverilog-packed-inner-lsb-write-linearized | **CONTRADICTED: neither** | DX1 (+P3) | `w_flat 00000000`, `v 00000000` (model `00010000`/`00000001`, Icarus `00011000`/`00000001`) |
| `label_kminus_w1` | iverilog-ascending-full-width-minus-select | **CONTRADICTED: neither** | DX1 (+P1) | `p = xx` in all 5 cycles (model `x1 x0 x1 x0 xz`, Icarus `10 01 11 0x z0`); `q` equal in all three |
| `array_param_labels_l7` | iverilog-single-element-minus-select | **CONTRADICTED: Xcelium equals Icarus** | DX2 (+P1) | `w = xx` (= Icarus), but also = the model forced to all-x |
| `fold_pcase_wide` | iverilog-wide-index-truncation | **CONTRADICTED: Xcelium equals Icarus** | T1 | `o3` read at the low 32 bits of the index (`BIGWBS`) |

### 3.2 The 23 `icarus_unavailable` declarations

All 23 rows run on Xcelium (status `ok`) and equal the model: 23 of 23 CONFIRMED (cluster U1).
Icarus 12.0 on this machine again fails on all 23 (and on `t2_ci`).

### 3.3 Statements in the tree that the pin contradicts

* `Examples/system-verilog/sem2/array_oob/array_oob.sv:5`: "so every simulator agrees here".
  Xcelium differs on this DUT: `m_flat` (the overhanging `m[1][5:2]` write is dropped, P3) and
  `over` (`m[1][5:2]` reads all x, P1).
* `Examples/system-verilog/sem2/array_oob_lsbwrite/array_oob_lsbwrite.sv:3-4`: "On a 1-D vector
  (v) every tool agrees (rows partsel*)". Xcelium drops the 1-D write (`v = 00000000`; model and
  Icarus `00000001`, `00000011`, ...) and differs on all five `partsel*` rows.
* `docs/sv-oracle-disagreements.md:166-173`: the 1-D write "agrees in every tool" and "Selects
  past the end of the LAST element agree in every tool ... (`array_oob` ...; 1-D overhangs on both
  ends and run-time bases, rows `partsel*`)". The paragraph ends "No licensed-simulator
  confirmation is claimed", so it is a claim about the tools then measured; against Xcelium it
  is false for exactly those rows.
* Statements that name their tools and stay true: `const_wrap.sv` ("Icarus 12.0 and Yosys 0.53
  agree on every value"), `param_types.sv`, `docs/sv-charter.md` ("Differential rows (Icarus
  12.0): `partsel` ... all match"). Xcelium differs on those rows too (P1, P2, P3).

## 4. Checks behind the numbers

* The set of 36 differing rows was computed four independent ways and is identical: this script,
  the infra stage's offline comparison of the stored traces, `diff_test2.py --golden` over the
  whole corpus (392 `XREF-MATCH`, 36 `XREF-DIFF`, 0 stale, 0 none) and the infra three-way script.
  The class counts (352 / 31 / 24 / 16 / 3 / 2) agree between this script and the infra
  three-way script.
* Model traces: `git status` shows no change under `LeanModels/` or to `harness/sv/runner2.lean`,
  the newest file named by `diff_test2.SV_LEAN_MODULES` predates the prepare run, and 18 rows (10 random with seed
  20261029, plus `partsel`, `dyn32`, `fold_pcase_wide`, `array_oob_lsbwrite`, `hier_width`,
  `label_kminus_w1`, `acg_alias_assign`, `t2_ci`) were re-run through the Lean runner: 18 of 18
  reproduce.
* Pin freshness: all 428 pinned hashes equal the hash of the current DUT, testbench and
  parameters. The infra stage re-ran 20 rows on vip-ng: 20 of 20 identical traces.
* Cell-level evidence printed by the script (`EVIDENCE`): P1/P2 286/286 and 52/52 cells all-x;
  P3 targets constant at their baseline; H1 42/42 cells a leading x prefix; T1 3/3 cells equal
  Icarus.
* The testbench is `gen_tb2.py`'s, unchanged: inputs at 3k, clock pulse 3k+1 / 3k+2, sample at
  negedge. A difference can therefore come from the simulator or from the DUT under that
  schedule; none of the 36 depends on the schedule (they persist across cycles and the DUTs are
  combinational or settle within the cycle).

## 5. Limits and open items

* One Xcelium version (24.03-s004), one run per row. Whether P1 to P3, H1 and T1 are 24.03
  behaviour or Xcelium behaviour is not known. The docs elsewhere cite 26.09 on compute-0 for
  other rows; a second pin needs its own file (the tool refuses to mix versions).
* The 198 refusal rows were not compared. Fifteen of their `measured` texts say Xcelium rejects
  the fixture (`MULAXX`, `ICDDIV`); those statements are not re-checked here.
* P1 as a universal rule is a fit to 44 rows (30 differing, 14 matching), not a probe. Open
  probes the pin cannot replace: H1 with a narrower variable or part-select actual and with a z
  versus x observation; the dyn32 signed-versus-unsigned question; a `-:` select over a
  single-element range that is not partly out of range under either reading (to separate
  `array_param_labels_l7` from P1); continuous-assign part-select writes that overhang (the
  rows use procedural writes because Icarus aborts on the continuous form).
* Decisions for the lead, not taken here: per cluster whether the model follows Xcelium (the
  reference rule) or records a documented Xcelium-specific divergence; re-labelling the two
  DUT header comments and the paragraph in `docs/sv-oracle-disagreements.md`; adding DX1, DX2
  and T1 to that page's bookkeeping.
* Nothing in CI, the harness defaults or the svGolf checker uses Xcelium or this audit.
  `tools/ci.sh` runs `test_xcelium_golden.py` (6dcb5bff) but not `test_xcelium_compare.py`; a step
  `step  "xcelium-compare-tests" python3 harness/sv/test_xcelium_compare.py` next to it would add it.
