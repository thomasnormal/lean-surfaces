# Xcelium audit of the ls-sv differential corpus

Status: measured, 2026-10-29. Reference: Xcelium `xrun(64) 24.03-s004` (the line
`refsim -version` prints on vip-ng is `TOOL: xrun(64) 24.03-s004`), pinned in
`harness/sv/xcelium_golden.json`; procedure and rule in
[sv-xcelium-reference.md](sv-xcelium-reference.md). Under the 2026-10-29 rule
(Xcelium is the reference; when it differs the model is suspect; Icarus, Verilator
and mox are witnesses) every difference below is an open question about the MODEL.
Sections 1 to 5 find and classify, as measured on the pin before any change: the
numbers in them are the numbers of the corpus AS PINNED (428 simulated rows) and are
not updated. **Section 6 records what was decided and done about them in round 6
(2026-10-29)**, including the verified triage of every cluster (each cluster was
re-derived by an independent verifier on its own designs); where the verifiers
corrected a claim made in sections 1 to 5 the correction is stated in section 6.1 and
marked "(corrected in 6.1)" at the claim.

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
Xcelium `xxxx`. Open point the traces cannot settle (settled by a verifier probe, 6.1 item 5):
for the 32-bit unsigned bases (`s - 2` at `s = 0..1`, `b32 = 0xFFFFFFFE`) an unsigned reading
makes the whole select out of range, which is also all x; the model, Icarus and Yosys read a
32-bit index as two's complement. No `dyn32` cell separates "Xcelium reads the base as
unsigned" from P2.

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
  Icarus lowering it describes is corroborated is undecided by this pin. (Corrected in 6.1:
  the VALUE trace cannot decide it, but Xcelium's elaboration diagnostic can, and it
  corroborates the declaration; the "CONTRADICTED" label is a value-masking artefact.)

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
| `array_param_labels_l7` | iverilog-single-element-minus-select | **CONTRADICTED: Xcelium equals Icarus** (value-masked by P1; direction CORROBORATED by Xcelium's BNDIPERR text, 6.1) | DX2 (+P1) | `w = xx` (= Icarus), but also = the model forced to all-x |
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

Round 6 corrected the first three (the two DUT comments and the paragraph of
`docs/sv-oracle-disagreements.md`); see 6.3.

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
  and T1 to that page's bookkeeping. (All taken in round 6: section 6.2.)
* Nothing in CI, the harness defaults or the svGolf checker uses Xcelium or this audit.
  `tools/ci.sh` runs `test_xcelium_golden.py` and `test_xcelium_compare.py` (the latter step was
  added after this audit was written).

## 6. Round 6 (2026-10-29): what was decided and done

Every cluster above was re-derived by an independent verifier on its OWN designs and
testbenches (Xcelium 24.03-s004 through the refsim gate on vip-ng, one run at a time; Icarus
12.0, Verilator 5.042, Yosys 0.53 locally; the model through `runner2.lean`). The rule of the
round is refusal-only: a change may add a loud refusal or add or correct a declared departure or
a document; no shape that was loud becomes admitted and no value the model computes changes
except by becoming a refusal. The policy (Thomas): where the tools split, or where the model
would follow one oracle against the LRM, REFUSE LOUDLY; Xcelium is the reference for decisions
but is not infallible, so where it departs from the LRM text the model neither follows it nor
picks silently.

### 6.1 Findings of the verification (corrections to sections 1 to 5 marked "corrected in 6.1")

1. **P1, P2 and P3 are ONE Xcelium rule.** Xcelium 24.03-s004 treats a part-select that has at
   least one bit in range and at least one out of range as WHOLLY INVALID: a read returns all x
   (all 0 for a 2-state source), a write is a no-op on the whole select. The rule fits 1248 of
   1248 cells of a 13-point verifier design (`+:`, `-:`, `[msb:lsb]`, descending and ascending
   vectors, constant and run-time bases, continuous assign and `always_comb`, reductions, a
   `$bits`-wrapped base, writes), 864 of 864 run-time-base cells, and 254 of 254 rows of the DX1
   verifier design (input port, local variable, net, 2-state variable, run-time base, the inner
   dimension of a packed array, `always_comb` and non-blocking writes); no cell returns a different
   known bit. It is a deterministic rule, not a time-zero race (identical at +1 ns, +9 ns, after
   later stimulus changes and at +1001 ns; identical forward, reversed and permuted), and the
   audit's "a fit to 44 rows, not a tested universal" is replaced by this. The collapse is specific
   to PACKED bit-level part-selects: an unpacked-array slice `m[3+:2]` of `m[0:3]` keeps the in-range
   element (`BNDMEM`). The wholly-out-of-range select (x read, no-op write) and the single
   out-of-range bit agree in every tool and are not part of it.
2. **The LRM is not ambiguous here.** IEEE 1800-2023 11.5.1 (printed page 296): "A part-select that
   addresses a range of bits that are completely out of the address bounds of the vector, packed
   array, packed structure, parameter or concatenation, or a part-select that is x or z shall yield
   the value x when read and shall have no effect on the data stored when written. Part-selects
   that are partially out of range shall, when read, return x for the bits that are out of range and
   shall, when written, only affect the bits that are in range." The model, Icarus, Yosys (on known
   bits) and slang follow it; Verilator (2-state) is an incoherent witness and Xcelium departs from
   it. The triage label "lrm_ambiguous_tools_split" was the nearest enum value and is wrong in its
   literal meaning; the accurate class is "the reference departs from an explicit LRM sentence".
3. **Consumers turn the all-x into defined values.** With `a = ...101101` and a parameter base `B = 10`,
   `if (|a[B+:4])` takes the other branch in Xcelium, `$countones(a[B+:4])` is 0 instead of 2,
   `case (a[B+:4]) 4'bxx11` does not match, and `(a[B+:4] === 4'bxx11)` is false. So the difference
   is not confined to the select: a silent wrong value in control flow is real, which is why the
   constant-base cases are REFUSED and not declared. A net-lvalue or port-actual overhang is a hard
   Xcelium elaboration ERROR (`BNDPERR`, `BNDIPERR`; docs/sv-xcelium-reference.md section 6), so for
   those shapes the reference rejects the design and a refusal is the only reference-consistent answer.
4. **`-ii_val` is a partial, context-dependent switch** ("Correct value for vector part-selects"): it
   restores the LRM value only for reads whose base is a locally declared variable and for reads inside
   testbench tasks, functions and `initial` blocks; it repairs no module-level `assign`/`always` read of
   a port or net base, no inner dimension of a packed array and no write. The triage's "changes nothing"
   is corrected: for 4-state port bases it changes nothing, for the other contexts it changes some.
   (Corrected in 6.1.) The pin stays on the default flags; docs/sv-xcelium-reference.md section 6.
5. **The dyn32 open point is settled and it is a second cause.** On a vector with a negative range
   (`w[3:-4]`) Xcelium reads a 32-bit UNSIGNED base as unsigned (`bu = 32'hFFFFFFFE`, `w[bu +: 4]` is
   `xxxx`) and a 32-bit signed base as signed (`bi = -2`, `w[bi +: 4]` is `1101`); Icarus, Yosys and
   Verilator read both as signed. So 8 of the 22 differing `dyn32` cells (`s - 2` at `s = 0, 1`; `b32` =
   `0xFFFFFFFE`, `0xFFFFFFFF`) are NOT the partial-overhang rule: they are the model's recorded
   two's-complement reading of a 32-bit unsigned base (`Param2.lean` `dynPartRead32`, the header of
   `dyn32.sv`), which follows Icarus and Yosys, against Xcelium and the typing rules of 11.8.1. This one
   is not an Xcelium departure from the LRM; it is a model decision that the reference contradicts, and
   round 6 (refusal-only) does not change it. It is an OPEN ITEM (6.4, item 1). (Corrected in 6.1: the
   audit's P2 count of 52 cells mixes the two causes; 44 are the partial rule, 8 the unsigned base.)
6. **DX2 is corroborated by an elaboration diagnostic, not by a value.** On a one-element range no
   value probe can separate the readings (`w >= 2` labels always include an out-of-range one, `w = 1`
   is the same select), and P3 drops every overhanging write. But an overhanging indexed
   part-select as a continuous-assign net TARGET is a hard elaboration error whose text prints the
   evaluated label range: `BNDIPERR` prints `[8:7]` for `u[8 -: 2]` over `[7:7]`, `[7:6]` for
   `u[7 -: 2]`, `[9:8]` for `u[8 +: 2]` (38 of 38 `-:` cases over `[7:7]` and 38 of 38 over `[0:0]`),
   and with the parameter-dependent base of the real row `u[L+1 -: 2]` prints `[8:7]`; never Icarus's
   `9:8`. So Xcelium's front end lowers `-:` over a single-element range as the LRM, the model, Yosys
   and Verilator do, and Icarus is the odd one out: the declaration is right. The strict verdict
   CONTRADICTED is a value-masking artefact (the Xcelium value trace equals Icarus's only through P1).
   Limit: this is front-end diagnostic text for a net-LHS select, not a simulated value, and it is
   not pinned data (`xcelium_golden.json` holds traces only; the proposal is a separate golden
   kind for diagnostics).
7. **H1 is context-dependent, which widens the guard.** The formal's high bits are undriven (z), not
   x (the observed `~i` turned z into x): `d = zzzz01` for a whole port net, an assign-driven wire, a
   full-range part-select, a constant bit-select, a signed net, another instance's output net; a `tri1`
   formal reads `111101`. A variable actual, a proper part-select (`in4[1:0]`), a constant, an operator
   expression and a `var`/2-state formal zero-extend as the model does. The z-fill is net-collapsing of
   width-mismatched net connections, so it is NOT a function of the connection's own syntax: `.i({in2})`
   alone zero-extends, but with a second width-mismatched bare-net connection of the same net BOTH
   become `zzzz01`; `{s}`, `{2'b00,s}`, `{s,1'b0}`, `{s[1],s[0]}` and `{iw}` flip the same way. The
   output direction has a twin (a narrower output formal into a wider NET actual leaves the high bits
   z; a wider variable actual zero-extends). A guard that refuses only a bare net identifier, a
   constant bit-select or a full-range part-select is unsound; the verified guard is: net-kind formal
   AND narrower actual AND an actual built only from net references, selects and constants with no
   operator. Four of five tools zero-extend, and the LRM text (23.3.3, 23.3.3.8, 10.7) implies
   zero-extension; no clause supports z. (Corrected in 6.1.)
8. **T1 is wider than one row, and truncation is not a single semantics.** Xcelium, Icarus and Verilator
   truncate a bit-select index wider than 32 bits to its low 32 bits (114 of 114 cells equal), and
   Xcelium's `BIGWBS` fires on the self-determined WIDTH (also for a constant, not for exactly 32 bits).
   The LRM-literal reading and Yosys `prep; eval` keep the whole value. The declaration
   `iverilog-wide-index-truncation` called this an Icarus quirk; it is not, so it is contradicted and
   the row is refused. Truncation is not one semantics: on a negative-range vector `[3:-4]` an index
   `2^32 - 1` is x in Xcelium (unsigned low 32 bits) and `nv[-1]` in Icarus and Verilator (signed), and
   Icarus drops the lvalue write where Xcelium performs it. The same truncation exists for a CONSTANT
   index (`v[36'h1_0000_0002]`), for an unpacked-array index (`BIGWIX`, matched by Icarus) and for a
   part-select base (`BIGWPL`); and SHIFT COUNTS wider than 32 bits are silently truncated by Xcelium
   alone, with no warning (`v >> a33` at `a33 = 2^32 + 1` shifts by 1; Icarus, Verilator and the
   whole-value model give 0): an undeclared, unwarned cluster (6.4, item 3).
9. **D4 rows 1 and 2 are weaker than "LRM-permitted", row 3 is clean.** `acg_alias_assign` and
   `acg_alias_port` are a split between the only two event-order-faithful tools (Xcelium and Icarus) on
   an LRM-ambiguous point: Icarus compiles `always_comb` as a loop with the event control at the start
   and propagates a continuous copy synchronously inside the block's own run, so the wake-up is lost and
   `y` lags `a` by one change (stale 48 of 48 samples including quiescence); Xcelium defers the net update
   until the process yields and runs the block twice. The LRM 4.8 example prints `p = 0` in Icarus and
   Verilator and `p = 1` in Xcelium. Verilator and Yosys are blind to event order (on the direct
   self-read control both give `y == a` although 9.2.2.2.1(b), Xcelium and Icarus all give the stale
   value), so their agreement is not evidence. The alias guard must follow the DEPENDENCY PATH and be
   transitive (`assign w = t; assign v = w; always_comb begin y = v; t = a; end` is admitted by the model
   today, equals Xcelium and is stale in Icarus), never the Icarus functor kind (a `~t` alias re-wakes).
   `acg_xproc_bits` is an Icarus-only departure from 9.2.2.2.1 with 6.5: no reading of the exception drops
   `t[0]`; it stays a declared departure.

### 6.2 Decisions and where each landed

Decisions of the lead (2026-10-29, not re-litigated), what each became, and who did it. Lanes A
and B report their own code and rows (docs/sv-charter.md, "Xcelium audit, round 6, lane A" and
"Xcelium audit, round 6, lane B"); this table only names the tags and counts so the books stay straight.
Lane C is declarations, rows, pins and documents.

| cluster | decision | landed as | rows |
|---|---|---|---|
| P1 (30 rows), P3 (6), DX1 (3): constant-base part-select PARTLY out of range, read and write | refuse statically | lane A: `ArraySel:partial-overhang` (`Param2.lean` `arrayPartRead` / `arrayPartTarget`, `partOverhangMsg`) and `Select:partial-overhang` for the legacy `PartSel` encoding (`RangeGuard2.lean`); a select wholly outside, a single-bit select and an in-range one are unchanged | **33 rows flipped** to loud-refusal rows (all 30 P1 rows, `array_oob_lsbwrite`, and `ctx_width_8`, `ctx_width_n2_8`, which had matched only because the x bit collapsed a sum); controls and refusal fixtures `overhang_read*`, `overhang_write*`, `overhang_legacy*` |
| P2: RUN-TIME-base partial read | declare (cannot be refused statically) | lane C: `oracle_disagreement` with `"sim": "xcelium"`, id `xcelium-runtime-partial-part-select-all-x`, checked live and against the pin (`XREF-DECLARED`), `declare_disagreement.py`, 24 new tests (18 in `test_oracle_disagreements.py`, 4 in `test_xcelium_golden.py`, 2 in `test_xcelium_compare.py`; one more test of the pin was renamed) | 6 declared rows: `partsel_dyn`, `partsel_dyn_n2_w5`, `partsel_dyn_n6_w2`, `partsel_dyn_n5_w1`, `partsel_dyn_n1_w4`, `dyn32_part`. Row `dyn32` itself stays an undeclared `XREF-DIFF` (6.1 item 5, 6.4 item 1) |
| H1: narrow NET actual into a wider NET formal | refuse | lane A: `PortConn:net-width` (extractor `_sym_net_bound_actual` marks the connected input, `Hier2.lean` `connProcs`); the guard is narrower than the verified one (6.4 item 5) | **3 rows flipped**: `hier_width`, `hier_width_n2`, `hier_width_n6`; refusal fixture `net_width_min`, control `net_width_ok`; lane C's `hier_width_ok*` keep the other four instances covered. Lane A repair: only `input`/`inout` ports and `wire`/implicit-type `output` are nets, an `output logic`/`output reg`/`output var logic` is a variable and stays admitted (controls `net_width_outvar`, `net_width_outvar1`; net OUTPUT actuals `net_width_outwire1` (scalar: `assign target 'ow' undeclared`) and `net_width_outwire` (vector: `unrecoverable packed dimensions`) are refused earlier than `PortConn:net-width`; Xcelium = Icarus on the controls, z-fill on the net outputs) |
| T1: bit-select index wider than 32 bits | refuse, correct the contradicted declaration | lane A: extractor `ElementSelectExpression:wide-index` and `Select:wide-index` per point (`RangeGuard2.lean`); lane C retired `iverilog-wide-index-truncation` and corrected the document | **5 rows flipped**: `fold_pcase_n31`, `_n40`, `_n40_pm1`, `_n40_p5`, `_wide`; fixture `wide_index`. Lane A repair: only instantiated generate code is judged (`wide_index_dead_*`), and a wide WRITE target at the default point reaches the envelope as `AssignmentExpression:target` (`wide_index_wr`) |
| D4 rows 1 and 2: `always_comb` that reads a continuous copy of a variable it writes | design-level alias guard (refuse); flip the rows, retire the declarations | lane B: `AlwaysComb:alias-read` (`CombAlias2.lean`), transitive through chains of assigns and ports | `acg_alias_assign`, `acg_alias_port` flipped, declarations retired with them; six new refusal rows (`acg_alias_wire` is in fact refused earlier, by `NetSymbol:net-z`) and six admitted counterparts, pinned |
| D4 row 3 `acg_xproc_bits` | stays a declared Icarus departure, tightened text | lane B (text) | unchanged row |
| DX1 `array_oob_part`, `array_oob_lsbwrite`, `label_kminus_w1` | split: confirmed parts stay as ordinary or declared rows, the partial-overhang parts become refusal rows | lane C: `array_oob_asc` (declared Icarus: `q[0][4]`), `label_kminus_q` and `label_kminus_p*` (ordinary rows); the three declarations retired | 4 + 1 new simulated rows |
| DX2 `array_param_labels_l7` | the declaration stays, text upgraded | lane C: text upgraded with Xcelium's value trace and the BNDIPERR corroboration; the row is refused by P1, the declaration is kept on it | 1 |
| D1 (11 rows), D2, D3 | the declarations stay, texts upgraded with the Xcelium confirmation | lane C: "No licensed-simulator confirmation is claimed" replaced by the pin; the retirement conditions are untouched | 13 rows' `observed` |
| U1 (24 rows) | none | none | none |
| the false comments | corrected | lane C: `array_oob.sv`, `array_oob_lsbwrite.sv` (and `array_oob_part.sv`, `dyn32.sv`), `docs/sv-oracle-disagreements.md` | 6.3 |
| the pin | keep default flags, record `-ii_val` | lane C: `docs/sv-xcelium-reference.md` section 6 | |

Row accounting: 41 simulated rows became loud-refusal rows by lane A (33 + 3 + 5) and 2 by lane B,
and lanes B and C add the admitted splits and controls; `cases2.json` has 676 rows, 422 simulated
and 254 loud-refusal. The pin (docs/sv-xcelium-reference.md, section 5) keeps the 43 entries of the
refused rows as evidence and has an entry for every one of the 422 simulated rows (465 in all). The splits that keep coverage of the admitted halves: `partsel_dyn*` (5 rows,
declared P2), `dyn32_part` (declared P2), `array_oob_asc` (declared Icarus), `label_kminus_p*` and
`label_kminus_q` (4 rows, ordinary), `hier_width_ok*` (3 rows), `param_types_ok*` (8 rows): in each,
the model, Icarus and Xcelium agree except where a declaration says otherwise.


### 6.3 Statements corrected in the tree

* The header comments of `Examples/system-verilog/sem2/array_oob/array_oob.sv` and
  `.../array_oob_lsbwrite/array_oob_lsbwrite.sv` said "every simulator agrees here" /
  "every tool agrees (rows partsel*)". They now say that the model, Icarus and Yosys agree
  and Xcelium does not (P1/P3). Two more headers were corrected in the same sweep:
  `.../array_oob_part/array_oob_part.sv` (its "a declared disagreement" is now a refusal
  row) and `.../dyn32/dyn32.sv` (it said the model, Icarus and Yosys read a 32-bit base as
  two's complement as if that were the whole story: Xcelium reads it unsigned, 6.1 item 5).
  A comment edit changes the source digest, so the four envelopes were re-extracted (only the
  `source_files` digest and the span line numbers differ), the declaration of `dyn32_part`
  was written after the edit, and the pin entries of every row on those files that is
  still simulated (`array_oob`, `array_oob_lsbwrite`, `array_oob_lsbwrite_l1`, `dyn32`,
  `dyn32_part`) were re-run on vip-ng: the five traces are identical, only the hash keys
  moved. (The pin entries of the rows that were refused in the meantime keep their old
  hashes as evidence.)
* `docs/sv-oracle-disagreements.md`: the paragraph that said the 1-D write "agrees in every
  tool" and that overhangs past either END of the vector "agree in every tool ...
  (`array_oob`, rows `partsel*`)" is rewritten; every "No licensed-simulator confirmation is
  claimed" of the declarations whose rows survive is replaced by what the pin shows (D1, D2,
  D3, DX2 in the declaration text; D4 by lane B); the declarations of rows that were
  refused are retired and recorded ("Declarations retired in round 6").
* `docs/sv-xcelium-reference.md`: the `-ii_val` decision and the flag and diagnostic table
  (section 6), `XREF-DECLARED`, and the evidence entries.

### 6.4 Open items found by the verifiers, NOT acted on in round 6

1. **A 32-bit unsigned run-time part-select base is read as signed by the model** (item 5 above; 8 cells
   of `dyn32`): Xcelium and the typing rules of 11.8.1 read it unsigned, so the model is the outlier
   among the reference and the LRM and agrees only with Icarus, Yosys and Verilator. Changing
   `dynBaseRead`'s `bw = 32` arm to the unsigned reading is a value change (refused by the round's
   rule); keeping `dynPartRead32` behind a refusal is possible. Row `dyn32` therefore stays an
   undeclared `XREF-DIFF` (its 14 partial-rule cells are declared on the sibling row `dyn32_part`,
   whose stimulus avoids the 8 cells).
2. **Element select of a packed-array-typed member of a packed struct or union is lowered by the
   extractor to a 1-bit `PartSel`** and the model gives wrong values SILENTLY, reads and writes, with
   canonical ranges too (`struct packed {logic [2:0][1:0] arr; logic t;} v`, `v.arr[2]` is a 1-bit select at
   `msb = lsb = 3` instead of the 2-bit element). Found by the U1 verifier outside any cluster; model
   `xxxxx1x` against Xcelium `xxxx01x` on `v.arr[1] = s`. Fix the extractor or refuse loudly.
   **Closed 2026-10-30 (WP-E1):** the extractor now lowers the select to the flat window of the selected
   ELEMENTS (`v.arr[1]` is the 2-bit window `[4:3]`), nested chains and writes included, and every select
   is checked against the compiler's type (`<ExprKind>:window-mismatch`); rows `member_elem_*`, see
   [sv-envelope-schema.md](sv-envelope-schema.md) "Member selects count elements".
3. **Shift counts, unpacked-array indices and part-select bases wider than 32 bits** (item 8): the shift
   cluster is undeclared and unwarned in Xcelium; the array-index twin is unchecked in the model.
4. **The verifier's remaining notes**: Verilator right-aligns a widened streaming-operator target (against the
   LRM, Xcelium and the model: not a witness there); Yosys is silently wrong on arrays of packed structs; the
   clause citation for an invalid array index is "7.4.6" in `docs/sv-oracle-disagreements.md`,
   `docs/sv-envelope-schema.md` and four declarations but "7.4.5" in `docs/sv-assignment-targets.md`,
   `docs/sv-charter.md` and the sv-tests corpus (the triage read "7.4.5, Indexing and slicing of arrays" in
   the 2023 text; the verifier could not re-read it): the repo is inconsistent and one of the two is wrong;
   `v[11 +: 2]` (partly out of range at the msb end) reads `xx` in Xcelium.
5. **The H1 guard that landed is narrower than the one the verifier derived** (6.1 item 7).
   `PortConn:net-width` refuses a NET formal fed by a BARE reference to a narrower NET actual
   (`_sym_net_bound_actual`). The verifier found that Xcelium's z-fill is net collapsing, decided
   by the net's whole connectivity: `{s}`, `{2'b00,s}`, `{s,1'b0}`, `{s[1],s[0]}`, a wire and
   another instance's output net zero-extend in isolation and z-fill as soon as the same net also
   feeds another width-mismatched net connection (one net feeding several instances is common).
   The concatenation forms stay admitted (they were admitted before: no loud shape became
   admitted), so a design that connects `{s}` next to a bare `s` still has a silent
   model-versus-Xcelium difference. The recorded gaps of the lane (a full-range part-select, a
   constant bit-select and the output twin) are the same family. (Repair: the net kind of the ACTUAL is
   decided by the direction token, because slang reports `output logic` as a variable with the same header as
   `input logic`; the first version marked a narrower `output logic`/`output reg` actual as a net and refused
   shapes every tool zero-extends.) The sound guard is conservative
   and syntactic: net-kind formal AND narrower actual AND an actual built only from net
   references, selects and constants with no operator.
6. **Only 24.03-s004 was measured**; 26.09 on compute-0 was not tried.
