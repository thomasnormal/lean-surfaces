# Dynamic-index NBA targets in `always_ff`

The clean-room fixture is
[`Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_target_step11.sv`](../Examples/system-verilog/sem2/dynamic_nba_target_step11/dynamic_nba_target_step11.sv).
It uses the source-shaped form

```systemverilog
always_ff @(posedge clk)
  if (en) q[idx] <= d;
```

The envelope retains the packed bit-select as `Lhs2.index`; no case expansion
or target unrolling is introduced.  IEEE 1800-2023 §§9.2.2.4 and 11.5.1 make
the index and RHS part of the NBA event before the update region.  The oracle
rows cover the first unknown state, known indices 0 and 3, x/z indices, an
out-of-range index 4, and a disabled write.  Icarus 13.0 and Xcelium
24.03-s004 agree on every row:

```text
first             q=xxxx
nba_idx_0_d1      q=xxx1
nba_idx_3_d0      q=0xx1
nba_idx_x_d1      q=0xx1
nba_idx_z_d0      q=0xx1
nba_idx_4_d1      q=0xx1
nba_idx_1_disabled q=0xx1
```

The legacy `run2` witness already gives the same no-op behavior for x/z and
out-of-range indices.  E-core-1 currently requires every NBA target to have a
static write window (`Stmt2.ffOkB`/`execFF`), so the fixture's `agree.lean`
pins that boundary.  Dynamic targets, nested unpacked targets, concatenated
targets, and multiple dynamic writes remain separate design decisions for the
E edge route.
