# Plain `always @(posedge clk)`

The clean-room fixture is
[`Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv`](../Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv).
It keeps the source spelling `always @(posedge clk)` and uses an NBA-only
body with an enable, a default branch, and a second NBA target.

IEEE 1800-2023 §§9.2.2.1 and 9.2.2.4 distinguish the general `always` process
from `always_ff`; this source-shaped form still has one positive-edge event and
NBA-only updates.  The existing E profile can admit it under the same sampled
edge contract when the clock is a one-bit input, every body update is a static
NBA, and no other process writes the targets.  The fixture does not rewrite the
process to `always_ff`.

The rows cover the first unknown state (printed by the testbench), disabled and
enabled updates, x/z enable values, x/z data, and the default branch.  Icarus
13.0 and Xcelium 24.03-s004 agree:

```text
first       q=xxxx q_copy=xxxx
en0_d9      q=1010 q_copy=1001
en1_d6      q=0110 q_copy=0110
enx_d3      q=1010 q_copy=0011
enz_dz      q=1010 q_copy=zzzz
en1_dxz     q=xz01 q_copy=xz01
```

The retained-node Lean proof pins `Process2.alwaysPlain` and
`ffOnlyProfileB = true`. Its preparatory legacy cycle witness is retired;
the source-oracle rows above are retained, and source-preserving E transport
remains on its review branch. Plain always procedures with blocking bodies,
multiple clocks, delays, or unsupported event controls remain loud.

## E-core review boundary

Reviewed against E-core-1 on 2026-11-10. The retained `Process2.alwaysPlain`
shape, NBA-only profile, and five simulator rows pass the focused Lean proof.
The source process is eligible for the same event/NBA contract, but the current
E elaborator has only the `FF` edge-process record and no source-kind-preserving
`alwaysPlain` elaboration. It therefore remains a named E front-end boundary;
no silent rewrite to `always_ff` was added. A future packet must retain the
source kind while proving the shared edge contract and its no-blocking/delay
restrictions.
