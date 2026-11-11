# E Step 11: plain `always @(posedge clk)`

The clean-room fixture is
[`Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv`](../Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv).
It keeps the source spelling `always @(posedge clk)` and uses an NBA-only
body with an enable, a default branch, and a second NBA target.

IEEE 1800-2023 §§9.2.2.1 and 9.2.2.4 distinguish the general `always` process
from `always_ff`; this source-shaped form still has one positive-edge event and
NBA-only updates. `Kernel/Core1Elab.lean` transports both retained single-event
source nodes into E through `FF.ofProcess2` and `Elab1.ofEdgeDesign2`. The
`FF.style` field retains `.alwaysPlain` or `.alwaysFF`; the clock event and body
are copied verbatim. `FF.toProcess2?` reads the source node back. The
preservation theorems prove that a successful transport retains every process
in source order, its entire body, the declarations and module name. No process
is filtered, and no statement is lowered.

This entry point requires scalar input clocks and `ffOkB` bodies. Mixed
comb/edge designs, asynchronous resets and unsupported process nodes
refuse explicitly. It has a separate name from Step 9's planned general
`Elab1.ofDesign2`. One-writer and no-clock-write conditions remain explicit
`EdgeProfile` obligations for R-EDGE. The unchanged E edge rule samples each
NBA RHS from the same pre-edge view and commits the issue-order queue; plain
`always` has no separate execution semantics.

Async-reset source preservation is outside this packet. The legacy loader's
`alwaysFFR` node does not retain whether the source was plain `always` or
`always_ff`, and it drops the source event's `reset_iff` guard. The loaded
source therefore cannot satisfy a source-preserving round trip for an
async-reset process. Until that metadata is retained, the source-preserving
E entry must refuse those forms; no async-reset execution or preservation
result is claimed here. The positive-edge, single-event packet below is the
complete scope of this review.

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

`agree.lean` replaces the earlier run2 witness with an E profile, a slot theorem
over every typed store and process-atomic legal schedule, and a kernel-checked
trace equality including startup. Its source-style guard checks the E image,
not just the loader's node. Blocking bodies, delays and unsupported event
controls remain loud in this edge fragment.

The second source,
[`plain_always_kinds_step11.sv`](../Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_kinds_step11.sv),
retains a plain `always` and an `always_ff` in one edge-only design. The plain
body issues two NBAs to `q` and executes a plain case; the other process reads
the old `q`. This checks both source styles, source-order NBA replacement,
exact x/z matching, and common pre-edge sampling under both process orders.
The first seven rows are:

| selector/data | `q` | `q_old` | `q_case` |
| --- | --- | --- | --- |
| initial | xxxx | xxxx | xxxx |
| 00/0000 | 1111 | xxxx | 0000 |
| 1x/0011 | 1100 | 1111 | 1010 |
| 1z/xz01 | xx10 | 1100 | 0101 |
| 00/zzzz | xxxx | xx10 | zzzz |
| 11/1010 | 0101 | xxxx | 0101 |
| 00/0110 | 1001 | 0101 | 0110 |

Six more rows drive explicit x/z clock transitions (IEEE §9.4.2), with the
selector held at `00`. Both simulators agree with E on all thirteen rows of
this source:

| clock transition / data | `q` | `q_old` | `q_case` |
| --- | --- | --- | --- |
| 0→x / 1001 | 0110 | 1001 | 1001 |
| x→z / 0001 (no edge) | 0110 | 1001 | 1001 |
| z→1 / 0101 | 1010 | 0110 | 0101 |
| 1→x / 1111 (no positive edge) | 1010 | 0110 | 0101 |
| x→1 / zzzz | xxxx | 1010 | zzzz |
| 0→z / 0011 | 1100 | xxxx | 0011 |

Both loaded sources have kernel-checked `EdgeProfile`, R-EDGE slot and trace
proofs. The existing executor frame and totality statements remain unchanged.
These four-state traces preserve the separate resolution-aware observation
boundary. All axiom audits contain only standard axioms.

After building the fixture, compare E's actual execution directly with both
source testbenches:

```sh
lake build 'Examples.«system-verilog».sem2.plain_always_posedge_step11.agree'
python3 Examples/system-verilog/sem2/plain_always_posedge_step11/check.py
```

The checker uses the Xcelium readiness gate, prints simulator versions and E
trace timings, and requires all nineteen rows. Subprocesses have a 120-second
limit. A refused or incomplete E trace fails.

The two-process oracle caches declared store values between closed slots.
`cacheConfig_eq` proves equality with the entire original configuration,
including non-flat and undeclared variables; `sampledSlotsCached_eq` proves
that the cached trace equals the ordinary E trace for every input list. The
kernel-checked row theorem still uses the ordinary trace. This prevents
accumulated function-store writes from slowing the interpreted test, without
changing E's state, event rule, inputs or observations. Measured here, the
uncached two-process trace hit both 120- and 300-second limits; caching reduced
its thirteen rows to 10 ms. The original six-row trace took 60 ms.
