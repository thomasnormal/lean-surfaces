# E Step 11: plain `always @(posedge clk)`

The clean-room fixture is
[`Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv`](../Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_posedge_step11.sv).
It keeps the source spelling `always @(posedge clk)` and uses an NBA-only
body with an enable, a default branch, and a second NBA target.

IEEE 1800-2023 §§9.2.2.1 and 9.2.2.4 distinguish the general `always` process
from `always_ff`; this source-shaped form still has one positive-edge event and
NBA-only updates. `Kernel/Core1Elab.lean` now transports both retained source
nodes into E through `FF.ofProcess2` and `Elab1.ofEdgeDesign2`. The `FF.style`
field retains `.alwaysPlain` or `.alwaysFF`; the single clock event and body are
copied verbatim. `FF.toProcess2?` reads the source node back. The preservation
theorems prove that a successful transport retains every process in source
order, its entire body, the declarations and module name. No process is
filtered, and no statement is lowered.

This entry point requires scalar input clocks and `ffOkB` bodies.
Mixed comb/edge designs, asynchronous resets and unsupported process nodes
refuse explicitly. It has a separate name from Step 9's planned general
`Elab1.ofDesign2`. One-writer and no-clock-write conditions remain explicit
`EdgeProfile` obligations for R-EDGE. The unchanged E edge rule samples each
NBA RHS from the same pre-edge view and commits the issue-order queue; plain
`always` has no separate execution semantics.

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

Async-reset transport is deliberately outside this narrow entry point.
The legacy loader's `alwaysFFR` node does not retain plain-always source
style, and its reset-event `iff` metadata is not yet represented. A transport
round trip over that node cannot establish preservation of the original
source. `FF.ofProcess2` therefore refuses every `alwaysFFR` before E
elaboration. This does not change E's separately constructed reset rules.
The loaded-source regression
[`plain_always_reset_metadata_step11.sv`](../Examples/system-verilog/sem2/plain_always_posedge_step11/plain_always_reset_metadata_step11.sv)
keeps an unguarded plain-always reset beside an `always_ff` reset guarded by
`iff gate` (§9.4.2.3). Its source oracle distinguishes a masked reset from an
enabled one. It must refuse this edge entry until the frontend retains the
complete source event. No E execution result is claimed for this regression.
The envelope uses the legacy default extraction mode so the loaded-source
guard exercises that metadata-loss path. Retained-procedure mode already
refuses the plain multi-event always. `reset_boundary.lean` rejects the loaded
default-mode design and both direct reset polarities; it does not pin the
loader's lossy node shape as expected behavior.

Xcelium 24.03-s004 verifies eleven source rows. Icarus 13.0 rejects the
event-control `iff` at the fixture's line 9, so no Icarus result is claimed
for this source. The checker accepts only that exact compiler diagnostic;
other compile failures fail the check, and an Icarus version that accepts
the source must execute all eleven rows.

| action | unguarded `q` | guarded `r` |
| --- | --- | --- |
| first | x | x |
| clock, data 1 | 1 | 1 |
| reset, gate 0 | 0 | 1 |
| clock, data 0, gate 0 | 0 | 0 |
| clock, data 1 | 1 | 1 |
| reset, gate 1 | 0 | 0 |
| clock, data x | x | x |
| clock, data z | z | z |
| clock, data 1 | 1 | 1 |
| reset, gate x | 0 | 1 |
| reset, gate z | 0 | 1 |

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
lake build 'Examples.«system-verilog».sem2.plain_always_posedge_step11.agree' \
  'Examples.«system-verilog».sem2.plain_always_posedge_step11.reset_boundary'
python3 Examples/system-verilog/sem2/plain_always_posedge_step11/check.py
```

The checker uses the Xcelium readiness gate, prints simulator versions and E
trace timings, and requires all nineteen E rows. It separately checks the
eleven reset-guard source rows, with the explicit Icarus limitation above.
Subprocesses have a 120-second
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
