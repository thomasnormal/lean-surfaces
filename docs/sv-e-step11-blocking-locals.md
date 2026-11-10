# E Step 11: blocking locals in `always_ff`

This clean-room fixture is
[`blocking_local_always_ff_step11.sv`](../Examples/system-verilog/sem2/blocking_local_always_ff_step11/blocking_local_always_ff_step11.sv).
One `always_ff @(posedge clk)` declares a four-state block-local `logic [3:0]
t`, assigns it with blocking statements, and samples it into two nonblocking
architectural outputs.  The envelope and source shape are checked by
`agree.lean`; no core-specific rewrite or new run2 meaning is introduced.

IEEE 1800-2023 §9.2.2.4 gives the `always_ff` event and single-writer
restrictions.  The local declaration and its blocking assignments are still in
the process's active-region execution.  The default block-variable lifetime
rules in §6.21 make `t` a private static variable of this named procedural
block; it is not a module signal and no other process may write it.  The
nonblocking assignments to `q` and `q_not` sample the local values in the
active region and commit them in the NBA region.

The proposed E rule is a scoped edge frame: on each edge, enter the named
block's local store, execute blocking assignments left to right against the
pre-edge module view and the local store, evaluate RHS expressions for NBA
updates immediately, then commit the queued module writes.  The frame retains
the local's static value between activations, while the fixture's first
assignment makes the observed result independent of its initial unknown value.
Automatic blocks, local declarations with initializers, local arrays, loops,
and local variables used as NBA targets remain separate loud boundaries until
their own storage rules are specified.  A blocking assignment to a module
variable remains refused under the `always_ff` profile even when this local
shape is admitted.

## Differential rows

The testbench is [`blocking_local_always_ff_step11_tb.sv`](../Examples/system-verilog/sem2/blocking_local_always_ff_step11/blocking_local_always_ff_step11_tb.sv).
Icarus Verilog 13.0 and Xcelium 24.03-s004 agree:

| row | `d` | `q` | `q_not` |
| --- | --- | --- | --- |
| `first` (before the first edge) | `xxxx` | `xxxx` | `xxxx` |
| `local_0000` | `0000` | `0000` | `1111` |
| `local_1010` | `1010` | `1010` | `0101` |
| `local_xz01` | `xz01` | `xz01` | `xx10` |
| `local_zzzz` | `zzzz` | `zzzz` | `xxxx` |

The current loader retains `LocalDecl` as
`block-local declaration requires scoped procedural storage` and marks the
semantic process loud.  If that boundary is passed, the existing E edge
executor's next explicit boundary is `9.2.2.4: blocking assignment in
always_ff is outside E-core-1`; neither is silently reinterpreted by this
fixture.
