# E Step 11: blocking locals in `always_ff`

This clean-room fixture is
[`blocking_local_always_ff_step11.sv`](../Examples/system-verilog/sem2/blocking_local_always_ff_step11/blocking_local_always_ff_step11.sv).
One `always_ff @(posedge clk)` declares a four-state block-local `logic [3:0]
t`, assigns it with blocking statements, and samples it into two nonblocking
architectural outputs.  The envelope and source shape are checked by
`agree.lean`. The frontend also retains Slang's scope and resolved lifetime
metadata. This is frontend preservation and source-oracle evidence;
blocking-local execution in E is still incomplete.

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

## Static storage and scope evidence

[`static_local_lifetime_step11.sv`](../Examples/system-verilog/sem2/blocking_local_always_ff_step11/static_local_lifetime_step11.sv)
adds a parameterized `W`-bit implicit-static local, a two-state local, an
explicit-static signed local, and a nested block with another local named
`t`. Its testbench distinguishes old and new NBA samples around blocking
writes, re-entry without an assignment, partial reset, two-state x/z
conversion, and signed widening. Static locals retain their value even when
their block performs no write (§6.21). Four-state locals start at x and
two-state locals at zero (§6.8, Table 6-7); the outputs start at x.

The extractor retains the declaration inside its original Block. A
storage-bearing Block carries its Slang name, lexical/hierarchical paths and
default lifetime. A LocalDecl carries Slang's resolved lifetime, paths,
signed/two-state metadata, symbolic declared type and its existing optional
initializer. The resolved width is evidence for the default parameter point,
not a substitute for the declaration's dimension AST. Slang's printed paths
omit anonymous scopes and are not unique identities: the source spans and
enclosing tree must also be preserved. Other blocks keep their existing
envelope fields. No local is lifted to module storage by this change.

The source rows below use `W=4`. Columns are `q_old`, `q_new`, `q_shadow`,
`q_known`, `q_signed`. Icarus 13.0 and readiness-gated Xcelium 24.03-s004
verify both tables. The repeated rows intentionally test static retention.

| action | `q_old` | `q_new` | `q_shadow` | `q_known` | `q_signed` |
| --- | --- | --- | --- | --- | --- |
| before first edge | `xxxx` | `xxxx` | `xxxx` | `xxxx` | `xxxxxxxx` |
| no write | `xxxx` | `xxxx` | `xxxx` | `0000` | `xxxxxxxx` |
| load `1010` | `xxxx` | `1010` | `0101` | `0000` | `11111010` |
| no write | `1010` | `1010` | `0101` | `1010` | `11111010` |
| load `xz01` | `1010` | `xz01` | `xx10` | `1010` | `xxxxxz01` |
| no write | `xz01` | `xz01` | `xx10` | `0001` | `xxxxxz01` |
| load `zzzz` | `xz01` | `zzzz` | `xxxx` | `0001` | `zzzzzzzz` |
| no write | `zzzz` | `zzzz` | `xxxx` | `0000` | `zzzzzzzz` |
| partial reset | `0000` | `0000` | `xxxx` | `0000` | `00000000` |
| no write | `0000` | `0000` | `xxxx` | `0000` | `00000000` |

Run the source checks with
`python3 Examples/system-verilog/sem2/blocking_local_always_ff_step11/check.py`.
The checker prints simulator versions, readiness-gates Xcelium and verifies
all fifteen source rows. It explicitly claims no E execution result.

## Remaining E representation boundary

`Stmt2` currently has neither a scoped declaration nor a scoped Block node;
`Ingest2` therefore keeps LocalDecl loud. The E edge executor returns only
NBA issues, and its Active-phase frame proof leaves the complete store
unchanged. A persistent private-cell write cannot satisfy that frame.

The shared-representation review keeps `Stmt2` frozen: new constructs stay
in the envelope/PStmt frontend until the planned single `Sv.Ast` exists.
This packet preserves the metadata in the envelope; the existing PStmt
parser continues to mark execution unsupported. That future AST needs
source-scoped declarations with lifetime/type/initializer, plus an activation
result containing both private static-cell writes and NBA issues. E already provides typed stores
and block segments in `VarId.path`; these can identify private cells without
module-level hoisting. The one body engine must retain the fixed module
sampling view while threading private writes left to right. Its NBA-only
rule should be a proved special case. The rule, initialization/lifetime
proofs, admission, loaded-source E traces and simulator agreement remain
required before this Step 11 construct is complete.

## Current E review

On 2026-11-11, public master `05f089221` was checked after the procedural
local metadata landing `ffbb5ee04`.  The retained envelope preserves the
named block, Slang scope paths, resolved lifetime, signed/two-state metadata,
symbolic type, and optional initializer; the semantic `LocalDecl` boundary
still refuses before E execution.  The focused Lean receipt loads both
source-shaped designs and keeps the refusal guards green.  The source checker
verifies five rows for the block-local fixture and ten rows for the static-
lifetime fixture with Icarus Verilog 13.0 and readiness-gated Xcelium
24.03-s004.  No E trace is claimed for these rows.

This review intentionally does not add a `Stmt2` constructor or a parallel
local interpreter.  The next implementation must use the planned single
source AST and one E body engine, with private static-cell state and NBA
issues in one activation result; automatic locals, local initializers, local
arrays, loops, and local NBA targets remain loud until their rules are
specified.  Resolution, `DecisionKnown`, `Spec2`, run2, and MemCycle are
unchanged.
