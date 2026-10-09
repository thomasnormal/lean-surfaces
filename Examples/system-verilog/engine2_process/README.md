# Engine 2 process-lifecycle evidence

These real SystemVerilog source fixtures distinguish a blocked process from a
completed process and distinguish process completion from simulation completion.
They use ordinary `initial` procedures, positive-edge event control, and
positive delay control, without the `process` class API.

- `blocked_sensitivity.sv` displays `waiting`, then blocks on `@(posedge flag)`.
  No process subsequently writes `flag` or schedules a timer. Both simulators
  exit normally without displaying `unreachable`, despite this pending wait.
- `wait_resume_completion.sv` displays `waiting 0`, blocks on a positive edge,
  resumes at time 2, displays `resumed 2`, and reaches the end of its body.
  A distinct process continues waiting until time 5 and then displays
  `other completed 5`. This fixture declares a 1ns time unit and precision;
  decimal `$time` observations therefore report the integer simulation ticks.

No two processes display concurrently at the same simulation time. Neither
fixture uses `$finish`, forced termination, suspension, forks, named events,
process-handle observation, or implementation-specific scheduling order.

## Normative scope

IEEE 1800-2023 clause 9.2.1 states that an `initial` procedure executes once
and ceases activity when its statement finishes. Clause 9.4.2 defines
positive-edge event control, and clause 9.4.1 defines delay control. Clause
9.7 distinguishes normal process termination (`FINISHED`) from waiting in a
blocking statement (`WAITING`). These sources do not call `status()` and do
not directly measure those public state labels or any internal kernel state.

Clause 4.5's simulation reference algorithm continues while some time slot
is nonempty. A process waiting on an event that never occurs is not by itself
a future calendar entry. The first fixture observes normal simulation exit
without satisfying the wait; the second observes continued simulation after
one process reaches its body's end. The observations are scoped to source
behavior, not a proof of the kernel's process bookkeeping or completion rule.

## Measured on October 9, 2026

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and compiled Engine 2 each
compile and run both fixtures with exit status 0. Their unfiltered stdout
matches byte-for-byte and matches the committed `.out` files: two fixtures,
zero differences. The `.out` files record the measured outputs, not a
hand-written process-state trace.

The matched Mox artifacts are
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-verilog` and
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-sim`. Both report Mox revision
`67ee7a12d28855967d750c9b0f63934b567d763d`; the compiler also reports frontend
`mox-frontend-v1:b96a6752d711f7306fdf11057031f947d5d86946201a8f1ee5f46b6adcbaa568`
and slang `10.0.0+ace09c5`. SHA-256 receipts pin the binaries independently of
the emitter worktree's checkout:

```text
mox-verilog e41c78e04c5f3a6aec9443ae1a1354954d35e13069e1157b51176a5eb0d295c8
mox-sim    6214f174a2e916c4b30a431f49983963db52b947bd8d229829a324788c2a9190
```

Receipts are retained externally under
`/var/tmp/thomas-ahle/fleet2/logs/ls-spec-process-fixtures-*`, including emitted
MLIR, compile/simulation stdout and stderr, versions, binary hashes, and
comparison exit statuses. These observations do not establish Lean execution
of the sources or C++ refinement of the pure Lean process schema.

The focused existing Lean source harness passes its `builtin_values` baseline
and explicitly refuses both new fixtures: `blocked_sensitivity` at
`TimedStatement:SignalEventControl`, and `wait_resume_completion` at `$time`
(`CallExpression`). Its one-pass/two-refusal result exits 1; the preserved
refusals are not agreements or evidence that Lean executes these sources.

## Reproduce

Run from the repository root with matched Mox binaries and Icarus. Set
`MOX_BIN_DIR` to the build's `bin` directory and choose either fixture:

```console
FIXTURE=blocked_sensitivity
WORK_DIR=$(mktemp -d)
SOURCE="Examples/system-verilog/engine2_process/$FIXTURE.sv"
"$MOX_BIN_DIR/mox-verilog" --ir-sim --four-state --top="$FIXTURE" "$SOURCE" -o "$WORK_DIR/fixture.mlir"
"$MOX_BIN_DIR/mox-sim" --mode=engine2-compiled --top="$FIXTURE" "$WORK_DIR/fixture.mlir" > "$WORK_DIR/mox.out"
iverilog -g2012 -s "$FIXTURE" -o "$WORK_DIR/fixture.vvp" "$SOURCE"
vvp "$WORK_DIR/fixture.vvp" > "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "Examples/system-verilog/engine2_process/$FIXTURE.out"
```
