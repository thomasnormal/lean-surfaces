# Engine 2 wait-registration evidence

These real SystemVerilog source fixtures observe alternatives in one event
control and a fresh event control reached after resumption. They use ordinary
`initial` procedures and explicitly declare a 1ns time unit and precision.

- `multi_signal_once.sv` waits on `@(posedge first or negedge second)`.
  A single driver changes both signals at time 1 with no intervening delay or
  event control. The waiting body increments its counter once, delays one
  tick, and displays `resumes 1 at 2`. The observation is one resumption for
  this event control, not one resumption per alternative.
- `edge_rearm.sv` waits on a positive edge twice in succession. Its driver
  raises the signal at time 1, lowers it at time 2, and raises it again at
  time 3. The second wait does not consume the earlier edge or the intervening
  negative edge; the body displays `edge occurrences 2 at 3`.

Both waits are reached before the driver's first delayed change. Neither
fixture uses `$finish`, races between output statements, process-class APIs,
`iff` conditions, implicit sensitivity, level-sensitive `wait`, or callbacks.
The sources do not inspect registration identifiers, dependency indexes,
queue contents, or internal process status.

## Normative scope

IEEE 1800-2023 clause 9.4.2 defines synchronization by value changes and edge
event control. Clause 9.4.2.1 defines an event OR as alternatives in one event
control: an occurrence of any alternative enables its following statement.
Clause 9.4.1 defines the positive delays separating changes in these sources.
These observations concern source behavior, not the particular representation
or removal policy of a native wait registration.

The second fixture uses signal edges rather than named events. A preliminary
`named_event_rearm.sv` source used two successive `@(pulse)` controls and
explicit `-> pulse` occurrences, as described by clauses 15.5.1 and 15.5.2.
Icarus ran it successfully, displaying `named occurrences 2 at 2`. Mox's
frontend compiled it, but compiled Engine 2 refused during emission with
`EM_UNSUPPORTED_OPERATION`, opcode `llvm.load`, reason
`module-value-not-admitted`. Its source, MLIR, refusal, and oracle output are
retained externally. That attempt is not counted as agreement or as evidence
that named-event execution is supported.

## Measured on October 9, 2026

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and compiled Engine 2 each
compile and run the two committed fixtures with exit status 0. Their
unfiltered stdout matches byte-for-byte and matches the committed `.out`
files: two fixtures, zero differences. The `.out` files record measured
outputs, not a hand-written registration or scheduler trace.

The matched Mox artifacts are
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-verilog` and
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-sim`. Both report Mox revision
`67ee7a12d28855967d750c9b0f63934b567d763d`; the compiler also reports frontend
`mox-frontend-v1:b96a6752d711f7306fdf11057031f947d5d86946201a8f1ee5f46b6adcbaa568`
and slang `10.0.0+ace09c5`. SHA-256 receipts taken before and after the runs
pin unchanged binaries independently of the emitter worktree's checkout:

```text
mox-verilog e41c78e04c5f3a6aec9443ae1a1354954d35e13069e1157b51176a5eb0d295c8
mox-sim    6214f174a2e916c4b30a431f49983963db52b947bd8d229829a324788c2a9190
```

Receipts are retained externally under
`/var/tmp/thomas-ahle/fleet2/logs/ls-spec-wait-fixtures-*`, including emitted
MLIR, compile/simulation stdout and stderr, versions, binary hashes, comparison
exit statuses, and the preliminary named-event refusal. These source
observations do not establish Lean execution, general simulator conformance,
or C++ refinement of the pure Lean wait-registration schema.

The focused existing Lean source harness passes its `builtin_values` baseline
and explicitly refuses both committed fixtures: `multi_signal_once` at
`TimedStatement:EventListControl` and `edge_rearm` at
`TimedStatement:SignalEventControl`. Its one-pass/two-refusal result exits 1.
The preserved refusals are not agreements or Lean execution of these sources.

## Reproduce

Run from the repository root with matched Mox binaries and Icarus. Set
`MOX_BIN_DIR` to the build's `bin` directory and choose either fixture:

```console
FIXTURE=multi_signal_once
WORK_DIR=$(mktemp -d)
SOURCE="Examples/system-verilog/engine2_wait/$FIXTURE.sv"
"$MOX_BIN_DIR/mox-verilog" --ir-sim --four-state --top="$FIXTURE" "$SOURCE" -o "$WORK_DIR/fixture.mlir"
"$MOX_BIN_DIR/mox-sim" --mode=engine2-compiled --top="$FIXTURE" "$WORK_DIR/fixture.mlir" > "$WORK_DIR/mox.out"
iverilog -g2012 -s "$FIXTURE" -o "$WORK_DIR/fixture.vvp" "$SOURCE"
vvp "$WORK_DIR/fixture.vvp" > "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "Examples/system-verilog/engine2_wait/$FIXTURE.out"
```
