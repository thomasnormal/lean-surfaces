# Engine 2 scheduled-event evidence

These deterministic fixtures observe two source-level consequences represented
by the normalized Engine 2 event vocabulary:

- `delayed_signal_update.sv` waits one 1ns tick, publishes a signal value, and
  prints `updated 1 1`.
- `resume_after_update.sv` arms a positive-edge wait before a distinct process
  publishes the signal at 1ns; the waiter prints `resumed 1`.

They demonstrate source observations only. They do not expose event IDs,
calendar queues, origin fields, enqueue sequence numbers, named-event
occurrences, cancellation, or region-order policy.

## Normative scope

IEEE 1800-2023 clause 4.4 assigns every event one execution time and separates
process execution from value updates; clauses 9.4.2 and 9.4.2.1 define edge
controls and OR alternatives. The pure Lean schema keeps process resume,
ordinary signal update, and named-event occurrence as distinct actions. It does
not infer a total order for independent events or claim that a source delay
itself identifies a region.

The fixtures avoid NBA ordering, named-event source objects, `iff`, level waits,
clocking/sequence events, `$time` formatting beyond a simple integer, and races
between output statements. They are not a Lean execution or C++ refinement
proof.

## Measured on October 9, 2026

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and compiled Engine 2 each
compile and run both fixtures with exit status 0. Their unfiltered stdout
matches byte-for-byte and matches the committed `.out` files: two fixtures,
zero differences.

Matched binaries:
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-verilog` and
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-sim`.
Receipts under `/var/tmp/thomas-ahle/fleet2/logs/ls-spec-event-fixtures-*` pin
MLIR, streams, versions, and SHA-256 hashes. The emitter checkout is treated as
an external artifact and is not modified by this lane.

The existing Lean source harness does not execute these timing/event-control
shapes; any focused refusals remain refusals, not agreement.

## Reproduce

```console
FIXTURE=delayed_signal_update
WORK_DIR=$(mktemp -d)
SOURCE="Examples/system-verilog/engine2_event/$FIXTURE.sv"
$MOX_BIN_DIR/mox-verilog --ir-sim --four-state --top="$FIXTURE" "$SOURCE" -o "$WORK_DIR/fixture.mlir"
$MOX_BIN_DIR/mox-sim --mode=engine2-compiled --top="$FIXTURE" "$WORK_DIR/fixture.mlir" > "$WORK_DIR/mox.out"
iverilog -g2012 -s "$FIXTURE" -o "$WORK_DIR/fixture.vvp" "$SOURCE"
vvp "$WORK_DIR/fixture.vvp" > "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "Examples/system-verilog/engine2_event/$FIXTURE.out"
```
