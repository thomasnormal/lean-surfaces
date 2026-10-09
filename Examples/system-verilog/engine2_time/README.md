# Engine 2 simulation-time evidence

These real SystemVerilog source fixtures observe integer simulation-time ticks.
Each module explicitly declares a 1ns time unit and 1ns precision, so the global
simulation time unit is also 1ns. Decimal `%0d` observations of `$time` avoid
the separate `%t`/`$timeformat` formatting convention.

- `tick_delays.sv` observes time 0, then the distinct future slots 2 and 5
  after successive positive delays of 2 and 3 ticks.
- `zero_delay_slot.sv` observes time 2 on both sides of `#0`, then time 3
  after a positive delay. The equal timestamps do not mean that `#0` is a
  no-op: the process suspends within the existing slot.

## Normative scope

IEEE 1800-2023 clauses 3.14.1 and 3.14.3 describe local delay precision and
the global simulation time unit; clause 9.4.1 describes delay control.
Clause 4.4 groups events by execution time and advances to the next nonempty
slot only after completing the current slot. Clause 4.4.2.3 schedules a
module process's explicit `#0` continuation through Inactive in the current
slot, resuming in an Inactive-to-Active iteration. Clause 20.3.1 defines
`$time` as a 64-bit integer scaled to the invoking module's time unit.

These fixtures deliberately avoid real-valued delays, fractional rounding,
mixed module scales, `$realtime`, `#1step`, overflow, concurrent processes,
and nondeterministic within-region ordering. They do not establish a time
conversion or overflow policy for the pure Lean time schema.

## Measured on October 9, 2026

Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and compiled Engine 2 each
compile and run both fixtures with exit status 0. Their unfiltered stdout
matches byte-for-byte and matches the committed `.out` files: two fixtures,
zero differences. The `.out` files record the measured outputs, not a
hand-written scheduler image.

The matched Mox artifacts are
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-verilog` and
`/var/tmp/thomas-ahle/wt/emitter/build-opt/bin/mox-sim`. Both report Mox revision
`b904bf0f66b8ecd242cc2ad1598fb41fb93a790d`; the compiler reports slang
`10.0.0+0`. SHA-256 receipts pin the binaries independently of the emitter
worktree's current checkout, which contains unrelated ongoing edits:

```text
mox-verilog 195d5fccc172a891c1c392b2166fb9ff3259edbda749a0f04548cc621975b97d
mox-sim    28fe8c9d41258efc8a522e9aaf6feba7cefba11b30d783ba4a624182aea57c05
```

Receipts are retained externally under
`/var/tmp/thomas-ahle/fleet2/logs/ls-spec-time-fixtures-*`, including emitted
MLIR, compile/simulation stdout and stderr, versions, binary hashes, and
comparison exit statuses.

The existing Lean source self-check harness does **not** execute these timing
examples: it refuses `tick_delays` at `$time` (`CallExpression`) and
`zero_delay_slot` at delay control (`TimedStatement:DelayControl`). Those
refusal receipts are retained separately; they are not agreements. The pure
Lean time schema and these source observations are separate evidence, not a
proof that Lean executes these files or that C++ refines the schema.

## Reproduce

Run from the repository root with matched Mox binaries and Icarus. Set
`MOX_BIN_DIR` to the build's `bin` directory and choose either fixture:

```console
FIXTURE=tick_delays
WORK_DIR=$(mktemp -d)
SOURCE="Examples/system-verilog/engine2_time/$FIXTURE.sv"
"$MOX_BIN_DIR/mox-verilog" --ir-sim --four-state --top="$FIXTURE" "$SOURCE" -o "$WORK_DIR/fixture.mlir"
"$MOX_BIN_DIR/mox-sim" --mode=engine2-compiled --top="$FIXTURE" "$WORK_DIR/fixture.mlir" > "$WORK_DIR/mox.out"
iverilog -g2012 -s "$FIXTURE" -o "$WORK_DIR/fixture.vvp" "$SOURCE"
vvp "$WORK_DIR/fixture.vvp" > "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "Examples/system-verilog/engine2_time/$FIXTURE.out"
```
