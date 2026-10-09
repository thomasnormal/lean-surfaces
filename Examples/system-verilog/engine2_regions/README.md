# Engine 2 region evidence

These are real SystemVerilog source fixtures for the first pure region-schema
piece in `LeanModels/Sv/Engine2/Regions.lean`, not hand-written kernel images or
theorems about the C++ implementation.

- `zero_delay_nba.sv` observes the old value before and after `#0`, then the
  NBA-updated value at the next simulation time.
- `nba_reentry.sv` additionally observes the NBA update waking a posedge process
  in the same time slot, before the next-time observation.

The output label `inactive` denotes the continuation after a zero delay. It
does not assert that `$display` executes as an Inactive-region event: clause
4.4.2.3 resumes the process in an Inactive-to-Active iteration. The second
fixture demonstrates why inventory positions cannot be an execution rank.
Neither fixture claims to exercise the eight PLI-only callback points.

## Measured on October 9, 2026

Both unchanged fixtures compile and run successfully with Icarus Verilog 13.0
and with the compiled Engine 2 consumer. Each simulator's unfiltered stdout
matches the corresponding `.out` byte-for-byte: two fixtures, zero differences.
Mox's matched compiler/simulator artifacts are from revision
`b904bf0f66b8ecd242cc2ad1598fb41fb93a790d`, in the emitter worktree; the simulator
reports that revision and the worktree is clean. The measured pipeline lowers
the actual source to MLIR before requesting `--mode=engine2-compiled`.

An older engine2-worktree simulator does not recognize that mode; its refusal
is retained in the measurement receipts and is not an agreement. Likewise,
the existing Lean self-check source harness refuses delay control and the
posedge process. The new Lean module checks the region inventory and its
vocabulary bridge, not execution of these source files. A future scheduling
relation must supply the missing semantic connection.

## Reproduce

Run from the repository root with matched current Mox binaries, Icarus, and
an external output directory. Set `MOX_BIN_DIR` to that build's `bin` directory
and choose either fixture name. These commands are illustrative shell usage:

```console
FIXTURE=zero_delay_nba
WORK_DIR=$(mktemp -d)
SOURCE="Examples/system-verilog/engine2_regions/$FIXTURE.sv"
"$MOX_BIN_DIR/mox-verilog" --ir-sim --four-state --top="$FIXTURE" "$SOURCE" -o "$WORK_DIR/fixture.mlir"
"$MOX_BIN_DIR/mox-sim" --mode=engine2-compiled --top="$FIXTURE" "$WORK_DIR/fixture.mlir" > "$WORK_DIR/mox.out"
iverilog -g2012 -s "$FIXTURE" -o "$WORK_DIR/fixture.vvp" "$SOURCE"
vvp "$WORK_DIR/fixture.vvp" > "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "$WORK_DIR/icarus.out"
cmp "$WORK_DIR/mox.out" "Examples/system-verilog/engine2_regions/$FIXTURE.out"
```

Native pointers, ABI ordinal equality, FIFO choices, update-before-evaluation
policy, and compiled-thunk refinement are not inferred from these outputs.
