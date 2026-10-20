# Forever loop source control

IEEE 1800-2023 §12.7.6 and §12.8, compiled through the existing loop control:

- `values.sv`: nearest-loop break/continue, nesting, automatic array
  reinitialization and finish without a fallthrough iteration.
- `timers.sv`: retained body tails, continue skipping the remaining delay,
  live four-state payload reads, and break after resumption.
- `waits.sv`: an event body remains blocked until an event occurs; another
  process can finish the run.

Complete outputs were independently observed in value-preserving mode on
2026-10-20. All three match both source and reverse schedule oracles; values
also matches the time-zero runner. Source SHA-256 hashes are recorded in
`proof.lean` and their envelopes. The source-bound certificates cover retained
event/delay boundaries, break after a delay and rearming at the next iteration.

Run from the repository root:

```sh
python3 extractors/sv/extract.py Examples/system-verilog/forever_loops/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/forever_loops/proof.lean
```

`Forever.body` compiles to the existing `forLoop` with a true condition and
empty initializer/step lists. No scheduler or evaluator constructor is added.
Named-block disable, procedural edge publication, timed clock queries,
zero-delay Inactive delivery, unmodelled scalar body lifetimes and symbolic
loops retain their existing refusals. A loop that runs without suspending or exiting exhausts fuel as timeout.
