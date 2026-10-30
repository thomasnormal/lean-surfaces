# Blocking intra-assignment timing

`capture.sv` changes the RHS, destination index and neighboring bits during
a positive delay. Copyback uses the saved RHS and resumed index.
`reentry.sv` checks mixed two-state/four-state concatenation, prior NBA work
and fresh capture on each loop visit. `counts.sv` checks signed, zero and
unknown repeated-event counts, then retains a positive wait despite later
count and source changes. Their complete independent transcripts run under
both source and reverse schedule oracles in `proof.lean`.

`zero.sv` independently confirms Active/Inactive/NBA ordering, but the model
refuses it because Inactive delivery is not admitted. `events.sv` independently
confirms repeated and single event behavior; procedural clock writes now publish
through the retained edge queue and the receipt executes the complete transcript.

Three kernel theorems cover capture-before-wait, copyback at the resumed
index, and saved repeat control. Compiled-statement certificates connect
them to these extracted sources. Reference source hashes are recorded with
the receipt in `proof.lean`.

Regenerate with `python3 extractors/sv/extract.py` followed by the five source
paths. Run the receipt from the repository root:

```sh
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 \
  Examples/system-verilog/intra_assignment/proof.lean
```

See [the contract](../../../docs/sv-intra-assignment.md) for admission and
runtime boundaries.
