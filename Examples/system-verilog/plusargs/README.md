# Explicit command-line inputs

`values.sv` checks prefix matching, first-match order, signed and based values,
two-state conversion, selected copyback, absence and short circuiting.
`numeric.sv` checks truncation, padding and separators. `timers.sv` repeats
selected writes across retained delay continuations under both schedule
oracles. Their complete independent transcripts and explicit inputs are in
`proof.lean`, together with kernel theorems bound to actual compiled statements.

`diagnostic.sv` is deliberately loud with `BAD=12q`: the independent run emits
a conversion diagnostic and retains the destination. It is not counted as an
execution match.

Regenerate the envelopes with `python3 extractors/sv/extract.py` followed by
the four source paths. Run the receipt from the repository root with:

```sh
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 \
  Examples/system-verilog/plusargs/proof.lean
```

See [the input contract](../../../docs/sv-plusargs.md) for the API and boundaries.
