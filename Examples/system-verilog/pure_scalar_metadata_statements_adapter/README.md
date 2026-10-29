# Discarded pure scalar metadata queries in the adapter

The adapter follows the extractor's `clog2_statement`,
`isunbounded_statement`, `signing_statement`, and `time_scale_statement`
markers. Constant queries, integral signing casts, and timescale metadata are
pure and discarded results carry no represented state. Effectful, malformed,
and value-position calls remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_scalar_metadata_statements_adapter/proof.lean
```
