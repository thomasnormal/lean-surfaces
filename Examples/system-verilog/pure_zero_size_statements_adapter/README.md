# Discarded pure zero-size queries in the adapter

The adapter follows the extractor's `zero_size_statement` marker for discarded
`len` and `size` calls on untouched empty string and queue storage. Initialized,
populated, and effectful histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_zero_size_statements_adapter/proof.lean
```
