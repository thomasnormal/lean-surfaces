# Discarded pure fixed-array queries in the adapter

The adapter follows the extractor's `array_query_statement` and
`array_reduction_statement` markers for discarded fixed-array `min`, `max`,
`unique`, `unique_index`, `sum`, `product`, `and`, `or`, and `xor` calls,
including source-pure `with` clauses. Dynamic or effectful array histories and
`with` expressions remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_array_query_statements_adapter/proof.lean
```
