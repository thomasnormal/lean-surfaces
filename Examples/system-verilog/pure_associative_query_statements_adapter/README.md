# Discarded pure associative-array queries in the adapter

The adapter follows the extractor's `associative_empty_query_statement` and
`associative_empty_endpoint_statement` markers for discarded `num`, `size`,
`first`, and `last` calls on untouched arrays. Populated, dynamic, and
effectful histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_associative_query_statements_adapter/proof.lean
```
