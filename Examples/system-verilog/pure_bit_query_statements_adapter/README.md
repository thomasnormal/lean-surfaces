# Discarded pure bit queries in the adapter

The adapter follows the extractor's `bit_query_statement` marker for discarded
literal and source-pure named-history calls to `$countbits`, `$countones`,
`$onehot`, `$onehot0`, and `$isunknown`. Computed, dynamic, and effectful
operands remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_bit_query_statements_adapter/proof.lean
```
