# Discarded pure fixed dimension queries in the adapter

The adapter follows the extractor's `dimension_query_statement` marker for
fixed packed and unpacked dimension queries. Dynamic, selected, and
effectful operands remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_dimension_query_statements_adapter/proof.lean
```
