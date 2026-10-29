# Discarded pure string queries in the adapter

The adapter follows the extractor's `string_query_statement` marker for
source-pure `len`, `getc`, `atoi`, `atobin`, `compare`, and `icompare` calls.
Unknown, effectful, and dynamic string histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_string_query_statements_adapter/proof.lean
```
