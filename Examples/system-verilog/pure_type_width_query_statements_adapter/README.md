# Discarded pure type and width queries in the adapter

The adapter follows the extractor's `typename_statement` and `bits_statement`
markers for discarded `$typename` and `$bits` calls. Their expression
arguments are not evaluated, so effectful arguments remain unrepresented and
later state stays exact. Malformed and value-position calls remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_type_width_query_statements_adapter/proof.lean
```
