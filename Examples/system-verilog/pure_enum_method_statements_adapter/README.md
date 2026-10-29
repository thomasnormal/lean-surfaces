# Discarded pure enum methods in the adapter

The adapter follows the extractor's `enum_name_statement` and
`enum_numeric_statement` markers for discarded source-pure enum `name`,
`first`, `last`, `num`, `next`, and `prev` calls. Effectful receivers and
step arguments remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_enum_method_statements_adapter/proof.lean
```
