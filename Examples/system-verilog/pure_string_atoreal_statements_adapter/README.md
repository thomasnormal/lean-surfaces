# Discarded pure `string.atoreal()` calls in the adapter

The adapter follows the extractor's `floating_string_atoreal_statement` marker
for a discarded conversion of a source-pure ASCII string. Dynamic, non-ASCII,
and effectful string histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_string_atoreal_statements_adapter/proof.lean
```
