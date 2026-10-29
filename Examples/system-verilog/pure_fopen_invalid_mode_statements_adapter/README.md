# Discarded invalid-literal `$fopen` calls in the adapter

The adapter follows the extractor's `fopen_invalid_mode_statement` marker for
an invalid literal mode. The rejected call performs no represented filesystem
operation; dynamic modes and valid opens remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_fopen_invalid_mode_statements_adapter/proof.lean
```
