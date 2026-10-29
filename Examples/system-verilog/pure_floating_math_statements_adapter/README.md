# Discarded pure floating math in the adapter

The adapter follows the extractor's `floating_math_statement` marker for
source-pure discarded `$sqrt`, `$pow`, and `$sin` calls. Effectful, timed,
unsupported, and value-position forms remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_floating_math_statements_adapter/proof.lean
```
