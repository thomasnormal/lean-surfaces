# Pure literal-return function values in the adapter

The adapter follows the extractor's `literal_function_statement`,
`literal_function_return`, and `empty_function_default` lowerings. A
literal-return function with pure input actuals, or an empty function whose
return default is known, contributes no callable state to the flat adapter
view. Effectful, computed, output-bearing, and unsupported calls remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_literal_function_values_adapter/proof.lean
```
