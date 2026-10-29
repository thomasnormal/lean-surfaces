# Discarded stdout file-position errors in the adapter

The adapter follows the extractor's `fseek_stdout_error_statement` and
`ftell_stdout_error_statement` markers. Seeking or querying the predefined
stdout descriptor with the admitted literal arguments produces the fixed error
result and no represented adapter state; dynamic descriptors and other
arguments remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_stdout_position_error_statements_adapter/proof.lean
```
