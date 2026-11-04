# Discarded pure empty subroutine calls in the adapter

The adapter follows the extractor's `empty_subroutine_call` and
`empty_input_task_call` markers. Empty tasks and functions with pure input
actuals have no represented state or output, so their declaration and
statement are erased from the flat adapter view. Nonempty, effectful,
output-bearing, and value-position calls remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_empty_subroutine_statements_adapter/proof.lean
```
