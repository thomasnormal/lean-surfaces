# Qualified `if` fallbacks in the adapter

The adapter follows the extractor's `qualified_fallback_lowered` lowering for
`unique if` and `priority if` chains with explicit fallbacks. The qualifier has
no diagnostic effect when the chain is complete, so the lowered control is
ordinary adapter `if` state; incomplete or overlapping forms remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_qualified_if_fallback_adapter/proof.lean
```
