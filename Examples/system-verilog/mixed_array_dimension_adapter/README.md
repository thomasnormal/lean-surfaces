# Mixed-dimension array declarations in the adapter

The legacy adapter follows the extractor's declaration-only path for an
untouched 2-state array with fixed dimensions around a dynamic dimension. Such
a declaration contributes no flat state when later code does not read or write
its value. Initializers and value uses remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/mixed_array_dimension_adapter/proof.lean
```
