# Empty dynamic-array declarations in the adapter

The legacy adapter follows the extractor's declaration-only path for dynamic
arrays initialized with `new[0]` or an empty assignment pattern.  These forms
create no flat cells.  Nonzero allocations and later value uses remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/empty_dynamic_decl_adapter/proof.lean
```
