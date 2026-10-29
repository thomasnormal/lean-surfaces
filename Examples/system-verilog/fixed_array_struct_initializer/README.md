# Fixed unpacked arrays of initialized structs

This fixture covers complete positional assignment patterns for a finite fixed
unpacked array of an untagged integral struct. Each struct element is flattened
into its existing field cells in declared array order. Partial, effectful,
replicated, and aggregate forms remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/fixed_array_struct_initializer/proof.lean
```
