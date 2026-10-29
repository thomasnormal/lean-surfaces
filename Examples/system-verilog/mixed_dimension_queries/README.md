# Mixed fixed and dynamic dimension queries

This fixture covers IEEE 1800 dimension metadata for `int values[3][][5]`.
The flat self-check state does not represent the dynamic array, but `$size`
can still inspect fixed dimensions one and three, and
`$unpacked_dimensions` reports all three unpacked dimensions. Selecting the
dynamic dimension, initializing the array, or reading and writing a value
remains outside this declaration-only slice.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/mixed_dimension_queries/proof.lean
```
