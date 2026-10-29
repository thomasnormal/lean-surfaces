# Fixed unpacked byte-array string initializer

This fixture covers the IEEE string-to-unpacked-byte-array initializer. The
literal is sampled into fixed cells in declared index order, and a shorter
literal zero-pads the remaining cells. Dynamic strings, non-ASCII literals,
and non-byte element arrays remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/fixed_array_string_initializer/proof.lean
```
