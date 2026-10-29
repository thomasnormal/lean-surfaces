# Fixed string-array elements in loops

This fixture exercises source-pure ASCII elements of a finite unpacked
`string` array in `foreach`, `while`, and `do...while`. The array has no flat
runtime slot; the extractor replays its literal cells and lowers dynamic
indices to the existing ternary expression path. Writes and aggregate uses
remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/fixed_string_array_loops/proof.lean
```
