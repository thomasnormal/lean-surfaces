# Constant-extent dynamic arrays in the adapter

The legacy adapter follows the extractor's flat-cell lowering when a
procedural dynamic-array declaration has a source-pure constant extent. The
declaration contributes one ordinary cell per element; symbolic extents and
dynamic array operations remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/dynamic_extent_adapter/proof.lean
```
