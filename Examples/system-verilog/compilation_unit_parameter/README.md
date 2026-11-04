# Compilation-unit parameter

This fixture keeps a compilation-unit `parameter` as elaboration metadata. Its
value supplies a packed width and a displayed constant while the module itself
uses only the legacy self-check surface.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/compilation_unit_parameter/proof.lean
```
