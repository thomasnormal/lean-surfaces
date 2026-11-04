# Resolved forward typedef metadata

SystemVerilog permits a forward typedef declaration before or after the
matching typedef. Once the name resolves to an integral alias, the declaration
has no self-check state of its own. An unresolved forward typedef remains a
loud extractor boundary.

The receipt can be run with:

```sh
lake env lean Examples/system-verilog/forward_typedef_metadata/proof.lean
```
