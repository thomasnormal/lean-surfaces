# Package metadata

This fixture uses a package containing only an integral typedef. The package,
its import, and the typedef are elaboration metadata; the module still runs on
the ordinary legacy self-check state.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/package_metadata/proof.lean
```
