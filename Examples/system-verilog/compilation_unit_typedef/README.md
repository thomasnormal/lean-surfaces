# Compilation-unit typedef metadata

This fixture uses a compilation-unit integral typedef as a type alias for a
module cell. The alias is elaboration metadata and does not create a separate
self-check state slot.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/compilation_unit_typedef/proof.lean
```
