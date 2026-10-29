# Elaborated generate adapter

The legacy adapter follows the extractor's `elaboration_lowered` path for a
generated scope whose converted module contains no unsupported nodes. Its
generated processes and declarations are checked through the ordinary
self-check vocabulary; generated scopes that leave unsupported state remain
loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/generate_adapter/proof.lean
```
