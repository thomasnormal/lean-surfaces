# Opaque declaration erasure

Declaration-only `real`, `realtime`, `shortreal`, `chandle`, and `event`
objects have no slot in the legacy self-check state. The extractor and adapter
census erase those declarations while preserving loud boundaries for reads,
writes, triggers, and waits.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/opaque_declarations/proof.lean
```
