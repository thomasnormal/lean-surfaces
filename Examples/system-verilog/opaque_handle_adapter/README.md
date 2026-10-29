# Opaque class-handle declarations in the adapter

The extractor already erases uninitialized `mailbox` and `semaphore` handles
as opaque declaration metadata. The legacy adapter follows that same route in
module and procedural scopes. Handle reads, construction, assignments, and
methods remain loud at their existing boundaries.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/opaque_handle_adapter/proof.lean
```
