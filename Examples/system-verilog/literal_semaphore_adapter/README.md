# Literal semaphore declaration in the adapter

The legacy adapter follows the extractor's declaration-only shortcut for a
local `semaphore` initialized by a nonnegative literal `new(N)`. The opaque
handle itself contributes no flat state; dynamic constructors and semaphore
operations remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/literal_semaphore_adapter/proof.lean
```
