# Fixed arrays of untagged unions

This fixture covers a finite fixed unpacked array whose leaf is an equal-width
untagged union. Each element is represented by one flat cell, so selecting
either union member aliases that element's cell. Mixed-width, tagged, aggregate
initializer, and whole-array forms remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/fixed_array_unpacked_union/proof.lean
```
