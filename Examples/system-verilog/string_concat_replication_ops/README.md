# Source-pure string concatenation and replication

Literal string concatenation and constant replication retain their exact ASCII
history when assigned to a string. The self-check tier replays those values at
`$display` without adding string storage; dynamic or effectful histories remain
loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/string_concat_replication_ops/proof.lean
```
