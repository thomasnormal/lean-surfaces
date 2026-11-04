# Bound `inside` adapter expression

This fixture checks that an `inside` expression with elaborated localparam
items follows the extractor's existing literal membership lowering.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/inside_parameter_adapter/proof.lean
```
