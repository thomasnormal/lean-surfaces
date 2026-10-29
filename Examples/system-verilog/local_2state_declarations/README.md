# Local two-state declarations

The legacy self-check adapter admits scalar and packed two-state locals through
the same `LocalDecl` lowering used by the interpreter. Their declaration and
initializer boundaries are represented; reads of unsupported values and
effectful initializers remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/local_2state_declarations/proof.lean
```
