# Invalid packed dimensions in the adapter

Malformed integral packed dimensions are rejected during elaboration and do
not allocate runtime self-check cells. The adapter follows that compile-time
declaration boundary, including a direct literal initializer; effectful
initializers and value uses remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/invalid_dimension_adapter/proof.lean
```
