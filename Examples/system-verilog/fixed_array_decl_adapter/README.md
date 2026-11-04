# Fixed-array declarations in the adapter

The legacy adapter follows the extractor's flat-cell lowering for procedural
fixed unpacked arrays when the converted declaration consists only of ordinary
`Var`/`Empty` cells. Unsupported leaves and aggregate operations remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/fixed_array_decl_adapter/proof.lean
```
