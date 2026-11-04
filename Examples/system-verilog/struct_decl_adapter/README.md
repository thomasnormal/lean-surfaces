# Unpacked-struct declarations in the adapter

The legacy adapter follows the extractor's flat-cell lowering for procedural
untagged unpacked structs whose fields all have representable scalar or packed
integral leaves. Unsupported fields and aggregate operations remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/struct_decl_adapter/proof.lean
```
