# Associative-array declarations in the adapter

The legacy adapter follows the extractor's static declaration erasure for
associative arrays. The declaration contributes no flat state until a finite
cell lowering proves a supported history; dynamic keys and value operations
remain loud at their assignment or call boundaries.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/associative_decl_adapter/proof.lean
```
