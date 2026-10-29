# Array ordering adapter

The legacy adapter follows the extractor's flat-cell lowering for source-pure
fixed-array `sort` and `rsort` calls. `reverse` and struct-array ordering use
the same represented assignment blocks. Unknown, dynamic, and otherwise
unsupported array histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/ordering_adapter/proof.lean
```
