# Discarded pure `$sformatf` calls in the adapter

The adapter follows the extractor's `sformatf_statement` marker for discarded
literal integral `$sformatf` calls. The formatted packed string is unobserved,
so the call carries no represented state. Dynamic formats, unsupported
conversions, and effectful operands remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_sformatf_statements_adapter/proof.lean
```
