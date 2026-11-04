# Discarded pure real conversions in the adapter

The adapter follows the extractor's existing source-pure statement markers for
`$itor`, `$bitstoreal`, `$bitstoshortreal`, `$rtoi`, `$realtobits`, and
`$shortrealtobits`. Their discarded results have no represented self-check
state; effectful or unsupported operands remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_real_conversion_statements_adapter/proof.lean
```
