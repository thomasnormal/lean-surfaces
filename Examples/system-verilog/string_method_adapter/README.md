# Source-pure string statement methods

The legacy adapter follows the extractor's source-history proof for discarded
`string.putc`, `itoa`, `bintoa`, `octtoa`, and `hextoa` calls. Literal forms do
not allocate a self-check string cell; dynamic and effectful forms remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/string_method_adapter/proof.lean
```
