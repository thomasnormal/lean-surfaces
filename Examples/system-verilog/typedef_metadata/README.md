# Compile-time typedef metadata

Integral and flat integral-struct typedefs allocate no runtime state. The
extractor and adapter census erase those aliases while retaining loud
boundaries for unsupported aggregate forms and value operations.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/typedef_metadata/proof.lean
```
