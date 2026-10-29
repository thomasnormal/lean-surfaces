# Discarded literal coverage queries in the adapter

The adapter follows the extractor's `coverage_nocov_statement` marker for
literal coverage calls whose result is discarded. With no represented coverage
database, these queries return the fixed empty-coverage result and carry no
adapter state; dynamic arguments and covergroup-backed designs remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_coverage_nocov_statements_adapter/proof.lean
```
