# Assertion-control diagnostics in the adapter

Literal and source-pure assertion-control arguments are lowered by the
extractor to an inert `pure_diagnostic` node because the legacy self-check
state has no assertion-control register. Dynamic control arguments remain
loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/assertcontrol_adapter/proof.lean
```
