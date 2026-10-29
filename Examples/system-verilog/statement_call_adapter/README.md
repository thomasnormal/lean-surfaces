# Represented statement calls

The legacy adapter census admits the four statement calls whose effects are
represented in the self-check state: `$display`, `$write`, `$finish`, and
`$stop`. Other system and user calls remain loud at their existing boundaries.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/statement_call_adapter/proof.lean
```
