# Severity-task adapter

The legacy adapter admits the extractor's represented forms of `$info`,
`$warning`, `$error`, and `$fatal`. Severity diagnostics evaluate their pure
arguments without adding a diagnostic stream to the self-check state; `$fatal`
retains its represented whole-run halt. Unsupported argument forms remain
loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/severity_adapter/proof.lean
```
