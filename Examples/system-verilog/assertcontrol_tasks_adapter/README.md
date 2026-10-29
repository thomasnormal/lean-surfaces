# Bare assertion-control tasks in the adapter

Bare `$asserton`, `$assertoff`, and `$assertkill` calls are lowered by the
extractor to inert `pure_diagnostic` nodes because the legacy self-check state
has no assertion-control register. Argumented forms remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/assertcontrol_tasks_adapter/proof.lean
```
