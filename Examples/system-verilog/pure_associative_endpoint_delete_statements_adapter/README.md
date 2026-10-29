# Finite associative endpoint and delete statements in the adapter

The adapter follows the extractor's finite-history lowerings for discarded
`first`/`last` endpoint statements and literal-key or whole-array `delete`
operations. Dynamic keys and effectful histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_associative_endpoint_delete_statements_adapter/proof.lean
```
