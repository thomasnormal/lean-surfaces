# Finite associative count, exists, and empty delete statements in the adapter

The adapter follows the extractor's `associative_count_statement`,
`associative_exists_statement`, and `associative_empty_delete_statement`
lowerings. Discarded finite count and presence observations, plus deletes on
untouched associative arrays, carry no represented adapter state; dynamic or
effectful histories remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_associative_count_exists_delete_statements_adapter/proof.lean
```
