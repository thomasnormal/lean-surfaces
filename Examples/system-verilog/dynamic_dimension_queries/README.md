# Dynamic-array and queue dimension queries

This fixture covers IEEE 1800-2023 §20.7 metadata queries on an unallocated
dynamic array, a dynamic array after one constant `new[4]` allocation, and an
empty queue. The legacy flat self-check state exposes the current bounds and
declared rank without representing aggregate storage. Dynamic allocation
sizes, later mutations, and value reads remain loud.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/dynamic_dimension_queries/proof.lean
```
