# Unreferenced subroutine metadata

A task declaration does not execute its body merely because the module is
loaded. The extractor already erases an uncalled subroutine; the legacy
adapter census follows that same identity-based reference check. Referenced
subroutines remain loud at the callable boundary.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/unreferenced_subroutine_metadata/proof.lean
```
