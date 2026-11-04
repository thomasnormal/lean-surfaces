# Display format escape in the adapter

The first string argument to `$display` is a format string. This fixture pins
an octal escape that the existing formatter renders before adapter expression
walking begins.

Run the receipt from the repository root with:

```sh
lake env lean Examples/system-verilog/display_format_escape_adapter/proof.lean
```
