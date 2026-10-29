# Empty display arguments

SystemVerilog macro expansion can leave omitted arguments in `$display` and
`$write` calls. In the no-conversion form, each omitted argument is a literal
space. The extractor lowers that space through the existing `%s` renderer;
conversion-specifier forms with an omitted operand remain loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/empty_display_arguments/proof.lean
```
