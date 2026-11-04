# Pure diagnostic markers in the adapter

The adapter follows the extractor's existing `pure_diagnostic` lowering for
static VCD controls, monitor toggles, the null `$system` task, literal
`$sdf_annotate`, and a literal `$timeformat` with no `%t` consumer. These calls
have no represented self-check state; dynamic or effectful arguments remain
loud.

Run the receipt with:

```sh
lake env lean Examples/system-verilog/pure_diagnostic_markers_adapter/proof.lean
```
