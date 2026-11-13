# Source-shaped edge function wall

This clean-room fixture keeps an automatic input-only function as a parser
`Function` declaration and `FunctionCall` expression.  The envelope is
generated with the approved source-preserving command:

```text
python3 extractors/sv/extract.py --retain-proc-rewrites \
  --top function_source_edge_canonical_e \
  -o Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv.json \
  Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv
```

Canonical E refuses the call as `CallExpression:user-function`; it does not
inline the function body.  Icarus Verilog 13.0 and Xcelium 24.03-s004 both
execute the two source rows (`q=x`, then `q=1`), so the refusal is a measured
E boundary rather than a simulator mismatch.
