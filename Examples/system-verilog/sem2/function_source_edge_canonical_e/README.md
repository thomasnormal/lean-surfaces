# Source-shaped edge function wall

This clean-room fixture keeps an automatic input-only function as a parser
`Function` declaration and `FunctionCall` expression in an edge-triggered
body.  The ordinary E route evaluates that retained source call directly,
with the function formals as a local value environment.  The envelope is
generated with the approved source-preserving command:

```text
python3 extractors/sv/extract.py --retain-proc-rewrites \
  --top function_source_edge_canonical_e \
  -o Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv.json \
  Examples/system-verilog/sem2/function_source_edge_canonical_e/function_source_edge_canonical_e.sv
```

The evaluator admits automatic functions whose formals are input-only; static
functions and output/ref/inout formals remain named refusals.  Icarus Verilog
13.0 and Xcelium 24.03-s004 both execute the eight source rows, including the
first uninitialized sample and `0`, `1`, `x`, and `z` function operands:
`q=x,1,1,x,x,x,x,0`.
