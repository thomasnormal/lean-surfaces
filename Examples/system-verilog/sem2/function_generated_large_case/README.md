# Generated function case

This clean-room receipt keeps an automatic, input-only `lookup5` function as a
source-shaped `Function` declaration. Its complete 32-arm `unique case` and
default function-name assignment are represented by the function body's
case-equality expression; the 13 generated part-select calls remain
`FunctionCall` nodes in the envelope. The function-enabled E elaborator binds
the actuals to the retained formals while instantiating the source-shaped
design.

Regenerate the receipt with:

```sh
python3 extractors/sv/extract.py \
  --top function_generated_large_case --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/function_generated_large_case/function_generated_large_case.sv.json \
  Examples/system-verilog/sem2/function_generated_large_case/function_generated_large_case.sv
```

Run `python3 check.py` for the E rows and the Icarus 13.0 comparison. The
Xcelium 24.03-s004 row is included when the simulator readiness gate passes;
otherwise the check reports `no Xcelium result`.
