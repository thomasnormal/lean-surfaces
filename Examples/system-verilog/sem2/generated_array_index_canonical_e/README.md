# Generated fixed-array index wall

The approved source-preserving extractor retains the generate-for assignment
as an `ArraySel` whose `GenvarRef` index is substituted by canonical E during
generate expansion. This keeps the parser's fixed unpacked array source shape
and applies IEEE 1800-2023 §§7.4.6 and 27.4 at the concrete generated point.

The receipt is regenerated with:

```text
python3 extractors/sv/extract.py --top generated_array_index_canonical_e \
  --retain-proc-rewrites \
  -o Examples/system-verilog/sem2/generated_array_index_canonical_e/generated_array_index_canonical_e.sv.json \
  Examples/system-verilog/sem2/generated_array_index_canonical_e/generated_array_index_canonical_e.sv
```

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the same nine rows as E,
including the first uninitialized value, defaults, and x/z inputs.
