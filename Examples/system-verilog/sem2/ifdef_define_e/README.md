# Slang preprocessor `-D` fixture

This clean-room fixture exercises IEEE 1800-2023 §22.5.  The extractor's
`-D NAME[=VALUE]` option passes definitions to Slang's preprocessor, so the
parser sees the selected `ifdef` branch without textual rewriting.  The
committed envelope is regenerated with:

```text
python3 extractors/sv/extract.py --top ifdef_define_e -D FEATURE=1 \
  -o Examples/system-verilog/sem2/ifdef_define_e/ifdef_define_e.sv.json \
  Examples/system-verilog/sem2/ifdef_define_e/ifdef_define_e.sv
```

`agree.lean` checks that the envelope contains the `FEATURE` branch.  The
receipt also checks extraction with no definition and runs both preprocessor
branches against Icarus Verilog 13.0 and Xcelium 24.03-s004 (when the
readiness check grants the licensed simulator): four rows each for
`FEATURE=1` and for the undefined case, including x/z inputs.

```text
python3 Examples/system-verilog/sem2/ifdef_define_e/check.py
```
