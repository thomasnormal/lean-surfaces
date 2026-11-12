# Parameterized module hierarchy at the E boundary

This clean-room fixture exercises IEEE 1800-2023 §23.3.3 module
instantiation: a parameterized parent instantiates two parameterized children,
overrides each child width with `W/2`, and connects sliced input and output
ports.  The extractor keeps the instance and connection nodes source-shaped;
`PDesign.instantiateH` performs the ordinary hierarchical elaboration and
preserves the instance-qualified child declarations.

The resulting `Design2` is executed by canonical E-core-0.  The five rows
cover zero, known values, and an x-valued input; each child is an identity
driver, so the parent output equals its input.  The Lean receipt checks both
the flattened declaration/process shape and the E execution.  `check.py`
compares the same rows with Icarus Verilog 13.0 and readiness-gated Xcelium
24.03-s004.

Run the focused receipt and differential comparison with:

```text
lake env lean Examples/system-verilog/sem2/hierarchy_e/agree.lean
python3 Examples/system-verilog/sem2/hierarchy_e/check.py
```
