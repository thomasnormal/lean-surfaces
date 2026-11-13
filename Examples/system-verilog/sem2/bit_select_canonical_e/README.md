# Canonical E packed bit selects

This clean-room source keeps a parameter-sized packed input beside constant
and run-time bit selects.  Canonical E retains the parser's `BitSel` node and
uses its declaration element-width table to lower the base to a source-shaped
slice or dynamic index.  An x/z index reads all-x under IEEE 1800-2023
§11.5.1; no cell expansion or expression lowering is introduced.

The five rows cover known constant and dynamic selects plus x/z dynamic
indices.  The Lean receipt agrees with Icarus Verilog 13.0 and Xcelium
24.03-s004 through the simulator readiness gate.
