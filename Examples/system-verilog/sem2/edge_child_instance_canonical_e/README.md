# Edge-child hierarchy through ordinary canonical E

The ordinary `load_design_sv2` route follows the parser-native child instance
through the canonical hierarchy merge. The child edge process remains
source-shaped and its connected clock, data, and output names are retained in
the native E design.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=x`, then `y=0`), matching ordinary canonical E.
