# Flat edge-child hierarchy wall

The parent retains an `Instance` node whose child contains an edge process.
Canonical E refuses the instance at its flat memory entry point with the
source-shaped `Instance:` boundary; hierarchy is handled by the separate
canonical hierarchy route and does not silently flatten an edge child.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=x`, then `y=0`), so the refusal is a measured E boundary.
