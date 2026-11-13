# Implicit event control memory boundary

This clean-room fixture exercises the canonical-memory route after time-zero
initialization: `always @*` reads a source-shaped unpacked memory and writes a
scalar output with blocking assignment. The retained process waits for a raw
read change, including the selected memory cell and its index, then runs once
in source order. A body that changes one of its own watched reads remains loud
because it needs another Active-region pass.

IEEE 1800-2023 §§4.7 and 9.4.2.2.2 define the one-time initializer and the
implicit sensitivity. The parser node and memory select stay source-shaped;
there is no cell expansion or event-list lowering. `check.py` compares the
canonical-E rows with Icarus Verilog 13.0 and Xcelium 24.03-s004 when licensed.
