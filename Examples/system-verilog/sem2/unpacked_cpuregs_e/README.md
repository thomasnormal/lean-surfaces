# One-rank unpacked register-file memory in E

This clean-room fixture is the PicoRV32 `cpuregs` shape: one parameter-sized
unpacked declaration, a run-time read index in a continuous assignment, and a
run-time write index in an `always_ff` nonblocking assignment.  The source is
kept in the parser envelope; it is not flattened into one scalar per cell.

`MemEDesign.ofPDesign` already supplies the generic E memory profile for this
shape.  Its native `MemState` starts each cell at x, reads an x/z index as x,
and ignores an x/z write index; known writes commit at the edge and the
continuous read observes the committed cell.  Those choices follow the
SystemVerilog array-select and 4-state rules (IEEE 1800-2023 §§7.4, 11.5.1,
10.4 and 4.6).

The Lean receipt in `agree.lean` runs eleven rows at `N=32`, including the
first x state, two run-time writes, known reads, x/z reads, an x-index write,
and an x-valued write enable.  `check.py` compares the same rows with Icarus
Verilog 13.0 and Xcelium 24.03-s004; both report 11 rows MATCH E.

The ordinary `instantiateE2`/`Core0E` route still refuses the declaration as
`UnpackedDecl:memory`.  This packet therefore records the source-shaped E
memory behavior and requests integration of `MemState` into the canonical E
store separately; it does not claim that PicoRV32 executes through E yet.
