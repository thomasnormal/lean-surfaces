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

The scalar `instantiateE2`/`Core0E` process route still refuses the declaration
as `UnpackedDecl:memory`.  The canonical E entry now attaches the source-shaped
`MemEDesign` beside that scalar store, and the receipt runs its memory state
through `Elab.memoryInitial`/`Elab.memoryStep`; the scheduler's array-valued
store remains a separate reviewed widening step, so this does not yet claim
that PicoRV32 executes through the ordinary scalar E process loop.
