# Step 12: one-rank unpacked storage in E

This note is the handoff for the one-rank unpacked-array shape used by a
parameterized register file such as `logic [W-1:0] cpuregs [P]`.  It describes
the canonical E route; it does not introduce a cycle model or a second store.

## Admission and representation

Slang's `UnpackedDecl` is retained as a source declaration.  At a concrete
parameter point, `PDecl.memShape?` evaluates the packed element width and the
unpacked bounds, and `MemShape` keeps the declaration name, element width and
source labels.  `MemState.ofShapes` creates one native memory object per
declaration.  It does not make one scalar declaration per cell and does not
unroll a parameterized bound.  Nested ranks, zero-width elements and shapes
that cannot be evaluated are loud refusals at `MemElab`.

The complete canonical state is `CoreMemState`, with the existing scalar
`Store` and one `MemState`.  `CoreMemDesign.initial` initializes both from the
same source-shaped declarations.  Scalar views are only a name-facing view
used while evaluating a body; `storeFromView` compacts that view back into the
authoritative scalar store at process boundaries.  There is no scalar-memory
coercion and no parallel `MemE` meaning.

## Reads and writes

An `ArraySel`/`PLhs.arrayElem` with exactly one index is evaluated at run time.
The index is converted to an `Int` and passed to `MemState.readIndexId` or
`MemState.writeTarget`; the source declaration supplies the label range.  A
known in-range index reads or writes that cell.  A known out-of-range read is
the all-x element required by IEEE 1800-2023 §§7.4.5 and 7.4.6, and an
out-of-range write has no effect (§11.5.1).  An x or z index is not guessed or
collapsed to a simulator choice: the native memory operation returns the
four-state result prescribed by the E memory boundary.  Partial array
targets, nested ranks and non-cell memory expressions refuse by name.

The index remains symbolic in the source AST and is evaluated when the
assignment executes.  Thus a `for (int i = 1; i < P; i++)` body is retained as
`PStmt.forLoop`; its runtime trip values issue one cell operation per
iteration.  No parameter-sized loop is expanded at elaboration.

## NBA timing and scheduling

For an edge process, the right-hand side and index are evaluated from the
pre-edge `CoreMemState`.  Cell updates are placed in the existing
`MemState.issueNba` queue, then committed once in the NBA region.  A scalar
NBA uses the same source-shaped queue and scalar destination width; it is not
represented as a memory cell.  Continuous assignments and `always_comb`
settle after the commit through the ordinary E fixed-point pass.  The edge,
NBA and settle order is the canonical E schedule, so the route preserves
IEEE 1800-2023 §§4.6, 9.4 and 10.4 rather than selecting a convenient order.

## Unknown and out-of-range cases

The memory object starts with the declaration's exact four-state initial value.
Known writes replace one cell; other cells are preserved.  An unknown index,
an out-of-range index and an uninitialized cell remain observable through the
same `LVec`/`Logic` operations as scalar E values.  The route never binds one
power-up unknown to a shared value or silently turns an x/z decision into a
Boolean branch.

## MemE status

The older `Kernel/MemE` and `MemCycle` files are compatibility and measurement
surfaces only.  New storage work belongs in `Kernel/MemElab.lean` and
`Kernel/CoreMemExec.lean`.  Any remaining MemE receipt must be justified by a
refinement theorem back to `CoreMemDesign.step`; it is not a second semantics
for users.  The next implementation gate is a loaded parameterized storage
design running through `CoreMemDesign.initialState` and `CoreMemDesign.step`,
with simulator rows at two parameter points and x/z index probes.
