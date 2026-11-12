# E Step 12: one-rank unpacked memory in the canonical store

This note fixes the representation boundary for a one-rank unpacked
declaration such as

```systemverilog
logic [31:0] cpuregs [0:N-1];
assign rdata = cpuregs[raddr];
always_ff @(posedge clk) if (we) cpuregs[waddr] <= wdata;
```

The declaration remains one source node with its packed element type and
unpacked bounds. Elaboration evaluates the bounds at the parameter point and
creates one typed memory object keyed by the declaration identity. It does not
expand the cells into scalar declarations, generate assignments, or a second
process AST. This is the canonical E store/design view; the current
source-shaped MemE profile is a temporary adapter and is retired or proved a
derived view when this boundary lands.

## State and initialization

The canonical state has the existing typed scalar store beside a memory store.
Each memory entry carries its source declaration identity, element width,
signedness, two-state flag, and inclusive label range. A four-state cell that
has not been written starts as all x; an undriven net keeps its separate all-z
startup rule. A two-state element applies the IEEE 1800-2023 §6.11 x/z to zero
conversion at initialization and on every assignment. The declaration's
packed element width is checked before the memory object is created; zero-width
elements, unresolved bounds, and ranks greater than one are named refusals.

The memory object is keyed by the structured declaration identity, never by a
flattened cell name. A source path or generated scope therefore identifies the
object even when two instances use the same declaration spelling. A memory
object is not visible through scalar name lookup except through the
source-shaped array expression.

## Reads and writes

For `PExpr.arrayElem` with one index, E evaluates the index in the current
source view and converts it with the signed index rule of IEEE 1800-2023
§11.5.1. An x/z index or an index outside the declared label range returns an
all-x element and performs no write. A valid index reads exactly one cell. The
index expression itself remains part of the read set. A plain `always @*`
therefore wakes for a change to the selected cell or to a signal used by its
index, but not for an unrelated cell (§9.4.2.2.2).

A blocking array assignment updates the selected cell in the Active region.
An unknown or out-of-range index is a no-op after the RHS has been evaluated.
For a nonblocking assignment, §10.4.2 fixes both the RHS value and the index
when the statement issues. The NBA record carries the memory identity, the
resolved cell label, and the converted element value; the commit phase applies
records in issue order, so a later write to the same cell wins. The commit does
not re-evaluate an index, a parameter, or the RHS. The same rule applies when
a packed element is assigned through a selected memory cell; dynamic
concatenated targets and memory slices remain outside this step.

Continuous scalar drivers and memory-cell reads use the same Active settling
view. A source-order chain in which an earlier driver reads a signal written by
a later driver is refused until the canonical settling theorem covers it; the
E store must never return the stale one-pass value (§§4.5, 10.3).

## Scheduler boundary

E keeps process atomicity: an activation has one source-shaped body and no
suspension point. A combinational activation settles its scalar and memory
blocking writes before the next ready process is chosen. An edge activation
samples its pre-edge view, issues scalar and memory NBAs, and commits them in
the NBA region. A committed memory cell change reactivates a waiting
`always @*` process when that cell is in its source read set. An activation
does not wake itself from an internal write before its body completes.

This scheduler rule is derived from E's existing Active/NBA regions; it adds no
fuel, schedule choice, x-resolution relation, `Stmt2` constructor, or run2 or
MemCycle meaning. Cycle views and contracts must use the canonical memory
transition and carry their usual refinement theorem back to E.

## Admission and proof obligations

The first admitted shape is one unpacked rank, scalar packed elements, a
runtime read index, and a runtime NBA write index. The following remain loud:

* nested or multi-rank unpacked storage, array slices and whole-memory
  assignments;
* dynamic concatenated targets, unsupported index expressions, and a memory
  read embedded in an unsupported expression;
* automatic or block-local memory declarations, until scoped storage has its
  own E frame;
* self-retriggering combinational memory processes and continuous-driver
  cycles without a settling certificate.

The implementation must prove that scalar-only designs are the old E design
under projection, that a memory-free process never consults memory state, and
that the memory transition agrees with the source-shaped MemE rows. The
memory read/write lemmas must cover valid, x/z, negative, and out-of-range
indices, two-state conversion, old-state RHS sampling, overlapping NBA issue
order, and sensitivity to the selected cell. Every theorem is over E's exact
semantics; simulator traces are differential evidence, not a definition.

The existing `unpacked_cpuregs_e` receipt supplies the first 11 rows: startup
x cells, known indexed reads and writes, x/z indices, an x-index write, and an
x write-enable. Its Icarus Verilog 13.0 and Xcelium 24.03-s004 traces remain
the acceptance oracle while the canonical entry is implemented. No whole
PicoRV32 execution or retirement theorem is claimed by this note.
