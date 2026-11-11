# Retirement safety over E

[`LeanModels/Refine/RvfiE.lean`](../LeanModels/Refine/RvfiE.lean) proves
`RvfiE.safe_of_invariant` over E's `ESig` / `Obs_E` interface. **Status:
derived, conditional on a loaded-core invariant.** No real core or R2 rung is
certified by this bridge alone.

The conclusion is `SafeOn`: for every E choice, admitted disciplined
environment and completed behaviour, all observed cycles decode and the
ordered retirement stream equals the current stateful RV32I model's stream
for a witnessed mixed program. The theorem reuses `Rv32iRvfiTrace` and its
existing ISA agreement theorem. It introduces no SV executor, statement
syntax, instruction decoder or alternative ISA step.

The loaded-core proof supplies three concrete things:

- A partial decoder of the actual RVFI ports in the trusted cycle samples.
  A failed decode is `none`; a successfully decoded invalid row is a bubble.
  The decoder is an explicit parameter here. The concrete one-channel
  [`RvfiPorts.decodePost`](../LeanModels/Refine/RvfiPorts.lean) adapter below
  supplies the non-trapping RV32 slice; its connection to a loaded core
  remains an invariant obligation.
- A relation indexed by retirement order, with initialization proved on
  every admitted E run. The initial memory and environment admission remain
  explicit, including any reset and memory protocol requirements.
- `RvfiE.StepRefines` on each cycle interval of each such run. A valid row
  gives an existing mixed RV32I instruction boundary, the current order tag,
  and the next related ISA state. A bubble keeps the order and ISA state.

The interval starts at the preceding cycle's post sample, or at the first
pre sample for the initial cycle, and ends at the current cycle's post
sample. Thus the invariant must cover the intervening E steps as well as
the edge itself. It cannot assume that one source process or one NBA commit
constitutes a complete cycle. Internal configurations are proof cut points;
the observable conclusion sees only declared ports.

The proof walks `List.range (E.cycles env)` in ascending order. It retains
every decoded row, including bubbles, before applying the existing RVFI
normalizer. Failure to decode a row cannot silently remove that cycle.

Completion of E runs and progress toward each requested retirement prefix
remain separate obligations. `SafeOn` by itself admits empty behaviours and
is not an all-prefix liveness theorem. The current stateful RV32I adapter
and its existing official-model validation obligations also remain as
recorded; this change supplies no new Sail agreement theorem.

## Concrete port adapter

`RvfiPorts` reads the standard single-channel signal names with a caller-supplied
prefix (`"rvfi_"` conventionally), `ILEN = XLEN = 32`, and a 64-bit order.
`readBits_eq_some_iff` requires the exact declared width and every source bit
known; `readBits_ofBitVec` proves preservation for arbitrary known vectors.
The conversion uses a width equality, never a resize. `decode_valid` proves
that a successfully decoded row has the actual known valid bit. Thus an
undecodable active row cannot become a bubble or disappear from `decodeSamples`.

The wire contract is pinned to [riscv-formal c992aa61](https://github.com/YosysHQ/riscv-formal/blob/c992aa61fdfe0846c5ed90324c596202a1c69b76/docs/source/rvfi.rst),
sections “Instruction metadata”, “Integer register read/write”, “Program
counter” and “Memory access”. It gives invalid cycles arbitrary payloads, so
the adapter reads only `valid` on a bubble and returns a canonical invalid
record. Those canonical payloads describe no hardware value and no retirement.
For valid cycles the adapter conservatively requires even unused payloads to
be known. It preserves the raw register, address, mask and memory-data fields;
it does not shift aligned masks or infer missing data. The existing
machine-mode, RV32 and canonical-mask guard remains in force. This is a
partial decoder, not a complete checker for all RVFI obligations.

Standard RVFI has no `rd_wdata_valid` signal. The adapter derives that field
from `rd_addr != 0`: zero denotes either no destination or x0, neither of
which changes architectural registers. The order becomes a `Nat` without
discarding its upper 32 bits. Finite order wraparound cannot silently satisfy
the existing consecutive-order normalizer.

This adapter refuses active `trap`, `halt` and `intr` flags. RVFI supplies no
precise cause port, and `intr` marks the first instruction of a trap handler,
not the cause of the trapping instruction. Reusing the old `causeWellFormedB`
interpretation on arbitrary wire rows would require a separate reviewed
contract. No cause is inferred from an instruction word. Trap handling,
aligned-memory mode, rollback and other RVFI extensions remain outside this
adapter's contract.

`decodePost` selects registered outputs at the trusted post-cycle sample.
The actual loaded-core invariant must justify this timing convention. The
codec's synthetic field/refusal checks and its actual `E1` bridge typecheck
are in [`cores/picorv32/rvfi_ports.lean`](../Examples/system-verilog/cores/picorv32/rvfi_ports.lean).
These checks claim neither simulator execution nor a PicoRV32 invariant.

## Existing contract findings

The older `R2Headline` helpers are not used by this bridge. Two issues need
explicit migration analysis before those helpers are used for a real core:

1. `Progress.schedulePrefix` prepends `schedule n` to the shorter prefix.
   For the identity schedule its length-three result is `[2, 1, 0]`. Reading
   that list as a chronological execution reverses the program.
2. `Rv32iCycleStepRefines` quantifies an arbitrary order while its state
   relation has no order index. Applying the premise at orders zero and one
   to the same related state and admitted input forces the same valid row's
   order to be both zero and one. Consequently the premise implies every
   such transition is a bubble. The old headline therefore cannot support
   a real retiring core under those hypotheses.

Both findings were checked in Lean, including a general proof of the
second implication with only `propext`, `Classical.choice` and `Quot.sound`.
The existing statements are retained unchanged for review. The E bridge
uses the chronological range and an order-indexed relation from the start.

## Observation-interface integration

The bridge imports `Sv.Observe`, the interface currently imported by the
clocked E backend `Kernel.Core1Obs`. Its theorem uses only E's signature and
observations. That module still contains legacy interpreter transports;
none is used as a meaning or as a proof premise here.

At this base, importing `Sv.ObserveE` beside `Kernel.Core1Obs` fails because
both `Observe` and `ObserveE` define the same observation names. Similarly,
`Kernel.Core0` and `Kernel.Core0E` still duplicate the same kernel
definitions in separate import cones. These are migration handoff issues
reported to the owner. This change neither adds another copy nor edits
the shared interface. The E0-only cone cannot import this clocked-interface
bridge until that duplication is removed.

```sh
LEAN_NUM_THREADS=2 nice -n 19 lake build LeanModels.Refine.RvfiE
LEAN_NUM_THREADS=2 nice -n 19 lake build LeanModels.Refine.RvfiPorts \
  'Examples.«system-verilog».cores.picorv32.rvfi_ports'
```

The new theorem's axiom audit contains only the standard three axioms.
There is no simulator claim: this item changes a proof bridge, not SV
execution. Native `@*`, scoped blocking locals, mixed scheduling and E
memory execution remain separate implementation obligations.

## E-core-0 unification handoff

The E migration currently has two physically separate definitions of the
same core-0 names. `Kernel/Core0.lean` imports `Comb2`, while
`Kernel/Core0E.lean` imports `CombEBase` and `Param2`; both define `Seg`,
`VarId`, `VType`, `Val`, `Store`, `Proc0`, `Elab`, `Config`, `step`, and
`SlotCloses`. The E file is the correct authority: it is used by the E
executors and retains the parser's `always @*` node as `Proc0.implicit` with
its distinct startup and raw-read sensitivity rules. `Core0Comb`,
`Core0Proc`, and the E edge consumers should therefore be rebased onto
`Core0E`; `Core0.lean` should become a compatibility import with no
definitions. `Core0Comb` should import `Comb2` directly for its legacy
transport theorems instead of receiving it through the old core file. This
keeps the E definitions source-shaped and leaves the old `combSettle2`
transport as a derived bridge while it is being retired.

The observation collision needs a separate interface step. `Kernel/Core0Obs`
currently owns the long E-to-`run2` transport and defines `Behaves0`, `E0`,
and `Obs_E0` over `Observe`; `Kernel/Obs_E0` defines those names again over
`ObserveE`. Importing both cones is therefore impossible even though the
names describe the same E backend. The migration order is:

1. Extract the interface-only declarations (`Iface`, `ESig`, `Obs_E`, and
   the observation records) into one run2-free `ObserveBase` module. Make
   `Observe` the compatibility module for the legacy `Obs_run2` backend and
   make `ObserveE` the compatibility module for E-specific consumers; neither
   compatibility module may redeclare the base names.
2. Keep `Kernel/Obs_E0` as the canonical E-core-0 backend. Move its
   `Behaves0`/`E0` definitions into the unified file, and change
   `Kernel/Core0Obs` into the transport layer that imports that backend plus
   the legacy `Obs_run2` compatibility module. Its theorem names and the
   conditional E-to-`run2` statements remain source-compatible during the
   run2 retirement.
3. Delete the compatibility declarations from `Core0.lean` and
   `Core0Obs.lean` only after the E-only cone (`RunE`, `Core1Obs`, and the
   E-side refinement bridge) and the legacy transport cone each build from a
   fresh checkout. The duplicate names disappear rather than being hidden
   behind import order.

The measured proof ergonomics issue in the current E-only cone is independent
of the merge: `Obs_E0.Design` does not reduce to `Elab`, so `rw`/`simp` can
fail at `Obs_E0.sample E st`. The base interface should mark `Obs_E` (or the
canonical `Obs_E0` abbreviation) `@[reducible]`; if that exposes too much
structure, add named `sample`/`step` simplification lemmas instead. This is a
small proof-surface change, not a second observation semantics.

Two follow-up provenance questions from the owner are not yet implemented.
The JSON envelope already carries `source_sha256`, but `load_design_sv2` only
reads the envelope and never verifies the source bytes named by that field; a
future hash-pinned load form belongs in the ingestion/provenance backlog and
must fail closed on a missing or mismatched source. Likewise,
`PInst.pathPrefix` currently includes the Slang generate label and the current
genvar value (`g[3].`), and `Design2.namesNodup` checks one flattened
parameter point, but there is no separate stable identity/receipt proving
distinct generated names across all parameter points. That generated-name
audit belongs after the core-0 merge and before relying on hierarchy names in
the R2 proof; it must preserve the parser's path and refuse a collision
rather than inventing a suffix.

The implementation order is therefore: **(i)** canonicalize `Core0E` and
rebase `Core0Comb`/`Core0Proc`; **(ii)** extract `ObserveBase` and consolidate
`Obs_E0`; **(iii)** add the reducibility/simp surface; **(iv)** add source-hash
verification and a quantified generated-name collision check. No shared
judgment, resolution relation, `Stmt2`, `DecisionKnown`, or run2 meaning is
changed by this handoff document.
