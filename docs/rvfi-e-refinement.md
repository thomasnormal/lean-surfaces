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
  The decoder is an explicit parameter here, not a proved wire adapter.
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
```

The new theorem's axiom audit contains only the standard three axioms.
There is no simulator claim: this item changes a proof bridge, not SV
execution. Native `@*`, scoped blocking locals, mixed scheduling and E
memory execution remain separate implementation obligations.
