import LeanModels.Refine.RvfiUpperMixed
import LeanModels.Refine.RvfiProgress

/-!
# Mixed-step packaging for an upper-immediate invariant

`RvfiUpperMixed` gives the LUI/AUIPC per-cycle bridge.  This file packages the
two dependent obligations a loaded-core proof carries at every cycle, so the
same invariant can be handed to the generic mixed RV32I reset contracts.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The local obligations for a LUI/AUIPC-only loaded-core invariant.

The step field retains the decoded `UpperInstruction` witness and its
memory-threaded post-state.  The order field remains separate because the raw
RVFI observation does not assign a retirement index by itself.
-/
structure Rv32iUpperInvariant {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop) : Prop where
  step : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
    rel state memoryState → admit input →
    let (state', observation) := machine.step state input
    if observation.valid then
      ∃ instruction : UpperInstruction,
        input.memory = memoryState.memory ∧
        observation.upperBoundary memoryState.arch input instruction ∧
        rel state'
          { arch := UpperKind.next memoryState.arch instruction.kind,
            memory := memoryState.memory }
    else rel state' memoryState
  order : ∀ (start : Nat) (state : State)
    (memoryState : RvMemoryState) (input : Input),
    rel state memoryState → admit input →
    let (_, observation) := machine.step state input
    if observation.valid then observation.order = start else True

/-- The packaged upper-immediate invariant discharges the unified mixed
per-cycle obligation. -/
theorem Rv32iUpperInvariant.toMixedStep
    {State : Type} {machine : RvfiCycleMachine State}
    {rel : State → RvMemoryState → Prop} {admit : Input → Prop}
    (invariant : Rv32iUpperInvariant machine rel admit) :
    Rv32iCycleStepRefines machine rel admit := by
  exact rv32iCycleStepRefines_of_upper_memory machine rel admit
    invariant.step invariant.order

#print axioms LeanModels.Refine.Rv32iUpperInvariant.toMixedStep

end LeanModels.Refine
