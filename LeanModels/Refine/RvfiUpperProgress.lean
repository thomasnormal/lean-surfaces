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

/-- The upper-immediate invariant establishes the full structure-valued reset
refinement, retaining the decoded program and cycle certificate at every
target prefix. -/
theorem rv32i_reset_upper_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ instruction : UpperInstruction,
          input.memory = memoryState.memory ∧
          observation.upperBoundary memoryState.arch input instruction ∧
          rel state'
            { arch := UpperKind.next memoryState.arch instruction.kind,
              memory := memoryState.memory }
      else rel state' memoryState)
    (horder : ∀ (start : Nat) (state : State)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (_, observation) := machine.step state input
      if observation.valid then observation.order = start else True)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    Rv32iResetRefinement profile machine rel schedule target := by
  exact rv32i_reset_refinement profile machine rel admit
    (rv32iCycleStepRefines_of_upper_memory machine rel admit hstep horder)
    hinit hschedule progress

/-- Packaged-invariant form of the full upper-immediate reset contract. -/
theorem rv32i_reset_upper_refines_of_invariant
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (invariant : Rv32iUpperInvariant machine rel admit)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    Rv32iResetRefinement profile machine rel schedule target := by
  exact rv32i_reset_upper_refines profile machine rel admit hinit
    invariant.step invariant.order hschedule progress

/-- Direct committed-stream form of the upper-immediate reset contract. -/
theorem rv32i_reset_upper_stream_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ instruction : UpperInstruction,
          input.memory = memoryState.memory ∧
          observation.upperBoundary memoryState.arch input instruction ∧
          rel state'
            { arch := UpperKind.next memoryState.arch instruction.kind,
              memory := memoryState.memory }
      else rel state' memoryState)
    (horder : ∀ (start : Nat) (state : State)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (_, observation) := machine.step state input
      if observation.valid then observation.order = start else True)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    ∀ k : Nat, ∃ boundary : Nat,
      cycleTrace machine.toCycleMachine machine.init
          (schedulePrefix schedule boundary) =
        trace (rvMemoryMachineWith profile)
          (rvMemoryMachineWith profile).init (schedulePrefix target k) ∧
      rel (rvfiStateAfter machine machine.init
          (schedulePrefix schedule boundary))
        (rvMemoryStateAfter profile (rvMemoryMachineWith profile).init
          (schedulePrefix target k)) := by
  exact rv32i_reset_stream_refines profile machine rel admit
    (rv32iCycleStepRefines_of_upper_memory machine rel admit hstep horder)
    hinit hschedule progress

/-- Packaged-invariant form of the direct upper-immediate stream contract. -/
theorem rv32i_reset_upper_stream_refines_of_invariant
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (invariant : Rv32iUpperInvariant machine rel admit)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    ∀ k : Nat, ∃ boundary : Nat,
      cycleTrace machine.toCycleMachine machine.init
          (schedulePrefix schedule boundary) =
        trace (rvMemoryMachineWith profile)
          (rvMemoryMachineWith profile).init (schedulePrefix target k) ∧
      rel (rvfiStateAfter machine machine.init
          (schedulePrefix schedule boundary))
        (rvMemoryStateAfter profile (rvMemoryMachineWith profile).init
          (schedulePrefix target k)) := by
  exact rv32i_reset_upper_stream_refines profile machine rel admit hinit
    invariant.step invariant.order hschedule progress

#print axioms LeanModels.Refine.Rv32iUpperInvariant.toMixedStep
#print axioms LeanModels.Refine.rv32i_reset_upper_refines
#print axioms LeanModels.Refine.rv32i_reset_upper_refines_of_invariant
#print axioms LeanModels.Refine.rv32i_reset_upper_stream_refines
#print axioms LeanModels.Refine.rv32i_reset_upper_stream_refines_of_invariant

end LeanModels.Refine
