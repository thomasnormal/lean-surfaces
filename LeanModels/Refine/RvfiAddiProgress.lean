import LeanModels.Refine.RvfiAddiMixed
import LeanModels.Refine.RvfiProgress

/-!
# From-reset stream refinement for an ADDI-only invariant

The ADDI invariant bridge and the generic progress theorem are useful on
their own, but a first core proof should be able to state the complete
from-reset contract in one place.  This theorem composes those two pieces:
the per-cycle ADDI boundary plus explicit order premise supplies the mixed
step obligation, and the independent progress witness supplies every finite
target prefix.

No target schedule is synthesized here.  As in the generic theorem, the
caller provides the admitted schedule and its progress witness.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The local obligations for an ADDI-only loaded-core invariant.

The step field describes the memory-threaded ADDI boundary and post-state;
the order field supplies the RVFI order tag separately.  Keeping them in one
named proposition lets a core proof carry its invariant without repeating the
dependent cycle-step predicates at every reset theorem call.
-/
structure Rv32iAddiInvariant {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop) : Prop where
  step : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
    rel state memoryState → admit input →
    let (state', observation) := machine.step state input
    if observation.valid then
      ∃ w rd rs1 imm,
        input.memory = memoryState.memory ∧
        observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
        rel state'
          { arch := addiNext memoryState.arch rd rs1 imm,
            memory := memoryState.memory }
    else rel state' memoryState
  order : ∀ (start : Nat) (state : State)
    (memoryState : RvMemoryState) (input : Input),
    rel state memoryState → admit input →
    let (_, observation) := machine.step state input
    if observation.valid then observation.order = start else True

/-- The packaged ADDI invariant discharges the unified mixed per-cycle
obligation. -/
theorem Rv32iAddiInvariant.toMixedStep
    {State : Type} {machine : RvfiCycleMachine State}
    {rel : State → RvMemoryState → Prop} {admit : Input → Prop}
    (invariant : Rv32iAddiInvariant machine rel admit) :
    Rv32iCycleStepRefines machine rel admit := by
  exact rv32iCycleStepRefines_of_addi_memory machine rel admit
    invariant.step invariant.order

/-- The ADDI-only invariant establishes the full structure-valued reset
refinement, retaining the decoded program and cycle certificate at every
target prefix. -/
theorem rv32i_reset_addi_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          input.memory = memoryState.memory ∧
          observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
          rel state'
            { arch := addiNext memoryState.arch rd rs1 imm,
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
    (rv32iCycleStepRefines_of_addi_memory machine rel admit hstep horder)
    hinit hschedule progress

/-- Packaged-invariant form of the full ADDI reset contract. -/
theorem rv32i_reset_addi_refines_of_invariant
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (invariant : Rv32iAddiInvariant machine rel admit)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    Rv32iResetRefinement profile machine rel schedule target := by
  exact rv32i_reset_addi_refines profile machine rel admit hinit
    invariant.step invariant.order hschedule progress

/-- An order-aware, memory-threaded ADDI invariant refines every finite target
retirement prefix from reset through the public committed-stream contract. -/
theorem rv32i_reset_addi_stream_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          input.memory = memoryState.memory ∧
          observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
          rel state'
            { arch := addiNext memoryState.arch rd rs1 imm,
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
    (rv32iCycleStepRefines_of_addi_memory machine rel admit hstep horder)
    hinit hschedule progress

/-- Packaged-invariant form of the direct committed-stream reset contract. -/
theorem rv32i_reset_addi_stream_refines_of_invariant
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (invariant : Rv32iAddiInvariant machine rel admit)
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
  exact rv32i_reset_addi_stream_refines profile machine rel admit hinit
    invariant.step invariant.order hschedule progress

#print axioms LeanModels.Refine.rv32i_reset_addi_stream_refines
#print axioms LeanModels.Refine.rv32i_reset_addi_refines
#print axioms LeanModels.Refine.Rv32iAddiInvariant.toMixedStep
#print axioms LeanModels.Refine.rv32i_reset_addi_refines_of_invariant
#print axioms LeanModels.Refine.rv32i_reset_addi_stream_refines_of_invariant

end LeanModels.Refine
