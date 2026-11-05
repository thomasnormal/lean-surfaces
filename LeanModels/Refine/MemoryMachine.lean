import LeanModels.Refine.Commit

/-!
# Stateful RISC-V memory at the commit boundary

`Machine` keeps the always-ready memory view in `Input` because that is the
smallest contract for a commit observation.  A real core instead carries the
architectural memory across instructions.  This adapter gives that stateful
shape without changing `Retirement` or the stateless trace theorem: a
`RvMemoryState` stores the ISA state and byte memory, and `threadRvInputs`
materializes the memory view that the stateless machine would have seen at
each step.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- Architectural state plus the byte-addressed memory at the commit point. -/
structure RvMemoryState where
  arch : ArchState
  memory : Memory

/-- A profile-parametric machine that threads stores through its memory state.
The `Input.memory` field is ignored by the stateful machine; it is overwritten
only when constructing its retirement observation. -/
def rvMemoryMachineWith (profile : PlatformProfile) : Machine RvMemoryState where
  init := { arch := ArchState.init 0, memory := fun _ => 0 }
  step state input :=
    let (arch', effects) := isaStepWith profile state.arch state.memory
      input.fetched input.irq
    let observedInput := { input with memory := state.memory }
    ({ arch := arch', memory := applyMemEffect state.memory effects.mem },
      Retirement.ofRvStep state.arch observedInput arch' effects)

/-- Replace each scheduled input's memory view with the stateful memory that
precedes it, then thread the ISA state and memory to the next input. -/
def threadRvInputs (profile : PlatformProfile) : ArchState → Memory → List Input → List Input
  | _, _, [] => []
  | arch, memory, input :: inputs =>
      let (arch', effects) := isaStepWith profile arch memory input.fetched input.irq
      { input with memory := memory } ::
        threadRvInputs profile arch' (applyMemEffect memory effects.mem) inputs

/-- The stateful memory machine and the stateless adapter agree after the
schedule is normalized to the memory that preceded each instruction. -/
theorem rvMemoryMachine_trace (profile : PlatformProfile) (arch : ArchState)
    (memory : Memory) (inputs : List Input) :
    trace (rvMemoryMachineWith profile) { arch := arch, memory := memory } inputs =
      trace (rvMachineWith profile) arch (threadRvInputs profile arch memory inputs) := by
  induction inputs generalizing arch memory with
  | nil => rfl
  | cons input inputs ih =>
      simp only [trace, rvMemoryMachineWith, rvMachineWith, threadRvInputs]
      generalize hstep : isaStepWith profile arch memory input.fetched input.irq = step
      rcases step with ⟨arch', effects⟩
      have htail := ih arch' (applyMemEffect memory effects.mem)
      congr 1

end LeanModels.Refine

#print axioms LeanModels.Refine.rvMemoryMachine_trace
