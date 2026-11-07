import LeanModels.Refine.RvfiRv32i
import Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary

/-!
# PicoRV32 unified RV32I RVFI boundary witness

The measured non-trapping PicoRV32 prefix is certified through the indexed
`Rv32iBoundary` dispatcher.  This keeps the concrete RVFI rows tied to the
threaded architectural post-state and retirement without claiming a symbolic
RTL invariant while the loader still refuses the upstream register memory.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_rv32i_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
open Examples.«system-verilog».cores.picorv32.trace_proof

theorem pinned_addi_unified :
    Rv32iBoundary (ArchState.init 0) addiInput addi1
      { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
        memory := addiInput.memory }
      (aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) := by
  exact RvfiObservation.addiBoundary_rv32i
    0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_store_unified :
    Rv32iBoundary storeState storeInput storeRaw
      { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
        memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }
      (memRetirement storeState storeInput (.store .word) 1 0 0x100) := by
  exact RvfiObservation.swBoundary_rv32i
    0x10102023 0 1 0x100 pinned_store_boundary

theorem pinned_load_unified :
    Rv32iBoundary loadState loadInput loadRaw
      { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
        memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }
      (memRetirement loadState loadInput (.load true .word) 2 0 0x100) := by
  exact RvfiObservation.lwBoundary_rv32i
    0x10002103 2 0 0x100 pinned_load_boundary

theorem pinned_addi2_unified :
    Rv32iBoundary addi2State addi2Input addi2Raw
      { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
        memory := addi2Input.memory }
      (aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact RvfiObservation.addiBoundary_rv32i
    0x00110193 3 2 1 pinned_addi2_boundary

theorem pinned_unified_boundary_window :
    Rv32iBoundary (ArchState.init 0) addiInput addi1
        { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
          memory := addiInput.memory }
        (aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) ∧
    Rv32iBoundary storeState storeInput storeRaw
        { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
          memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }
        (memRetirement storeState storeInput (.store .word) 1 0 0x100) ∧
    Rv32iBoundary loadState loadInput loadRaw
        { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
          memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }
        (memRetirement loadState loadInput (.load true .word) 2 0 0x100) ∧
    Rv32iBoundary addi2State addi2Input addi2Raw
        { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
          memory := addi2Input.memory }
        (aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact ⟨pinned_addi_unified, pinned_store_unified,
    pinned_load_unified, pinned_addi2_unified⟩

theorem pinned_unified_machine_commits :
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := ArchState.init 0, memory := addiInput.memory } addiInput =
      ({ arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
          memory := addiInput.memory },
        aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := storeState, memory := storeInput.memory } storeInput =
      (({ arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
          memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 } : RvMemoryState),
        memRetirement storeState storeInput (.store .word) 1 0 0x100) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := loadState, memory := loadInput.memory } loadInput =
      (({ arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
          memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 } : RvMemoryState),
        memRetirement loadState loadInput (.load true .word) 2 0 0x100) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := addi2State, memory := addi2Input.memory } addi2Input =
      ({ arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
          memory := addi2Input.memory },
        aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact ⟨pinned_addi_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_store_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_load_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_addi2_unified.rvMemoryMachineWith cv32e40pProfile⟩

/-! ## A finite core-facing cycle obligation -/

/-- A one-bit finite machine that emits the measured ADDI row once and then
stutters.  The input admission predicate below pins the measured parcel; the
machine shape is only a concrete consumer of the generic cycle constructor,
not a model of PicoRV32's blocked RTL. -/
def pinnedAddiCycleMachine : RvfiCycleMachine Bool where
  init := false
  step done _ :=
    if done then (true, bubbleObservation) else (true, addi1)

def pinnedAddiCycleRel (done : Bool) (state : RvMemoryState) : Prop :=
  if done then
    state =
      { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
        memory := addiInput.memory }
  else state = { arch := ArchState.init 0, memory := addiInput.memory }

def pinnedAddiCycleAdmit (input : Input) : Prop := input = addiInput

theorem pinned_addi_cycle_refines :
    RvfiCycleStepRefines pinnedAddiCycleMachine
      (rvMemoryMachineWith cv32e40pProfile)
      pinnedAddiCycleRel pinnedAddiCycleAdmit := by
  apply rvfiCycleStepRefines_of_rv32i_memory cv32e40pProfile
    pinnedAddiCycleMachine pinnedAddiCycleRel pinnedAddiCycleAdmit
  · rfl
  · intro state memoryState input hrel hadmit
    cases state with
    | false =>
        have hinput : input = addiInput := hadmit
        subst input
        have hmem : memoryState =
            { arch := ArchState.init 0, memory := addiInput.memory } := by
          simpa [pinnedAddiCycleRel] using hrel
        subst memoryState
        simp only [pinnedAddiCycleMachine]
        refine ⟨
          { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
            memory := addiInput.memory },
          aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5),
          by simp, pinned_addi_unified, ?_⟩
        simp [pinnedAddiCycleRel]
    | true =>
        simpa [pinnedAddiCycleMachine, bubbleObservation] using hrel

def pinnedAddiCycleInputs : List Input := [addiInput, addiInput]

def pinnedAddiCycleRetirements : List Retirement :=
  [aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)]

theorem pinned_addi_cycle_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedAddiCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs) =
      some pinnedAddiCycleRetirements := by
  decide

theorem pinned_addi_cycle_trace_refines :
    pinnedAddiCycleRetirements =
      trace (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs) := by
  exact rvfiCycleStepRefines_normalized_trace_refines
    pinned_addi_cycle_refines pinnedAddiCycleMachine.init
    (rvMemoryMachineWith cv32e40pProfile).init pinnedAddiCycleInputs
    (by rfl)
    (by
      intro input hinput
      simpa [pinnedAddiCycleInputs, pinnedAddiCycleAdmit] using hinput)
    pinned_addi_cycle_observations_normalize

theorem pinned_addi_cycle_normalized_refines :
    (pinnedAddiCycleRetirements =
      trace (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs)) ∧
    pinnedAddiCycleRel
      (rvfiStateAfter pinnedAddiCycleMachine
        pinnedAddiCycleMachine.init pinnedAddiCycleInputs)
      (machineStateAfter (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs)) := by
  exact rvfiCycleStepRefines_normalized
    pinned_addi_cycle_refines pinnedAddiCycleMachine.init
    (rvMemoryMachineWith cv32e40pProfile).init pinnedAddiCycleInputs
    (by rfl)
    (by
      intro input hinput
      simpa [pinnedAddiCycleInputs, pinnedAddiCycleAdmit] using hinput)
    pinned_addi_cycle_observations_normalize

#print axioms pinned_addi_unified
#print axioms pinned_store_unified
#print axioms pinned_load_unified
#print axioms pinned_addi2_unified
#print axioms pinned_unified_boundary_window
#print axioms pinned_unified_machine_commits
#print axioms pinned_addi_cycle_refines
#print axioms pinned_addi_cycle_observations_normalize
#print axioms pinned_addi_cycle_trace_refines
#print axioms pinned_addi_cycle_normalized_refines

end Examples.«system-verilog».cores.picorv32.rvfi_rv32i_boundary
