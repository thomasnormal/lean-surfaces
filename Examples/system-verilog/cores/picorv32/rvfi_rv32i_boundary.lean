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

theorem pinned_addi_unified :
    Rv32iBoundary (ArchState.init 0) addiInput addi1
      { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
        memory := addiInput.memory }
      (aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) := by
  apply Rv32iBoundary.alu 0x00500093 .add 1 (.reg 0) (.imm 5)
  simpa [RvfiObservation.addiBoundary, RvfiObservation.aluBoundary,
    RvfiObservation.addiFields, RvfiObservation.aluFields,
    aluSrc1Fields, aluSrc2Fields, addiNext, aluNext,
    addiRetirement, aluRetirement, addiEffects, aluEffects,
    src1Val, src2Val, aluSem,
    and_assoc] using pinned_addi_boundary

theorem pinned_store_unified :
    Rv32iBoundary storeState storeInput storeRaw
      { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
        memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }
      (memRetirement storeState storeInput (.store .word) 1 0 0x100) := by
  apply Rv32iBoundary.mem 0x10102023 (.store .word) 1 0 0x100
  unfold RvfiObservation.memBoundary RvfiObservation.memFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_load_unified :
    Rv32iBoundary loadState loadInput loadRaw
      { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
        memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }
      (memRetirement loadState loadInput (.load true .word) 2 0 0x100) := by
  apply Rv32iBoundary.mem 0x10002103 (.load true .word) 2 0 0x100
  unfold RvfiObservation.memBoundary RvfiObservation.memFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_addi2_unified :
    Rv32iBoundary addi2State addi2Input addi2Raw
      { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
        memory := addi2Input.memory }
      (aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  apply Rv32iBoundary.alu 0x00110193 .add 3 (.reg 2) (.imm 1)
  simpa [RvfiObservation.addiBoundary, RvfiObservation.aluBoundary,
    RvfiObservation.addiFields, RvfiObservation.aluFields,
    aluSrc1Fields, aluSrc2Fields, addiNext, aluNext,
    addiRetirement, aluRetirement, addiEffects, aluEffects,
    src1Val, src2Val, aluSem,
    and_assoc] using pinned_addi2_boundary

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

#print axioms pinned_addi_unified
#print axioms pinned_store_unified
#print axioms pinned_load_unified
#print axioms pinned_addi2_unified
#print axioms pinned_unified_boundary_window
#print axioms pinned_unified_machine_commits

end Examples.«system-verilog».cores.picorv32.rvfi_rv32i_boundary
