import LeanModels.Refine.RvfiMem
import Examples.«system-verilog».cores.picorv32.rvfi_proof
import Examples.«system-verilog».cores.picorv32.trace_proof

/-!
# PicoRV32 raw RVFI SW boundary witness

This is the measured `sw x1, 0x100(x0)` row after the first ADDI.  The
architectural state is threaded through the existing ISA machine, then the
raw memory write is connected to the exact profile-parametric store step.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.trace_proof

def storeRaw : RvfiObservation :=
  { store1 with rs1Addr := 0, rs1Rdata := 0, rs2Addr := 1, rs2Rdata := 5, rdWdataValid := false }

def storeInput : Input :=
  { fetched := .word 0x10102023, memory := memZero, irq := 0 }

def storeState : ArchState :=
  machineStateAfter rvMachine (ArchState.init 0) (nontrapInputs.take 1)

theorem pinned_store_state :
    storeState.pc = 4 ∧ storeState.readReg 1 = 5 ∧
      storeState.readReg 0 = 0 := by
  decide

theorem pinned_store_boundary :
    RvfiObservation.swBoundary storeState storeInput storeRaw
      0x10102023 0 1 0x100 := by
  unfold RvfiObservation.swBoundary RvfiObservation.swFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_store_memory :
    isaStepMemWith cv32e40pProfile storeState storeInput.memory
      storeInput.fetched storeInput.irq =
      (swNext storeState, storeVal storeInput.memory .word 0x100 5) := by
  exact RvfiObservation.swBoundary_isaStepMemWith
    cv32e40pProfile storeRaw storeState storeInput
      0x10102023 0 1 0x100 pinned_store_boundary

theorem pinned_store_machine_commit :
    (rvMachineWith cv32e40pProfile).step storeState storeInput =
      (swNext storeState,
        swRetirement storeState storeInput 0 1 0x100) := by
  exact RvfiObservation.swBoundary_rvMachineWith
    cv32e40pProfile storeRaw storeState storeInput
      0x10102023 0 1 0x100 pinned_store_boundary

theorem pinned_store_stateful_machine_commit :
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := storeState, memory := storeInput.memory } storeInput =
      ({ arch := swNext storeState,
          memory := storeVal storeInput.memory .word 0x100 5 },
        swRetirement storeState storeInput 0 1 0x100) := by
  exact RvfiObservation.swBoundary_rvMemoryMachineWith
    cv32e40pProfile storeRaw storeState storeInput
      0x10102023 0 1 0x100 pinned_store_boundary

#guard storeInput.fetched = .word 0x10102023
#guard storeRaw.toRetirement? == some
  (swRetirement storeState storeInput 0 1 0x100)

#print axioms pinned_store_state
#print axioms pinned_store_boundary
#print axioms pinned_store_memory
#print axioms pinned_store_machine_commit
#print axioms pinned_store_stateful_machine_commit

end Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
