import LeanModels.Refine.RvfiMem
import Examples.«system-verilog».cores.picorv32.rvfi_proof
import Examples.«system-verilog».cores.picorv32.trace_proof

/-!
# PicoRV32 raw RVFI LW boundary witness

This is the measured `lw x2, 0x100(x0)` row after the ADDI/SW prefix.  The
state is threaded through the architectural machine while the input carries
the explicit memory response of 5.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.trace_proof

def loadRaw : RvfiObservation :=
  { load1 with rs1Addr := 0, rs1Rdata := 0, rdAddr := 2, rdWdata := 5, rdWdataValid := true, memRdata := 5 }

def loadInput : Input :=
  { fetched := .word 0x10002103, memory := memFive, irq := 0 }

def loadState : ArchState :=
  machineStateAfter rvMachine (ArchState.init 0) (nontrapInputs.take 2)

theorem pinned_load_state :
    loadState.pc = 8 ∧ loadState.readReg 1 = 5 ∧
      loadState.readReg 0 = 0 := by
  decide

theorem pinned_load_boundary :
    RvfiObservation.lwBoundary loadState loadInput loadRaw
      0x10002103 2 0 0x100 := by
  unfold RvfiObservation.lwBoundary RvfiObservation.lwFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_load_memory :
    isaStepMemWith cv32e40pProfile loadState loadInput.memory
      loadInput.fetched loadInput.irq =
      (lwNext loadState loadInput.memory 2 0 0x100, loadInput.memory) := by
  exact RvfiObservation.lwBoundary_isaStepMemWith
    cv32e40pProfile loadRaw loadState loadInput
      0x10002103 2 0 0x100 pinned_load_boundary

theorem pinned_load_machine_commit :
    (rvMachineWith cv32e40pProfile).step loadState loadInput =
      (lwNext loadState loadInput.memory 2 0 0x100,
        lwRetirement loadState loadInput 2 0 0x100) := by
  exact RvfiObservation.lwBoundary_rvMachineWith
    cv32e40pProfile loadRaw loadState loadInput
      0x10002103 2 0 0x100 pinned_load_boundary

#guard loadInput.fetched = .word 0x10002103
#guard loadRaw.toRetirement? == some
  (lwRetirement loadState loadInput 2 0 0x100)

#print axioms pinned_load_state
#print axioms pinned_load_boundary
#print axioms pinned_load_memory
#print axioms pinned_load_machine_commit

end Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
