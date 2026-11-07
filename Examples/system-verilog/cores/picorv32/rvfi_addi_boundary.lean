import LeanModels.Refine.RvfiAddi
import Examples.«system-verilog».cores.picorv32.rvfi_proof
import Examples.«system-verilog».cores.picorv32.trace_proof

/-!
# PicoRV32 raw RVFI ADDI boundary witness

`addi1` is the first non-trapping row from the pinned PicoRV32 RVFI probe.
This theorem checks the raw wire predicate against the reset architectural
state, including the exact fetched word and decode, source and destination
values, the no-trap/no-memory boundary, and the semantic `addiRetirement`
equality.  It is a measured boundary witness, not a theorem about the
currently blocked symbolic RTL load.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.trace_proof

def addiInput : Input :=
  { fetched := .word 0x00500093, memory := fun _ => 0, irq := 0 }

/-- The measured second ADDI row with the source fields retained.  The older
compact `rvfi_proof` row intentionally omitted those fields because its
normalization theorem does not consume them. -/
def addi2Raw : RvfiObservation :=
  { addi2 with rs1Addr := 2, rs1Rdata := 5 }

def addi2Input : Input :=
  { fetched := .word 0x00110193, memory := memFive, irq := 0 }

def addi2State : ArchState :=
  machineStateAfter rvMachine (ArchState.init 0) (nontrapInputs.take 3)

theorem pinned_addi_boundary :
    RvfiObservation.addiBoundary (ArchState.init 0) addiInput addi1
      0x00500093 1 0 5 := by
  unfold RvfiObservation.addiBoundary RvfiObservation.addiFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_addi_boundary_fields :
    addi1.addiFields (ArchState.init 0) addiInput 0x00500093 1 0 5 := by
  exact pinned_addi_boundary.1

theorem pinned_addi_boundary_semantic :
    addi1.toRetirement? = some
      (addiRetirement (ArchState.init 0) addiInput 1 0 5) := by
  exact pinned_addi_boundary.2

theorem pinned_addi_boundary_no_trap :
    addi1.trap = false ∧ addi1.intr = false ∧ addi1.cause = none := by
  exact RvfiObservation.addiBoundary_no_trap
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi_boundary_no_memory :
    addi1.memRmask = 0 ∧ addi1.memWmask = 0 ∧
      (addiRetirement (ArchState.init 0) addiInput 1 0 5).memory = none := by
  have hm := RvfiObservation.addiBoundary_no_memory_masks
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  have he := RvfiObservation.addiBoundary_memory_none
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  exact ⟨hm.1, hm.2, he⟩

theorem pinned_addi_x0_preserved :
    (addiNext (ArchState.init 0) 1 0 5).readReg 0 = 0 := by
  have hx := RvfiObservation.addiBoundary_x0
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  rw [hx]
  rfl

theorem pinned_addi_isa_step :
    isaStepMemWith cv32e40pProfile (ArchState.init 0) addiInput.memory
      addiInput.fetched addiInput.irq =
      (addiNext (ArchState.init 0) 1 0 5, addiInput.memory) := by
  exact RvfiObservation.addiBoundary_isaStepMemWith
    cv32e40pProfile addi1 (ArchState.init 0) addiInput
      0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi_machine_commit :
    (rvMachineWith cv32e40pProfile).step (ArchState.init 0) addiInput =
      (addiNext (ArchState.init 0) 1 0 5,
        addiRetirement (ArchState.init 0) addiInput 1 0 5) := by
  exact RvfiObservation.addiBoundary_rvMachineWith
    cv32e40pProfile addi1 (ArchState.init 0) addiInput
      0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi2_state :
    addi2State.pc = 12 ∧ addi2State.readReg 2 = 5 ∧
      addi2State.readReg 0 = 0 := by
  decide

theorem pinned_addi2_boundary :
    RvfiObservation.addiBoundary addi2State addi2Input addi2Raw
      0x00110193 3 2 1 := by
  unfold RvfiObservation.addiBoundary RvfiObservation.addiFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_addi2_isa_step :
    isaStepMemWith cv32e40pProfile addi2State addi2Input.memory
      addi2Input.fetched addi2Input.irq =
      (addiNext addi2State 3 2 1, addi2Input.memory) := by
  exact RvfiObservation.addiBoundary_isaStepMemWith
    cv32e40pProfile addi2Raw addi2State addi2Input
      0x00110193 3 2 1 pinned_addi2_boundary

#guard addiInput.fetched = .word 0x00500093
#guard addi1.toRetirement? == some
  (addiRetirement (ArchState.init 0) addiInput 1 0 5)

#print axioms pinned_addi_boundary
#print axioms pinned_addi_boundary_fields
#print axioms pinned_addi_boundary_semantic
#print axioms pinned_addi_boundary_no_trap
#print axioms pinned_addi_boundary_no_memory
#print axioms pinned_addi_x0_preserved
#print axioms pinned_addi_isa_step
#print axioms pinned_addi_machine_commit
#print axioms pinned_addi2_state
#print axioms pinned_addi2_boundary
#print axioms pinned_addi2_isa_step

end Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
