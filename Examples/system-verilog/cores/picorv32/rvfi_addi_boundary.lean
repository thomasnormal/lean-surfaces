import LeanModels.Refine.RvfiAddi
import Examples.«system-verilog».cores.picorv32.rvfi_proof

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

def addiInput : Input :=
  { fetched := .word 0x00500093, memory := fun _ => 0, irq := 0 }

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

#guard addiInput.fetched = .word 0x00500093
#guard addi1.toRetirement? == some
  (addiRetirement (ArchState.init 0) addiInput 1 0 5)

#print axioms pinned_addi_boundary
#print axioms pinned_addi_boundary_fields
#print axioms pinned_addi_boundary_semantic
#print axioms pinned_addi_boundary_no_trap
#print axioms pinned_addi_boundary_no_memory
#print axioms pinned_addi_x0_preserved

end Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
