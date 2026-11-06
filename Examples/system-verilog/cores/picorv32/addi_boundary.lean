import LeanModels.Refine.Rv32i

/-!
# PicoRV32 R2 ADDI boundary witness

This is the first concrete architecture-side milestone for the real-core
proof.  It pins the measured `addi x1, x0, 5` word and checks the exact ISA
boundary contract.  It is not a proof about the blocked PicoRV32 RTL; the
future core invariant must use these equations after generated-member memory
support lands.
-/

namespace Examples.«system-verilog».cores.picorv32.addi_boundary

open LeanModels.Rv
open LeanModels.Refine

def addi5Word : Word := 0x00500093

def zeroMem : Memory := fun _ => 0

theorem addi5_decode :
    Fetched.decode (.word addi5Word) =
      some (.alu .add (1 : Reg) (.reg 0) (.imm (5 : Word))) := by
  decide

theorem addi5_isa_boundary (s : ArchState) :
    isaStepMemWith cv32e40pProfile s zeroMem (.word addi5Word) 0 =
      (addiNext s 1 0 5, zeroMem) := by
  exact isaStepMemWith_addi cv32e40pProfile s zeroMem addi5Word 1 0 5
    addi5_decode

theorem addi5_commit_boundary (s : ArchState) :
    (rvMachineWith cv32e40pProfile).step s
        { fetched := .word addi5Word, memory := zeroMem, irq := 0 } =
      (addiNext s 1 0 5,
        addiRetirement s
          { fetched := .word addi5Word, memory := zeroMem, irq := 0 }
          1 0 5) := by
  exact rvMachineWith_addi cv32e40pProfile s zeroMem addi5Word 1 0 5
    addi5_decode

#print axioms addi5_isa_boundary
#print axioms addi5_commit_boundary

end Examples.«system-verilog».cores.picorv32.addi_boundary
