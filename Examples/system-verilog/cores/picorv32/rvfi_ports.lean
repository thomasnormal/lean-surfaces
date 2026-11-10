import LeanModels.Refine.RvfiPorts
import LeanModels.Refine.RvfiE
import LeanModels.Sv.Kernel.Core1Obs

/-!
Port-codec checks against the fixed-width RVFI contract. The distinct payloads
below are synthetic adapter data, not an RTL execution or a core invariant.
The existing source-simulator witness remains in `rvfi_proof.lean`.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_ports

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Refine
open LeanModels.Refine.RvfiPorts

/-- Distinct values make a swapped port observable; the order exceeds 32 bits. -/
def active : PortSample := ⟨[
  ("rvfi_valid", .ofNat 1 1),
  ("rvfi_order", .ofNat 64 0x123456789abcdef0),
  ("rvfi_insn", .ofNat 32 0x10002103),
  ("rvfi_trap", .ofNat 1 0),
  ("rvfi_halt", .ofNat 1 0),
  ("rvfi_intr", .ofNat 1 0),
  ("rvfi_mode", .ofNat 2 3),
  ("rvfi_ixl", .ofNat 2 1),
  ("rvfi_rs1_addr", .ofNat 5 1),
  ("rvfi_rs2_addr", .ofNat 5 2),
  ("rvfi_rs1_rdata", .ofNat 32 0x11111111),
  ("rvfi_rs2_rdata", .ofNat 32 0x22222222),
  ("rvfi_rd_addr", .ofNat 5 3),
  ("rvfi_rd_wdata", .ofNat 32 0x33333333),
  ("rvfi_pc_rdata", .ofNat 32 0x44444444),
  ("rvfi_pc_wdata", .ofNat 32 0x55555555),
  ("rvfi_mem_addr", .ofNat 32 0x66666666),
  ("rvfi_mem_rmask", .ofNat 4 15),
  ("rvfi_mem_wmask", .ofNat 4 0),
  ("rvfi_mem_rdata", .ofNat 32 0x77777777),
  ("rvfi_mem_wdata", .ofNat 32 0x88888888)]⟩

def expected : RvfiObservation :=
  { insn := 0x10002103, order := 0x123456789abcdef0,
    rs1Addr := 1, rs2Addr := 2, rs1Rdata := 0x11111111, rs2Rdata := 0x22222222,
    rdAddr := 3, rdWdata := 0x33333333, rdWdataValid := true,
    pcRdata := 0x44444444, pcWdata := 0x55555555, memAddr := 0x66666666,
    memRmask := 15, memWmask := 0, memRdata := 0x77777777, memWdata := 0x88888888 }

def replacePort (name : String) (value : LVec) : PortSample :=
  ⟨(name, value) :: active.vals⟩

-- Non-vacuity and all field positions, including the high order bits.
#guard decode "rvfi_" active == some expected
#guard decode "other_" active == none
#guard decodePost "rvfi_" ⟨⟨[]⟩, active⟩ == some expected
#guard decodePost "rvfi_" ⟨active, ⟨[]⟩⟩ == none

-- Every required field refuses missing, narrow, wide, x and z inputs.
#guard active.vals.all fun (name, value) =>
  (decode "rvfi_" ⟨active.vals.filter fun p => p.1 != name⟩).isNone &&
  (decode "rvfi_" (replacePort name (.ofNat (value.width - 1) 0))).isNone &&
  (decode "rvfi_" (replacePort name (.ofNat (value.width + 1) 0))).isNone &&
  (decode "rvfi_" (replacePort name (.replicate value.width .lx))).isNone &&
  (decode "rvfi_" (replacePort name (.replicate value.width .lz))).isNone

-- Invalid-cycle payloads have no meaning. Unknown valid is still a refusal.
#guard decode "rvfi_" ⟨[("rvfi_valid", .ofNat 1 0)]⟩ == some bubble
#guard decode "rvfi_" ⟨[("rvfi_valid", .ofNat 1 0),
  ("rvfi_order", .replicate 64 .lx), ("rvfi_halt", .ofLogic .lz)]⟩ == some bubble
#guard decode "rvfi_" ⟨[("rvfi_valid", .ofLogic .lx)]⟩ == none
#guard decode "rvfi_" ⟨[("rvfi_valid", .ofLogic .lz)]⟩ == none

-- Standard RVFI has no rd write-enable; x0 and no-destination both use zero.
#guard (decode "rvfi_" (replacePort "rvfi_rd_addr" (.ofNat 5 0))).map
  RvfiObservation.rdWdataValid == some false
#guard (decode "rvfi_" (replacePort "rvfi_rd_addr" (.ofNat 5 31))).map
  RvfiObservation.rdAddr == some 31

-- Explicit contract boundaries, not guessed trap annotations or mask shifts.
#guard ["trap", "halt", "intr"].all fun field =>
  (decode "rvfi_" (replacePort ("rvfi_" ++ field) (.ofNat 1 1))).isNone
#guard decode "rvfi_" (replacePort "rvfi_mode" (.ofNat 2 0)) == none
#guard decode "rvfi_" (replacePort "rvfi_ixl" (.ofNat 2 2)) == none
#guard decode "rvfi_" (replacePort "rvfi_mem_rmask" (.ofNat 4 2)) == none
#guard decode "rvfi_" (replacePort "rvfi_mem_wmask" (.ofNat 4 15)) == none

-- This concrete decoder has the type required by the actual clocked E bridge.
#check RvfiE.safe_of_invariant (LeanModels.Sv.Kernel.E1 "clk")
  (decode := decodePost "rvfi_")

end Examples.«system-verilog».cores.picorv32.rvfi_ports
