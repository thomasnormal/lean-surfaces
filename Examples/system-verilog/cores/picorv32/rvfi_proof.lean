import LeanModels.Refine.Rvfi

/-!
# PicoRV32 RVFI boundary witness

The observations below are the four non-trapping rows emitted by the pinned
PicoRV32 source under `rvfi_probe.v`, with `RISCV_FORMAL` defined.  The
simulation witness is intentionally kept as data in this proof: the theorem
checks the exact packed-to-semantic conversion used by the eventual core
refinement, including the store/load masks and values.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_proof

open LeanModels.Rv
open LeanModels.Refine

def addi1 : RvfiObservation :=
  { valid := true, order := 0, insn := 0x00500093, pcRdata := 0,
    pcWdata := 4, rdAddr := 1, rdWdata := 5, rdWdataValid := true,
    mode := 3, ixl := 1 }

def store1 : RvfiObservation :=
  { valid := true, order := 1, insn := 0x10102023, pcRdata := 4,
    pcWdata := 8, memAddr := 0x100, memWmask := 0b1111,
    memWdata := 5, mode := 3, ixl := 1 }

def load1 : RvfiObservation :=
  { valid := true, order := 2, insn := 0x10002103, pcRdata := 8,
    pcWdata := 12, rdAddr := 2, rdWdata := 5, rdWdataValid := true,
    memAddr := 0x100, memRmask := 0b1111, memRdata := 5,
    memWdata := 5, mode := 3, ixl := 1 }

def addi2 : RvfiObservation :=
  { valid := true, order := 3, insn := 0x00110193, pcRdata := 12,
    pcWdata := 16, rdAddr := 3, rdWdata := 6, rdWdataValid := true,
    mode := 3, ixl := 1 }

def ebreak : RvfiObservation :=
  { valid := true, order := 4, insn := 0x00100073, pcRdata := 16,
    pcWdata := 16, trap := true, mode := 3, ixl := 1,
    cause := some .breakpoint }

def ebreakUnannotated : RvfiObservation := { ebreak with cause := none }

def observations : List RvfiObservation := [addi1, store1, load1, addi2, ebreak]

def expected : List Retirement :=
  [ { pc := 0, instr := 0x00500093, nextPc := 4,
      writes := [(1, 5)] }
  , { pc := 4, instr := 0x10102023, nextPc := 8,
      writes := [],
      memory := some (.write 0x100 .word 5) }
  , { pc := 8, instr := 0x10002103, nextPc := 12,
      writes := [(2, 5)], memory := some (.read 0x100 .word 5) }
  , { pc := 12, instr := 0x00110193, nextPc := 16,
      writes := [(3, 6)] }
  , { pc := 16, instr := 0x00100073, nextPc := 16,
      writes := [], trap := some .breakpoint } ]

theorem pinned_rows_normalize :
    observations.map RvfiObservation.toRetirement? = expected.map some := by
  decide

theorem pinned_orders_are_consecutive :
    observations.map RvfiObservation.order = [0, 1, 2, 3, 4] := by
  rfl

theorem unannotated_trap_is_refused :
    ebreakUnannotated.toRetirement? = none := by
  rfl

#guard observations.map RvfiObservation.toRetirement? == expected.map some
#guard observations.map RvfiObservation.order == [0, 1, 2, 3, 4]
#guard ebreakUnannotated.toRetirement? == none

#print axioms pinned_rows_normalize
#print axioms pinned_orders_are_consecutive
#print axioms unannotated_trap_is_refused

end Examples.«system-verilog».cores.picorv32.rvfi_proof
