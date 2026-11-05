import Examples.«system-verilog».cores.toy_rv32i.proof

/-!
# RVFI adapter example

The toy's ADDI retirement is encoded once as packed RVFI-style signals and
then decoded through the generic adapter.  The theorem compares the result
with the existing semantic `Retirement.ofRvStep`; malformed and invalid
records are rejected by the same boundary.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.rvfi_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof

def toyRvfi : RvfiObservation :=
  { valid := true
    order := 0
    insn := addiWord
    pcRdata := 0
    pcWdata := 4
    mode := 3
    ixl := 1
    rs1Addr := 0
    rs1Rdata := 0
    rs2Addr := 0
    rs2Rdata := 0
    rdAddr := 1
    rdWdata := 1
    rdWdataValid := true
    memAddr := 0
    memRmask := 0
    memWmask := 0
    memRdata := 0
    memWdata := 0
    cause := none }

def toyRetirement : Retirement :=
  Retirement.ofRvStep (ArchState.init 0) addiInput (toyNext (ArchState.init 0))
    (toyEffects (ArchState.init 0))

theorem toy_rvfi_normalizes :
    toyRvfi.toRetirement? = some toyRetirement := by
  decide

def invalidRvfi : RvfiObservation := { toyRvfi with valid := false }

def malformedRvfi : RvfiObservation := { toyRvfi with memRmask := 0b0101 }

#guard toyRvfi.toRetirement? == some toyRetirement
#guard invalidRvfi.toRetirement? == none
#guard malformedRvfi.toRetirement? == none

#print axioms toy_rvfi_normalizes

end Examples.«system-verilog».cores.toy_rv32i.rvfi_proof
