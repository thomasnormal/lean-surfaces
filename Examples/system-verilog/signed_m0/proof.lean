/- M0 signed declaration/operator receipt for signed_m0.sv. -/
import LeanModels.Sv.Semantics

namespace Examples.«system-verilog».signed_m0.proof

open LeanModels.Sv

def signedA : LVec := .ofNat 8 255
def signedB : LVec := .ofNat 8 1

#guard LVec.slt signedA signedB == .l1
#guard LVec.slt signedB signedA == .l0
#guard LVec.slt (.lit "xxxxxxxx") signedB == .lx

end Examples.«system-verilog».signed_m0.proof
