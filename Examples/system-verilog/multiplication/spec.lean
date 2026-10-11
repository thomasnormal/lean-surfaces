import Examples.«system-verilog».multiplication.proof

namespace Examples.systemVerilog.multiplication

open LeanModels.Sv

theorem multiplication_modular {width : Nat} (left right : BitVec width) :
    proof.runProduct left right = .ok (.ofBitVec (left * right)) :=
  proof.multiplication_modular left right

#print axioms multiplication_modular

end Examples.systemVerilog.multiplication
