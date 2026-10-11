import Examples.«system-verilog».compound_assignments.proof

namespace Examples.systemVerilog.compoundAssignments

open LeanModels.Sv LeanModels.Sv.SelfCheck

theorem compound_updates :
    proof.runCompound = .ok
      ([ ("value", .ofNat 4 9), ("delta", .ofNat 4 3) ], [], {}) :=
  proof.compound_updates

#print axioms compound_updates

end Examples.systemVerilog.compoundAssignments
