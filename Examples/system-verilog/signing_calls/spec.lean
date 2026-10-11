import Examples.«system-verilog».signing_calls.proof

namespace Examples.systemVerilog.signingCalls

open LeanModels.Sv LeanModels.Sv.SelfCheck

theorem signing_assignment_contexts (value : LVec) :
    proof.runSigning value = .ok
      ([ ("value", value), ("same_signed", value), ("same_unsigned", value),
        ("wide_signed", value.resizeSigned 8),
        ("wide_unsigned", resizeV 8 value) ], [], {}) :=
  proof.signing_assignment_contexts value

#print axioms signing_assignment_contexts

end Examples.systemVerilog.signingCalls
