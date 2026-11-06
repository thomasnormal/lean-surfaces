import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
namespace Examples.«system-verilog».seq_mixed_comb.proof
open LeanModels.Sv
load_design_sv2 mixedComb from "Examples/system-verilog/seq_mixed_comb/mixed_comb_profile.sv.json"
#guard mixedComb.sem.ffMixedProfileB == true
#guard mixedComb.sem.ffResetProfileB == false
#guard mixedComb.sem.ffOnlyProfileB == false
#guard (cycleStep2 mixedComb.sem σ_src 64
    [("clk", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .xVec 1), ("n", .xVec 1)]
    (initState2 mixedComb.sem) 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .ofNat 1 1), ("n", .ofNat 1 1)]
#guard (cycleStep2 mixedComb.sem σ_src 64
    [("clk", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 0), ("n", .ofNat 1 1)]
    [("clk", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .ofNat 1 0), ("n", .ofNat 1 1)] 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 1), ("n", .ofNat 1 1)]
end Examples.«system-verilog».seq_mixed_comb.proof
