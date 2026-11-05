import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.qualified_case_timing.proof

open LeanModels.Sv

load_design_sv2 pre from "Examples/system-verilog/sem2/qualified_case_timing/pre_edge.sv.json"
load_design_sv2 post from "Examples/system-verilog/sem2/qualified_case_timing/post_edge.sv.json"

#guard (run2ExecChecks pre.sem σ_src 128
    [[("clk", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .ofNat 1 0)]]).toOption == none

#guard (run2ExecChecks post.sem σ_src 128 [
    [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 0), ("q", .xVec 1)],
    [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 0)],
    [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 1)]
  ]).toOption == none

end Examples.«system-verilog».sem2.qualified_case_timing.proof
