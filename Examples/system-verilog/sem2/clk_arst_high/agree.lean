import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.clk_arst_high.agree
open LeanModels.Sv
load_design_sv2 clk_arst_high from "Examples/system-verilog/sem2/clk_arst_high/clk_arst_high.sv.json"
#guard !(clk_arst_high.sem 4).hasUnsupported
end Examples.«system-verilog».sem2.clk_arst_high.agree
