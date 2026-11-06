import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sklansky_guards.clog2_int.gen
open LeanModels.Sv
load_design_sv2 clog2_int from "Examples/system-verilog/sklansky_guards/clog2_int/clog2_int.sv.json"
#guard clog2_int.pdesign.int32Agrees [16]
#guard clog2_int.pdesign.int32Agrees [1]
end Examples.«system-verilog».sklansky_guards.clog2_int.gen
