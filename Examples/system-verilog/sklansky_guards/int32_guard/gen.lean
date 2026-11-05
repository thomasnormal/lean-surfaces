import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sklansky_guards.int32_guard.gen
open LeanModels.Sv
load_design_sv2 only_n16 from "Examples/system-verilog/sklansky_guards/int32_guard/only_n16.sv.json"
#guard only_n16.pdesign.int32Agrees [16]
#guard only_n16.pdesign.int32Agrees [1]
end Examples.«system-verilog».sklansky_guards.int32_guard.gen
