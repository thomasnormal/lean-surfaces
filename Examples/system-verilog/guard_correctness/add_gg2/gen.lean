import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».guard_correctness.add_gg2.gen
open LeanModels.Sv
load_design_sv2 add_gg2 from "Examples/system-verilog/guard_correctness/add_gg2/add_gg2.sv.json"
#guard add_gg2.pdesign.int32Agrees [16]
#guard add_gg2.pdesign.int32Agrees [5]
end Examples.«system-verilog».guard_correctness.add_gg2.gen
