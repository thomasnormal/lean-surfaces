import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».guard_correctness.add_int32.gen
open LeanModels.Sv
load_design_sv2 add_int32 from "Examples/system-verilog/guard_correctness/add_int32/add_int32.sv.json"
#guard add_int32.pdesign.int32Agrees [16]
#guard add_int32.pdesign.int32Agrees [5]
end Examples.«system-verilog».guard_correctness.add_int32.gen
