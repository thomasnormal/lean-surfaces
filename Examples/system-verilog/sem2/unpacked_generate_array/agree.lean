/-
A parameter-dependent unpacked array changes its declaration layout at each
point. The symbolic envelope retains the source shape but the loader refuses
it loudly rather than flattening a default-point array.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.unpacked_generate_array.agree

open LeanModels.Sv

#guard_msgs (drop error) in
load_design_sv2 unpacked_generate_array from
  "Examples/system-verilog/sem2/unpacked_generate_array/unpacked_generate_array.sv.json"

end Examples.«system-verilog».sem2.unpacked_generate_array.agree
