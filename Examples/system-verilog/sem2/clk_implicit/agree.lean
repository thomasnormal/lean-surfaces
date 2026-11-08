import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_implicit.agree

open LeanModels.Sv

load_design_sv2 clk_implicit from
  "Examples/system-verilog/sem2/clk_implicit/clk_implicit.sv.json"

#guard match run2 clk_implicit.sem σ_src 128 [
    [("a", .ofNat 1 0), ("d", .ofNat 1 1)]] with
  | .unsupported msg => msg.startsWith "Clock:implicit:"
  | _ => false

end Examples.«system-verilog».sem2.clk_implicit.agree
