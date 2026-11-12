import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.sva_kind_clock_e
open LeanModels.Sv
load_design_sv2 svaKindClockE from "Examples/system-verilog/sem2/sva_kind_clock_e/sva_kind_clock_e.sv.json"
#guard match svaKindClockE.pdesign.properties with
  | [{ kind := "restrict", clock := some "clk", .. }] => true
  | _ => false
end Examples.«system-verilog».sem2.sva_kind_clock_e
