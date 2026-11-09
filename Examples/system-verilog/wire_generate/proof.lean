import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
namespace Examples.«system-verilog».wire_generate.proof
open LeanModels.Sv
load_design_sv2 wireGen from "Examples/system-verilog/wire_generate/wire_generate.sv.json"
#guard !(wireGen.sem 4).hasUnsupported
#guard !(wireGen.sem 8).hasUnsupported
#guard (run2 (wireGen.sem 4) σ_src 128 [
    [("x", .ofNat 4 0)],
    [("x", .ofNat 4 5)],
    [("x", .ofNat 4 10)] ]).toOption.map (List.map (SvState.showSignal · "y")) ==
  some ["0000", "0101", "1010"]
end Examples.«system-verilog».wire_generate.proof
