import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile

namespace Examples.«system-verilog».seq_plain.proof

open LeanModels.Sv

load_design_sv2 plainAlways from "Examples/system-verilog/seq_plain/posedge_always_profile.sv.json"

#guard plainAlways.sem.ffOnlyProfileB == true
#guard plainAlways.sem.processes.toList.any fun p => match p with
  | .alwaysPlain "clk" (.nbaAssign (.ident "q") (.ident "d")) => true
  | _ => false
#guard (cycleStep2 plainAlways.sem σ_src 64
    [("clk", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .xVec 1)]
    (initState2 plainAlways.sem) 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 1)]

end Examples.«system-verilog».seq_plain.proof
