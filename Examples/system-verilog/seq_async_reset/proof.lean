import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile

namespace Examples.«system-verilog».seq_async_reset.proof

open LeanModels.Sv

load_design_sv2 asyncReset from "Examples/system-verilog/seq_async_reset/async_reset_ff_profile.sv.json"

#guard asyncReset.sem.ffResetProfileB == true
#guard asyncReset.sem.ffOnlyProfileB == false
#guard asyncReset.sem.processes.toList.any fun p => match p with
  | .alwaysFFR "clk" "rstn" _ false => true
  | _ => false

#guard (cycleStep2 asyncReset.sem σ_src 64
    [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .xVec 1)]
    (initState2 asyncReset.sem) 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .ofNat 1 0)]

#guard (cycleStep2 asyncReset.sem σ_src 64
    [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 0)]
    [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1), ("q", .ofNat 1 0)] 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1), ("q", .ofNat 1 1)]

end Examples.«system-verilog».seq_async_reset.proof
