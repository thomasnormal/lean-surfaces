import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile

namespace Examples.«system-verilog».seq_async_comb.proof

open LeanModels.Sv

load_design_sv2 mixedReset from "Examples/system-verilog/seq_async_comb/async_reset_comb_profile.sv.json"

#guard mixedReset.sem.ffResetProfileB == true
#guard mixedReset.sem.ffOnlyProfileB == false
#guard mixedReset.sem.ffMixedProfileB == true
#guard mixedReset.sem.processes.toList.any fun p => match p with
  | .assign (.ident "n") (.ident "d") => true
  | _ => false
#guard mixedReset.sem.processes.toList.any fun p => match p with
  | .alwaysFFR "clk" "rstn" _ false => true
  | _ => false

#guard (cycleStep2 mixedReset.sem σ_src 64
    [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1),
      ("q", .xVec 1), ("n", .xVec 1)]
    (initState2 mixedReset.sem) 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1),
    ("q", .ofNat 1 0), ("n", .ofNat 1 1)]

#guard (cycleStep2 mixedReset.sem σ_src 64
    [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1),
      ("q", .ofNat 1 0), ("n", .ofNat 1 1)]
    [("clk", .ofNat 1 0), ("rstn", .ofNat 1 0), ("d", .ofNat 1 1),
      ("q", .ofNat 1 0), ("n", .ofNat 1 1)] 0).toOption.map (·.1) ==
  some [("clk", .ofNat 1 1), ("rstn", .ofNat 1 1), ("d", .ofNat 1 1),
    ("q", .ofNat 1 1), ("n", .ofNat 1 1)]

end Examples.«system-verilog».seq_async_comb.proof
