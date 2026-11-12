import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
namespace Examples.«system-verilog».sem2.profile_mixed_e
open LeanModels.Sv
load_design_sv2 profileMixedE from
  "Examples/system-verilog/sem2/profile_mixed_e/profile_mixed_e.sv.json"
#guard profileMixedE.pdesign.others == []
#guard profileMixedE.sem.ffResetProfileB
#guard profileMixedE.sem.ffMixedProfileB
#guard !profileMixedE.sem.ffOnlyProfileB
#guard match profileMixedE.sem.processes.toList with
  | [.alwaysFFR "clk" "rst" _ _, .assign (.ident "y") (.ident "q")] => true
  | _ => false
end Examples.«system-verilog».sem2.profile_mixed_e
