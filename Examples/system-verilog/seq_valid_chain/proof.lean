import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqProfile
namespace Examples.«system-verilog».seq_valid_chain.proof
open LeanModels.Sv
load_design_sv2 validChain from "Examples/system-verilog/seq_valid_chain/valid_chain_profile.sv.json"
private def d := validChain.sem 8
private def outputs (st : SvState) := (SvState.lookup st "valid_o", SvState.lookup st "data_o")
private def stim : List SvState := [
  [("clk", .ofNat 1 0), ("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 165)],
  [("clk", .ofNat 1 1), ("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 165)],
  [("clk", .ofNat 1 0), ("rst", .ofNat 1 0), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 90)],
  [("clk", .ofNat 1 1), ("rst", .ofNat 1 0), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 90)] ]
#guard d.ffMixedProfileB == true
#guard d.ffOnlyProfileB == false
#guard (run2 d σ_src 128 stim).toOption.map (List.map outputs) ==
  some [(some (.ofNat 1 1), some (.ofNat 8 165)),
    (some (.ofNat 1 1), some (.ofNat 8 165)),
    (some (.ofNat 1 0), some (.ofNat 8 90)),
    (some (.ofNat 1 0), some (.ofNat 8 90))]
end Examples.«system-verilog».seq_valid_chain.proof
