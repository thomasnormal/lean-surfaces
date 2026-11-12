import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_inside.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 insideProp from
  "Examples/system-verilog/sem2/sva_inside/sva_inside.sv.json"
private def env : IEnv := { widths := [("clk", 1), ("a", 4), ("q", 4)] }
private def edge (clk a : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a)] } }
#guard match insideProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 0, edge 1 0, edge 0 1, edge 1 1] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false
end Examples.«system-verilog».sem2.sva_inside.proof
