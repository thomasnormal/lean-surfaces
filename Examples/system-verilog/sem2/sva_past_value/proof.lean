import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_past_value.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 pastValue from
  "Examples/system-verilog/sem2/sva_past_value/sva_past_value.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("valid", 1), ("inc", 1), ("depth", 4), ("q", 1)] }
private def edge (clk valid inc depth : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("valid", LVec.ofNat 1 valid), ("inc", LVec.ofNat 1 inc), ("depth", LVec.ofNat 4 depth)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("valid", LVec.ofNat 1 valid), ("inc", LVec.ofNat 1 inc), ("depth", LVec.ofNat 4 depth)] } }
private def samePass := [edge 0 0 0 3, edge 1 1 0 3, edge 0 1 0 3, edge 1 0 0 3]
private def plusPass := [edge 0 0 0 3, edge 1 1 1 3, edge 0 1 0 4, edge 1 0 0 4]
private def sameFail := [edge 0 0 0 3, edge 1 1 0 3, edge 0 1 0 3, edge 1 0 0 4]
private def plusFail := [edge 0 0 0 3, edge 1 1 1 3, edge 0 1 0 3, edge 1 0 0 3]

#guard pastValue.pdesign.properties.length == 2
#guard match pastValue.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval samePass with | .ok true => true | _ => false
    | .error _ => false
  | none => false
#guard match pastValue.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval plusPass with | .ok true => true | _ => false
    | .error _ => false
  | none => false
#guard match pastValue.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval sameFail with | .ok false => true | _ => false
    | .error _ => false
  | none => false
#guard match pastValue.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval plusFail with | .ok false => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_past_value.proof
