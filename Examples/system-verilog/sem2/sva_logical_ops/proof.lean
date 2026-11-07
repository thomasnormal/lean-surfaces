import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_logical_ops.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 logicalOps from
  "Examples/system-verilog/sem2/sva_logical_ops/sva_logical_ops.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 1), ("b", 1), ("q", 1)] }
private def edge (clk a b : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a), ("b", LVec.ofNat 1 b)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a), ("b", LVec.ofNat 1 b)] } }
private def passing := [edge 0 0 0, edge 1 1 1, edge 0 0 0, edge 1 1 1]
private def failingEq := [edge 0 0 1, edge 1 0 1]
private def failingImp := [edge 0 1 0, edge 1 1 0]

#guard logicalOps.pdesign.properties.length == 2
#guard match logicalOps.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval passing with | .ok true => true | _ => false
    | .error _ => false
  | none => false
#guard match logicalOps.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval passing with | .ok true => true | _ => false
    | .error _ => false
  | none => false
#guard match logicalOps.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval failingEq with | .ok false => true | _ => false
    | .error _ => false
  | none => false
#guard match logicalOps.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval failingImp with | .ok false => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_logical_ops.proof
