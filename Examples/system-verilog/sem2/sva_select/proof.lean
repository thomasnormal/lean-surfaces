import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_select.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 selectProp from
  "Examples/system-verilog/sem2/sva_select/sva_select.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("a", 4), ("i", 2), ("q", 1)] }

private def edge (clk a i q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("i", LVec.ofNat 2 i), ("q", LVec.ofNat 1 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                        ("i", LVec.ofNat 2 i), ("q", LVec.ofNat 1 q)] } }

#guard match selectProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 9 0 1, edge 1 9 2 0] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_select.proof
