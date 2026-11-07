import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_past_logic.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 pastLogicProp from
  "Examples/system-verilog/sem2/sva_past_logic/sva_past_logic.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("a", 1), ("b", 1), ("q", 1)] }

private def edge (clk a b q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                       ("b", LVec.ofNat 1 b), ("q", LVec.ofNat 1 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                        ("b", LVec.ofNat 1 b), ("q", LVec.ofNat 1 q)] } }

#guard match pastLogicProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 0 0 0, edge 1 0 1 0, edge 0 1 0 0,
                              edge 1 1 1 1] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_past_logic.proof
