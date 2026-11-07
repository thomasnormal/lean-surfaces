import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_past_cmp.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 pastCmpProp from
  "Examples/system-verilog/sem2/sva_past_cmp/sva_past_cmp.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 4), ("b", 4), ("q", 1)] }
private def edge (clk a b q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("b", LVec.ofNat 4 b), ("q", LVec.ofNat 1 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                        ("b", LVec.ofNat 4 b), ("q", LVec.ofNat 1 q)] } }

#guard match pastCmpProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 0 2 0, edge 1 0 2 0,
                              edge 0 4 3 0, edge 1 4 3 1] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_past_cmp.proof
