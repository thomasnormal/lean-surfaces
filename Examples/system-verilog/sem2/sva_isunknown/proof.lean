import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_isunknown.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 unknownProp from
  "Examples/system-verilog/sem2/sva_isunknown/sva_isunknown.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 1), ("q", 1)] }
private def edge (clk a q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                       ("q", LVec.ofNat 1 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                        ("q", LVec.ofNat 1 q)] } }

#guard match unknownProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 0 0, edge 1 1 1] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_isunknown.proof
