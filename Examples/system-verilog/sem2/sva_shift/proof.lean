import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_shift.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 shiftProp from
  "Examples/system-verilog/sem2/sva_shift/sva_shift.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 4), ("q", 4)] }
private def edge (clk a q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("q", LVec.ofNat 4 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                        ("q", LVec.ofNat 4 q)] } }

#guard match shiftProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 1 2, edge 1 2 4] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_shift.proof
