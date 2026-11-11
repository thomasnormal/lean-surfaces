import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_param_cast.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 paramCastProp from
  "Examples/system-verilog/sem2/sva_param_cast/sva_param_cast.sv.json"

private def env : IEnv :=
  { nvals := [("N", (4, 32, true))]
    widths := [("clk", 1), ("a", 4), ("q", 4)] }

private def edge (clk a q : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("q", LVec.ofNat 4 q)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("q", LVec.ofNat 4 q)] } }

#guard match paramCastProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.check.property with
      | .implies _ (.atom (.valueCmp _ (.current _) (.binary _ (.paramCast (some 4) _) _))) =>
          match c.eval [edge 0 0 0, edge 1 0 0, edge 0 2 2, edge 1 2 2] with
          | .ok true => true | _ => false
      | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_param_cast.proof
