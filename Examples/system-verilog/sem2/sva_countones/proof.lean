import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_countones.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 countProp from
  "Examples/system-verilog/sem2/sva_countones/sva_countones.sv.json"

private def env : IEnv := { widths := [("clk", 1), ("a", 4), ("q", 32)] }
private def edge (clk a : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                       ("q", LVec.ofNat 32 2)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a),
                        ("q", LVec.ofNat 32 2)] } }

#guard match countProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 3, edge 1 3] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_countones.proof
