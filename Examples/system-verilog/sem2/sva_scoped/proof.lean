import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_scoped.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 scopedProp from
  "Examples/system-verilog/sem2/sva_scoped/sva_scoped.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("a", 1), ("q", 1), ("u.flag", 1)] }

private def edge (clk a q flag : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                       ("q", LVec.ofNat 1 q), ("u.flag", LVec.ofNat 1 flag)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 1 a),
                        ("q", LVec.ofNat 1 q), ("u.flag", LVec.ofNat 1 flag)] } }

#guard match scopedProp.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 0 0 0 0, edge 1 1 1 1] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_scoped.proof
