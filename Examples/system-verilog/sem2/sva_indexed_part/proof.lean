import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_indexed_part.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 indexedPart from
  "Examples/system-verilog/sem2/sva_indexed_part/sva_indexed_part.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("a", 8), ("base", 3)] }

private def edge (a base : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 8 a),
                       ("base", LVec.ofNat 3 base)] }
    post := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 8 a),
                       ("base", LVec.ofNat 3 base)] } }

#guard match indexedPart.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => match c.eval [edge 1 0, edge 4 2] with
      | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_indexed_part.proof
