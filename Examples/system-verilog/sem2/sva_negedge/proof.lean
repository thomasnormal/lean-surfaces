import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_negedge.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 negedge from
  "Examples/system-verilog/sem2/sva_negedge/sva_negedge.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("req", 1), ("ack", 1)] }

private def edge (clk req ack : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("req", LVec.ofNat 1 req),
      ("ack", LVec.ofNat 1 ack)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("req", LVec.ofNat 1 req),
      ("ack", LVec.ofNat 1 ack)] } }

-- Selected samples are 1->0 transitions: req at the first negedge is
-- followed by ack at the next negedge, and the cover sequence is reached.
private def trace : List (CycleObs PortSample) :=
  [ edge 1 0 0, edge 0 1 0, edge 1 0 0, edge 0 0 1
  , edge 1 0 0, edge 0 0 0 ]

#guard negedge.pdesign.properties.length == 2
#guard match negedge.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => c.check.edge == "negedge" && c.check.kind == .assert &&
        match c.eval trace with | .ok true => true | _ => false
    | .error _ => false
  | none => false
#guard match negedge.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => c.check.edge == "negedge" && c.check.kind == .cover &&
        match c.eval trace with | .ok true => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_negedge.proof
