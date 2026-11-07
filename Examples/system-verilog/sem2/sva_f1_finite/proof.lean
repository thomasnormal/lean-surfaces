import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_f1_finite.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 finite from
  "Examples/system-verilog/sem2/sva_f1_finite/sva_f1_finite.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("rst", 1), ("req", 1), ("ack", 1), ("q", 1)] }

private def edge (clk rst req ack : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("rst", LVec.ofNat 1 rst),
      ("req", LVec.ofNat 1 req), ("ack", LVec.ofNat 1 ack)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("rst", LVec.ofNat 1 rst),
      ("req", LVec.ofNat 1 req), ("ack", LVec.ofNat 1 ack)] } }

private def trace : List (CycleObs PortSample) :=
  [ edge 0 0 0 0, edge 1 0 1 1, edge 0 1 1 1, edge 1 1 0 0
  , edge 0 1 0 0, edge 1 1 1 1, edge 0 1 1 1, edge 1 1 0 1 ]

#guard finite.pdesign.properties.length == 2
#guard match finite.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => c.check.kind == .assert && c.check.edge == "posedge" &&
        c.eval trace == .ok true
    | .error _ => false
  | none => false
#guard match finite.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => c.check.kind == .assume && c.eval trace == .ok true
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_f1_finite.proof
