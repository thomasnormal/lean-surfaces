import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_assume_disable.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 disabled from
  "Examples/system-verilog/sem2/sva_assume_disable/sva_assume_disable.sv.json"

private def env : IEnv :=
  { widths := [("clk", 1), ("rst", 1), ("valid", 1), ("data", 1)] }

private def edge (clk rst valid data : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("rst", LVec.ofNat 1 rst),
      ("valid", LVec.ofNat 1 valid), ("data", LVec.ofNat 1 data)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("rst", LVec.ofNat 1 rst),
      ("valid", LVec.ofNat 1 valid), ("data", LVec.ofNat 1 data)] } }

private def trace : List (CycleObs PortSample) :=
  [ edge 0 0 0 0, edge 1 0 1 0, edge 0 1 0 1
  , edge 1 1 1 1, edge 0 1 0 0, edge 1 1 0 0 ]

#guard disabled.pdesign.properties.length == 1
#guard match disabled.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty env [] p with
    | .ok c => c.check.kind == .assume && c.eval trace == .ok true
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_assume_disable.proof
