import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_unbased_literal.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 unbased from
  "Examples/system-verilog/sem2/sva_unbased_literal/sva_unbased_literal.sv.json"

private def svaEnv : IEnv := { widths := [("clk", 1), ("a", 4)] }

private def edge (clk a : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("a", LVec.ofNat 4 a)] } }

private def passing : List (CycleObs PortSample) :=
  [edge 0 0, edge 1 0, edge 0 0, edge 1 0]

private def failing : List (CycleObs PortSample) :=
  [edge 0 0, edge 1 5]

#guard match unbased.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty svaEnv [] p with
    | .ok c => match c.eval passing with | .ok true => true | _ => false
    | .error _ => false
  | none => false

#guard match unbased.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty svaEnv [] p with
    | .ok c => match c.eval failing with | .ok false => true | _ => false
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_unbased_literal.proof
