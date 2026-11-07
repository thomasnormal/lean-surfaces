import LeanModels.Sv.Ingest2
import LeanModels.Sv.SvaContract

namespace Examples.«system-verilog».sem2.sva_property_retained.proof

open LeanModels.Sv
open LeanModels.Sv.Observe

load_design_sv2 retained from
  "Examples/system-verilog/sem2/sva_property_retained/sva_property_retained.sv.json"

private def edge (clk rstn a b : Nat) : CycleObs PortSample :=
  { pre := { vals := [("clk", LVec.ofNat 1 clk), ("rst_n", LVec.ofNat 1 rstn),
      ("a", LVec.ofNat 1 a), ("b", LVec.ofNat 1 b)] }
    post := { vals := [("clk", LVec.ofNat 1 clk), ("rst_n", LVec.ofNat 1 rstn),
      ("a", LVec.ofNat 1 a), ("b", LVec.ofNat 1 b)] } }

private def trace : List (CycleObs PortSample) :=
  [edge 0 1 1 0, edge 1 1 1 1, edge 0 1 0 0, edge 1 1 0 1]

#guard retained.pdesign.properties.length == 3
#guard match retained.pdesign.properties[0]? with
  | some p => (SvaContract.ofProperty ({} : IEnv) [] p).toOption.isSome
  | none => false
#guard match retained.pdesign.properties[1]? with
  | some p => (SvaContract.ofProperty ({} : IEnv) [] p).toOption.isSome
  | none => false
#guard match retained.pdesign.properties[2]? with
  | some p => (SvaContract.ofProperty ({} : IEnv) [] p).toOption.isSome
  | none => false
#guard match retained.pdesign.properties[0]? with
  | some p => match SvaContract.ofProperty ({} : IEnv) [] p with
    | .ok c => c.eval (SvaContract.portRegion trace) == .ok true
    | .error _ => false
  | none => false
#guard match retained.pdesign.properties[1]? with
  | some p => match SvaContract.ofProperty ({} : IEnv) [] p with
    | .ok c => c.eval (SvaContract.portRegion trace) == .ok true
    | .error _ => false
  | none => false
#guard match retained.pdesign.properties[2]? with
  | some p => match SvaContract.ofProperty ({} : IEnv) [] p with
    | .ok c => c.eval (SvaContract.portRegion trace) == .ok true
    | .error _ => false
  | none => false

end Examples.«system-verilog».sem2.sva_property_retained.proof
