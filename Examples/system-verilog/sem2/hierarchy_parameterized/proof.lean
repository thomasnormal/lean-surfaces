import LeanModels.Sv.Ingest2
import LeanModels.Sv.HierarchyNode2

/-! A parameterized hierarchy whose parent output wire is tiled by child output
    connections.  The net remains a net-as-variable in the envelope; the two
    source-shaped ranges are retained on the instance nodes. -/

namespace Examples.«system-verilog».sem2.hierarchy_parameterized

open LeanModels.Sv

set_option maxRecDepth 100000 in
load_design_sv2 hierarchyParameterized
  from "Examples/system-verilog/sem2/hierarchy_parameterized/hierarchy_parameterized.sv.json"

#guard hierarchyParameterized.plib.length == 1

#guard match hierarchyParameterized.pdesign.instantiateNode2
    hierarchyParameterized.plib [8] with
  | .ok node =>
      match node.instances with
      | [lo, hi] =>
          lo.ports.any (fun p => match p with
            | .output "y" (some (.arrayPart "y" [] .range _ _)) => true
            | _ => false)
          && hi.ports.any (fun p => match p with
            | .output "y" (some (.arrayPart "y" [] .range _ _)) => true
            | _ => false)
      | _ => false
  | _ => false

#guard match hierarchyParameterized.pdesign.instantiateNode2
    hierarchyParameterized.plib [8] with
  | .ok node =>
      match runHier2 node σ_src 32 [[("a", LVec.lit "00000001")]] with
      | .unsupported "Instance:hierarchy: source-shaped instance nodes require the E composition route; no flattening rewrite is applied" => true
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.hierarchy_parameterized
