import LeanModels.Sv.Ingest2
import LeanModels.Sv.HierarchyNode2

/-! Source-shaped hierarchy is a general SV E fixture, independent of any
RISC-V core.  The instance remains a node, with child design and source port
connections retained; `runHierE0` composes the direct child without flattening. -/

namespace Examples.«system-verilog».sem2.hierarchy_instance

open LeanModels.Sv

set_option maxRecDepth 100000 in
load_design_sv2 hierarchyInstance
  from "Examples/system-verilog/sem2/hierarchy_instance/hierarchy_instance.sv.json"

#guard match hierarchyInstance.pdesign.instantiateNode2
    hierarchyInstance.plib [] with
  | .ok node =>
      match node.instances with
      | [i] => node.core.processes.isEmpty && i.name == "u_leaf" &&
          i.module == "leaf" && i.args == [] &&
          i.ports == [.input "a" (some (.ident "a")) false,
                      .output "y" (some (.ident "y"))]
      | _ => false
  | _ => false

#guard match hierarchyInstance.pdesign.instantiateNode2
    hierarchyInstance.plib [] with
  | .ok node =>
      match runHierE0 node σ_src 32
          [[("a", LVec.lit "1")]] with
      | .ok [st] => SvState.showSignal st "y" == "1"
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.hierarchy_instance
