/- Clean-room canonical E receipt for a parameterized two-child hierarchy.

   The source-shaped module library is elaborated by `PDesign.instantiateH`;
   the resulting flattened `Design2` is then executed by E-core-0. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyE

namespace Examples.«system-verilog».sem2.hierarchy_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 hierarchyE
  from "Examples/system-verilog/sem2/hierarchy_e/hierarchy_parameterized.sv.json"

#guard hierarchyE.pdesign.name == "hierarchy_parameterized"
#guard hierarchyE.plib.length == 1
#guard hierarchyE.pdesign.params.length == 1

def flat : Res Design2 :=
  hierarchyE.pdesign.instantiateH hierarchyE.plib [8]
    (PDesign.surfaceFuel [8])

def E : Elab :=
  match flat with
  | .ok d => Elab.ofDesign2 d
  | .timeout | .unsupported _ => { decls := #[], procs := #[] }

def run (a : String) : Option String :=
  match exec E σ_src 100 (Config.start E [("a", LVec.lit a)]) with
  | .closed c => some (SvState.showSignal (E.view c.store) "y")
  | .refused _ | .outOfBudget _ => none

def runViaHierarchy (a : String) : Option String :=
  match runHierarchyE hierarchyE.pdesign hierarchyE.plib [8] 100
      [("a", LVec.lit a) :: []] with
  | .ok [row] => some (SvState.showSignal row "y")
  | .ok _ | .timeout | .unsupported _ => none

#guard match flat with
  | .ok d => d.decls.size == 6 && d.processes.size == 6
  | .timeout | .unsupported _ => false
#guard run "00000000" == some "00000000"
#guard run "00000001" == some "00000001"
#guard run "10100101" == some "10100101"
#guard run "11110000" == some "11110000"
#guard run "xxxxxxxx" == some "xxxxxxxx"
#guard runViaHierarchy "10100101" == some "10100101"

end Examples.«system-verilog».sem2.hierarchy_e
