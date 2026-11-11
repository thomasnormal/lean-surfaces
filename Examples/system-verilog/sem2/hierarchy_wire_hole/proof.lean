import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.hierarchy_wire_hole.proof
open LeanModels.Sv
load_design_sv2 hierarchyWireHole from
  "Examples/system-verilog/sem2/hierarchy_wire_hole/hierarchy_wire_hole.sv.json"

#guard hierarchyWireHole.pdesign.params.length == 2

-- The parent output remains a net in the retained symbolic envelope.  The
-- differential row exercises its uncovered parameter-point bit through the
-- labelled legacy executor; this guard checks the source-shaped declaration.
#guard hierarchyWireHole.pdesign.decls.any
    (fun dc => dc.name == "y" && dc.isNet) == true

end Examples.«system-verilog».sem2.hierarchy_wire_hole.proof
