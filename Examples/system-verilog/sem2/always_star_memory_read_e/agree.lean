import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Clean-room E admission receipt for a source-shaped plain `always @*`
memory read.  The parser keeps the implicit event and the runtime ArraySel;
the current one-cycle memory profile refuses the event explicitly rather than
skipping it and fabricating a value. -/
namespace Examples.«system-verilog».sem2.always_star_memory_read_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 alwaysStarMemoryReadE
  from "Examples/system-verilog/sem2/always_star_memory_read_e/always_star_memory_read_e.sv.json"

#guard alwaysStarMemoryReadE.pdesign.others == []
#guard match alwaysStarMemoryReadE.pdesign.processes with
  | [.alwaysFF "clk" _, .alwaysImplicit (.block [
      .blockingAssign "q" (.arrayElem "mem" [LeanModels.Sv.PExpr.ident "ridx"])])] => true
  | _ => false

#guard match MemEDesign.ofPDesign alwaysStarMemoryReadE.pdesign [4] with
  | .unsupported "E memory route does not yet admit implicit event-controlled processes" => true
  | _ => false

end Examples.«system-verilog».sem2.always_star_memory_read_e
