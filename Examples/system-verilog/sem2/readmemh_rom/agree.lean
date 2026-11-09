/- Clean-room F4 boundary: an initial `$readmemh` process remains a named
   source-process refusal until initial-process scheduling and file loading are
   part of E.  The ROM declaration and read assignment stay visible. -/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.readmemh_rom.agree

open LeanModels.Sv

load_design_sv2 readmemhRom from
  "Examples/system-verilog/sem2/readmemh_rom/readmemh_rom.sv.json"

#guard (match readmemhRom.pdesign.processes with
  | .initial (.unsupported k msg) :: _ =>
      k == "ExpressionStatement:CallExpression" &&
      msg == "$readmemh(\"rom.hex\", rom);"
  | _ => false)

#guard (match (readmemhRom.pdesign.instantiateD2 []).processes.toList with
  | .unsupported k msg :: _ =>
      k == "T2:Initial" &&
      msg == "initial process outside the cycle semantic tier"
  | _ => false)

#guard (readmemhRom.pdesign.processes.any fun p =>
  match p with
  | .assign "q" _ => true
  | _ => false)

end Examples.«system-verilog».sem2.readmemh_rom.agree
