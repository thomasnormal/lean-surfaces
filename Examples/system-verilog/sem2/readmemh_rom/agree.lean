/- Clean-room F4 boundary: the ordinary Design2 route keeps the initial
   `$readmemh` process loud, while the source-shaped memory route loads its
   literal file at time zero. -/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.readmemh_rom.agree

open LeanModels.Sv

load_design_sv2 readmemhRom from
  "Examples/system-verilog/sem2/readmemh_rom/readmemh_rom.sv.json"

#guard (match readmemhRom.pdesign.processes with
  | .initial (.block [.unsupported k msg]) :: _ =>
      k == "SystemTask:readmemh" &&
      msg == "file=rom.hex;target=rom;data=00,11,22,33"
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
