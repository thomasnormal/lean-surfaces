/- Clean-room R2 memory witness: a parameter-sized register file keeps its
   run-time read and write selectors as source-shaped memory operations. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

namespace Examples.«system-verilog».sem2.unpacked_register_memory.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unpackedRegisterMemory from
  "Examples/system-verilog/sem2/unpacked_register_memory/unpacked_register_memory.sv.json"

private def memD : MemDesign2 :=
  unpackedRegisterMemory.pdesign.instantiateMemD2 [4]

#guard memD.memDecls.length == 1
#guard (match memD.processes with
  | .alwaysFF "clk"
      (.ifStmt (.ident "we")
        (.nbaAssignL (.arrayElem "regs" [.ident "waddr"]) (.ident "d")) none) ::
      .assign "q" (.arrayElem "regs" [.ident "raddr"]) :: _ => true
  | _ => false)

#guard match runMem2 memD 128
    [[("clk", .ofNat 1 0), ("we", .ofNat 1 0),
      ("waddr", .ofNat 2 0), ("raddr", .ofNat 2 0), ("d", .ofNat 8 0)],
     [("clk", .ofNat 1 1), ("we", .ofNat 1 1),
      ("waddr", .ofNat 2 2), ("raddr", .ofNat 2 2), ("d", .ofNat 8 165)],
     [("clk", .ofNat 1 0), ("we", .ofNat 1 0),
      ("waddr", .ofNat 2 0), ("raddr", .ofNat 2 2), ("d", .ofNat 8 0)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "xxxxxxxx" &&
      SvState.showSignal s1 "q" == "10100101" &&
      SvState.showSignal s2 "q" == "10100101"
  | _ => false

end Examples.«system-verilog».sem2.unpacked_register_memory.agree
