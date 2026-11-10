/- Clean-room item-2 memory witness: the source-shaped combinational read
   process observes the same parameter-sized memory after an NBA commit. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».sem2.unpacked_memory_comb.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unpackedMemoryComb from
  "Examples/system-verilog/sem2/unpacked_memory_comb/unpacked_memory_comb.sv.json"

private def memD : MemDesign2 := unpackedMemoryComb.pdesign.instantiateMemD2 [4]

#guard memD.memDecls.length == 1
#guard (match memD.processes with
  | .alwaysFF "clk" (.ifStmt (.ident "we")
      (.nbaAssignL (.arrayElem "mem" [.ident "widx"]) (.ident "d")) none) ::
      .alwaysComb (.block [.blockingAssign "q" (.arrayElem "mem" [.ident "ridx"])]) :: _ => true
  | _ => false)

#guard match runMem2 memD 128
    [[("clk", .ofNat 1 0), ("we", .ofNat 1 0),
      ("widx", .ofNat 2 0), ("ridx", .ofNat 2 0), ("d", .ofNat 8 0)],
     [("clk", .ofNat 1 1), ("we", .ofNat 1 1),
      ("widx", .ofNat 2 2), ("ridx", .ofNat 2 2), ("d", .ofNat 8 165)],
     [("clk", .ofNat 1 0), ("we", .ofNat 1 0),
      ("widx", .ofNat 2 0), ("ridx", .ofNat 2 2), ("d", .ofNat 8 0)]] with
  | .ok [s0, s1, s2] =>
      SvState.showSignal s0 "q" == "xxxxxxxx" &&
      SvState.showSignal s1 "q" == "10100101" &&
      SvState.showSignal s2 "q" == "10100101"
  | _ => false

end Examples.«system-verilog».sem2.unpacked_memory_comb.agree
