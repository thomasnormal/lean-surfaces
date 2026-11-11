import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Clean-room E receipt for an undriven scalar net beside unpacked memory. -/

namespace Examples.«system-verilog».sem2.unpacked_memory_netz_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 netzE
  from "Examples/system-verilog/sem2/unpacked_memory_netz_e/unpacked_memory_netz_e.sv.json"

private def design : Res MemEDesign :=
  MemEDesign.ofPDesign netzE.pdesign [4]

private def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 0xa5)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0xa5)]]

private def runRows (d : MemEDesign) (s : MemEState) :
    List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

private def outputs : Except String (List (Option LVec × Option LVec)) :=
  match design with
  | .ok d =>
      match runRows d d.init stimuli with
      | .ok ss => .ok (ss.map fun s =>
          (SvState.lookup s.scalar "q", SvState.lookup s.scalar "zq"))
      | .error e => .error e
  | .timeout => .error "memory design elaboration timed out"
  | .unsupported e => .error e

#guard netzE.pdesign.others == [("NetSymbol:net-z", "pcpi_mul_wr")]

#guard match MemEDesign.ofPDesign
    { netzE.pdesign with others := [("NetSymbol:unknown", "w")] } [4] with
  | .unsupported "E memory route does not yet admit unsupported module members" => true
  | _ => false

#guard match design with
  | .ok d =>
      d.others == netzE.pdesign.others &&
      (d.decls.find? (·.name == "pcpi_mul_wr")).map (fun dc =>
        (dc.width, dc.isNet, dc.init)) ==
        some (1, true, some (LVec.replicate 1 .lz))
  | .timeout => false
  | .unsupported _ => false

#guard match outputs with
  | .ok [(q0, z0), (q1, z1), (q2, z2)] =>
      q0 == some (LVec.xVec 8) && z0 == some (LVec.replicate 1 .lz) &&
      q1 == some (LVec.ofNat 8 0xa5) && z1 == some (LVec.replicate 1 .lz) &&
      q2 == some (LVec.ofNat 8 0xa5) && z2 == some (LVec.replicate 1 .lz)
  | _ => false

end Examples.«system-verilog».sem2.unpacked_memory_netz_e
