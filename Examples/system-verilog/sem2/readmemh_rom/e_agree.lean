/- Clean-room E memory witness: a structured `$readmemh` task performs its
   time-zero write before the direct memory-backed continuous assignment. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

namespace Examples.«system-verilog».sem2.readmemh_rom.e_agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 readmemhRomE
  from "Examples/system-verilog/sem2/readmemh_rom/readmemh_rom.sv.json"

def design : Res MemEDesign :=
  MemEDesign.ofPDesign readmemhRomE.pdesign []

def stimulus : List SvState :=
  [[("addr", LVec.lit "00")],
   [("addr", LVec.lit "01")],
   [("addr", LVec.lit "10")],
   [("addr", LVec.lit "11")],
   [("addr", LVec.lit "xx")]]

def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

#guard match design with
  | .ok d =>
      d.readmemh.length == 1 &&
      d.sourceDecls.length == 6 &&
      (MemEDesign.initialBodies d.processes).length == 1
  | _ => false

#guard match design with
  | .ok d =>
      match MemEDesign.flatIndices "rom"
          (d.sourceDecls.filter (fun pd => pd.flatBase == some "rom")) with
      | .ok [0, 1, 2, 3] => true
      | _ => false
  | _ => false

#guard !MemEDesign.flatOrderOk [0, 2, 1]

#guard match design with
  | .ok d =>
      match d.timeZero with
      | .ok s =>
          SvState.lookup s.scalar "rom[0]" == some (LVec.ofNat 8 0) &&
          SvState.lookup s.scalar "rom[1]" == some (LVec.ofNat 8 17) &&
          SvState.lookup s.scalar "rom[2]" == some (LVec.ofNat 8 34) &&
          SvState.lookup s.scalar "rom[3]" == some (LVec.ofNat 8 51)
      | _ => false
  | _ => false

#guard match design with
  | .ok d =>
      match d.timeZero with
      | .ok s =>
          match runRows d s stimulus with
          | .ok [s0, s1, s2, s3, sx] =>
              SvState.lookup s0.scalar "q" == some (LVec.ofNat 8 0) &&
              SvState.lookup s1.scalar "q" == some (LVec.ofNat 8 17) &&
              SvState.lookup s2.scalar "q" == some (LVec.ofNat 8 34) &&
              SvState.lookup s3.scalar "q" == some (LVec.ofNat 8 51) &&
              SvState.lookup sx.scalar "q" == some (LVec.xVec 8)
          | _ => false
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.readmemh_rom.e_agree
