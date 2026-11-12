import LeanModels.Sv.Ingest2

/-! The committed envelope is the `FEATURE` branch selected by Slang's
    preprocessor (`extract.py --top ifdef_define_e -D FEATURE=1`). -/

namespace Examples.«system-verilog».sem2.ifdef_define_e.agree

open LeanModels.Sv

load_design_sv2 ifdefDefineE
  from "Examples/system-verilog/sem2/ifdef_define_e/ifdef_define_e.sv.json"

#guard ifdefDefineE.pdesign.others == []
#guard match ifdefDefineE.pdesign.processes with
  | [.assign "y" (.ident "a")] => true
  | _ => false

end Examples.«system-verilog».sem2.ifdef_define_e.agree
