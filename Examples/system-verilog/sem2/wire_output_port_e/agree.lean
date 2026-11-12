import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.wire_output_port_e
open LeanModels.Sv
load_design_sv2 wireOutputPortE from
  "Examples/system-verilog/sem2/wire_output_port_e/wire_output_port_e.sv.json"
#guard wireOutputPortE.pdesign.others == []
#guard match wireOutputPortE.sem.decls.toList with
  | [_, { name := "y", isNet := true, isOutput := true, .. }] => true
  | _ => false
#guard match wireOutputPortE.sem.processes.toList with
  | [.assign (.ident "y") (.ident "a")] => true
  | _ => false
end Examples.«system-verilog».sem2.wire_output_port_e
