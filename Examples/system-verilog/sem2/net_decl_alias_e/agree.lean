/-
Clean-room E boundary for a source-shaped net declaration assignment.

`wire t = a` is retained as a continuous driver by the parser.  It remains
loud at the current E declaration boundary, so this fixture proves retention
and the exact refusal rather than claiming execution.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».sem2.net_decl_alias_e.agree

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 netDeclAliasE
  from "Examples/system-verilog/sem2/net_decl_alias_e/net_decl_alias_e.sv.json"

#guard netDeclAliasE.pdesign.others == []
#guard match netDeclAliasE.pdesign.decls.find? (fun d => d.name == "t") with
  | some d => d.isNet && d.init.isSome
  | none => false

#guard match netDeclAliasE.pdesign.processes with
  | [.assign "q" (.ident "t")] => true
  | _ => false

private def flat : Design2 := netDeclAliasE.pdesign.instantiateD2 []

#guard match flat.processes.toList with
  | [.unsupported "Instantiate"
      "decl 't': non-literal initializer outside the M0 tier"] => true
  | _ => false

private def memory : MemDesign2 := netDeclAliasE.pdesign.instantiateMemD2 []

#guard match memory.processes with
  | [.unsupported "Instantiate"
      "decl 't': non-literal net initializer is a continuous driver outside E"] => true
  | _ => false

end Examples.«system-verilog».sem2.net_decl_alias_e.agree
