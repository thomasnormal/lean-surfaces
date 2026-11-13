import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 picorv32AluCase from
  "Examples/system-verilog/sem2/picorv32_alu_case_canonical_e/picorv32_alu_case_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("reg_op1", .ofNat 32 5), ("reg_op2", .ofNat 32 3),
    ("instr_beq", .ofNat 1 1), ("instr_bne", .ofNat 1 0),
    ("instr_bge", .ofNat 1 0), ("instr_bgeu", .ofNat 1 0),
    ("instr_xor", .ofNat 1 0), ("instr_or", .ofNat 1 0),
    ("instr_and", .ofNat 1 0), ("is_slti_blt_slt", .ofNat 1 0),
    ("is_sltiu_bltu_sltu", .ofNat 1 0), ("is_alu", .ofNat 1 0),
    ("is_compare", .ofNat 1 1), ("alu_eq", .ofNat 1 1),
    ("alu_lts", .ofNat 1 0), ("alu_ltu", .ofNat 1 0),
    ("alu_add_sub", .ofNat 32 8)],
   [("reg_op1", .ofNat 32 5), ("reg_op2", .ofNat 32 3),
    ("instr_beq", .ofNat 1 0), ("instr_bne", .ofNat 1 0),
    ("instr_bge", .ofNat 1 0), ("instr_bgeu", .ofNat 1 0),
    ("instr_xor", .ofNat 1 1), ("instr_or", .ofNat 1 0),
    ("instr_and", .ofNat 1 0), ("is_slti_blt_slt", .ofNat 1 0),
    ("is_sltiu_bltu_sltu", .ofNat 1 0), ("is_alu", .ofNat 1 0),
    ("is_compare", .ofNat 1 0), ("alu_eq", .ofNat 1 0),
    ("alu_lts", .ofNat 1 0), ("alu_ltu", .ofNat 1 0),
    ("alu_add_sub", .ofNat 32 8)]]

def outputs : Res (List String) := do
  let d ← picorv32AluCase.e 0
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "alu_out")

#guard match picorv32AluCase.e 0 with
  | .ok d => d.memories.size == 0 && d.processes.size == 1
  | _ => false
#guard outputs == .ok ["00000000000000000000000000000001", "00000000000000000000000000000110"]

end Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e
