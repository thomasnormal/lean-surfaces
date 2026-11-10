/-
Clean-room E body activation for PicoRV32's TWO_CYCLE_ALU body.

The source envelope retains the plain `always @*` event-controlled process;
its frozen process boundary remains loud because E has no event-list constructor.
This packet enters the retained six-statement body through `instStmt2` in a
lexical context built from the loaded port declarations, and proves one
fuel-free `execBody` activation. It does not claim native `@*` scheduling or
whole-core execution.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombFragE

namespace Examples.«system-verilog».sem2.picorv32_alu_body_e.agree

open LeanModels.Sv LeanModels.Sv.Kernel LeanModels.Sv.Loop2

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

load_design_sv2 picorv32AluBodyE
  from "Examples/system-verilog/sem2/picorv32_alu_body_e/picorv32_alu_body_e.sv.json"

/-- The retained source body is a block of the six original assignments. -/
def sourceStmts : List PStmt :=
  match picorv32AluBodyE.pdesign.processes with
  | [.alwaysImplicit (.block xs)] => xs
  | _ => []

#guard picorv32AluBodyE.pdesign.others == []
#guard match picorv32AluBodyE.pdesign.processes with
  | [.alwaysImplicit (.block xs)] => xs.length == 6
  | _ => false
#guard match picorv32AluBodyE.pdesign.instantiateD2 [] |>.processes.toList with
  | [.unsupported "ProceduralBlockSymbol:Always" _] => true
  | _ => false

/- The port declarations are the lexical E context.  `elems` is retained for
   the constant part-select `reg_op2[4:0]`; omitting it would manufacture a
   `PartSel:base` refusal. -/
def frozen : Design2 := picorv32AluBodyE.pdesign.instantiateD2 []
def decls : Array Decl := frozen.decls
def env : IEnv := {
  int32 := true
  dims := decls.toList.map (fun dc => (dc.name, []))
  widths := decls.toList.map (fun dc => (dc.name, dc.width))
}
def elems : List (String × Nat) := decls.toList.map (fun dc => (dc.name, 1))
def body : Stmt2 := .block (instStmts2 env elems sourceStmts).toArray

def bodyDesign : Design2 := {
  name := frozen.name
  decls := decls
  processes := #[.alwaysComb body]
}
def bodyE : Elab := Elab.ofDesign2 bodyDesign

#guard body.combOk bodyDesign
#guard match body with
  | .block ss => ss.size == 6
  | _ => false
#guard bodyDesign.processes.toList.all fun p =>
  match p with | .alwaysComb _ => true | _ => false

/-- One concrete input activation (all five controls are known). -/
def inputEntry : SvState :=
  [("reg_op1", .ofNat 32 5), ("reg_op2", .ofNat 32 3),
   ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 0),
   ("instr_srai", .ofNat 1 0)]
def inputStore : Store := bodyE.applyInputs bodyE.initStore inputEntry

def runView (s : Store) : Option SvState :=
  match execBody bodyE body s with
  | .ok (.ok (), s') => some (bodyE.view s')
  | _ => none

def outputNames : List String :=
  ["alu_add_sub", "alu_eq", "alu_lts", "alu_ltu", "alu_shl", "alu_shr"]
def outputRow : Option (List String) :=
  (runView inputStore).map (fun st => outputNames.map (SvState.showSignal st))

#guard outputRow == some [
  "00000000000000000000000000001000", "0", "0", "0",
  "00000000000000000000000000101000", "00000000000000000000000000000000"]

/-- E's existing body soundness theorem supplies the activation result for
    every typed store admitted by the body checker.  The concrete row above
    supplies the kernel-computed witness for this clean-room point. -/
theorem body_activation (h4 : AllFour bodyE)
    (hok : body.combOk bodyE.toDesign2 = true)
    (hclaim : body.claims bodyE.toDesign2 (bodyE.view inputStore)) :
    ∃ s', execBody bodyE body inputStore = .ok (.ok (), s') ∧
      bodyE.Typed s' ∧ bodyE.view s' = body.sem bodyE.toDesign2 (bodyE.view inputStore) := by
  exact Stmt2.sem_run h4 hok
    (Elab.typed_initStore bodyE |>.applyInputs inputEntry) hclaim


def rowOf (s : Store) : Option (List String) :=
  (runView s).map (fun st => outputNames.map (SvState.showSignal st))
def rowInputs : List SvState :=
  [[("reg_op1", .ofNat 32 5), ("reg_op2", .ofNat 32 3),
    ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 0), ("instr_srai", .ofNat 1 0)],
   [("reg_op1", .ofNat 32 5), ("reg_op2", .ofNat 32 3),
    ("instr_sub", .ofNat 1 1), ("instr_sra", .ofNat 1 0), ("instr_srai", .ofNat 1 0)],
   [("reg_op1", .ofNat 32 0x80000000), ("reg_op2", .ofNat 32 4),
    ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 1), ("instr_srai", .ofNat 1 0)],
   [("reg_op1", .ofNat 32 0x80000000), ("reg_op2", .ofNat 32 4),
    ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 0), ("instr_srai", .ofNat 1 0)],
   [("reg_op1", ⟨List.replicate 32 .lx |>.toArray⟩), ("reg_op2", .ofNat 32 1),
    ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 0), ("instr_srai", .ofNat 1 0)],
   [("reg_op1", .ofNat 32 0x80000000), ("reg_op2", .ofNat 32 4),
    ("instr_sub", .ofNat 1 0), ("instr_sra", .ofNat 1 0), ("instr_srai", .ofNat 1 1)]]
def traceRows : List (Option (List String)) :=
  rowOf bodyE.initStore :: rowInputs.map (fun entry => rowOf (bodyE.applyInputs bodyE.initStore entry))
#eval traceRows

#print axioms body_activation

end Examples.«system-verilog».sem2.picorv32_alu_body_e.agree
