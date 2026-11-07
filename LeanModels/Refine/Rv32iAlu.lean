import LeanModels.Refine.Commit
import LeanModels.Refine.Rvfi

/-!
# RV32I ALU retirement boundary

The ISA model buckets OP, OP-IMM, LUI, and AUIPC under one `.alu` constructor.
This boundary follows that semantic shape directly: the operation and both
operand sources remain parameters, while the architectural equations keep the
single register write and sequential pc advance explicit.  Specialized ADDI,
LUI, and AUIPC contracts remain available for callers that want decoded names.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The architectural state reached by one 32-bit RV32I ALU instruction. -/
def aluNext (s : ArchState) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) : ArchState :=
  { s.writeReg rd (aluSem op (src1Val s src1) (src2Val s src2)) with
    pc := s.pc + 4 }

/-- The architectural effects of one 32-bit RV32I ALU instruction. -/
def aluEffects (s : ArchState) : StepEffects :=
  { pcTarget := s.pc + 4 }

/-- The exact ISA-side boundary contract for an ALU parcel. -/
def aluRetirement (s : ArchState) (input : Input) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) : Retirement :=
  Retirement.ofRvStep s input (aluNext s op rd src1 src2) (aluEffects s)

/-- RVFI fields for the first ALU source.  A pc source has no architectural
register read; its wire fields are fixed to the neutral x0-shaped values used
by this boundary. -/
def aluSrc1Fields (s : ArchState) (o : RvfiObservation) : Src1 → Prop
  | .reg rs1 => o.rs1Addr = rs1 ∧ o.rs1Rdata = s.readReg rs1
  | .pc => o.rs1Addr = 0 ∧ o.rs1Rdata = 0

/-- RVFI fields for the second ALU source.  Immediate sources carry no
register read, so the boundary leaves their source fields unconstrained. -/
def aluSrc2Fields (s : ArchState) (o : RvfiObservation) : Src2 → Prop
  | .reg rs2 => o.rs2Addr = rs2 ∧ o.rs2Rdata = s.readReg rs2
  | .imm _ => True

/-- Every profile takes one non-trapping ISA step for a decoded ALU
instruction when interrupts are absent. -/
theorem isaStepWith_alu (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (hdecode : Fetched.decode (.word w) =
      some (.alu op rd src1 src2)) :
    isaStepWith profile s mem (.word w) 0 =
      (aluNext s op rd src1 src2, aluEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [aluNext, aluEffects, execInstr, Fetched.size]

/- The ALU contract with architectural memory threaded through the
one-instruction driver: ALU instructions preserve memory exactly. -/
theorem isaStepMemWith_alu (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (hdecode : Fetched.decode (.word w) =
      some (.alu op rd src1 src2)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (aluNext s op rd src1 src2, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_alu profile s mem w op rd src1 src2 hdecode]
  rfl

/-- The generic machine adapter exposes the same ALU commit boundary. -/
theorem rvMachineWith_alu (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (hdecode : Fetched.decode (.word w) =
      some (.alu op rd src1 src2)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (aluNext s op rd src1 src2,
        aluRetirement s { fetched := .word w, memory := mem, irq := 0 }
          op rd src1 src2) := by
  simp only [rvMachineWith]
  rw [isaStepWith_alu profile s mem w op rd src1 src2 hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_alu
#print axioms LeanModels.Refine.isaStepMemWith_alu
#print axioms LeanModels.Refine.rvMachineWith_alu

end LeanModels.Refine
