import LeanModels.Refine.RvfiTrap
import LeanModels.Refine.RvfiSystem
import LeanModels.Refine.RvfiFence
import LeanModels.Refine.RvfiJump
import LeanModels.Refine.RvfiBranch
import LeanModels.Refine.RvfiAlu
import LeanModels.Refine.RvfiMemAll
import LeanModels.Refine.RvfiCsr
import LeanModels.Refine.RvfiAddi
import LeanModels.Refine.RvfiUpper
import LeanModels.Refine.RvfiMem

/-!
# Unified RV32I RVFI boundary

The individual RVFI predicates retain each instruction family's exact wire
fields.  `Rv32iBoundary` is the family dispatcher a loaded-core invariant can
consume: it is indexed by the architectural post-state and retirement, so a
proof cannot erase which state transition a valid row supplied.  The union is
deliberately limited to RV32I plus the admitted machine-mode system/CSR and
trap cases; M-extension operations and interrupt dispatch remain outside this
R2 boundary.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Indexed family union -/

inductive Rv32iBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) : RvMemoryState → Retirement → Prop where
  | alu (w : Word) (op : AluOp) (rd : Reg) (src1 : Src1) (src2 : Src2)
      (h : o.aluBoundary s input w op rd src1 src2) :
      Rv32iBoundary s input o
        { arch := aluNext s op rd src1 src2, memory := input.memory }
        (aluRetirement s input op rd src1 src2)
  | branch (w : Word) (cond : BranchCond) (rs1 rs2 : Reg) (offset : Word)
      (h : o.branchBoundary s input w cond rs1 rs2 offset) :
      Rv32iBoundary s input o
        { arch := branchNext s cond rs1 rs2 offset, memory := input.memory }
        (branchRetirement s input cond rs1 rs2 offset)
  | jal (w : Word) (rd : Reg) (offset : Word)
      (h : o.jalBoundary s input w rd offset) :
      Rv32iBoundary s input o
        { arch := jalNext s rd offset, memory := input.memory }
        (jalRetirement s input rd offset)
  | jalr (w : Word) (rd rs1 : Reg) (offset : Word)
      (h : o.jalrBoundary s input w rd rs1 offset) :
      Rv32iBoundary s input o
        { arch := jalrNext s rd rs1 offset, memory := input.memory }
        (jalrRetirement s input rd rs1 offset)
  | mem (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
      (h : o.memBoundary s input w kind r rs1 imm) :
      Rv32iBoundary s input o
        { arch := memNext s input.memory kind r rs1 imm,
          memory := memAfter input.memory s kind r rs1 imm }
        (memRetirement s input kind r rs1 imm)
  | fence (w : Word) (kind : FenceKind)
      (h : o.fenceBoundary s input w kind) :
      Rv32iBoundary s input o
        { arch := fenceNext s kind, memory := input.memory }
        (fenceRetirement s input kind)
  | system (w : Word) (kind : SysKind)
      (h : o.systemBoundary s input w kind) :
      Rv32iBoundary s input o
        { arch := systemNext s kind, memory := input.memory }
        (systemRetirement s input kind)
  | csr (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
      (h : o.csrBoundary s input w row kind) :
      Rv32iBoundary s input o
        { arch := csrNext s row kind, memory := input.memory }
        (csrRetirement s input row kind)
  | illegal (w : Word) (h : o.illegalBoundary s input w) :
      Rv32iBoundary s input o
        { arch := illegalNext s, memory := input.memory }
        (illegalRetirement s input)
  | illegalCsr (w : Word) (kind : CsrOpKind)
      (h : o.illegalCsrBoundary s input w kind) :
      Rv32iBoundary s input o
        { arch := illegalNext s, memory := input.memory }
        (illegalRetirement s input)

/-! ## Specialized-boundary adapters -/

theorem RvfiObservation.addiBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    Rv32iBoundary s input o
      { arch := aluNext s .add rd (.reg rs1) (.imm imm),
        memory := input.memory }
      (aluRetirement s input .add rd (.reg rs1) (.imm imm)) := by
  apply Rv32iBoundary.alu w .add rd (.reg rs1) (.imm imm)
  simpa [RvfiObservation.addiBoundary, RvfiObservation.aluBoundary,
    RvfiObservation.addiFields, RvfiObservation.aluFields,
    aluSrc1Fields, aluSrc2Fields, addiNext, aluNext,
    addiRetirement, aluRetirement, addiEffects, aluEffects,
    src1Val, src2Val, aluSem, and_assoc] using h

theorem RvfiObservation.luiBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd : Reg) (imm : Word)
    (h : o.luiBoundary s input w rd imm) :
    Rv32iBoundary s input o
      { arch := aluNext s .add rd (.reg 0) (.imm imm),
        memory := input.memory }
      (aluRetirement s input .add rd (.reg 0) (.imm imm)) := by
  apply Rv32iBoundary.alu w .add rd (.reg 0) (.imm imm)
  simpa [RvfiObservation.luiBoundary, RvfiObservation.aluBoundary,
    RvfiObservation.luiFields, RvfiObservation.aluFields,
    aluSrc1Fields, aluSrc2Fields, luiNext, aluNext,
    luiRetirement, aluRetirement, luiEffects, aluEffects,
    src1Val, src2Val, aluSem, and_assoc] using h

theorem RvfiObservation.auipcBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd : Reg) (imm : Word)
    (h : o.auipcBoundary s input w rd imm) :
    Rv32iBoundary s input o
      { arch := aluNext s .add rd .pc (.imm imm),
        memory := input.memory }
      (aluRetirement s input .add rd .pc (.imm imm)) := by
  apply Rv32iBoundary.alu w .add rd .pc (.imm imm)
  simpa [RvfiObservation.auipcBoundary, RvfiObservation.aluBoundary,
    RvfiObservation.auipcFields, RvfiObservation.aluFields,
    aluSrc1Fields, aluSrc2Fields, auipcNext, aluNext,
    auipcRetirement, aluRetirement, auipcEffects, aluEffects,
    src1Val, src2Val, aluSem, and_assoc] using h

theorem RvfiObservation.swBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    Rv32iBoundary s input o
      { arch := memNext s input.memory (.store .word) rs2 rs1 imm,
        memory := memAfter input.memory s (.store .word) rs2 rs1 imm }
      (memRetirement s input (.store .word) rs2 rs1 imm) := by
  apply Rv32iBoundary.mem w (.store .word) rs2 rs1 imm
  simpa [RvfiObservation.swBoundary, RvfiObservation.memBoundary,
    RvfiObservation.swFields, RvfiObservation.memFields,
    MemOp.toInstr, MemOp.toDir, MemOp.width, loadVal, maskOfWidth,
    swNext, memNext, swRetirement, memRetirement,
    swEffects, memEffects, memAfter, and_assoc] using h

theorem RvfiObservation.lwBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    Rv32iBoundary s input o
      { arch := memNext s input.memory (.load true .word) rd rs1 imm,
        memory := memAfter input.memory s (.load true .word) rd rs1 imm }
      (memRetirement s input (.load true .word) rd rs1 imm) := by
  apply Rv32iBoundary.mem w (.load true .word) rd rs1 imm
  simpa [RvfiObservation.lwBoundary, RvfiObservation.memBoundary,
    RvfiObservation.lwFields, RvfiObservation.memFields,
    MemOp.toInstr, MemOp.toDir, MemOp.width, loadVal, maskOfWidth,
    lwNext, memNext, lwRetirement, memRetirement,
    lwEffects, memEffects, memAfter, and_assoc] using h

theorem RvfiObservation.branchBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (cond : BranchCond) (rs1 rs2 : Reg) (offset : Word)
    (h : o.branchBoundary s input w cond rs1 rs2 offset) :
    Rv32iBoundary s input o
      { arch := branchNext s cond rs1 rs2 offset,
        memory := input.memory }
      (branchRetirement s input cond rs1 rs2 offset) := by
  exact Rv32iBoundary.branch w cond rs1 rs2 offset h

theorem RvfiObservation.jalBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd : Reg) (offset : Word)
    (h : o.jalBoundary s input w rd offset) :
    Rv32iBoundary s input o
      { arch := jalNext s rd offset,
        memory := input.memory }
      (jalRetirement s input rd offset) := by
  exact Rv32iBoundary.jal w rd offset h

theorem RvfiObservation.jalrBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (rd rs1 : Reg) (offset : Word)
    (h : o.jalrBoundary s input w rd rs1 offset) :
    Rv32iBoundary s input o
      { arch := jalrNext s rd rs1 offset,
        memory := input.memory }
      (jalrRetirement s input rd rs1 offset) := by
  exact Rv32iBoundary.jalr w rd rs1 offset h

theorem RvfiObservation.fenceBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (kind : FenceKind)
    (h : o.fenceBoundary s input w kind) :
    Rv32iBoundary s input o
      { arch := fenceNext s kind,
        memory := input.memory }
      (fenceRetirement s input kind) := by
  exact Rv32iBoundary.fence w kind h

theorem RvfiObservation.systemBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (kind : SysKind)
    (h : o.systemBoundary s input w kind) :
    Rv32iBoundary s input o
      { arch := systemNext s kind,
        memory := input.memory }
      (systemRetirement s input kind) := by
  exact Rv32iBoundary.system w kind h

theorem RvfiObservation.csrBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (h : o.csrBoundary s input w row kind) :
    Rv32iBoundary s input o
      { arch := csrNext s row kind,
        memory := input.memory }
      (csrRetirement s input row kind) := by
  exact Rv32iBoundary.csr w row kind h

theorem RvfiObservation.illegalBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (h : o.illegalBoundary s input w) :
    Rv32iBoundary s input o
      { arch := illegalNext s,
        memory := input.memory }
      (illegalRetirement s input) := by
  exact Rv32iBoundary.illegal w h

theorem RvfiObservation.illegalCsrBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (w : Word) (kind : CsrOpKind)
    (h : o.illegalCsrBoundary s input w kind) :
    Rv32iBoundary s input o
      { arch := illegalNext s,
        memory := input.memory }
      (illegalRetirement s input) := by
  exact Rv32iBoundary.illegalCsr w kind h

theorem Rv32iBoundary.toRetirement?_eq_some
    {s : ArchState} {input : Input} {o : RvfiObservation}
    {post : RvMemoryState} {retirement : Retirement}
    (h : Rv32iBoundary s input o post retirement) :
    o.toRetirement? = some retirement := by
  cases h with
  | alu _ _ _ _ _ h => exact h.2
  | branch _ _ _ _ _ h => exact h.2
  | jal _ _ _ h => exact h.2
  | jalr _ _ _ _ h => exact h.2
  | mem _ _ _ _ _ h => exact h.2
  | fence _ _ h => exact h.2
  | system _ _ h => exact h.2
  | csr _ _ _ h => exact h.2
  | illegal _ h => exact h.2
  | illegalCsr _ _ h => exact h.2

/-! ## Indexed transition projection -/

theorem Rv32iBoundary.rvMemoryMachineWith
    (profile : PlatformProfile) {s : ArchState} {input : Input}
    {o : RvfiObservation} {post : RvMemoryState} {retirement : Retirement}
    (h : Rv32iBoundary s input o post retirement) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input = (post, retirement) := by
  cases h with
  | alu w op rd src1 src2 h =>
      exact o.aluBoundary_rvMemoryMachineWith profile s input w op rd src1 src2 h
  | branch w cond rs1 rs2 offset h =>
      exact o.branchBoundary_rvMemoryMachineWith
        profile s input w cond rs1 rs2 offset h
  | jal w rd offset h =>
      exact o.jalBoundary_rvMemoryMachineWith profile s input w rd offset h
  | jalr w rd rs1 offset h =>
      exact o.jalrBoundary_rvMemoryMachineWith profile s input w rd rs1 offset h
  | mem w kind r rs1 imm h =>
      exact o.memBoundary_rvMemoryMachineWith profile s input w kind r rs1 imm h
  | fence w kind h =>
      exact o.fenceBoundary_rvMemoryMachineWith profile s input w kind h
  | system w kind h =>
      exact o.systemBoundary_rvMemoryMachineWith profile s input w kind h
  | csr w row kind h =>
      exact o.csrBoundary_rvMemoryMachineWith profile s input w row kind h
  | illegal w h =>
      exact o.illegalBoundary_rvMemoryMachineWith profile s input w h
  | illegalCsr w kind h =>
      exact o.illegalCsrBoundary_rvMemoryMachineWith profile s input w kind h

/-! ## One core-facing RV32I dispatcher -/

/-- A loaded RV32I core can discharge one valid cycle through one indexed
family witness.  The extra `wellFormed` premise is exposed at this dispatcher
because the individual predicates already carry it, but keeping it explicit
makes the generic cycle theorem independent of their tuple layout. -/
theorem rvfiCycleStepRefines_of_rv32i_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ post retirement,
          input.memory = memoryState.memory ∧
          observation.wellFormed ∧
          Rv32iBoundary memoryState.arch input observation post retirement ∧
          rel state' post
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ post retirement,
        input.memory = memoryState.memory ∧
        observation.wellFormed ∧
        Rv32iBoundary memoryState.arch input observation post retirement ∧
        rel state' post := by
      simpa [hv] using hcase
    rcases hcase' with ⟨post, retirement, hmem, hwell, hboundary, hrel'⟩
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepBoundary := hboundary.rvMemoryMachineWith profile
    have hstepBoundary' :
        (rvMemoryMachineWith profile).step memoryState input =
          (post, retirement) := by
      rw [hstate]
      simpa [hmem] using hstepBoundary
    have hsome := observation.toRetirement?_eq_some hv hwell
    have hboundarySome := hboundary.toRetirement?_eq_some
    have hto : observation.toRetirement = retirement :=
      Option.some.inj (hsome.symm.trans hboundarySome)
    simp only [hv]
    exact ⟨post, retirement, hmem, hwell,
      hto, hstepBoundary', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.Rv32iBoundary.rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_rv32i_memory

end LeanModels.Refine
