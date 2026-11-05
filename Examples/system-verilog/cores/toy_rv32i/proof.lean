import LeanModels.Refine

/-!
# R1 toy in-order core

This file is the compiled proof-shape test for the commit interface.  The SV
source beside it is intentionally tiny: it retires only `addi x1, x0, 1` and
holds an always-ready, zeroed memory.  The theorem is conditional on that
admitted input subset; an unsupported instruction is not turned into a fake
retirement.  The production-core proof will replace `toyMachine` with the
cycle-to-commit extraction of a real design while reusing `StepRefines` and
`trace_refines` unchanged.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.proof

open LeanModels.Rv
open LeanModels.Refine

def addiWord : Word := 0x00100093

def zeroMem : Memory := fun _ => 0

def toyNext (s : ArchState) : ArchState :=
  { s with
    pc := s.pc + 4
    regs := fun r => if r = (1 : Reg) then 1 else s.regs r }

def toyEffects (s : ArchState) : StepEffects :=
  { pcTarget := s.pc + 4 }

def toyMachine : Machine ArchState where
  init := ArchState.init 0
  step s input :=
    let s' := toyNext s
    (s', Retirement.ofRvStep s input s' (toyEffects s))

def toyAdmits (input : Input) : Prop :=
  input.fetched = .word addiWord ∧
  input.irq = 0 ∧
  ∀ address, input.memory address = 0

def toyRel (core isa : ArchState) : Prop :=
  core = isa ∧ isa.csrs = {} ∧ isa.WF

/-! The ISA calculation for the one admitted instruction. -/

theorem isa_addi_step (s : ArchState) (m : Memory)
    (hcsrs : s.csrs = {}) (hWF : s.WF) :
    isaStep s m (.word addiWord) 0 = (toyNext s, toyEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [hcsrs, takeInterrupt?, CsrFile.mstatusMie]
  have hdecode :
      Fetched.decode (.word addiWord) =
        some (.alu .add (1 : Reg) (.reg 0) (.imm (1 : BitVec 32))) := by
    decide
  simp only [isaStep, isaStepWith]
  rw [hirq, hdecode]
  have hx0 : s.regs 0 = 0 := by
    simpa [ArchState.WF] using hWF
  simp [toyNext, toyEffects, execInstr, src1Val, src2Val, aluSem,
    ArchState.writeReg, ArchState.readReg, Fetched.size, hcsrs, hx0]

/-! A one-step contract for the toy.  The invariant that x0 is zero is the
architectural well-formedness condition used by the RISC-V state. -/

theorem toy_step (s a : ArchState) (hsa : s = a) (hcsrs : a.csrs = {})
    (hWF : a.WF)
    (input : Input) (hi : toyAdmits input) :
    let (s', co) := toyMachine.step s input
    let (a', io) := rvMachine.step a input
    toyRel s' a' ∧ co = io := by
  rcases hi with ⟨hf, hiirq, hmem⟩
  subst s
  simp only [toyMachine, rvMachine]
  rw [hf, hiirq]
  rw [isa_addi_step a input.memory hcsrs hWF]
  have hx0 : a.regs 0 = 0 := by
    simpa [ArchState.WF] using hWF
  simp [toyRel, toyNext, ArchState.WF, hcsrs, hx0]

theorem toy_step_refines :
    StepRefines toyMachine rvMachine toyRel toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro c a input hrel hi
  rcases hrel with ⟨rfl, hcsrs, hWF⟩
  exact toy_step c c rfl hcsrs hWF input hi

/-! A finite stream of toy commits is exactly the ISA stream. -/

def addiInput : Input := { fetched := .word addiWord, memory := zeroMem }

theorem toy_trace_refines (n : Nat) :
    trace toyMachine toyMachine.init (List.replicate n addiInput) =
      trace rvMachine rvMachine.init (List.replicate n addiInput) := by
  refine trace_refines toy_step_refines _ _ _ ?_ ?_
  · exact ⟨rfl, rfl, rfl⟩
  · intro input hi
    have heq : input = addiInput := (List.mem_replicate.mp hi).2
    subst input
    simp [addiInput, toyAdmits, zeroMem]

theorem toy_trace_windows :
    trace toyMachine toyMachine.init ([addiInput] ++ [addiInput]) =
      trace toyMachine toyMachine.init [addiInput] ++
        trace toyMachine
          (machineStateAfter toyMachine toyMachine.init [addiInput])
          [addiInput] := by
  exact machineTrace_append toyMachine toyMachine.init
    [addiInput] [addiInput]

#guard (toyNext (ArchState.init 0)).pc == 4
#guard (toyNext (ArchState.init 0)).readReg 1 == 1
#guard (trace toyMachine toyMachine.init [addiInput]).length == 1
#guard (trace rvMachine rvMachine.init [addiInput]).length == 1
#guard (trace toyMachine toyMachine.init
  ([addiInput] ++ [addiInput])).length == 2

#print axioms toy_step_refines
#print axioms toy_trace_refines
#print axioms toy_trace_windows

end Examples.«system-verilog».cores.toy_rv32i.proof
