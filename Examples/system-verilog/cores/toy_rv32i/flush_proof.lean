import Examples.«system-verilog».cores.toy_rv32i.packet_proof

/-!
# Flush-aware refinement example

The first cycle changes a speculative phase and flushes without an ISA step;
the next cycle retires ADDI.  The architectural relation ignores the phase,
which is the shape a real branch-recovery proof will use.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.flush_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof

structure FlushState where
  arch : ArchState
  phase : Nat

def flushMachine : FlushMachine FlushState where
  init := { arch := ArchState.init 0, phase := 0 }
  step s _ :=
    if s.phase = 0 then
      ({ arch := s.arch, phase := 1 }, .flush)
    else
      let next := toyNext s.arch
      ({ arch := next, phase := 1 },
        .retire [(addiInput, Retirement.ofRvStep s.arch addiInput next
          (toyEffects s.arch))])

def flushRel (s : FlushState) (a : ArchState) : Prop :=
  s.arch = a ∧ a.csrs = {} ∧ a.WF

theorem flush_step_refines :
    FlushStepRefines flushMachine rvMachine flushRel toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro s a cycleInput hrel
  rcases hrel with ⟨harch, hcsrs, hWF⟩
  cases s with
  | mk arch phase =>
      have harch' : arch = a := harch
      subst arch
      by_cases hp : phase = 0
      · simp [flushMachine, hp, flushRel, hcsrs, hWF]
      · simp only [flushMachine, hp, ↓reduceIte]
        refine ⟨toyNext a, ?_, ?_⟩
        · exact ⟨rfl, hcsrs, by simpa [toyNext, ArchState.WF] using hWF⟩
        · have hstep :
              rvMachine.step a addiInput =
                (toyNext a, Retirement.ofRvStep a addiInput
                  (toyNext a) (toyEffects a)) := by
            simp only [rvMachine, addiInput]
            rw [isa_addi_step a zeroMem hcsrs hWF]
          refine PacketRefines.cons ?_ hstep rfl (PacketRefines.nil _)
          simp [toyAdmits, addiInput, zeroMem]

theorem flush_trace_one :
    flushTrace flushMachine flushMachine.init [addiInput, addiInput] =
      trace rvMachine rvMachine.init [addiInput] := by
  have h := flush_trace_refines flush_step_refines
      flushMachine.init rvMachine.init [addiInput, addiInput]
      (by exact ⟨rfl, rfl, rfl⟩)
  simpa [flushMachine, flushTrace, flushInputs] using h

#guard (flushTrace flushMachine flushMachine.init [addiInput, addiInput]).length == 1
#guard (flushInputs flushMachine flushMachine.init [addiInput, addiInput]).length == 1

#print axioms flush_step_refines
#print axioms flush_trace_one

end Examples.«system-verilog».cores.toy_rv32i.flush_proof
