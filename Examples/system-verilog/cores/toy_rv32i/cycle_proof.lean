import Examples.«system-verilog».cores.toy_rv32i.proof

/-!
# Cycle-to-retirement bridge example

The source beside this directory is a one-cycle toy, but a production core
usually needs several clock cycles before it retires an instruction.  This
example wraps the same admitted ADDI worker in a two-cycle pipeline: the first
cycle is a bubble and the second cycle commits.  The proof uses
`CycleStepRefines` and `cycle_trace_refines`; the architectural relation does
not expose the pipeline's pending bit.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.cycle_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof

structure PipelineState where
  arch : ArchState
  pending : Bool

def pipelineMachine : CycleMachine PipelineState where
  init := { arch := ArchState.init 0, pending := false }
  step s input :=
    if s.pending then
      let s' := toyNext s.arch
      ( { arch := s', pending := false },
        some (Retirement.ofRvStep s.arch input s' (toyEffects s.arch)) )
    else
      ({ arch := s.arch, pending := true }, none)

def pipelineRel (p : PipelineState) (a : ArchState) : Prop :=
  p.arch = a ∧ a.csrs = {} ∧ a.WF

theorem pipeline_step (p : PipelineState) (a : ArchState)
    (hrel : pipelineRel p a) (input : Input) (hi : toyAdmits input) :
    let (p', po) := pipelineMachine.step p input
    match po with
    | none => pipelineRel p' a
    | some coreRetirement =>
        let (a', isaRetirement) := rvMachine.step a input
        pipelineRel p' a' ∧ coreRetirement = isaRetirement := by
  rcases hrel with ⟨hpa, hcsrs, hWF⟩
  simp only [pipelineMachine]
  by_cases hp : p.pending
  · simp only [hp]
    rcases hi with ⟨hf, hiirq, hmem⟩
    simp only [rvMachine]
    rw [hf, hiirq]
    rw [isa_addi_step a input.memory hcsrs hWF]
    have hx0 : a.regs 0 = 0 := by
      simpa [ArchState.WF] using hWF
    simp [pipelineRel, hpa, toyNext, toyEffects,
      Retirement.ofRvStep, ArchState.WF, hcsrs, hx0]
  · simp only [hp]
    exact ⟨hpa, hcsrs, hWF⟩

theorem pipeline_step_refines :
    CycleStepRefines pipelineMachine rvMachine pipelineRel toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro p a input hrel hi
  exact pipeline_step p a hrel input hi

def pipelineInput : Input := addiInput

theorem pipeline_trace_refines (n : Nat) :
    cycleTrace pipelineMachine pipelineMachine.init
      (List.replicate (2 * n) pipelineInput) =
      trace rvMachine rvMachine.init (List.replicate n pipelineInput) := by
  have hinputs :
      retireInputs pipelineMachine pipelineMachine.init
        (List.replicate (2 * n) pipelineInput) =
        List.replicate n pipelineInput := by
    have aux : ∀ (k : Nat) (s : PipelineState), s.pending = false →
        retireInputs pipelineMachine s (List.replicate (2 * k) pipelineInput) =
          List.replicate k pipelineInput := by
      intro k
      induction k with
      | zero =>
          intro s _
          rfl
      | succ k ih =>
          intro s hs
          cases s with
          | mk arch pending =>
              cases pending with
              | false =>
                  have hrep : List.replicate (2 * (k + 1)) pipelineInput =
                      pipelineInput :: pipelineInput ::
                        List.replicate (2 * k) pipelineInput := by
                    rw [Nat.mul_succ]
                    have htwo : 2 * k + 2 = (2 * k + 1) + 1 := by omega
                    rw [htwo, List.replicate_succ, List.replicate_succ]
                  rw [hrep]
                  simp only [retireInputs, pipelineMachine, Bool.false_eq_true,
                    ↓reduceIte]
                  change pipelineInput ::
                    retireInputs pipelineMachine
                      { arch := toyNext arch, pending := false }
                      (List.replicate (2 * k) pipelineInput) =
                    List.replicate (k + 1) pipelineInput
                  rw [ih _ rfl, List.replicate_succ]
              | true =>
                  simp at hs
    exact aux n pipelineMachine.init rfl
  have h := cycle_trace_refines pipeline_step_refines
      pipelineMachine.init rvMachine.init (List.replicate (2 * n) pipelineInput)
      (by exact ⟨rfl, rfl, rfl⟩)
      (by
        intro input hi
        have heq : input = pipelineInput := (List.mem_replicate.mp hi).2
        subst input
        simp [pipelineInput, toyAdmits, addiInput, zeroMem])
  rw [h, hinputs]

#guard (cycleTrace pipelineMachine pipelineMachine.init
    [pipelineInput, pipelineInput]).length == 1

#print axioms pipeline_step_refines
#print axioms pipeline_trace_refines

end Examples.«system-verilog».cores.toy_rv32i.cycle_proof
