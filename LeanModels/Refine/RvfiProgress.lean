import LeanModels.Refine.Progress
import LeanModels.Refine.RvfiRv32iProgram

/-!
# All-prefix progress for mixed RVFI refinement

`Rv32iRvfiCycleTrace_of_step_refines` gives the end-to-end result for one
finite cycle window.  A real core runs on an unbounded cycle schedule, so its
refinement statement also needs an explicit progress witness: every finite
prefix of the target retirement-input stream is reached at some finite cycle
boundary.  This file states that witness for the packed RVFI boundary and
combines it with the mixed RV32I certificate.

The target is an input schedule rather than a guessed decoder stream.  The
per-cycle invariant remains responsible for identifying each valid row as an
admitted `Rv32iInstruction`; the progress witness only says where a target
prefix appears.  Thus no scheduler, retirement order, or instruction choice
is hidden in this layer.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Explicit progress at the RVFI cycle boundary -/

/-- Every finite target input prefix is retained by `retireInputs` at some
    finite boundary of the packed cycle schedule. -/
def Rv32iRetiresTarget {State : Type}
    (machine : RvfiCycleMachine State) (initial : State)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat, ∃ n : Nat,
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target k

theorem schedulePrefix_admit {α : Type} (schedule : Nat → α)
    (admit : α → Prop) (hschedule : ∀ n, admit (schedule n)) :
    ∀ n input, input ∈ schedulePrefix schedule n → admit input := by
  intro n
  induction n with
  | zero =>
      intro input hmem
      simp [schedulePrefix] at hmem
  | succ n ih =>
      intro input hmem
      simp only [schedulePrefix_succ, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hschedule n
      · exact ih input hmem

/-! ## Mixed RV32I all-prefix theorem -/

/-- An indexed mixed per-cycle invariant plus explicit progress gives the
    stateful ISA trace for every finite target prefix.

    The existential program and certificate are retained in the result, so a
    caller can also consume the post-window core relation rather than merely
    comparing normalized observations. -/
theorem rv32i_progress_trace_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (hrel : rel coreState memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine coreState schedule target) :
    ∀ k : Nat, ∃ n : Nat, ∃ program : List Rv32iInstruction,
      ∃ _certificate :
        Rv32iRvfiCycleTrace machine start coreState memoryState
          (schedulePrefix schedule n) program,
        normalizeRvfiTrace? start
            (rvfiObservations machine coreState (schedulePrefix schedule n)) =
          some (trace (rvMemoryMachineWith profile) memoryState
            (schedulePrefix target k)) ∧
        rel (rvfiStateAfter machine coreState (schedulePrefix schedule n))
          (rv32iProgramState memoryState program) := by
  intro k
  rcases progress k with ⟨n, htarget⟩
  have hall : ∀ input ∈ schedulePrefix schedule n, admit input := by
    intro input hmem
    exact schedulePrefix_admit schedule admit hschedule n input hmem
  obtain ⟨program, certificate, htrace, hfinal⟩ :=
    rv32iRvfiCycleTrace_of_step_refines profile machine rel admit hstep
      start coreState memoryState (schedulePrefix schedule n) hrel hall
  refine ⟨n, program, certificate, ?_, hfinal⟩
  calc
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState (schedulePrefix schedule n)) =
        some (trace (rvMemoryMachineWith profile) memoryState
          (retireInputs machine.toCycleMachine coreState
            (schedulePrefix schedule n))) := htrace
    _ = some (trace (rvMemoryMachineWith profile) memoryState
          (schedulePrefix target k)) := by rw [htarget]

end LeanModels.Refine

#print axioms LeanModels.Refine.rv32i_progress_trace_refines
