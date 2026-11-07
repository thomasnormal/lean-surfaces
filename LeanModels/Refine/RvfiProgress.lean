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

/-! The result below is the public stream-level shape of the R2 claim.  A
loaded-core proof still supplies the indexed per-cycle invariant and the
progress witness; this structure keeps the resulting certificate, normalized
trace, and target-state relation together at each finite target prefix. -/

/-- A single target-prefix witness for an all-prefix RV32I refinement. -/
structure Rv32iPrefixRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (schedule target : Nat → Input) (k : Nat) where
  boundary : Nat
  program : List Rv32iInstruction
  certificate :
    Rv32iRvfiCycleTrace machine start coreState memoryState
      (schedulePrefix schedule boundary) program
  trace_eq :
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState (schedulePrefix schedule boundary)) =
      some (trace (rvMemoryMachineWith profile) memoryState
        (schedulePrefix target k))
  state_rel :
    rel (rvfiStateAfter machine coreState (schedulePrefix schedule boundary))
      (rvMemoryStateAfter profile memoryState (schedulePrefix target k))

/-- The all-prefix stream refinement exposed to a loaded-core theorem. -/
def Rv32iAllPrefixRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat,
    Nonempty (Rv32iPrefixRefinement profile machine rel start coreState
      memoryState schedule target k)

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

/-! The state form below ties the existential mixed program back to the
target's own stateful ISA execution.  This is the form a whole-core theorem
usually consumes: the final relation is stated over the target prefix rather
than over an auxiliary decoder list. -/

/-- The all-prefix mixed RVFI result with the final relation expressed over
the stateful ISA machine run on the target retirement-input prefix. -/
theorem rv32i_progress_trace_refines_state
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
          (rvMemoryStateAfter profile memoryState (schedulePrefix target k)) := by
  intro k
  rcases progress k with ⟨n, htarget⟩
  have hall : ∀ input ∈ schedulePrefix schedule n, admit input := by
    intro input hmem
    exact schedulePrefix_admit schedule admit hschedule n input hmem
  obtain ⟨program, certificate, htrace, hfinal⟩ :=
    rv32iRvfiCycleTrace_of_step_refines profile machine rel admit hstep
      start coreState memoryState (schedulePrefix schedule n) hrel hall
  have hinputs : rv32iProgramInputs memoryState program =
      schedulePrefix target k := by
    calc
      rv32iProgramInputs memoryState program =
          retireInputs machine.toCycleMachine coreState
            (schedulePrefix schedule n) := certificate.retireInputs_eq.symm
      _ = schedulePrefix target k := htarget
  have hstate : rv32iProgramState memoryState program =
      rvMemoryStateAfter profile memoryState (schedulePrefix target k) := by
    calc
      rv32iProgramState memoryState program =
          machineStateAfter (rvMemoryMachineWith profile) memoryState
            (rv32iProgramInputs memoryState program) :=
        (rvMemoryMachineWith_rv32i_program_state profile memoryState program).symm
      _ = machineStateAfter (rvMemoryMachineWith profile) memoryState
            (schedulePrefix target k) := by rw [hinputs]
      _ = rvMemoryStateAfter profile memoryState (schedulePrefix target k) := rfl
  have htrace' : normalizeRvfiTrace? start
        (rvfiObservations machine coreState (schedulePrefix schedule n)) =
      some (trace (rvMemoryMachineWith profile) memoryState
        (schedulePrefix target k)) := by
    calc
      normalizeRvfiTrace? start
          (rvfiObservations machine coreState (schedulePrefix schedule n)) =
          some (trace (rvMemoryMachineWith profile) memoryState
            (retireInputs machine.toCycleMachine coreState
              (schedulePrefix schedule n))) := htrace
      _ = some (trace (rvMemoryMachineWith profile) memoryState
            (schedulePrefix target k)) := by rw [htarget]
  refine ⟨n, program, certificate, htrace', ?_⟩
  exact hstate ▸ hfinal

/-! The structure-valued form is the reusable R2 boundary. -/

/-- The mixed RV32I invariant and progress witness establish the public
all-prefix refinement contract. -/
theorem rv32i_progress_refinement
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (hrel : rel coreState memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine coreState schedule target) :
    Rv32iAllPrefixRefinement profile machine rel start coreState memoryState
      schedule target := by
  unfold Rv32iAllPrefixRefinement
  intro k
  rcases rv32i_progress_trace_refines_state profile machine rel admit hstep
      start coreState memoryState hrel hschedule progress k with
    ⟨boundary, program, certificate, trace_eq, state_rel⟩
  exact ⟨{
    boundary := boundary
    program := program
    certificate := certificate
    trace_eq := trace_eq
    state_rel := state_rel }⟩

/-- The reset-specialized form of the R2 contract: RVFI order starts at zero,
the core starts at its loaded-machine state, and the ISA starts at the
profile's stateful-machine initial state. -/
def Rv32iResetRefinement {State : Type}
    (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop)
    (schedule target : Nat → Input) : Prop :=
  Rv32iAllPrefixRefinement profile machine rel 0 machine.init
    (rvMemoryMachineWith profile).init schedule target

/-- A reset relation, indexed step invariant, and explicit target progress
establish the all-prefix refinement contract from reset. -/
theorem rv32i_reset_refinement
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget machine machine.init schedule target) :
    Rv32iResetRefinement profile machine rel schedule target := by
  exact rv32i_progress_refinement profile machine rel admit hstep
    0 machine.init (rvMemoryMachineWith profile).init hinit hschedule progress

end LeanModels.Refine

#print axioms LeanModels.Refine.rv32i_progress_trace_refines
#print axioms LeanModels.Refine.rv32i_progress_trace_refines_state
#print axioms LeanModels.Refine.rv32i_progress_refinement
#print axioms LeanModels.Refine.rv32i_reset_refinement
