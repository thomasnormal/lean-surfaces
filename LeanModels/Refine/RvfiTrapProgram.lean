import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iTrap

/-!
# Symbolic RVFI programs made only of RV32I trap instructions

`TrapInstruction` retains either an undecodable word or a decoded Zicsr
word whose CSR row is absent, together with the exact parser-derived proofs.
The folds below carry an arbitrary trap program through the stateful RV32I machine.  `TrapRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed illegal boundary for the next architectural
state.

This is the illegal-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded trap program -/

/-! The two illegal-instruction trap shapes retained by one decoded instruction. -/
inductive TrapInstruction where
  | word (word : Word) (decode : Fetched.decode (.word word) = none)
  | csr (word : Word) (kind : CsrOpKind)
      (decode : Fetched.decode (.word word) = some kind.toInstr)
      (row : findCsr? kind.addr = none)

def TrapInstruction.wordOf (instruction : TrapInstruction) : Word := by
  cases instruction with
  | word word decode => exact word
  | csr word kind decode row => exact word

/-- The architectural input associated with one trap instruction. -/
def trapProgramInput (memory : Memory) (instruction : TrapInstruction) : Input :=
  { fetched := .word instruction.wordOf, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a trap program.  Illegal instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def trapProgramInputs (memory : Memory) : List TrapInstruction → List Input
  | [] => []
  | instruction :: program =>
      trapProgramInput memory instruction :: trapProgramInputs memory program

/-- The architectural state after executing a trap program. -/
def trapProgramState (state : ArchState) : List TrapInstruction → ArchState
  | [] => state
  | _ :: program =>
      trapProgramState
        (illegalNext state) program

/-- The exact retirement stream for a trap program. -/
def trapProgramRetirements (memory : Memory) (state : ArchState) :
    List TrapInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      illegalRetirement state (trapProgramInput memory instruction) ::
        trapProgramRetirements memory
          (illegalNext state) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem trapProgramInputs_append (memory : Memory)
    (first second : List TrapInstruction) :
    trapProgramInputs memory (first ++ second) =
      trapProgramInputs memory first ++ trapProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, trapProgramInputs, ih, List.cons_append]

/-- The architectural illegal fold resumes from the state reached by its prefix. -/
theorem trapProgramState_append (state : ArchState)
    (first second : List TrapInstruction) :
    trapProgramState state (first ++ second) =
      trapProgramState (trapProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, trapProgramState]
      exact ih (state :=
        illegalNext state)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem trapProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List TrapInstruction) :
    trapProgramRetirements memory state (first ++ second) =
      trapProgramRetirements memory state first ++
        trapProgramRetirements memory (trapProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, trapProgramRetirements]
      rw [ih (state :=
        illegalNext state)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded trap instruction drives the exact illegal-instruction
transition with no memory update. -/
theorem rvMemoryMachineWith_trap_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : TrapInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (trapProgramInput memory instruction) =
      ({ arch := illegalNext state, memory := memory },
        illegalRetirement state (trapProgramInput memory instruction)) := by
  cases instruction with
  | word word decode =>
      simp only [rvMemoryMachineWith, trapProgramInput, TrapInstruction.wordOf]
      rw [isaStepWith_illegal profile state memory word decode]
      rfl
  | csr word kind decode row =>
      simp only [rvMemoryMachineWith, trapProgramInput, TrapInstruction.wordOf]
      rw [isaStepWith_illegal_csr profile state memory word kind decode row]
      rfl

/-- Threading the stateful ISA machine through every trap instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_trap_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List TrapInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory program) =
      { arch := trapProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [trapProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_trap_step profile state memory instruction]
      simpa [trapProgramState] using
        (ih (state := illegalNext state))

/-- The same trap program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_trap_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List TrapInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory program) =
      trapProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [trapProgramInputs, trace, trapProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (trapProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (trapProgramInput memory instruction)).1
            (trapProgramInputs memory program) = _
      rw [rvMemoryMachineWith_trap_step profile state memory instruction]
      simpa using
        (ih (state := illegalNext state))

/-- The stateful illegal machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_trap_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List TrapInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (trapProgramInputs memory first))
        (trapProgramInputs memory second) := by
  rw [trapProgramInputs_append, machineStateAfter_append]

/-- The stateful illegal retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_trap_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List TrapInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (trapProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (trapProgramInputs memory first))
          (trapProgramInputs memory second) := by
  rw [trapProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary trap program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied illegal
program. -/
inductive TrapRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List TrapInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      TrapRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List TrapInstruction}
      (hvalid : observation.valid = false)
      (tail : TrapRvfiTrace memory start state observations program) :
      TrapRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : TrapInstruction} {program : List TrapInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (trapProgramInput memory instruction) observation
          { arch := illegalNext state,
            memory := memory }
          (illegalRetirement state (trapProgramInput memory instruction)))
      (tail :
        TrapRvfiTrace memory (start + 1)
          (illegalNext state)
          observations program) :
      TrapRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic trap certificate is an ordinary RVFI normalization
certificate. -/
theorem TrapRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List TrapInstruction}
    (certificate : TrapRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (trapProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `TrapRvfiTrace` certificate. -/
theorem TrapRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List TrapInstruction}
    (certificate : TrapRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trapProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic trap stream is the stateful ISA trace for the same
program. -/
theorem TrapRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List TrapInstruction}
    (certificate : TrapRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (trapProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_trap_program_trace]

/-! ## Composing raw trap certificates -/

/-- Raw trap certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem TrapRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List TrapInstruction}
    (first : TrapRvfiTrace memory start state firstObservations firstProgram)
    (second : TrapRvfiTrace memory
      (start + firstProgram.length)
      (trapProgramState state firstProgram)
      secondObservations secondProgram) :
    TrapRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [trapProgramState] using second
  | bubble hvalid tail ih =>
      refine TrapRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [trapProgramState] using second
  | retire horder boundary tail ih =>
      refine TrapRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [trapProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The illegal invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact trap input
whose memory view it reports. -/
inductive TrapRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List TrapInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      TrapRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List TrapInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : TrapRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      TrapRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : TrapInstruction} {program : List TrapInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = trapProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (trapProgramInput memory instruction) observation
          { arch := illegalNext state,
            memory := memory }
          (illegalRetirement state (trapProgramInput memory instruction)))
      (tail : TrapRvfiCycleTrace machine memory (start + 1) coreState'
        (illegalNext state)
        cycles program) :
      TrapRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware trap certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem TrapRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List TrapInstruction}
    (certificate : TrapRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trapProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, trapProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware trap certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem TrapRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List TrapInstruction}
    (certificate : TrapRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      trapProgramInputs memory program := by
  induction certificate with
  | nil start coreState state => rfl
  | @bubble start coreState coreState' state cycleInput cycles program
      observation hstep hvalid tail ih =>
      have hstep' :
          machine.toCycleMachine.step coreState cycleInput =
            (coreState', none) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep,
          RvfiObservation.toRetirement?, hvalid]
      simp only [retireInputs, hstep']
      exact ih
  | @retire start coreState coreState' state cycleInput cycles
      instruction program observation hstep hinput horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      have hstep' :
          machine.toCycleMachine.step coreState cycleInput =
            (coreState', some (illegalRetirement state (trapProgramInput memory instruction))) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [trapProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware trap certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem TrapRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List TrapInstruction}
    (certificate : TrapRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (trapProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (trapProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_trap_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware trap certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem TrapRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List TrapInstruction}
    (first : TrapRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : TrapRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (trapProgramState state firstProgram)
      secondCycles secondProgram) :
    TrapRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, trapProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine TrapRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine TrapRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, trapProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.trapProgramInputs_append
#print axioms LeanModels.Refine.trapProgramState_append
#print axioms LeanModels.Refine.trapProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_trap_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_trap_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_trap_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_trap_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_trap_program_trace_append
#print axioms LeanModels.Refine.TrapRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.TrapRvfiTrace.normalize
#print axioms LeanModels.Refine.TrapRvfiTrace.trace_refines
#print axioms LeanModels.Refine.TrapRvfiTrace.append
#print axioms LeanModels.Refine.TrapRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.TrapRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.TrapRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.TrapRvfiCycleTrace.append

end LeanModels.Refine
