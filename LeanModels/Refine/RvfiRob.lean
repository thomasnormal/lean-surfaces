import LeanModels.Refine.Rvfi
import LeanModels.Refine.Rob

/-!
# RVFI observations at the ROB commit boundary

`RvfiCycleMachine` exposes one packed observation per cycle, while
`RobMachine` exposes a tagged packet of architectural commits.  The adapter
below is the one-entry-per-cycle projection used by an RVFI channel: a
decoded observation becomes a singleton tagged packet carrying its original
`order` and cycle input, and a bubble (including a malformed valid row) is an
empty packet.  Normalization remains the admission certificate, so the
projection never repairs a tag or invents a retirement.
-/

namespace LeanModels.Refine

/-- Project one packed RVFI channel into the tagged ROB commit interface. -/
def RvfiCycleMachine.toRobMachine {State : Type}
    (machine : RvfiCycleMachine State) : RobMachine State where
  init := machine.init
  step state input :=
    let (state', observation) := machine.step state input
    let packet := match observation.toRetirement? with
      | none => []
      | some retirement =>
          [{ order := observation.order, input := input, retirement := retirement }]
    (state', packet)

@[simp] theorem RvfiCycleMachine.toRobMachine_init {State : Type}
    (machine : RvfiCycleMachine State) :
    machine.toRobMachine.init = machine.init := rfl

/-- The ROB projection and the optional-retirement cycle projection emit the
same architectural stream, including for observations that are refused by
the packed decoder. -/
theorem RvfiCycleMachine.toRobMachine_trace {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input) :
    robTrace machine.toRobMachine state inputs =
      cycleTrace machine.toCycleMachine state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp [robTrace, cycleTrace, RvfiCycleMachine.toRobMachine,
            RvfiCycleMachine.toCycleMachine, hstep]
          cases hret : observation.toRetirement? with
          | none =>
              simp
              exact ih state'
          | some retirement =>
              simp
              exact ih state'

/-- The cycle inputs retained by the ROB projection are exactly the inputs
retained by the ordinary cycle bridge. -/
theorem RvfiCycleMachine.toRobMachine_inputs {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input) :
    robInputs machine.toRobMachine state inputs =
      retireInputs machine.toCycleMachine state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp [robInputs, retireInputs, RvfiCycleMachine.toRobMachine,
            RvfiCycleMachine.toCycleMachine, hstep]
          cases hret : observation.toRetirement? with
          | none =>
              simp
              exact ih state'
          | some retirement =>
              simp
              exact ih state'

/-- Successful RVFI normalization therefore also supplies the ROB-projected
trace.  The `order` tags are checked by `normalizeRvfiTrace?` before this
corollary is used; the adapter only transports them into `TaggedCommit`. -/
theorem normalizeRvfiRobTrace {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start (rvfiObservations machine state inputs) =
      some retirements) :
    robTrace machine.toRobMachine state inputs = retirements := by
  rw [machine.toRobMachine_trace]
  exact normalizeRvfiCycleTrace machine state inputs h

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiCycleMachine.toRobMachine_trace
#print axioms LeanModels.Refine.RvfiCycleMachine.toRobMachine_inputs
#print axioms LeanModels.Refine.normalizeRvfiRobTrace
