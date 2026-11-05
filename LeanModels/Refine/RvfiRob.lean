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

/-- The tagged ROB adapter retains exactly the packed RVFI state after a
finite window.  Packet contents are observational only for this projection;
the underlying core state is threaded unchanged. -/
theorem RvfiCycleMachine.toRobMachine_stateAfter {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input) :
    robStateAfter machine.toRobMachine state inputs =
      rvfiStateAfter machine state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp only [robStateAfter, rvfiStateAfter,
            RvfiCycleMachine.toRobMachine, hstep]
          exact ih state'

/-! ## Flattened tagged single-channel streams -/

/-- Flatten one RVFI channel into tagged ROB commits, retaining the source
input and the packed observation's architectural order.  Bubbles and
malformed rows contribute no tagged commit; successful normalization is the
certificate that no valid row was silently discarded. -/
def rvfiRobTags {State : Type} (machine : RvfiCycleMachine State) :
    State → List Input → TaggedPacket
  | _, [] => []
  | state, input :: inputs =>
      let (state', observation) := machine.step state input
      (match observation.toRetirement? with
      | none => []
      | some retirement =>
          [{ order := observation.order, input := input, retirement := retirement }]) ++
        rvfiRobTags machine state' inputs

/-- The tagged RVFI stream composes across adjacent windows by threading the
packed machine state reached by the first window. -/
theorem rvfiRobTags_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input) :
    rvfiRobTags machine state (first ++ second) =
      rvfiRobTags machine state first ++
        rvfiRobTags machine (rvfiStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          simp only [List.cons_append, rvfiRobTags, rvfiStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

/-- The flattened tagged stream has one entry exactly for each decoded
retirement in the packed observation stream. -/
theorem rvfiRobTags_length {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input) :
    (rvfiRobTags machine state inputs).length =
      ((rvfiObservations machine state inputs).filterMap
        RvfiObservation.toRetirement?).length := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          cases hret : observation.toRetirement? with
          | none =>
              simp [rvfiRobTags, rvfiObservations, hstep, hret]
              exact ih state'
          | some retirement =>
              simp [rvfiRobTags, rvfiObservations, hstep, hret]
              exact ih state'

/-! ## Normalized order tags -/

/-- A successful single-channel RVFI normalization certifies the flattened
tagged ROB stream: each decoded retirement carries the next order tag, while
bubbles remain absent from the ROB packet. -/
theorem normalizeRvfiRobTags {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    InOrderTags start (rvfiRobTags machine state inputs) := by
  induction inputs generalizing state start retirements with
  | nil =>
      simp [rvfiRobTags] at h ⊢
      cases h
      rfl
  | cons input inputs ih =>
      cases hstep : machine.step state input with
      | mk state' observation =>
          have hobs : rvfiObservations machine state (input :: inputs) =
              observation :: rvfiObservations machine state' inputs := by
            simp [rvfiObservations, hstep]
          rw [hobs] at h
          cases hv : observation.valid with
          | false =>
              have htail : normalizeRvfiTrace? start
                  (rvfiObservations machine state' inputs) = some retirements := by
                simpa [normalizeRvfiTrace?, hv] using h
              have htags := ih state' (start := start)
                (retirements := retirements) htail
              simp only [rvfiRobTags, hstep, hv, RvfiObservation.toRetirement?]
              exact htags
          | true =>
              simp [normalizeRvfiTrace?, hv] at h
              by_cases ho : observation.order = start
              · simp [ho] at h
                cases hret : observation.toRetirement? with
                | none =>
                    simp [hret] at h
                | some retirement =>
                    cases htail : normalizeRvfiTrace? (start + 1)
                        (rvfiObservations machine state' inputs) with
                    | none =>
                        simp [hret, htail] at h
                    | some retirements =>
                        simp [hret, htail] at h
                        have htailTags := ih state' (start := start + 1)
                          (retirements := retirements) htail
                        simp only [rvfiRobTags, hstep, hret, List.cons_append]
                        change InOrderTags start
                          ({ order := observation.order, input := input,
                              retirement := retirement } ::
                            rvfiRobTags machine state' inputs)
                        rw [ho]
                        unfold InOrderTags at htailTags ⊢
                        simp only [List.map_cons, List.length_cons]
                        rw [orderPrefix_succ]
                        exact congrArg (List.cons start) htailTags
              · simp [ho] at h

/-- Local normalization certificates compose into one in-order certificate for
the concatenated tagged RVFI stream. -/
theorem normalizeRvfiRobTags_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    InOrderTags start (rvfiRobTags machine state (first ++ second)) := by
  rw [rvfiRobTags_append]
  have hfirstTags := normalizeRvfiRobTags machine state first hfirst
  have hsecondTags := normalizeRvfiRobTags machine
    (rvfiStateAfter machine state first) second hsecond
  have hfirstLength :
      (rvfiRobTags machine state first).length = firstRetirements.length := by
    rw [rvfiRobTags_length]
    rw [normalizeRvfiTrace?_filterMap hfirst]
  apply inOrderTags_append hfirstTags
  simpa [hfirstLength] using hsecondTags

/-- Lift ROB state/order transport through the single-channel RVFI adapter.
The final order counter advances by the inputs that actually retire, which is
the same stream exposed by the ordinary cycle projection. -/
theorem rvfiRobStateAfter_refines
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (start : Nat)
    (h : RobStepRefines machine.toRobMachine isa rel start admit) :
    ∀ (state : State) (isaState : IsaState) (order : Nat)
      (inputs : List Input),
      rel state isaState order →
      ∃ finalOrder,
        rel (rvfiStateAfter machine state inputs)
          (machineStateAfter isa isaState
            (retireInputs machine.toCycleMachine state inputs)) finalOrder ∧
        finalOrder = order +
          (retireInputs machine.toCycleMachine state inputs).length := by
  intro state isaState order inputs hrel
  rcases robStateAfter_refines h state isaState order inputs hrel with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, ?_⟩
  · rw [← RvfiCycleMachine.toRobMachine_stateAfter]
    simpa only [RvfiCycleMachine.toRobMachine_inputs] using hfinal
  · simpa only [RvfiCycleMachine.toRobMachine_inputs] using horder

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

/-- State-threaded normalization composition also gives the ROB-projected
retirement stream for two adjacent single-channel RVFI windows. -/
theorem normalizeRvfiRobTrace_append {State : Type}
    (machine : RvfiCycleMachine State) (state : State)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    robTrace machine.toRobMachine state (first ++ second) =
      firstRetirements ++ secondRetirements := by
  apply normalizeRvfiRobTrace machine state (first ++ second)
  exact normalizeRvfiCycleTrace_append machine state first second hfirst hsecond

/- A pair of local RVFI certificates composes all the way through the ROB
   refinement boundary: the concatenated normalized retirements equal the
   ISA trace over the adapter's concatenated input stream. -/
theorem normalizeRvfiRobTrace_refines_append
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiObservations machine
          (rvfiStateAfter machine state first) second) =
      some secondRetirements) :
    firstRetirements ++ secondRetirements =
      trace isa isaState
        (robInputs machine.toRobMachine state (first ++ second)) := by
  calc
    firstRetirements ++ secondRetirements =
        robTrace machine.toRobMachine state (first ++ second) :=
      (normalizeRvfiRobTrace_append machine state first second hfirst hsecond).symm
    _ = trace isa isaState
        (robInputs machine.toRobMachine state (first ++ second)) :=
      rob_trace_refines hrob state isaState start (first ++ second) hrel

/-- The reusable R1-to-R3 conclusion for a single RVFI channel: a successful
normalization certificate and a core-specific ROB refinement certificate give
the same retirement stream as the ISA run over the ROB's associated inputs. -/
theorem normalizeRvfiRobTrace_refines
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (inputs : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    retirements = trace isa isaState
      (robInputs machine.toRobMachine state inputs) := by
  calc
    retirements = robTrace machine.toRobMachine state inputs :=
      (normalizeRvfiRobTrace machine state inputs hobs).symm
    _ = trace isa isaState (robInputs machine.toRobMachine state inputs) :=
      rob_trace_refines hrob state isaState start inputs hrel

/-- A successful RVFI normalization also certifies the number of ROB inputs:
the adapter's retained input stream has exactly the normalized retirement
count, including bubbles and malformed rows that contribute neither side. -/
theorem normalizeRvfiRobTrace_input_length {State : Type}
    (machine : RvfiCycleMachine State) (state : State) (inputs : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    (robInputs machine.toRobMachine state inputs).length =
      retirements.length := by
  have htrace := normalizeRvfiRobTrace machine state inputs h
  have hlength := congrArg List.length htrace
  rw [robTrace_length_eq_robInputs_length] at hlength
  exact hlength

/-- Combine retained RVFI/ROB state transport with normalization.  The
normalized retirement count is therefore the exact increment of the carried
ROB order counter. -/
theorem rvfiRobStateAfter_refines_normalized
    {State IsaState : Type}
    (machine : RvfiCycleMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (start : Nat)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (state : State) (isaState : IsaState)
    (hrel : rel state isaState start)
    (inputs : List Input) (retirements : List Retirement)
    (hobs : normalizeRvfiTrace? start
        (rvfiObservations machine state inputs) = some retirements) :
    ∃ finalOrder,
      rel (rvfiStateAfter machine state inputs)
        (machineStateAfter isa isaState
          (retireInputs machine.toCycleMachine state inputs)) finalOrder ∧
      finalOrder = start + retirements.length := by
  rcases rvfiRobStateAfter_refines machine isa rel admit start hrob
      state isaState start inputs hrel with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, hfinal, ?_⟩
  have hlength :
      (retireInputs machine.toCycleMachine state inputs).length =
        retirements.length := by
    rw [← RvfiCycleMachine.toRobMachine_inputs]
    exact normalizeRvfiRobTrace_input_length machine state inputs hobs
  calc
    finalOrder = start +
        (retireInputs machine.toCycleMachine state inputs).length := horder
    _ = start + retirements.length := by rw [hlength]

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiCycleMachine.toRobMachine_trace
#print axioms LeanModels.Refine.RvfiCycleMachine.toRobMachine_inputs
#print axioms LeanModels.Refine.RvfiCycleMachine.toRobMachine_stateAfter
#print axioms LeanModels.Refine.rvfiRobTags_append
#print axioms LeanModels.Refine.rvfiRobTags_length
#print axioms LeanModels.Refine.normalizeRvfiRobTags
#print axioms LeanModels.Refine.normalizeRvfiRobTags_append
#print axioms LeanModels.Refine.rvfiRobStateAfter_refines
#print axioms LeanModels.Refine.normalizeRvfiRobTrace
#print axioms LeanModels.Refine.normalizeRvfiRobTrace_append
#print axioms LeanModels.Refine.normalizeRvfiRobTrace_refines_append
#print axioms LeanModels.Refine.normalizeRvfiRobTrace_refines
#print axioms LeanModels.Refine.normalizeRvfiRobTrace_input_length
#print axioms LeanModels.Refine.rvfiRobStateAfter_refines_normalized
