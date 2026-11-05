import LeanModels.Refine.Rvfi
import LeanModels.Refine.Packet
import LeanModels.Refine.Rob

/-!
# Packetized RVFI observations

Superscalar RVFI configurations can expose several observation channels at one
cycle boundary.  `RvfiPacketMachine` keeps those rows in the packet order
provided by the core, together with the architectural input associated with
each row.  The adapter filters only through `toRetirement?`; order and validity
are checked separately by `normalizeRvfiTrace?` over the flattened stream.
No completion order is selected by this layer.
-/

namespace LeanModels.Refine

/-- One packed RVFI row and the input whose architectural effect it reports. -/
structure RvfiPacketEntry where
  input : Input
  observation : RvfiObservation

/-- A cycle machine that may expose a finite RVFI packet at each boundary. -/
structure RvfiPacketMachine (State : Type) where
  init : State
  step : State → Input → State × List RvfiPacketEntry

/-- Project a packed RVFI packet into the generic architectural packet. -/
def RvfiPacketMachine.toPacketMachine {State : Type}
    (machine : RvfiPacketMachine State) : PacketMachine State where
  init := machine.init
  step state cycleInput :=
    let (state', entries) := machine.step state cycleInput
    let packet := entries.filterMap fun entry =>
      entry.observation.toRetirement?.map (fun retirement =>
        (entry.input, retirement))
    (state', packet)

/-- Project a packed RVFI packet into tagged ROB commits, preserving every
observation's architectural order tag and associated input. -/
def RvfiPacketMachine.toRobMachine {State : Type}
    (machine : RvfiPacketMachine State) : RobMachine State where
  init := machine.init
  step state cycleInput :=
    let (state', entries) := machine.step state cycleInput
    let packet := entries.filterMap fun entry =>
      entry.observation.toRetirement?.map (fun retirement =>
        { order := entry.observation.order
          input := entry.input
          retirement := retirement })
    (state', packet)

@[simp] theorem RvfiPacketMachine.toPacketMachine_init {State : Type}
    (machine : RvfiPacketMachine State) :
    machine.toPacketMachine.init = machine.init := rfl

@[simp] theorem RvfiPacketMachine.toRobMachine_init {State : Type}
    (machine : RvfiPacketMachine State) :
    machine.toRobMachine.init = machine.init := rfl

/-- Flatten all packed observations in cycle order, retaining bubbles so the
normalizer can validate them. -/
def rvfiPacketObservations {State : Type} (machine : RvfiPacketMachine State) :
    State → List Input → List RvfiObservation
  | _, [] => []
  | state, cycleInput :: cycles =>
      let (state', entries) := machine.step state cycleInput
      entries.map RvfiPacketEntry.observation ++
        rvfiPacketObservations machine state' cycles

private theorem packetEntries_snd (entries : List RvfiPacketEntry) :
    (entries.filterMap (fun entry =>
      entry.observation.toRetirement?.map (fun retirement =>
        (entry.input, retirement)))).map Prod.snd =
      (entries.map RvfiPacketEntry.observation).filterMap
        RvfiObservation.toRetirement? := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [hret, ih]
      | some retirement => simp [hret, ih]

private theorem packetEntries_tagged_snd (entries : List RvfiPacketEntry) :
    (entries.filterMap (fun entry =>
      entry.observation.toRetirement?.map (fun retirement =>
        { order := entry.observation.order
          input := entry.input
          retirement := retirement }))).map TaggedCommit.retirement =
      (entries.map RvfiPacketEntry.observation).filterMap
        RvfiObservation.toRetirement? := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [hret, ih]
      | some retirement => simp [hret, ih]

private theorem packetEntries_tagged_fst (entries : List RvfiPacketEntry) :
    (entries.filterMap (fun entry =>
      entry.observation.toRetirement?.map (fun retirement =>
        { order := entry.observation.order
          input := entry.input
          retirement := retirement }))).map TaggedCommit.input =
      (entries.filterMap (fun entry =>
        entry.observation.toRetirement?.map (fun retirement =>
          (entry.input, retirement)))).map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [hret, ih]
      | some retirement => simp [hret, ih]

/-- The packet projection emits exactly the filtered flattened observations. -/
theorem RvfiPacketMachine.toPacketMachine_trace {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    packetTrace machine.toPacketMachine state cycles =
      (rvfiPacketObservations machine state cycles).filterMap
        RvfiObservation.toRetirement? := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [packetTrace, rvfiPacketObservations,
            RvfiPacketMachine.toPacketMachine, hstep]
          change (entries.filterMap (fun entry =>
            entry.observation.toRetirement?.map
              (fun retirement => (entry.input, retirement)))).map Prod.snd ++
              packetTrace machine.toPacketMachine state' cycles =
            (entries.map RvfiPacketEntry.observation ++
              rvfiPacketObservations machine state' cycles).filterMap
                RvfiObservation.toRetirement?
          rw [packetEntries_snd]
          have htail := ih state'
          change packetTrace machine.toPacketMachine state' cycles =
            (rvfiPacketObservations machine state' cycles).filterMap
              RvfiObservation.toRetirement? at htail
          rw [htail]
          simp only [List.filterMap_append]

/-- The tagged ROB projection emits the same retirements as the untagged
packet projection. -/
theorem RvfiPacketMachine.toRobMachine_trace {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    robTrace machine.toRobMachine state cycles =
      packetTrace machine.toPacketMachine state cycles := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [robTrace, packetTrace, RvfiPacketMachine.toRobMachine,
            RvfiPacketMachine.toPacketMachine, hstep]
          change (entries.filterMap (fun entry =>
            entry.observation.toRetirement?.map (fun retirement =>
              { order := entry.observation.order
                input := entry.input
                retirement := retirement }))).map TaggedCommit.retirement ++
              robTrace machine.toRobMachine state' cycles =
            (entries.filterMap (fun entry =>
              entry.observation.toRetirement?.map (fun retirement =>
                (entry.input, retirement)))).map Prod.snd ++
              packetTrace machine.toPacketMachine state' cycles
          rw [packetEntries_tagged_snd, packetEntries_snd]
          have htail := ih state'
          change robTrace machine.toRobMachine state' cycles =
            packetTrace machine.toPacketMachine state' cycles at htail
          rw [htail]

/-- The inputs carried by tagged ROB commits are the packet inputs. -/
theorem RvfiPacketMachine.toRobMachine_inputs {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    robInputs machine.toRobMachine state cycles =
      packetInputs machine.toPacketMachine state cycles := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [robInputs, packetInputs, RvfiPacketMachine.toRobMachine,
            RvfiPacketMachine.toPacketMachine, hstep]
          change (entries.filterMap (fun entry =>
            entry.observation.toRetirement?.map (fun retirement =>
              { order := entry.observation.order
                input := entry.input
                retirement := retirement }))).map TaggedCommit.input ++
              robInputs machine.toRobMachine state' cycles =
            (entries.filterMap (fun entry =>
              entry.observation.toRetirement?.map (fun retirement =>
                (entry.input, retirement)))).map Prod.fst ++
              packetInputs machine.toPacketMachine state' cycles
          have htail := ih state'
          change robInputs machine.toRobMachine state' cycles =
            packetInputs machine.toPacketMachine state' cycles at htail
          rw [packetEntries_tagged_fst, htail]

/-- A successful flattened RVFI certificate is the packet machine's exact
retirement stream. -/
theorem normalizeRvfiPacketTrace {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    packetTrace machine.toPacketMachine state cycles = retirements := by
  rw [machine.toPacketMachine_trace]
  exact normalizeRvfiTrace?_filterMap h

/-- A successful flattened RVFI certificate also supplies the tagged ROB
retirement stream. -/
theorem normalizeRvfiPacketRobTrace {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    robTrace machine.toRobMachine state cycles = retirements := by
  rw [machine.toRobMachine_trace]
  exact normalizeRvfiPacketTrace machine state cycles h

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_inputs
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace
