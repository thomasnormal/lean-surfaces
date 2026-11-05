import LeanModels.Refine.Rvfi
import LeanModels.Refine.Packet

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

@[simp] theorem RvfiPacketMachine.toPacketMachine_init {State : Type}
    (machine : RvfiPacketMachine State) :
    machine.toPacketMachine.init = machine.init := rfl

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

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_trace
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace
