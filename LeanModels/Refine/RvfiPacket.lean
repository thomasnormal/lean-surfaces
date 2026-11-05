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

/-- Decode one packet row into a tagged architectural commit when it carries a
retirement. -/
def RvfiPacketEntry.toTaggedCommit? (entry : RvfiPacketEntry) : Option TaggedCommit :=
  entry.observation.toRetirement?.map (fun retirement =>
    { order := entry.observation.order, input := entry.input, retirement := retirement })

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
    let packet := entries.filterMap RvfiPacketEntry.toTaggedCommit?
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

/-! ## State-threaded packet windows -/

/-- The core state after a finite packet-cycle window.  Packet contents are
discarded here; only the state transition is needed to continue a stream. -/
def rvfiPacketStateAfter {State : Type} (machine : RvfiPacketMachine State) :
    State → List Input → State
  | state, [] => state
  | state, cycleInput :: cycles =>
      rvfiPacketStateAfter machine (machine.step state cycleInput).1 cycles

theorem rvfiPacketStateAfter_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    rvfiPacketStateAfter machine state (first ++ second) =
      rvfiPacketStateAfter machine
        (rvfiPacketStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons cycleInput first ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [List.cons_append, rvfiPacketStateAfter, hstep]
          exact ih state'

/-- Flattening a packet stream across two windows retains the state produced
by the first window, so no packet is dropped or replayed at the boundary. -/
theorem rvfiPacketObservations_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    rvfiPacketObservations machine state (first ++ second) =
      rvfiPacketObservations machine state first ++
        rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons cycleInput first ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [List.cons_append, rvfiPacketObservations,
            rvfiPacketStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

/-! ## Normalized packet-window composition -/

/-- The tagged packet emitted at every cycle boundary, including empty
packets.  This retains the packet boundaries needed by a ROB relation while
`rvfiPacketObservations` is the flattened validation view. -/
def rvfiPacketTags {State : Type} (machine : RvfiPacketMachine State) :
    State → List Input → List TaggedPacket
  | _, [] => []
  | state, cycleInput :: cycles =>
      let (state', entries) := machine.step state cycleInput
      entries.filterMap RvfiPacketEntry.toTaggedCommit? ::
        rvfiPacketTags machine state' cycles

/-- Every packet in a tagged stream starts immediately after the retirements
of its preceding packets. -/
def InOrderPacketStream : Nat → List TaggedPacket → Prop
  | _, [] => True
  | start, packet :: packets =>
      InOrderTags start packet ∧
        InOrderPacketStream (start + packet.length) packets

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
    (entries.filterMap RvfiPacketEntry.toTaggedCommit?).map TaggedCommit.retirement =
      (entries.map RvfiPacketEntry.observation).filterMap
        RvfiObservation.toRetirement? := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]
      | some retirement => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]

private theorem packetEntries_tagged_fst (entries : List RvfiPacketEntry) :
    (entries.filterMap RvfiPacketEntry.toTaggedCommit?).map TaggedCommit.input =
      (entries.filterMap (fun entry =>
        entry.observation.toRetirement?.map (fun retirement =>
          (entry.input, retirement)))).map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]
      | some retirement => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]

private theorem packetEntries_tagged_length (entries : List RvfiPacketEntry) :
    (entries.filterMap RvfiPacketEntry.toTaggedCommit?).length =
      ((entries.map RvfiPacketEntry.observation).filterMap
        RvfiObservation.toRetirement?).length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      cases hret : entry.observation.toRetirement? with
      | none => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]
      | some retirement => simp [RvfiPacketEntry.toTaggedCommit?, hret, ih]

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
          change (entries.filterMap RvfiPacketEntry.toTaggedCommit?).map
              TaggedCommit.retirement ++
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
          change (entries.filterMap RvfiPacketEntry.toTaggedCommit?).map
              TaggedCommit.input ++
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

/-- Two successful packet-window certificates compose at the carried RVFI
order.  The state transition between windows is explicit, and the second
window starts after the first window's retirement count. -/
theorem normalizeRvfiPacketTrace_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    normalizeRvfiTrace? start
        (rvfiPacketObservations machine state (first ++ second)) =
      some (firstRetirements ++ secondRetirements) := by
  rw [rvfiPacketObservations_append, normalizeRvfiTrace?_append]
  simp [hfirst, hsecond]

/-- A normalized packet's decoded commit tags are the consecutive prefix at
the supplied starting order.  Bubbles do not enter the packet, while a
retirement row contributes exactly the tag checked by normalization. -/
theorem normalizeRvfiPacketTags {start : Nat}
    {entries : List RvfiPacketEntry} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (entries.map RvfiPacketEntry.observation) = some retirements) :
    InOrderTags start (entries.filterMap RvfiPacketEntry.toTaggedCommit?) := by
  induction entries generalizing start retirements with
  | nil =>
      simp [normalizeRvfiTrace?] at h ⊢
      cases h
      rfl
  | cons entry entries ih =>
      by_cases hv : entry.observation.valid = true
      · simp [normalizeRvfiTrace?, hv] at h
        by_cases ho : entry.observation.order = start
        · simp [ho] at h
          cases hret : entry.observation.toRetirement? with
          | none => simp [hret] at h
          | some retirement =>
              cases htail : normalizeRvfiTrace? (start + 1)
                  (entries.map RvfiPacketEntry.observation) with
              | none => simp [hret, htail] at h
              | some retirements =>
                  simp [hret, htail] at h
                  have htailTags := ih (start := start + 1)
                    (retirements := retirements) htail
                  simp only [List.filterMap, RvfiPacketEntry.toTaggedCommit?,
                    hret, Option.map]
                  change InOrderTags start
                    ({ order := entry.observation.order, input := entry.input,
                        retirement := retirement } ::
                      entries.filterMap RvfiPacketEntry.toTaggedCommit?)
                  rw [ho]
                  unfold InOrderTags at htailTags ⊢
                  simp only [List.map_cons, List.length_cons]
                  rw [orderPrefix_succ]
                  exact congrArg (List.cons start) htailTags
        · simp [ho] at h
      · have hv' : entry.observation.valid = false := by
          cases hval : entry.observation.valid with
          | false => exact rfl
          | true => exact False.elim (hv hval)
        simp [normalizeRvfiTrace?, hv'] at h
        have hnone : entry.observation.toRetirement? = none := by
          simp [RvfiObservation.toRetirement?, hv']
        simp only [List.filterMap, RvfiPacketEntry.toTaggedCommit?, hnone]
        exact ih h

/-- A normalized packet trace carries a local in-order tag certificate for
every packet boundary. -/
theorem normalizeRvfiPacketTags_stream {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    InOrderPacketStream start (rvfiPacketTags machine state cycles) := by
  induction cycles generalizing state start retirements with
  | nil =>
      simp [rvfiPacketTags, InOrderPacketStream]
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          have hobs : rvfiPacketObservations machine state (cycleInput :: cycles) =
              entries.map RvfiPacketEntry.observation ++
                rvfiPacketObservations machine state' cycles := by
            simp [rvfiPacketObservations, hstep]
          rw [hobs] at h
          have htags : rvfiPacketTags machine state (cycleInput :: cycles) =
              entries.filterMap RvfiPacketEntry.toTaggedCommit? ::
                rvfiPacketTags machine state' cycles := by
            simp [rvfiPacketTags, hstep]
          rw [htags]
          rw [normalizeRvfiTrace?_append] at h
          cases hfirst : normalizeRvfiTrace? start
              (entries.map RvfiPacketEntry.observation) with
          | none => simp [hfirst] at h
          | some firstRetirements =>
              simp only [hfirst] at h
              cases htail : normalizeRvfiTrace? (start + firstRetirements.length)
                  (rvfiPacketObservations machine state' cycles) with
              | none => simp [htail] at h
              | some tailRetirements =>
                  simp only [htail, Option.map] at h
                  cases h
                  have htags := normalizeRvfiPacketTags hfirst
                  have hlen := normalizeRvfiTrace?_filterMap hfirst
                  have hpacketLen := packetEntries_tagged_length entries
                  have htailTags := ih state' (start := start + firstRetirements.length)
                    (retirements := tailRetirements) htail
                  constructor
                  · exact htags
                  · rw [hpacketLen, hlen]
                    exact htailTags

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

/-- The state-threaded normalization composition also gives the ROB-projected
retirement stream for the concatenated windows. -/
theorem normalizeRvfiPacketRobTrace_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input)
    {start : Nat} {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    robTrace machine.toRobMachine state (first ++ second) =
      firstRetirements ++ secondRetirements := by
  apply normalizeRvfiPacketRobTrace machine state (first ++ second)
  exact normalizeRvfiPacketTrace_append machine state first second hfirst hsecond

/-- The reusable R1-to-R3 conclusion: once a core-specific `RobStepRefines`
proof supplies the ISA effect relation, a successful normalized RVFI packet
stream is exactly the ISA trace over the packet's associated inputs. -/
theorem normalizeRvfiPacketRobTrace_refines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    retirements = trace isa isaState
      (robInputs machine.toRobMachine state cycles) := by
  calc
    retirements = robTrace machine.toRobMachine state cycles :=
      (normalizeRvfiPacketRobTrace machine state cycles hobs).symm
    _ = trace isa isaState (robInputs machine.toRobMachine state cycles) :=
      rob_trace_refines hrob state isaState start cycles hrel

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_inputs
#print axioms LeanModels.Refine.rvfiPacketStateAfter_append
#print axioms LeanModels.Refine.rvfiPacketObservations_append
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace_append
#print axioms LeanModels.Refine.normalizeRvfiPacketTags
#print axioms LeanModels.Refine.normalizeRvfiPacketTags_stream
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace_refines
