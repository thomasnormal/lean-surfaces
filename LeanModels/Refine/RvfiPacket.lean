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

/-- A finite stream of packet windows, each with its carried starting order
and the state produced by its predecessor.  Mismatched window/retirement
lists are rejected rather than silently truncated. -/
def normalizeRvfiPacketWindows {State : Type}
    (machine : RvfiPacketMachine State) :
    State → Nat → List (List Input) → List (List Retirement) → Prop
  | _, _, [], [] => True
  | state, start, cycles :: rest, retirements :: tails =>
      normalizeRvfiTrace? start
          (rvfiPacketObservations machine state cycles) = some retirements ∧
        normalizeRvfiPacketWindows machine
          (rvfiPacketStateAfter machine state cycles)
          (start + retirements.length) rest tails
  | _, _, [], _ :: _ => False
  | _, _, _ :: _, [] => False

/-- Window-by-window normalization is exactly normalization of the flattened
observation stream, with the retirement windows flattened in the same order. -/
theorem normalizeRvfiPacketWindows_flatten {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input)) (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    normalizeRvfiTrace? start
        (rvfiPacketObservations machine state windows.flatten) =
      some retirementWindows.flatten := by
  induction windows generalizing state start retirementWindows with
  | nil =>
      cases retirementWindows with
      | nil => rfl
      | cons retirements tails => cases h
  | cons cycles rest ih =>
      cases retirementWindows with
      | nil => cases h
      | cons retirements tails =>
          rcases h with ⟨hwindow, htail⟩
          rw [List.flatten_cons, rvfiPacketObservations_append,
            normalizeRvfiTrace?_append]
          simp only [hwindow]
          have htail' := ih
            (state := rvfiPacketStateAfter machine state cycles)
            (start := start + retirements.length)
            (retirementWindows := tails) htail
          rw [htail']
          rfl

/-- Independently certified window chains compose when the second chain is
started from the first chain's retained state and retirement-order boundary. -/
theorem normalizeRvfiPacketWindows_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    normalizeRvfiPacketWindows machine state start
      (firstWindows ++ secondWindows)
      (firstRetirementWindows ++ secondRetirementWindows) := by
  induction firstWindows generalizing state start firstRetirementWindows with
  | nil =>
      cases firstRetirementWindows with
      | nil => simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using hsecond
      | cons retirementWindow retirementWindows => cases hfirst
  | cons cycles rest ih =>
      cases firstRetirementWindows with
      | nil => cases hfirst
      | cons retirementWindow retirementWindows =>
          rcases hfirst with ⟨hwindow, htail⟩
          have hstate :
              rvfiPacketStateAfter machine state (cycles :: rest).flatten =
                rvfiPacketStateAfter machine
                  (rvfiPacketStateAfter machine state cycles) rest.flatten := by
            rw [List.flatten_cons, rvfiPacketStateAfter_append]
          rw [hstate] at hsecond
          constructor
          · exact hwindow
          · apply ih (state := rvfiPacketStateAfter machine state cycles)
              (start := start + retirementWindow.length)
              (firstRetirementWindows := retirementWindows) htail
            simpa [List.flatten_cons, List.length_append, Nat.add_assoc] using hsecond

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

/-- The number of tagged commits carried by a packet stream. -/
def packetStreamLength : List TaggedPacket → Nat
  | [] => 0
  | packet :: packets => packet.length + packetStreamLength packets

/-- Concatenate two locally in-order packet streams while carrying the first
stream's exact tagged width into the second stream. -/
theorem inOrderPacketStream_append {start : Nat}
    {first second : List TaggedPacket}
    (hfirst : InOrderPacketStream start first)
    (hsecond : InOrderPacketStream (start + packetStreamLength first) second) :
    InOrderPacketStream start (first ++ second) := by
  induction first generalizing start with
  | nil =>
      simpa [InOrderPacketStream, packetStreamLength] using hsecond
  | cons packet packets ih =>
      rcases hfirst with ⟨hpacket, hpackets⟩
      constructor
      · exact hpacket
      · apply ih hpackets
        simpa [packetStreamLength, Nat.add_assoc] using hsecond

/-- Flattening a locally in-order packet stream preserves the global tag
certificate expected by the generic ROB interface. -/
theorem inOrderPacketStream_flatten {start : Nat}
    {packets : List TaggedPacket}
    (h : InOrderPacketStream start packets) :
    InOrderTags start packets.flatten := by
  induction packets generalizing start with
  | nil => rfl
  | cons packet packets ih =>
      rcases h with ⟨hpacket, hpackets⟩
      have htail := ih (start := start + packet.length) hpackets
      simpa [InOrderTags] using inOrderTags_append hpacket htail

theorem rvfiPacketTags_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    rvfiPacketTags machine state (first ++ second) =
      rvfiPacketTags machine state first ++
        rvfiPacketTags machine (rvfiPacketStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons cycleInput first ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [List.cons_append, rvfiPacketTags,
            rvfiPacketStateAfter, hstep]
          rw [ih state']

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

theorem rvfiPacketTags_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    packetStreamLength (rvfiPacketTags machine state cycles) =
      ((rvfiPacketObservations machine state cycles).filterMap
        RvfiObservation.toRetirement?).length := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [rvfiPacketTags, rvfiPacketObservations,
            packetStreamLength, hstep, List.length_append,
            List.filterMap_append]
          rw [packetEntries_tagged_length]
          rw [ih state']

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

theorem RvfiPacketMachine.toRobMachine_stateAfter {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    robStateAfter machine.toRobMachine state cycles =
      rvfiPacketStateAfter machine state cycles := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [robStateAfter, rvfiPacketStateAfter,
            RvfiPacketMachine.toRobMachine, hstep]
          exact ih state'

theorem RvfiPacketMachine.toPacketMachine_stateAfter {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    packetStateAfter machine.toPacketMachine state cycles =
      rvfiPacketStateAfter machine state cycles := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [packetStateAfter, rvfiPacketStateAfter,
            RvfiPacketMachine.toPacketMachine, hstep]
          exact ih state'

theorem RvfiPacketMachine.toPacketMachine_stateAfter_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    packetStateAfter machine.toPacketMachine state (first ++ second) =
      packetStateAfter machine.toPacketMachine
        (packetStateAfter machine.toPacketMachine state first) second := by
  exact packetStateAfter_append machine.toPacketMachine state first second

/- The generic ROB state projection preserves state threading across adjacent
   cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_stateAfter_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    robStateAfter machine.toRobMachine state (first ++ second) =
      robStateAfter machine.toRobMachine
        (robStateAfter machine.toRobMachine state first) second := by
  exact robStateAfter_append machine.toRobMachine state first second

/- The generic ROB retirement trace preserves state threading across adjacent
   cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_trace_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    robTrace machine.toRobMachine state (first ++ second) =
      robTrace machine.toRobMachine state first ++
        robTrace machine.toRobMachine
          (rvfiPacketStateAfter machine state first) second := by
  rw [robTrace_append, machine.toRobMachine_stateAfter]

/- The packet-facing retirement trace preserves state threading across
   adjacent cycle windows. -/
theorem RvfiPacketMachine.toPacketMachine_trace_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    packetTrace machine.toPacketMachine state (first ++ second) =
      packetTrace machine.toPacketMachine state first ++
        packetTrace machine.toPacketMachine
          (packetStateAfter machine.toPacketMachine state first) second := by
  exact packetTrace_append machine.toPacketMachine state first second

/- The packet-facing input projection preserves state threading across
   adjacent cycle windows. -/
theorem RvfiPacketMachine.toPacketMachine_inputs_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    packetInputs machine.toPacketMachine state (first ++ second) =
      packetInputs machine.toPacketMachine state first ++
        packetInputs machine.toPacketMachine
          (packetStateAfter machine.toPacketMachine state first) second := by
  exact packetInputs_append machine.toPacketMachine state first second

/- The generic ROB input projection preserves packet input threading across
   adjacent cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_inputs_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    robInputs machine.toRobMachine state (first ++ second) =
      robInputs machine.toRobMachine state first ++
        robInputs machine.toRobMachine
          (rvfiPacketStateAfter machine state first) second := by
  rw [machine.toRobMachine_inputs, packetInputs_append,
    machine.toRobMachine_inputs, machine.toRobMachine_inputs]
  rw [machine.toPacketMachine_stateAfter]

/- The generic ROB tag projection preserves state threading across adjacent
   cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_tags_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    robTags machine.toRobMachine state (first ++ second) =
      robTags machine.toRobMachine state first ++
        robTags machine.toRobMachine
          (rvfiPacketStateAfter machine state first) second := by
  rw [robTags_append, machine.toRobMachine_stateAfter]

/- Erasing the generic ROB tags' payloads preserves packet-trace threading
   across adjacent cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_tags_retirements_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    (robTags machine.toRobMachine state (first ++ second)).map
        TaggedCommit.retirement =
      packetTrace machine.toPacketMachine state first ++
        packetTrace machine.toPacketMachine
          (packetStateAfter machine.toPacketMachine state first) second := by
  rw [robTags_retirements, machine.toRobMachine_trace_append,
    machine.toRobMachine_trace, machine.toRobMachine_trace]
  rw [machine.toPacketMachine_stateAfter]

/- Erasing the generic ROB tags' source inputs preserves packet-input
   threading across adjacent cycle windows. -/
theorem RvfiPacketMachine.toRobMachine_tags_inputs_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State)
    (first second : List Input) :
    (robTags machine.toRobMachine state (first ++ second)).map
        TaggedCommit.input =
      packetInputs machine.toPacketMachine state first ++
        packetInputs machine.toPacketMachine
          (packetStateAfter machine.toPacketMachine state first) second := by
  rw [robTags_inputs, machine.toRobMachine_inputs_append,
    machine.toRobMachine_inputs, machine.toRobMachine_inputs]
  rw [machine.toPacketMachine_stateAfter]

theorem rvfiPacketStateAfter_refines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (start : Nat)
    (h : RobStepRefines machine.toRobMachine isa rel start admit) :
    ∀ (state : State) (isaState : IsaState) (order : Nat)
      (cycles : List Input),
      rel state isaState order →
      ∃ finalOrder,
        rel (rvfiPacketStateAfter machine state cycles)
          (machineStateAfter isa isaState
            (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
        finalOrder = order +
          (packetInputs machine.toPacketMachine state cycles).length := by
  intro state isaState order cycles hrel
  rcases robStateAfter_refines h state isaState order cycles hrel with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, ?_⟩
  · rw [← RvfiPacketMachine.toRobMachine_stateAfter]
    simpa only [RvfiPacketMachine.toRobMachine_inputs] using hfinal
  · simpa only [RvfiPacketMachine.toRobMachine_inputs] using horder

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

/-- Local packet-stream tag certificates compose across adjacent windows after
the first window's exact tagged width is established. -/
theorem normalizeRvfiPacketTags_stream_append {State : Type}
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
    InOrderPacketStream start
      (rvfiPacketTags machine state (first ++ second)) := by
  rw [rvfiPacketTags_append]
  have hfirstTags := normalizeRvfiPacketTags_stream machine state first hfirst
  have hsecondTags := normalizeRvfiPacketTags_stream machine
    (rvfiPacketStateAfter machine state first) second hsecond
  have hfirstLength :
      packetStreamLength (rvfiPacketTags machine state first) =
        firstRetirements.length := by
    rw [rvfiPacketTags_length]
    rw [normalizeRvfiTrace?_filterMap hfirst]
  apply inOrderPacketStream_append hfirstTags
  simpa [hfirstLength] using hsecondTags

/-- A normalized packet stream therefore also supplies the flattened ROB tag
certificate, retaining the same decoded order prefix. -/
theorem normalizeRvfiPacketTags_flat {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    InOrderTags start (rvfiPacketTags machine state cycles).flatten := by
  exact inOrderPacketStream_flatten
    (normalizeRvfiPacketTags_stream machine state cycles h)

/-- The generic ROB tag stream for a packetized RVFI machine is exactly the
flattened packet stream retained by the packet-aware view. -/
theorem RvfiPacketMachine.toRobMachine_tags {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    robTags machine.toRobMachine state cycles =
      (rvfiPacketTags machine state cycles).flatten := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' entries =>
          simp only [robTags, rvfiPacketTags,
            RvfiPacketMachine.toRobMachine, hstep, List.flatten_cons]
          exact congrArg (List.append
            (entries.filterMap RvfiPacketEntry.toTaggedCommit?)) (ih state')

/- Erasing generic ROB tag metadata recovers the packet-facing retirement
   trace for every finite cycle prefix. -/
theorem RvfiPacketMachine.toRobMachine_tags_retirements {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    (robTags machine.toRobMachine state cycles).map TaggedCommit.retirement =
      packetTrace machine.toPacketMachine state cycles := by
  rw [robTags_retirements, machine.toRobMachine_trace]

/-- Flattened ROB tag inputs are exactly the packet machine's retained
architectural input stream. -/
theorem RvfiPacketMachine.toRobMachine_tags_inputs {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input) :
    (robTags machine.toRobMachine state cycles).map TaggedCommit.input =
      packetInputs machine.toPacketMachine state cycles := by
  rw [robTags_inputs, machine.toRobMachine_inputs]

/-- A successful packetized RVFI normalization therefore certifies the
flattened tag stream exposed by the generic ROB interface. -/
theorem normalizeRvfiPacketRobTags {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    InOrderTags start (robTags machine.toRobMachine state cycles) := by
  rw [machine.toRobMachine_tags]
  exact normalizeRvfiPacketTags_flat machine state cycles h

/-- Local packetized-RVFI tag certificates compose through the generic ROB
tag stream, carrying the exact normalized retirement width to the next
window. -/
theorem normalizeRvfiPacketRobTags_append {State : Type}
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
    InOrderTags start
      (robTags machine.toRobMachine state (first ++ second)) := by
  rw [robTags_append]
  have hfirstTags := normalizeRvfiPacketRobTags machine state first hfirst
  have hsecondTags := normalizeRvfiPacketRobTags machine
    (rvfiPacketStateAfter machine state first) second hsecond
  have hfirstLength :
      (robTags machine.toRobMachine state first).length =
        firstRetirements.length := by
    have htrace :
        robTrace machine.toRobMachine state first = firstRetirements := by
      rw [machine.toRobMachine_trace]
      exact normalizeRvfiPacketTrace machine state first hfirst
    have hlength := congrArg List.length htrace
    rw [robTrace_length_eq_robInputs_length] at hlength
    calc
      (robTags machine.toRobMachine state first).length =
          (robInputs machine.toRobMachine state first).length :=
        robTags_length_eq_robInputs_length machine.toRobMachine state first
      _ = firstRetirements.length := hlength
  apply inOrderTags_append hfirstTags
  have hstate := RvfiPacketMachine.toRobMachine_stateAfter
    machine state first
  simpa [hfirstLength, hstate] using hsecondTags

/- A successful normalized packet capture fixes the flattened generic ROB tag
   cardinality to the decoded retirement count. -/
theorem normalizeRvfiPacketRobTags_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    (robTags machine.toRobMachine state cycles).length = retirements.length := by
  have htrace :
      (robTags machine.toRobMachine state cycles).map TaggedCommit.retirement =
        retirements := by
    rw [machine.toRobMachine_tags_retirements]
    exact normalizeRvfiPacketTrace machine state cycles h
  have hlength := congrArg List.length htrace
  simpa using hlength

/- A successful normalized packet capture also fixes the mapped generic ROB
   source-input cardinality to the decoded retirement count. -/
theorem normalizeRvfiPacketRobTags_inputs_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (cycles : List Input)
    {start : Nat} {retirements : List Retirement}
    (h : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    ((robTags machine.toRobMachine state cycles).map TaggedCommit.input).length =
      retirements.length := by
  have hlen := normalizeRvfiPacketRobTags_length machine state cycles h
  simpa only [List.length_map] using hlen

/- ROB-tag cardinality composes across adjacent normalized packet windows, with
   the second window evaluated from the first window's retained state. -/
theorem normalizeRvfiPacketRobTags_length_append {State : Type}
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
    (robTags machine.toRobMachine state (first ++ second)).length =
      (firstRetirements ++ secondRetirements).length := by
  apply normalizeRvfiPacketRobTags_length machine state (first ++ second)
  exact normalizeRvfiPacketTrace_append machine state first second hfirst hsecond

/-- A normalized packetized RVFI stream and a ROB refinement certificate
jointly establish both global tag order and the ISA equality of its tagged
retirements. -/
theorem normalizeRvfiPacketRobTags_refines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    InOrderTags start (robTags machine.toRobMachine state cycles) ∧
      (robTags machine.toRobMachine state cycles).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state cycles) := by
  constructor
  · exact normalizeRvfiPacketRobTags machine state cycles hobs
  · have htrace :
        robTrace machine.toRobMachine state cycles = retirements := by
      rw [machine.toRobMachine_trace]
      exact normalizeRvfiPacketTrace machine state cycles hobs
    calc
      (robTags machine.toRobMachine state cycles).map
          TaggedCommit.retirement =
          robTrace machine.toRobMachine state cycles :=
        robTags_retirements machine.toRobMachine state cycles
      _ = retirements := htrace
      _ = trace isa isaState
          (robInputs machine.toRobMachine state cycles) :=
        htrace.symm.trans
          (rob_trace_refines hrob state isaState start cycles hrel)

/-- Normalized packet observations also determine the exact order increment
of the state-threaded packet/ISA refinement relation. -/
theorem rvfiPacketStateAfter_refines_normalized
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (start : Nat)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (state : State) (isaState : IsaState)
    (hrel : rel state isaState start)
    (cycles : List Input) (retirements : List Retirement)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length := by
  rcases rvfiPacketStateAfter_refines machine isa rel admit start hrob
      state isaState start cycles hrel with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, hfinal, ?_⟩
  have htrace :
      robTrace machine.toRobMachine state cycles = retirements := by
    rw [machine.toRobMachine_trace]
    exact normalizeRvfiPacketTrace machine state cycles hobs
  have hlength := congrArg List.length htrace
  rw [robTrace_length_eq_robInputs_length] at hlength
  have hpacketLength :
      (packetInputs machine.toPacketMachine state cycles).length =
        retirements.length := by
    calc
      (packetInputs machine.toPacketMachine state cycles).length =
          (robInputs machine.toRobMachine state cycles).length := by
        rw [machine.toRobMachine_inputs]
      _ = retirements.length := hlength
  calc
    finalOrder = start +
        (packetInputs machine.toPacketMachine state cycles).length := horder
    _ = start + retirements.length := by rw [hpacketLength]

/-- The normalized packet state/order transport composes across two adjacent
windows, with the second normalization starting at the first retirement
count. -/
theorem rvfiPacketStateAfter_refines_normalized_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (start : Nat)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (state : State) (isaState : IsaState)
    (hrel : rel state isaState start)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
          finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length := by
  have hcombined := normalizeRvfiPacketTrace_append machine state first second
    hfirst hsecond
  exact rvfiPacketStateAfter_refines_normalized machine isa rel admit start hrob
    state isaState hrel (first ++ second)
    (firstRetirements ++ secondRetirements) hcombined

/-- The combined normalized packet tag/ISA contract composes across adjacent
windows without weakening either the global order certificate or the tagged
retirement trace equality. -/
theorem normalizeRvfiPacketRobTags_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    InOrderTags start
        (robTags machine.toRobMachine state (first ++ second)) ∧
      (robTags machine.toRobMachine state (first ++ second)).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state (first ++ second)) := by
  have hcombined := normalizeRvfiPacketTrace_append machine state first second
    hfirst hsecond
  exact normalizeRvfiPacketRobTags_refines machine isa rel admit state isaState
    start (first ++ second) (firstRetirements ++ secondRetirements)
    hrob hrel hcombined

/- The complete two-window packet contract combines the tagged ROB/ISA
   equality with the state-threaded relation and its exact order increment. -/
theorem normalizeRvfiPacketRobTags_refines_state_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    (InOrderTags start
        (robTags machine.toRobMachine state (first ++ second)) ∧
      (robTags machine.toRobMachine state (first ++ second)).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state (first ++ second))) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
          finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length) := by
  constructor
  · exact normalizeRvfiPacketRobTags_refines_append machine isa rel admit
      state isaState start first second hrob hrel hfirst hsecond
  · exact rvfiPacketStateAfter_refines_normalized_append machine isa rel admit
      start hrob state isaState hrel first second hfirst hsecond

/- The single-window form of the complete packet contract, useful when a
   capture is consumed without an explicit chunk boundary. -/
theorem normalizeRvfiPacketRobTags_refines_state
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    (InOrderTags start
        (robTags machine.toRobMachine state cycles) ∧
      (robTags machine.toRobMachine state cycles).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state cycles)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length) := by
  constructor
  · exact normalizeRvfiPacketRobTags_refines machine isa rel admit state
      isaState start cycles retirements hrob hrel hobs
  · exact rvfiPacketStateAfter_refines_normalized machine isa rel admit start
      hrob state isaState hrel cycles retirements hobs

/-- A finite chain of normalized packet windows supplies the complete
flattened packet/ISA contract and the final state/order relation. -/
theorem normalizeRvfiPacketRobTags_refines_windows
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hwindows : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (InOrderTags start
        (robTags machine.toRobMachine state windows.flatten) ∧
      (robTags machine.toRobMachine state windows.flatten).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state windows.flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state windows.flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state windows.flatten))
          finalOrder ∧
      finalOrder = start + retirementWindows.flatten.length) := by
  have hflat := normalizeRvfiPacketWindows_flatten machine state start
    windows retirementWindows hwindows
  exact normalizeRvfiPacketRobTags_refines_state machine isa rel admit state
    isaState start windows.flatten retirementWindows.flatten hrob hrel hflat

/-- The complete refinement contract composes directly across two certified
window chains; the local append theorem supplies the only boundary proof. -/
theorem normalizeRvfiPacketRobTags_refines_windows_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (InOrderTags start
        (robTags machine.toRobMachine state
          (firstWindows ++ secondWindows).flatten) ∧
      (robTags machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten).map
          TaggedCommit.retirement =
        trace isa isaState
          (robInputs machine.toRobMachine state
            (firstWindows ++ secondWindows).flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state
          (firstWindows ++ secondWindows).flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state
            (firstWindows ++ secondWindows).flatten)) finalOrder ∧
      finalOrder = start +
        (firstRetirementWindows ++ secondRetirementWindows).flatten.length) := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketRobTags_refines_windows machine isa rel admit state
    isaState start (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hrob hrel hcombined

/-- A certified finite window chain also preserves the packet boundaries of
the flattened cycle stream, not only its generic ROB projection. -/
theorem normalizeRvfiPacketWindows_tags_stream {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    InOrderPacketStream start
      (rvfiPacketTags machine state windows.flatten) := by
  have hflat := normalizeRvfiPacketWindows_flatten machine state start
    windows retirementWindows h
  exact normalizeRvfiPacketTags_stream machine state windows.flatten hflat

/-- Packet-local order also composes directly across two independently
certified window chains. -/
theorem normalizeRvfiPacketWindows_tags_stream_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    InOrderPacketStream start
      (rvfiPacketTags machine state
        (firstWindows ++ secondWindows).flatten) := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_tags_stream machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/-- Erasing the packet boundaries from a certified window chain preserves the
same global consecutive tag prefix. -/
theorem normalizeRvfiPacketWindows_tags_flat {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    InOrderTags start
      (rvfiPacketTags machine state windows.flatten).flatten := by
  exact inOrderPacketStream_flatten
    (normalizeRvfiPacketWindows_tags_stream machine state start windows
      retirementWindows h)

/-- The flat tag projection composes directly across two certified window
chains, using the same carried state and retirement-order boundary. -/
theorem normalizeRvfiPacketWindows_tags_flat_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    InOrderTags start
      (rvfiPacketTags machine state
        (firstWindows ++ secondWindows).flatten).flatten := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_tags_flat machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/-- A certified finite packet-window chain also gives the generic ROB
interface's flattened tag-order certificate. -/
theorem normalizeRvfiPacketWindows_rob_tags {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    InOrderTags start
      (robTags machine.toRobMachine state windows.flatten) := by
  rw [machine.toRobMachine_tags]
  exact normalizeRvfiPacketWindows_tags_flat machine state start windows
    retirementWindows h

/-- Generic ROB tag order composes across two independently certified
packet-window chains. -/
theorem normalizeRvfiPacketWindows_rob_tags_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    InOrderTags start
      (robTags machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten) := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_tags machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/-- The generic ROB tag projection of a certified window chain carries
exactly the flattened retirement payloads accepted by normalization. -/
theorem normalizeRvfiPacketWindows_rob_tags_retirements {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (robTags machine.toRobMachine state windows.flatten).map
        TaggedCommit.retirement = retirementWindows.flatten := by
  have hflat := normalizeRvfiPacketWindows_flatten machine state start
    windows retirementWindows h
  have htrace :
      robTrace machine.toRobMachine state windows.flatten =
        retirementWindows.flatten := by
    rw [machine.toRobMachine_trace]
    exact normalizeRvfiPacketTrace machine state windows.flatten hflat
  calc
    (robTags machine.toRobMachine state windows.flatten).map
        TaggedCommit.retirement =
      robTrace machine.toRobMachine state windows.flatten :=
        robTags_retirements machine.toRobMachine state windows.flatten
    _ = retirementWindows.flatten := htrace

/-- A certified packet-window chain directly exposes its normalized
retirement payload as the ISA trace over the generic ROB inputs. -/
theorem normalizeRvfiPacketWindows_rob_trace_refines {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    retirementWindows.flatten =
      trace isa isaState
        (robInputs machine.toRobMachine state windows.flatten) := by
  have hcontract := normalizeRvfiPacketRobTags_refines_windows machine isa rel
    admit state isaState start windows retirementWindows hrob hrel h
  rcases hcontract with ⟨⟨horder, hret⟩, hstate⟩
  have hretire := normalizeRvfiPacketWindows_rob_tags_retirements machine state
    start windows retirementWindows h
  have htraceTags := hretire.symm.trans hret
  exact htraceTags

/-- The packet-chain ISA trace equality composes directly across two
certified window chains, using the second chain's carried state and order
boundary. -/
theorem normalizeRvfiPacketWindows_rob_trace_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (firstRetirementWindows ++ secondRetirementWindows).flatten =
      trace isa isaState
        (robInputs machine.toRobMachine state
          (firstWindows ++ secondWindows).flatten) := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_trace_refines machine isa rel admit
    state isaState start (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hrob hrel hcombined

/-- A certified packet-window chain exposes the ISA trace through the packet
machine's architectural input projection, without requiring callers to name
the intermediate generic ROB view. -/
theorem normalizeRvfiPacketWindows_trace_refines {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    retirementWindows.flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state windows.flatten) := by
  have htrace := normalizeRvfiPacketWindows_rob_trace_refines machine isa
    rel admit state isaState start windows retirementWindows hrob hrel h
  rw [machine.toRobMachine_inputs] at htrace
  exact htrace

/-- The packet-facing ISA trace equality composes across two certified window
chains while retaining the first chain's state and retirement-order boundary.
-/
theorem normalizeRvfiPacketWindows_trace_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (firstRetirementWindows ++ secondRetirementWindows).flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state
          (firstWindows ++ secondWindows).flatten) := by
  have htrace := normalizeRvfiPacketWindows_trace_refines machine isa rel
    admit state isaState start (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hrob hrel
    (normalizeRvfiPacketWindows_append machine state start firstWindows
      secondWindows firstRetirementWindows secondRetirementWindows hfirst hsecond)
  exact htrace

/-- A certified finite packet-window chain also supplies the final related
state and its exact normalized retirement-order increment. -/
theorem normalizeRvfiPacketWindows_refines_state
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state windows.flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state windows.flatten))
        finalOrder ∧
      finalOrder = start + retirementWindows.flatten.length := by
  have hcontract := normalizeRvfiPacketRobTags_refines_windows machine isa
    rel admit state isaState start windows retirementWindows hrob hrel h
  exact hcontract.2

/- The state/order-only finite-chain contract can expose the generic
   packet-machine state directly at the final boundary. -/
theorem normalizeRvfiPacketWindows_refines_state_packet
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    ∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state windows.flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state windows.flatten))
        finalOrder ∧
      finalOrder = start + retirementWindows.flatten.length := by
  rcases normalizeRvfiPacketWindows_refines_state machine isa rel admit state
      isaState start windows retirementWindows hrob hrel h with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/-- The packet-chain state/order refinement composes across two certified
window chains with the second chain's carried state and order boundary. -/
theorem normalizeRvfiPacketWindows_refines_state_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state
        (firstWindows ++ secondWindows).flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state
            (firstWindows ++ secondWindows).flatten)) finalOrder ∧
      finalOrder = start +
        (firstRetirementWindows ++ secondRetirementWindows).flatten.length := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_refines_state machine isa rel admit state
    isaState start (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hrob hrel hcombined

/- The projected state/order-only finite-chain contract composes across two
   certified window chains. -/
theorem normalizeRvfiPacketWindows_refines_state_packet_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    ∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state
          (firstWindows ++ secondWindows).flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state
            (firstWindows ++ secondWindows).flatten))
        finalOrder ∧
      finalOrder = start +
        (firstRetirementWindows ++ secondRetirementWindows).flatten.length := by
  rcases normalizeRvfiPacketWindows_refines_state_append machine isa rel admit
      state isaState start firstWindows secondWindows firstRetirementWindows
      secondRetirementWindows hrob hrel hfirst hsecond with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/-- The complete packet-facing finite-chain contract combines ISA trace
equality with the final related state and exact retirement-order increment. -/
theorem normalizeRvfiPacketWindows_refines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (retirementWindows.flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state windows.flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state windows.flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state windows.flatten))
        finalOrder ∧
      finalOrder = start + retirementWindows.flatten.length) := by
  constructor
  · exact normalizeRvfiPacketWindows_trace_refines machine isa rel admit
      state isaState start windows retirementWindows hrob hrel h
  · exact normalizeRvfiPacketWindows_refines_state machine isa rel admit
      state isaState start windows retirementWindows hrob hrel h

/- The complete finite-chain contract can expose the generic packet-machine
   state directly at the final boundary. -/
theorem normalizeRvfiPacketWindows_refines_packet
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (retirementWindows.flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state windows.flatten)) ∧
    (∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state windows.flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state windows.flatten))
        finalOrder ∧
      finalOrder = start + retirementWindows.flatten.length) := by
  rcases normalizeRvfiPacketWindows_refines machine isa rel admit state isaState
      start windows retirementWindows hrob hrel h with
    ⟨htrace, finalOrder, hfinal, horder⟩
  refine ⟨htrace, finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/-- The complete packet-facing contract composes across two certified window
chains, preserving both the packet input stream and the carried state/order
boundary. -/
theorem normalizeRvfiPacketWindows_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    ((firstRetirementWindows ++ secondRetirementWindows).flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state
          (firstWindows ++ secondWindows).flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state
        (firstWindows ++ secondWindows).flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state
            (firstWindows ++ secondWindows).flatten)) finalOrder ∧
      finalOrder = start +
        (firstRetirementWindows ++ secondRetirementWindows).flatten.length) := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_refines machine isa rel admit state isaState
    start (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hrob hrel hcombined

/- The projected finite-chain contract also composes across two certified
   window chains with the packet-machine state exposed directly. -/
theorem normalizeRvfiPacketWindows_refines_packet_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    ((firstRetirementWindows ++ secondRetirementWindows).flatten =
      trace isa isaState
        (packetInputs machine.toPacketMachine state
          (firstWindows ++ secondWindows).flatten)) ∧
    (∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state
          (firstWindows ++ secondWindows).flatten)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state
            (firstWindows ++ secondWindows).flatten))
        finalOrder ∧
      finalOrder = start +
        (firstRetirementWindows ++ secondRetirementWindows).flatten.length) := by
  rcases normalizeRvfiPacketWindows_refines_append machine isa rel admit state
      isaState start firstWindows secondWindows firstRetirementWindows
      secondRetirementWindows hrob hrel hfirst hsecond with
    ⟨htrace, finalOrder, hfinal, horder⟩
  refine ⟨htrace, finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/-- ROB retirement payload equality composes across two independently
certified packet-window chains. -/
theorem normalizeRvfiPacketWindows_rob_tags_retirements_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (robTags machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten).map
        TaggedCommit.retirement =
      (firstRetirementWindows ++ secondRetirementWindows).flatten := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_tags_retirements machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/-- A certified packet-window chain has one generic ROB tag per
normalized retirement payload. -/
theorem normalizeRvfiPacketWindows_rob_tags_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (robTags machine.toRobMachine state windows.flatten).length =
      retirementWindows.flatten.length := by
  have hret := normalizeRvfiPacketWindows_rob_tags_retirements machine state
    start windows retirementWindows h
  have hlen := congrArg List.length hret
  simpa using hlen

/-- A certified packet-window chain's generic ROB source inputs have
exactly the normalized retirement cardinality. -/
theorem normalizeRvfiPacketWindows_rob_tags_inputs_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    ((robTags machine.toRobMachine state windows.flatten).map
        TaggedCommit.input).length = retirementWindows.flatten.length := by
  have hlen := normalizeRvfiPacketWindows_rob_tags_length machine state start
    windows retirementWindows h
  simpa only [List.length_map] using hlen

/- ROB-tag cardinality composes across adjacent normalized packet-window
   chains, retaining the second chain's carried state and order boundary. -/
theorem normalizeRvfiPacketWindows_rob_tags_length_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (robTags machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten).length =
      (firstRetirementWindows ++ secondRetirementWindows).flatten.length := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_tags_length machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/- ROB-tag source-input cardinality composes across adjacent normalized
   packet-window chains. -/
theorem normalizeRvfiPacketWindows_rob_tags_inputs_length_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    ((robTags machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten).map TaggedCommit.input).length =
      (firstRetirementWindows ++ secondRetirementWindows).flatten.length := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_tags_inputs_length machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

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

/-- A certified finite packet-window chain exposes the exact flattened
ROB retirement stream, with packet boundaries erased only after every window
has supplied its carried normalization certificate. -/
theorem normalizeRvfiPacketWindows_rob_trace {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    robTrace machine.toRobMachine state windows.flatten =
      retirementWindows.flatten := by
  have hflat := normalizeRvfiPacketWindows_flatten machine state start
    windows retirementWindows h
  exact normalizeRvfiPacketRobTrace machine state windows.flatten hflat

/-- The flattened ROB retirement equality composes directly across two
certified packet-window chains. -/
theorem normalizeRvfiPacketWindows_rob_trace_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    robTrace machine.toRobMachine state
        (firstWindows ++ secondWindows).flatten =
      (firstRetirementWindows ++ secondRetirementWindows).flatten := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_rob_trace machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

/- A pair of local packetized-RVFI certificates composes through the ROB
   refinement boundary, with the first packet window's exact state feeding the
   second and the concatenated packet inputs driving the ISA trace. -/
theorem normalizeRvfiPacketRobTrace_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    firstRetirements ++ secondRetirements =
      trace isa isaState
        (robInputs machine.toRobMachine state (first ++ second)) := by
  calc
    firstRetirements ++ secondRetirements =
        robTrace machine.toRobMachine state (first ++ second) :=
      (normalizeRvfiPacketRobTrace_append machine state first second
        hfirst hsecond).symm
    _ = trace isa isaState
        (robInputs machine.toRobMachine state (first ++ second)) :=
      rob_trace_refines hrob state isaState start (first ++ second) hrel

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

/- A single normalized packet window exposes the packet-facing ISA trace and
   the final state/order relation together, without requiring callers to name
   the intermediate generic ROB projection. -/
theorem normalizeRvfiPacketRefines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    (retirements = trace isa isaState
      (packetInputs machine.toPacketMachine state cycles)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length) := by
  constructor
  · have htrace := normalizeRvfiPacketRobTrace_refines machine isa rel admit
      state isaState start cycles retirements hrob hrel hobs
    simpa only [RvfiPacketMachine.toRobMachine_inputs] using htrace
  · exact rvfiPacketStateAfter_refines_normalized machine isa rel admit start
      hrob state isaState hrel cycles retirements hobs

/- The complete packet-facing contract can expose the generic packet-machine
   state directly, while retaining the same trace and order conclusions. -/
theorem normalizeRvfiPacketRefines_packet
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    (retirements = trace isa isaState
      (packetInputs machine.toPacketMachine state cycles)) ∧
    (∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length) := by
  rcases normalizeRvfiPacketRefines machine isa rel admit state isaState start
      cycles retirements hrob hrel hobs with
    ⟨htrace, finalOrder, hfinal, horder⟩
  refine ⟨htrace, finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/- The direct packet-facing contract composes across two adjacent normalized
   windows, with the second window starting from the first one's state and
   retirement-order boundary. -/
theorem normalizeRvfiPacketRefines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements ++ secondRetirements =
      trace isa isaState
        (packetInputs machine.toPacketMachine state (first ++ second))) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter machine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
          finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length) := by
  have hcombined := normalizeRvfiPacketTrace_append machine state first second
    hfirst hsecond
  exact normalizeRvfiPacketRefines machine isa rel admit state isaState start
    (first ++ second) (firstRetirements ++ secondRetirements) hrob hrel hcombined

/- The complete packet-facing contract composes across adjacent windows while
   exposing the generic packet-machine state at the final boundary. -/
theorem normalizeRvfiPacketRefines_packet_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    (firstRetirements ++ secondRetirements =
      trace isa isaState
        (packetInputs machine.toPacketMachine state (first ++ second))) ∧
    (∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
        finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length) := by
  rcases normalizeRvfiPacketRefines_append machine isa rel admit state isaState
      start first second hrob hrel hfirst hsecond with
    ⟨htrace, finalOrder, hfinal, horder⟩
  refine ⟨htrace, finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/- The trace-only packet-facing projection is available without unpacking the
   state/order conjunct of the complete contract. -/
theorem normalizeRvfiPacketTrace_refines
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
      (packetInputs machine.toPacketMachine state cycles) := by
  have htrace := normalizeRvfiPacketRobTrace_refines machine isa rel admit
    state isaState start cycles retirements hrob hrel hobs
  simpa only [RvfiPacketMachine.toRobMachine_inputs] using htrace

/- The trace-only packet-facing projection composes across adjacent windows
   using the same carried normalization boundary as the complete contract. -/
theorem normalizeRvfiPacketTrace_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    firstRetirements ++ secondRetirements =
      trace isa isaState
        (packetInputs machine.toPacketMachine state (first ++ second)) := by
  have hcombined := normalizeRvfiPacketTrace_append machine state first second
    hfirst hsecond
  exact normalizeRvfiPacketTrace_refines machine isa rel admit state isaState
    start (first ++ second) (firstRetirements ++ secondRetirements)
    hrob hrel hcombined

/- The state/order-only packet-facing projection is available without unpacking
   the trace conjunct of the complete contract. -/
theorem normalizeRvfiPacketState_refines
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length := by
  exact rvfiPacketStateAfter_refines_normalized machine isa rel admit start
    hrob state isaState hrel cycles retirements hobs

/- The state/order-only packet-facing projection can state its core state
   directly through the generic packet-machine view. -/
theorem normalizeRvfiPacketState_refines_packet
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    ∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state cycles)
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state cycles)) finalOrder ∧
      finalOrder = start + retirements.length := by
  rcases normalizeRvfiPacketState_refines machine isa rel admit state isaState
      start cycles retirements hrob hrel hobs with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/- The state/order-only packet-facing projection composes across adjacent
   windows with the second window's carried state and retirement boundary. -/
theorem normalizeRvfiPacketState_refines_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter machine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
        finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length := by
  exact rvfiPacketStateAfter_refines_normalized_append machine isa rel admit
    start hrob state isaState hrel first second hfirst hsecond

/- The packet-machine state projection also composes across adjacent
   normalized windows without exposing the internal RVFI state view. -/
theorem normalizeRvfiPacketState_refines_packet_append
    {State IsaState : Type}
    (machine : RvfiPacketMachine State) (isa : Machine IsaState)
    (rel : State → IsaState → Nat → Prop) (admit : Input → Prop)
    (state : State) (isaState : IsaState) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hrob : RobStepRefines machine.toRobMachine isa rel start admit)
    (hrel : rel state isaState start)
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    ∃ finalOrder,
      rel (packetStateAfter machine.toPacketMachine state (first ++ second))
        (machineStateAfter isa isaState
          (packetInputs machine.toPacketMachine state (first ++ second)))
        finalOrder ∧
      finalOrder = start + (firstRetirements ++ secondRetirements).length := by
  rcases normalizeRvfiPacketState_refines_append machine isa rel admit state
      isaState start first second hrob hrel hfirst hsecond with
    ⟨finalOrder, hfinal, horder⟩
  refine ⟨finalOrder, ?_, horder⟩
  rw [RvfiPacketMachine.toPacketMachine_stateAfter]
  exact hfinal

/- A successful packet normalization fixes the packet input cardinality to
   the number of decoded retirements. -/
theorem normalizeRvfiPacketInputs_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (cycles : List Input) (retirements : List Retirement)
    (hobs : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state cycles) = some retirements) :
    (packetInputs machine.toPacketMachine state cycles).length =
      retirements.length := by
  have htrace : robTrace machine.toRobMachine state cycles = retirements := by
    rw [machine.toRobMachine_trace]
    exact normalizeRvfiPacketTrace machine state cycles hobs
  have hlength := congrArg List.length htrace
  rw [robTrace_length_eq_robInputs_length] at hlength
  calc
    (packetInputs machine.toPacketMachine state cycles).length =
        (robInputs machine.toRobMachine state cycles).length := by
      rw [machine.toRobMachine_inputs]
    _ = retirements.length := hlength

/- Input cardinality composes across adjacent normalized packet windows with
   the second window's retained state made explicit. -/
theorem normalizeRvfiPacketInputs_length_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (first second : List Input)
    {firstRetirements secondRetirements : List Retirement}
    (hfirst : normalizeRvfiTrace? start
        (rvfiPacketObservations machine state first) = some firstRetirements)
    (hsecond : normalizeRvfiTrace?
        (start + firstRetirements.length)
        (rvfiPacketObservations machine
          (rvfiPacketStateAfter machine state first) second) =
      some secondRetirements) :
    (packetInputs machine.toPacketMachine state (first ++ second)).length =
      (firstRetirements ++ secondRetirements).length := by
  have hstate := RvfiPacketMachine.toPacketMachine_stateAfter
    machine state first
  rw [packetInputs_append]
  rw [List.length_append]
  rw [normalizeRvfiPacketInputs_length machine state start first
    firstRetirements hfirst]
  rw [hstate]
  rw [normalizeRvfiPacketInputs_length machine
    (rvfiPacketStateAfter machine state first)
    (start + firstRetirements.length) second secondRetirements hsecond]
  simp only [List.length_append]

/- A certified packet-window chain fixes the packet input cardinality to the
   flattened normalized retirement stream. -/
theorem normalizeRvfiPacketWindows_inputs_length {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (windows : List (List Input))
    (retirementWindows : List (List Retirement))
    (h : normalizeRvfiPacketWindows machine state start windows
      retirementWindows) :
    (packetInputs machine.toPacketMachine state windows.flatten).length =
      retirementWindows.flatten.length := by
  have hflat := normalizeRvfiPacketWindows_flatten machine state start
    windows retirementWindows h
  exact normalizeRvfiPacketInputs_length machine state start windows.flatten
    retirementWindows.flatten hflat

/- Packet input cardinality composes across adjacent normalized window chains,
   with the second chain's carried state and order boundary retained. -/
theorem normalizeRvfiPacketWindows_inputs_length_append {State : Type}
    (machine : RvfiPacketMachine State) (state : State) (start : Nat)
    (firstWindows secondWindows : List (List Input))
    (firstRetirementWindows secondRetirementWindows : List (List Retirement))
    (hfirst : normalizeRvfiPacketWindows machine state start firstWindows
      firstRetirementWindows)
    (hsecond : normalizeRvfiPacketWindows machine
      (rvfiPacketStateAfter machine state firstWindows.flatten)
      (start + firstRetirementWindows.flatten.length) secondWindows
      secondRetirementWindows) :
    (packetInputs machine.toPacketMachine state
      (firstWindows ++ secondWindows).flatten).length =
      (firstRetirementWindows ++ secondRetirementWindows).flatten.length := by
  have hcombined := normalizeRvfiPacketWindows_append machine state start
    firstWindows secondWindows firstRetirementWindows secondRetirementWindows
    hfirst hsecond
  exact normalizeRvfiPacketWindows_inputs_length machine state start
    (firstWindows ++ secondWindows)
    (firstRetirementWindows ++ secondRetirementWindows) hcombined

end LeanModels.Refine

#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_trace
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_inputs
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_stateAfter
#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_stateAfter
#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_stateAfter_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_stateAfter_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_trace_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_trace_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toPacketMachine_inputs_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_inputs_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags_retirements_append
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags_inputs_append
#print axioms LeanModels.Refine.rvfiPacketStateAfter_refines
#print axioms LeanModels.Refine.rvfiPacketStateAfter_append
#print axioms LeanModels.Refine.rvfiPacketObservations_append
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_trace
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_trace_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_trace_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketTags
#print axioms LeanModels.Refine.normalizeRvfiPacketTags_stream
#print axioms LeanModels.Refine.normalizeRvfiPacketTags_stream_append
#print axioms LeanModels.Refine.normalizeRvfiPacketTags_flat
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags_retirements
#print axioms LeanModels.Refine.RvfiPacketMachine.toRobMachine_tags_inputs
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_length
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_inputs_length
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_length_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines
#print axioms LeanModels.Refine.rvfiPacketStateAfter_refines_normalized
#print axioms LeanModels.Refine.rvfiPacketStateAfter_refines_normalized_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines_state_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines_state
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_flatten
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines_windows
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTags_refines_windows_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_trace_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_trace_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_trace_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_state
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_state_packet
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_state_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_state_packet_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_packet
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_refines_packet_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_tags_stream
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_tags_stream_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_tags_flat
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_tags_flat_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_retirements
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_retirements_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_length
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_inputs_length
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_length_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_rob_tags_inputs_length_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace
#print axioms LeanModels.Refine.normalizeRvfiPacketRobTrace_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketRefines
#print axioms LeanModels.Refine.normalizeRvfiPacketRefines_packet
#print axioms LeanModels.Refine.normalizeRvfiPacketRefines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketRefines_packet_append
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketTrace_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketState_refines
#print axioms LeanModels.Refine.normalizeRvfiPacketState_refines_packet
#print axioms LeanModels.Refine.normalizeRvfiPacketState_refines_append
#print axioms LeanModels.Refine.normalizeRvfiPacketState_refines_packet_append
#print axioms LeanModels.Refine.normalizeRvfiPacketInputs_length
#print axioms LeanModels.Refine.normalizeRvfiPacketInputs_length_append
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_inputs_length
#print axioms LeanModels.Refine.normalizeRvfiPacketWindows_inputs_length_append
