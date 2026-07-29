import LeanModels.Circuit.DC

/-!
# Analysis-independent elaborated circuits

Frontends lower source syntax into one typed, hierarchy-free artifact.
Analysis procedures consume certified views of that artifact.  In particular,
an exact linear DC view is a capability, not the identity of the circuit.

The root artifact records linear devices and typed MOS Level-1 declarations.
Neither family determines the analysis semantics: exact linear DC and MOS1
are separate, fallible, proof-carrying views.
-/

namespace LeanModels.Circuit

structure ModelId where
  index : Nat
deriving Repr, BEq, DecidableEq, Inhabited

@[simp] theorem ModelId.beq_mk (left right : Nat) :
    (ModelId.mk left == ModelId.mk right) = (left == right) := by
  rfl

inductive MosPolarity where
  | nmos
  | pmos
deriving Repr, BEq, DecidableEq, Inhabited

@[simp] theorem MosPolarity.beq_nmos :
    (MosPolarity.nmos == MosPolarity.nmos) = true := by
  rfl

@[simp] theorem MosPolarity.beq_pmos :
    (MosPolarity.pmos == MosPolarity.pmos) = true := by
  rfl

/-- The typed parameters of the explicitly supported long-channel MOS
profile. Named source parameters are resolved before this artifact exists. -/
structure ElaboratedMos1Model where
  id : ModelId
  polarity : MosPolarity
  threshold : Rat
  transconductance : Rat
  channelLengthModulation : Rat
  junctionSaturation : Rat
deriving Repr, BEq, Inhabited

inductive ElaboratedModel where
  | mos1 (model : ElaboratedMos1Model)
deriving Repr, BEq, Inhabited

/-- A resolved electrical device. Source names are retained in the owning
`ElaboratedCircuit`; semantic connectivity uses numeric identifiers. -/
inductive ElaboratedDevice where
  | resistor (id : DeviceId) (positive negative : NodeId) (resistance : Rat)
  | voltageSource (id : DeviceId) (positive negative : NodeId) (voltage : Rat)
  | currentSource (id : DeviceId) (positive negative : NodeId) (current : Rat)
  | capacitor (id : DeviceId) (positive negative : NodeId) (capacitance : Rat)
  | inductor (id : DeviceId) (positive negative : NodeId) (inductance : Rat)
  | mosfet (id : DeviceId) (drain gate source bulk : NodeId) (model : ModelId)
deriving Repr, BEq, Inhabited

def ElaboratedDevice.id : ElaboratedDevice → DeviceId
  | .resistor id _ _ _
  | .voltageSource id _ _ _
  | .currentSource id _ _ _
  | .capacitor id _ _ _
  | .inductor id _ _ _
  | .mosfet id _ _ _ _ _ => id

def ElaboratedDevice.positive : ElaboratedDevice → NodeId
  | .resistor _ positive _ _
  | .voltageSource _ positive _ _
  | .currentSource _ positive _ _
  | .capacitor _ positive _ _
  | .inductor _ positive _ _ => positive
  | .mosfet _ drain _ _ _ _ => drain

def ElaboratedDevice.negative : ElaboratedDevice → NodeId
  | .resistor _ _ negative _
  | .voltageSource _ _ negative _
  | .currentSource _ _ negative _
  | .capacitor _ _ negative _
  | .inductor _ _ negative _ => negative
  | .mosfet _ _ _ source _ _ => source

def ElaboratedModel.id : ElaboratedModel → ModelId
  | .mos1 model => model.id

/-- The common semantic artifact produced by a source frontend. All nodes use
the conservative electrical discipline in the first vertical slice. -/
structure ElaboratedCircuit where
  title : String
  nodeNames : Array String
  deviceNames : Array String
  modelNames : Array String
  ground : NodeId
  devices : Array ElaboratedDevice
  models : Array ElaboratedModel
deriving Repr, BEq, Inhabited

/-- A checked source-level node reference tied to one elaborated artifact. -/
structure ElaboratedNode (circuit : ElaboratedCircuit) where
  id : NodeId
  valid : id.index < circuit.nodeNames.size

/-- A checked source-level device reference tied to one elaborated artifact. -/
structure ElaboratedDeviceRef (circuit : ElaboratedCircuit) where
  id : DeviceId
  valid : id.index < circuit.devices.size

def ElaboratedCircuit.node? (circuit : ElaboratedCircuit)
    (name : String) : Option NodeId :=
  (circuit.nodeNames.findIdx? (· == name.toLower)).map NodeId.mk

def ElaboratedCircuit.device? (circuit : ElaboratedCircuit)
    (name : String) : Option DeviceId :=
  (circuit.deviceNames.findIdx? (· == name.toLower)).map DeviceId.mk

def ElaboratedCircuit.model? (circuit : ElaboratedCircuit)
    (name : String) : Option ModelId :=
  (circuit.modelNames.findIdx? (· == name.toLower)).map ModelId.mk

inductive DCProjectionError where
  | unsupportedDevice (id : DeviceId)
deriving Repr, BEq, Inhabited

def ElaboratedDevice.toDCDevice :
    ElaboratedDevice → Except DCProjectionError DCDevice
  | .resistor id positive negative resistance =>
      .ok (.resistor id positive negative resistance)
  | .voltageSource id positive negative voltage =>
      .ok (.voltageSource id positive negative voltage)
  | .currentSource id positive negative current =>
      .ok (.currentSource id positive negative current)
  | .capacitor id positive negative capacitance =>
      .ok (.capacitor id positive negative capacitance)
  | .inductor id positive negative inductance =>
      .ok (.inductor id positive negative inductance)
  | .mosfet id _ _ _ _ _ => .error (.unsupportedDevice id)

/-- Project the common artifact into the exact linear DC capability. This is
fallible by design: future MOS and behavioral devices inhabit the same root
IR but do not falsely acquire this view. -/
def ElaboratedCircuit.toDCCircuit
    (circuit : ElaboratedCircuit) : Except DCProjectionError DCCircuit := do
  let mut devices := #[]
  for device in circuit.devices do
    devices := devices.push (← device.toDCDevice)
  pure {
    title := circuit.title
    nodeNames := circuit.nodeNames
    deviceNames := circuit.deviceNames
    ground := circuit.ground
    devices }

/-- A proof-carrying exact linear DC view of one particular elaborated
circuit. Frontends construct this only after successful projection. -/
class ExactDCView (circuit : ElaboratedCircuit) where
  dc : DCCircuit
  projected : circuit.toDCCircuit = .ok dc

def DCAssignment.observeVoltage (circuit : ElaboratedCircuit)
    (assignment : DCAssignment) (node : ElaboratedNode circuit) : Rat :=
  assignment.voltage node.id

def DCAssignment.observeCurrent (circuit : ElaboratedCircuit)
    (assignment : DCAssignment)
    (device : ElaboratedDeviceRef circuit) : Rat :=
  assignment.current device.id

/-- Universal exact-DC semantics exposed at the common circuit artifact. -/
def DCModels (circuit : ElaboratedCircuit) [view : ExactDCView circuit]
    (property :
      (ElaboratedNode circuit → Rat) →
      (ElaboratedDeviceRef circuit → Rat) → Prop) : Prop :=
  ∀ assignment, DCSatisfies view.dc assignment →
    property (assignment.observeVoltage circuit)
      (assignment.observeCurrent circuit)

def RealizableDC (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] : Prop :=
  ∃ assignment, DCSatisfies view.dc assignment

def DeterminateDC (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] : Prop :=
  ∀ left right, DCSatisfies view.dc left → DCSatisfies view.dc right →
    left = right

def NominalDCBehavior (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] :
    Behavior Unit DCAssignment Unit :=
  fun _world assignment _internal => DCSatisfies view.dc assignment

def solveCircuitDC (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] : Except DCSolveError DCSolution :=
  solveDC view.dc

end LeanModels.Circuit
