import LeanModels.Circuit.Elaboration

/-!
# Resolved MOS1 semantic view

This module is the only bridge from the analysis-neutral
`Circuit.ElaboratedCircuit` to the restricted MOS1 equations. It contains no
legacy JSON/netlist AST and performs no second parse.
-/

namespace LeanModels.Spice

structure NodeId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure SourceId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure TransistorId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure ModelId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

def node (name : String) : NodeId := ⟨name⟩
def sourceId (name : String) : SourceId := ⟨name⟩
def transistorId (name : String) : TransistorId := ⟨name⟩
def modelId (name : String) : ModelId := ⟨name⟩

instance : ToString NodeId := ⟨NodeId.name⟩
instance : ToString SourceId := ⟨SourceId.name⟩
instance : ToString TransistorId := ⟨TransistorId.name⟩
instance : ToString ModelId := ⟨ModelId.name⟩

def ground : NodeId := node "0"
def supply : NodeId := node "vdd"

/-- Exact parameters for the supported MOS Level-1 profile. Model references
have already been resolved by the shared frontend. -/
structure Mos1Model where
  id : ModelId
  polarity : LeanModels.Circuit.MosPolarity
  threshold : Rat
  transconductance : Rat
  channelLengthModulation : Rat
deriving Repr, BEq, DecidableEq, Inhabited

structure Mos1VoltageSource where
  id : SourceId
  positive : NodeId
  negative : NodeId
  voltage : Rat
deriving Repr, BEq, DecidableEq, Inhabited

structure Mos1Transistor where
  id : TransistorId
  drain : NodeId
  gate : NodeId
  source : NodeId
  bulk : NodeId
  model : Mos1Model
deriving Repr, BEq, DecidableEq, Inhabited

inductive Mos1Device where
  | voltageSource (source : Mos1VoltageSource)
  | transistor (transistor : Mos1Transistor)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Hierarchy-free, model-resolved semantic capability of one shared circuit
identity. -/
structure Mos1ResolvedCircuit where
  title : String
  devices : Array Mos1Device
deriving Repr, BEq, DecidableEq, Inhabited

def Mos1Device.nodes : Mos1Device → List NodeId
  | .voltageSource source => [source.positive, source.negative]
  | .transistor mos => [mos.drain, mos.gate, mos.source, mos.bulk]

def Mos1ResolvedCircuit.nodes
    (circuit : Mos1ResolvedCircuit) : List NodeId :=
  circuit.devices.toList.flatMap Mos1Device.nodes

abbrev Mos1ResolvedCircuit.Node (circuit : Mos1ResolvedCircuit) :=
  { candidate : NodeId // candidate ∈ circuit.nodes }

abbrev Mos1ResolvedCircuit.checkedNode
    (circuit : Mos1ResolvedCircuit) (candidate : NodeId)
    (_ : candidate ∈ circuit.nodes) : NodeId :=
  candidate

def Mos1ResolvedCircuit.nodeNames
    (circuit : Mos1ResolvedCircuit) : List String :=
  circuit.nodes.eraseDups.map NodeId.name

def Mos1ResolvedCircuit.describeNodes
    (circuit : Mos1ResolvedCircuit) : String :=
  String.intercalate ", " circuit.nodeNames

inductive SharedMos1ProjectionError where
  | unsupportedDevice (name : String)
  | missingModel (name : String)
  | invalidModel (name : String)
deriving Repr, BEq, DecidableEq, Inhabited

def sharedNode
    (circuit : LeanModels.Circuit.ElaboratedCircuit)
    (id : LeanModels.Circuit.NodeId) : NodeId :=
  node (circuit.nodeNames.getD id.index "")

def sharedModel
    (circuit : LeanModels.Circuit.ElaboratedCircuit)
    (id : LeanModels.Circuit.ModelId) :
    Except SharedMos1ProjectionError Mos1Model := do
  let name := circuit.modelNames.getD id.index ""
  let raw ← match circuit.models[id.index]? with
    | some raw => pure raw
    | none => throw (.missingModel name)
  match raw with
  | .mos1 model =>
      if model.transconductance ≤ 0 ||
          model.channelLengthModulation != 0 ||
          model.junctionSaturation != 0 ||
          model.threshold ≤ 0 then
        throw (.invalidModel name)
      pure
        { id := modelId name
          polarity := model.polarity
          threshold := model.threshold
          transconductance := model.transconductance
          channelLengthModulation := model.channelLengthModulation }

def sharedDevice
    (circuit : LeanModels.Circuit.ElaboratedCircuit) :
    LeanModels.Circuit.ElaboratedDevice →
      Except SharedMos1ProjectionError Mos1Device
  | .voltageSource id positive negative voltage =>
      let name := circuit.deviceNames.getD id.index ""
      .ok (.voltageSource
        { id := sourceId name
          positive := sharedNode circuit positive
          negative := sharedNode circuit negative
          voltage })
  | .mosfet id drain gate source bulk model => do
      let name := circuit.deviceNames.getD id.index ""
      pure (.transistor
        { id := transistorId name
          drain := sharedNode circuit drain
          gate := sharedNode circuit gate
          source := sharedNode circuit source
          bulk := sharedNode circuit bulk
          model := ← sharedModel circuit model })
  | device =>
      .error (.unsupportedDevice
        (circuit.deviceNames.getD device.id.index ""))

def sharedToMos1Circuit
    (circuit : LeanModels.Circuit.ElaboratedCircuit) :
    Except SharedMos1ProjectionError Mos1ResolvedCircuit := do
  let devices ← circuit.devices.toList.mapM (sharedDevice circuit)
  pure { title := circuit.title, devices := devices.toArray }

/-- Certified resolved MOS1 capability of a shared circuit identity. -/
class Mos1View (circuit : LeanModels.Circuit.ElaboratedCircuit) where
  mos1 : Mos1ResolvedCircuit
  projected : sharedToMos1Circuit circuit = .ok mos1

end LeanModels.Spice
