import LeanModels.Circuit.Contract
import LeanModels.Circuit.Spice

/-!
# Physical DC block boundaries

A `DCBlock` is a directly parsed leaf subcircuit together with its ordered
ports. Its port relation retains all device laws and internal KCL equations,
but leaves port KCL open for the environment current.
-/

namespace LeanModels.Circuit

structure DCBlock where
  name : String
  portNames : Array String
  portNodes : Array NodeId
  circuit : DCCircuit
deriving Repr, BEq, Inhabited

def DCBlock.portName (block : DCBlock) {size : Nat}
    (index : Fin size) : String :=
  block.portNames.getD index.val ""

def DCBlock.portNode (block : DCBlock) {size : Nat}
    (index : Fin size) : NodeId :=
  block.portNodes.getD index.val block.circuit.ground

def DCBlock.IsInternalNode (block : DCBlock) (node : NodeId) : Prop :=
  node ≠ block.circuit.ground ∧
    node ∉ block.portNodes

/-- Concrete boundary behavior. Currents are positive from the boundary node
into the block. At a hidden connection, the currents into the adjacent blocks
therefore sum to zero. -/
def DCBlock.PortBehavior (block : DCBlock) :
    PortRelation size :=
  fun voltage current =>
    block.portNames.size = size ∧
    block.circuit.isValid = true ∧
    ∃ assignment : DCAssignment,
      assignment.voltages.size = block.circuit.nodeNames.size ∧
      assignment.currents.size = block.circuit.devices.size ∧
      assignment.voltage block.circuit.ground = 0 ∧
      (∀ device ∈ block.circuit.devices,
        device.lawHolds assignment = true) ∧
      (∀ node ∈ block.circuit.nodes,
        block.IsInternalNode node →
          block.circuit.kcl assignment node = 0) ∧
      (∀ index, assignment.voltage (block.portNode index) = voltage index) ∧
      (∀ index,
        block.circuit.kcl assignment (block.portNode index) = current index)

/-- A leaf source subcircuit becomes a typed block without JSON or a parallel
hand-written netlist. Nested instances are handled by hierarchy composition,
not silently flattened for a leaf contract. -/
def Spice.SourceSubcircuit.toDCBlock
    (subcircuit : Spice.SourceSubcircuit) : Except String DCBlock := do
  unless subcircuit.instances.isEmpty do
    throw s!"subcircuit `{subcircuit.name}` is not a leaf"
  unless subcircuit.mosfets.isEmpty do
    throw s!"subcircuit `{subcircuit.name}` is not an exact linear DC block"
  let circuit ←
    (Spice.elaborateDC {
      title := subcircuit.name
      devices := subcircuit.devices
      mosfets := #[]
      models := #[]
      instances := #[]
      subcircuits := #[] })
  let mut portNodes := #[]
  for port in subcircuit.ports do
    match circuit.node? port with
    | some node => portNodes := portNodes.push node
    | none =>
        throw s!"port `{port}` is not connected in subcircuit `{subcircuit.name}`"
  pure {
    name := subcircuit.name
    portNames := subcircuit.ports
    portNodes
    circuit }

end LeanModels.Circuit
