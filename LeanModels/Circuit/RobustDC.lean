import Mathlib.Tactic
import LeanModels.Circuit.Elaboration
import LeanModels.Circuit.World

/-!
# Real-valued robust DC interpretation

Topology comes from the typed circuit. Fabricated resistances are selected
once per instance; source values belong to the run environment.
-/

namespace LeanModels.Circuit

structure DCFabricatedInstance where
  resistance : DeviceId → ℝ

structure DCEnvironment where
  sourceVoltage : DeviceId → ℝ
  sourceCurrent : DeviceId → ℝ := fun _ => 0

abbrev DCRunWorld :=
  RunWorld DCFabricatedInstance DCEnvironment Unit Unit

structure RealDCAssignment where
  voltage : NodeId → ℝ
  current : DeviceId → ℝ

def DCDevice.realLaw (world : DCRunWorld)
    (assignment : RealDCAssignment) : DCDevice → Prop
  | .resistor id positive negative _ =>
      assignment.current id =
        (assignment.voltage positive - assignment.voltage negative) /
          world.fabricated.resistance id
  | .voltageSource id positive negative _ =>
      assignment.voltage positive - assignment.voltage negative =
        world.environment.sourceVoltage id
  | .currentSource id _ _ _ =>
      assignment.current id = world.environment.sourceCurrent id
  | .capacitor id _ _ _ =>
      assignment.current id = 0
  | .inductor _ positive negative _ =>
      assignment.voltage positive = assignment.voltage negative

def DCDevice.realCurrentLeaving (assignment : RealDCAssignment)
    (node : NodeId) (device : DCDevice) : ℝ :=
  if node == device.positive then assignment.current device.id
  else if node == device.negative then -assignment.current device.id
  else 0

def DCCircuit.realKcl (circuit : DCCircuit)
    (assignment : RealDCAssignment) (node : NodeId) : ℝ :=
  circuit.devices.foldl
    (fun total device => total + device.realCurrentLeaving assignment node) 0

/-- Real-valued DC denotation over a fixed topology and one run world. -/
def RawRealDCSatisfies (circuit : DCCircuit) (world : DCRunWorld)
    (assignment : RealDCAssignment) : Prop :=
  circuit.isValid = true ∧
  assignment.voltage circuit.ground = 0 ∧
  (∀ device ∈ circuit.devices, device.realLaw world assignment) ∧
  (∀ node ∈ circuit.nodes, node ≠ circuit.ground →
    circuit.realKcl assignment node = 0)

def RawRealDCBehavior (circuit : DCCircuit) :
    Behavior DCRunWorld RealDCAssignment Unit :=
  fun world assignment _ => RawRealDCSatisfies circuit world assignment

def RealDCSatisfies (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] (world : DCRunWorld)
    (assignment : RealDCAssignment) : Prop :=
  RawRealDCSatisfies view.dc world assignment

def RealDCBehavior (circuit : ElaboratedCircuit)
    [view : ExactDCView circuit] :
    Behavior DCRunWorld RealDCAssignment Unit :=
  RawRealDCBehavior view.dc

theorem RealDCSatisfies.deviceLaw
    [ExactDCView circuit]
    (h : RealDCSatisfies circuit world assignment)
    (device : DCDevice)
    (membership : device ∈ (ExactDCView.dc (circuit := circuit)).devices) :
    device.realLaw world assignment :=
  h.2.2.1 device membership

theorem RealDCSatisfies.kclAt
    [ExactDCView circuit]
    (h : RealDCSatisfies circuit world assignment)
    (node : NodeId)
    (membership : node ∈ (ExactDCView.dc (circuit := circuit)).nodes)
    (nonground : node ≠ (ExactDCView.dc (circuit := circuit)).ground) :
    (ExactDCView.dc (circuit := circuit)).realKcl assignment node = 0 :=
  h.2.2.2 node membership nonground

/-- Nominal real world obtained from exact source literals. -/
noncomputable def DCCircuit.rawNominalWorld
    (circuit : DCCircuit) : DCRunWorld :=
  deterministicWorld
    { resistance := fun id =>
        match circuit.devices[id.index]? with
        | some (.resistor _ _ _ value) => value
        | _ => 0 }
    { sourceVoltage := fun id =>
        match circuit.devices[id.index]? with
        | some (.voltageSource _ _ _ value) => value
        | _ => 0
      sourceCurrent := fun id =>
        match circuit.devices[id.index]? with
        | some (.currentSource _ _ _ value) => value
        | _ => 0 }

noncomputable def ElaboratedCircuit.nominalWorld
    (circuit : ElaboratedCircuit) [view : ExactDCView circuit] : DCRunWorld :=
  view.dc.rawNominalWorld

end LeanModels.Circuit
