import LeanModels.Circuit.Behavior
import LeanModels.Circuit.Nature

/-!
# Typed exact DC circuits

The semantic circuit uses numeric node and device identifiers. Source names
are retained only in tables used by diagnostics and checked surface accessors.
Every solver result is checked against `DCSatisfies` before it is exposed.
-/

namespace LeanModels.Circuit

structure NodeId where
  index : Nat
deriving Repr, BEq, DecidableEq, Inhabited

structure DeviceId where
  index : Nat
deriving Repr, BEq, DecidableEq, Inhabited

@[simp] theorem NodeId.beq_mk (left right : Nat) :
    ((NodeId.mk left == NodeId.mk right) : Bool) = (left == right) := rfl

@[simp] theorem DeviceId.beq_mk (left right : Nat) :
    ((DeviceId.mk left == DeviceId.mk right) : Bool) = (left == right) := rfl

inductive DCDevice where
  | resistor (id : DeviceId) (positive negative : NodeId) (resistance : Rat)
  | voltageSource (id : DeviceId) (positive negative : NodeId) (voltage : Rat)
  | currentSource (id : DeviceId) (positive negative : NodeId) (current : Rat)
  | capacitor (id : DeviceId) (positive negative : NodeId) (capacitance : Rat)
  | inductor (id : DeviceId) (positive negative : NodeId) (inductance : Rat)
deriving Repr, BEq, Inhabited

def DCDevice.id : DCDevice → DeviceId
  | .resistor id _ _ _
  | .voltageSource id _ _ _
  | .currentSource id _ _ _
  | .capacitor id _ _ _
  | .inductor id _ _ _ => id

def DCDevice.positive : DCDevice → NodeId
  | .resistor _ positive _ _
  | .voltageSource _ positive _ _
  | .currentSource _ positive _ _
  | .capacitor _ positive _ _
  | .inductor _ positive _ _ => positive

def DCDevice.negative : DCDevice → NodeId
  | .resistor _ _ negative _
  | .voltageSource _ _ negative _
  | .currentSource _ _ negative _
  | .capacitor _ _ negative _
  | .inductor _ _ negative _ => negative

/-- Hierarchy-free, dimension-checked electrical DC circuit. -/
structure DCCircuit where
  title : String
  nodeNames : Array String
  deviceNames : Array String
  ground : NodeId
  devices : Array DCDevice
deriving Repr, BEq, Inhabited

/-- A node reference whose index is proved to belong to this circuit.
The circuit parameter prevents accidental cross-circuit observations. -/
structure CircuitNode (circuit : DCCircuit) where
  id : NodeId
  valid : id.index < circuit.nodeNames.size

/-- A device reference whose index is proved to belong to this circuit.
The circuit parameter prevents accidental cross-circuit parameter lookup. -/
structure CircuitDevice (circuit : DCCircuit) where
  id : DeviceId
  valid : id.index < circuit.devices.size

def DCCircuit.node? (circuit : DCCircuit) (name : String) : Option NodeId :=
  (circuit.nodeNames.findIdx? (· == name.toLower)).map NodeId.mk

def DCCircuit.hasNode (circuit : DCCircuit) (name : String) : Bool :=
  circuit.nodeNames.contains name.toLower

/-- Convert a source-facing node name to the numeric semantic identifier only
after membership in the literal circuit has been proved. -/
def DCCircuit.checkedNode (circuit : DCCircuit) (name : String)
    (_ : circuit.hasNode name = true) : NodeId :=
  NodeId.mk ((circuit.nodeNames.findIdx? (· == name.toLower)).getD 0)

def DCCircuit.device? (circuit : DCCircuit) (name : String) : Option DeviceId :=
  (circuit.deviceNames.findIdx? (· == name.toLower)).map DeviceId.mk

structure DCAssignment where
  voltages : Array Rat
  currents : Array Rat
deriving Repr, BEq, Inhabited

def DCAssignment.voltage (assignment : DCAssignment) (node : NodeId) : Rat :=
  assignment.voltages.getD node.index 0

def DCAssignment.current (assignment : DCAssignment) (device : DeviceId) : Rat :=
  assignment.currents.getD device.index 0

def DCAssignment.observeDCVoltage (circuit : DCCircuit)
    (assignment : DCAssignment) (node : CircuitNode circuit) : Rat :=
  assignment.voltage node.id

def DCAssignment.observeDCCurrent (circuit : DCCircuit)
    (assignment : DCAssignment) (device : CircuitDevice circuit) : Rat :=
  assignment.current device.id

def DCDevice.lawHolds (assignment : DCAssignment) : DCDevice → Bool
  | .resistor id positive negative resistance =>
      resistance != 0 &&
        assignment.current id ==
          (assignment.voltage positive - assignment.voltage negative) / resistance
  | .voltageSource _ positive negative voltage =>
      assignment.voltage positive - assignment.voltage negative == voltage
  | .currentSource id _ _ current =>
      assignment.current id == current
  | .capacitor id _ _ capacitance =>
      capacitance != 0 && assignment.current id == 0
  | .inductor _ positive negative inductance =>
      inductance != 0 &&
        assignment.voltage positive == assignment.voltage negative

/-- Current leaving `node`, with every device oriented positive-to-negative. -/
def DCDevice.currentLeaving (assignment : DCAssignment)
    (node : NodeId) (device : DCDevice) : Rat :=
  if node == device.positive then assignment.current device.id
  else if node == device.negative then -assignment.current device.id
  else 0

def DCCircuit.kcl (circuit : DCCircuit)
    (assignment : DCAssignment) (node : NodeId) : Rat :=
  circuit.devices.foldl
    (fun total device => total + device.currentLeaving assignment node) 0

def DCCircuit.nodes (circuit : DCCircuit) : List NodeId :=
  (List.range circuit.nodeNames.size).map NodeId.mk

/-- Structural well-formedness required by both semantics and solvers. -/
def DCCircuit.isValid (circuit : DCCircuit) : Bool :=
  circuit.ground.index < circuit.nodeNames.size &&
  circuit.devices.size == circuit.deviceNames.size &&
  circuit.devices.all fun device =>
    device.id.index < circuit.devices.size &&
    device.positive.index < circuit.nodeNames.size &&
    device.negative.index < circuit.nodeNames.size &&
    match device with
    | .resistor _ _ _ resistance => resistance != 0
    | .voltageSource _ _ _ _ => true
    | .currentSource _ _ _ _ => true
    | .capacitor _ _ _ capacitance => capacitance != 0
    | .inductor _ _ _ inductance => inductance != 0

/-- Executable form of the finite physical laws. -/
def dcSatisfiesBool (circuit : DCCircuit) (assignment : DCAssignment) : Bool :=
  circuit.isValid &&
  assignment.voltages.size == circuit.nodeNames.size &&
  assignment.currents.size == circuit.devices.size &&
  assignment.voltage circuit.ground == 0 &&
  circuit.devices.all (·.lawHolds assignment) &&
  circuit.nodes.all fun node =>
    node == circuit.ground || circuit.kcl assignment node == 0

/-- Ground, every constitutive law, and KCL at every non-ground node. -/
def DCSatisfies (circuit : DCCircuit) (assignment : DCAssignment) : Prop :=
  dcSatisfiesBool circuit assignment = true

instance (circuit : DCCircuit) (assignment : DCAssignment) :
    Decidable (DCSatisfies circuit assignment) := by
  unfold DCSatisfies
  infer_instance

theorem DCSatisfies.valid
    (h : DCSatisfies circuit assignment) :
    circuit.isValid = true := by
  unfold DCSatisfies dcSatisfiesBool at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1

def RawDCModels (circuit : DCCircuit)
    (property :
      (CircuitNode circuit → Rat) →
      (CircuitDevice circuit → Rat) → Prop) : Prop :=
  ∀ assignment, DCSatisfies circuit assignment →
    property (assignment.observeDCVoltage circuit)
      (assignment.observeDCCurrent circuit)

def RawRealizableDC (circuit : DCCircuit) : Prop :=
  ∃ assignment, DCSatisfies circuit assignment

def RawDeterminateDC (circuit : DCCircuit) : Prop :=
  ∀ left right, DCSatisfies circuit left → DCSatisfies circuit right →
    left = right

/-- Exact nominal DC as an instance of the analysis-independent relational
behavior root. -/
def RawNominalDCBehavior (circuit : DCCircuit) :
    Behavior Unit DCAssignment Unit :=
  fun _world assignment _internal => DCSatisfies circuit assignment

/-! ## Checked exact MNA -/

inductive DCUnknown where
  | voltage (node : NodeId)
  | current (device : DeviceId)
deriving Repr, BEq, DecidableEq, Inhabited

inductive DCSolveError where
  | malformed
  | inconsistent
  | underdetermined (column : Nat)
  | candidateRejected
deriving Repr, BEq, DecidableEq, Inhabited

structure DCLinearSystem where
  unknowns : List DCUnknown
  rows : List (List Rat)
deriving Repr, BEq, Inhabited

structure DCSolution where
  voltages : Array Rat
  currents : Array Rat
deriving Repr, BEq, DecidableEq, Inhabited

def DCSolution.assignment (solution : DCSolution) : DCAssignment :=
  ⟨solution.voltages, solution.currents⟩

private def nodeUnknowns (circuit : DCCircuit) : List DCUnknown :=
  circuit.nodes.map .voltage

private def currentUnknowns (circuit : DCCircuit) : List DCUnknown :=
  (List.range circuit.devices.size).map (fun index => .current ⟨index⟩)

private def dcUnknowns (circuit : DCCircuit) : List DCUnknown :=
  nodeUnknowns circuit ++ currentUnknowns circuit

private def deviceAt? (circuit : DCCircuit) (id : DeviceId) : Option DCDevice :=
  circuit.devices[id.index]?

private def kclUnknownCoefficient (circuit : DCCircuit)
    (node : NodeId) : DCUnknown → Rat
  | .voltage _ => 0
  | .current id =>
      match deviceAt? circuit id with
      | some device =>
          if node == device.positive then 1
          else if node == device.negative then -1
          else 0
      | none => 0

private def groundCoefficient (ground : NodeId) : DCUnknown → Rat
  | .voltage node => if node == ground then 1 else 0
  | .current _ => 0

private def deviceCoefficient (device : DCDevice) : DCUnknown → Rat
  | .voltage node =>
      match device with
      | .resistor _ positive negative resistance =>
          if node == positive then -(1 / resistance)
          else if node == negative then 1 / resistance
          else 0
      | .voltageSource _ positive negative _ =>
          if node == positive then 1
          else if node == negative then -1
          else 0
      | .currentSource _ _ _ _ => 0
      | .capacitor _ _ _ _ => 0
      | .inductor _ positive negative _ =>
          if node == positive then 1
          else if node == negative then -1
          else 0
  | .current id =>
      match device with
      | .resistor own _ _ _ => if id == own then 1 else 0
      | .voltageSource _ _ _ _ => 0
      | .currentSource own _ _ _ => if id == own then 1 else 0
      | .capacitor own _ _ _ => if id == own then 1 else 0
      | .inductor _ _ _ _ => 0

private def deviceRhs : DCDevice → Rat
  | .resistor _ _ _ _ => 0
  | .voltageSource _ _ _ voltage => voltage
  | .currentSource _ _ _ current => current
  | .capacitor _ _ _ _ => 0
  | .inductor _ _ _ _ => 0

def assembleDC (circuit : DCCircuit) : DCLinearSystem :=
  let unknowns := dcUnknowns circuit
  let groundRow := unknowns.map (groundCoefficient circuit.ground) ++ [0]
  let kclRows :=
    circuit.nodes.filter (· != circuit.ground) |>.map fun node =>
      unknowns.map (kclUnknownCoefficient circuit node) ++ [0]
  let deviceRows := circuit.devices.toList.map fun device =>
    unknowns.map (deviceCoefficient device) ++ [deviceRhs device]
  { unknowns, rows := groundRow :: kclRows ++ deviceRows }

private def replaceAt (xs : List α) (index : Nat) (value : α) : List α :=
  xs.take index ++ value :: xs.drop (index + 1)

private def swapAt (xs : List α) (left right : Nat) : List α :=
  match xs[left]?, xs[right]? with
  | some x, some y => replaceAt (replaceAt xs left y) right x
  | _, _ => xs

private def findPivot (rows : List (List Rat)) (column : Nat) : Nat → Option Nat
  | row =>
      if row < rows.length then
        if (rows[row]?.bind (·[column]?)).getD 0 != 0 then some row
        else findPivot rows column (row + 1)
      else none
termination_by row => rows.length - row

private def scaleRow (factor : Rat) (row : List Rat) : List Rat :=
  row.map (factor * ·)

private def addScaled (factor : Rat) (source target : List Rat) : List Rat :=
  List.zipWith (fun x y => x + factor * y) target source

private def eliminateColumn (rows : List (List Rat)) (pivotRow column : Nat) :
    List (List Rat) :=
  match rows[pivotRow]? with
  | none => rows
  | some pivot => rows.zipIdx.map fun (row, index) =>
      if index == pivotRow then row
      else addScaled (-row[column]!) pivot row

private def inconsistentRow (dimension : Nat) (row : List Rat) : Bool :=
  (row.take dimension).all (· == 0) &&
    row[dimension]?.getD 0 != 0

private def gaussJordan.go (dimension : Nat) : Nat → List (List Rat) →
    Except DCSolveError (List (List Rat))
  | column, rows =>
      if column < dimension then do
        let pivotRow ← match findPivot rows column column with
          | some row => pure row
          | none =>
              if rows.drop column |>.any (inconsistentRow dimension) then
                throw .inconsistent
              else
                throw (.underdetermined column)
        let rows := swapAt rows column pivotRow
        let pivot := (rows[column]?.bind (·[column]?)).getD 0
        if pivot == 0 then throw (.underdetermined column)
        let rows := replaceAt rows column (scaleRow (1 / pivot) rows[column]!)
        gaussJordan.go dimension (column + 1)
          (eliminateColumn rows column column)
      else pure rows
termination_by column => dimension - column

private def gaussJordan (system : DCLinearSystem) :
    Except DCSolveError (List Rat) := do
  let dimension := system.unknowns.length
  let reduced ← gaussJordan.go dimension 0 system.rows
  pure (reduced.take dimension |>.map fun row => row[dimension]!)

private def candidateSolution (circuit : DCCircuit) :
    Except DCSolveError DCSolution := do
  unless circuit.isValid do throw .malformed
  let values ← gaussJordan (assembleDC circuit)
  pure {
    voltages := (values.take circuit.nodeNames.size).toArray
    currents :=
      (values.drop circuit.nodeNames.size |>.take circuit.devices.size).toArray }

private def checkedSolution (circuit : DCCircuit) (candidate : DCSolution) :
    Except DCSolveError DCSolution :=
  if _h : DCSatisfies circuit candidate.assignment then .ok candidate
  else .error .candidateRejected

def solveDC (circuit : DCCircuit) : Except DCSolveError DCSolution := do
  checkedSolution circuit (← candidateSolution circuit)

private theorem checkedSolution_satisfies {circuit : DCCircuit}
    {candidate solution : DCSolution}
    (h : checkedSolution circuit candidate = .ok solution) :
    DCSatisfies circuit solution.assignment := by
  unfold checkedSolution at h
  split at h
  · next hs =>
      simp at h
      subst solution
      exact hs
  · simp at h

theorem solveDC_satisfies {circuit : DCCircuit} {solution : DCSolution}
    (h : solveDC circuit = .ok solution) :
    DCSatisfies circuit solution.assignment := by
  unfold solveDC at h
  generalize hc : candidateSolution circuit = candidate at h
  cases candidate with
  | error error => cases h
  | ok candidate => exact checkedSolution_satisfies h

end LeanModels.Circuit
