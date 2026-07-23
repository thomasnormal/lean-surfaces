import LeanModels.Spice.Solve

/-!
# Exact interface contracts for linear DC subcircuits

A `PortContract k` describes the affine relation between the `k` port
voltages and the currents injected into the block by its environment.  Vectors
and matrices are functions on `Fin`; this makes their dimensions part of their
types without depending on a linear-algebra package.

`HasContract` deliberately contains two fields.  `sound` permits clients to
forget the implementation, while `realize` says that every point admitted by
the affine relation has an internal realization.  The latter is essential for
composition.
-/

namespace LeanModels.Spice

/-- A dimension-indexed vector. -/
abbrev Vec (k : Nat) (Value : Type := Rat) := Fin k → Value

/-- A dimension-indexed row-major matrix. -/
abbrev Matrix (rows cols : Nat) (Value : Type := Rat) :=
  Fin rows → Fin cols → Value

/-- A finite dot product, implemented using core `List.ofFn`. -/
def dot {k : Nat} {Value : Type} [Mul Value] [Add Value] [OfNat Value 0]
    (left right : Vec k Value) : Value :=
  (List.ofFn fun i : Fin k => left i * right i).foldl (fun total x => total + x) 0

/-- Matrix-vector multiplication over a value type with ring operations. -/
def matVec {rows cols : Nat} {Value : Type}
    [Mul Value] [Add Value] [OfNat Value 0]
    (matrix : Matrix rows cols Value)
    (vector : Vec cols Value) : Vec rows Value :=
  fun row => dot (matrix row) vector

/-- The exact affine port relation `I = Y V + J`. -/
structure PortContract (k : Nat) (Value : Type := Rat) where
  Y : Matrix k k Value
  J : Vec k Value

/-- Evaluate the current vector prescribed by a port contract. -/
def PortContract.apply {Value : Type}
    [Mul Value] [Add Value] [OfNat Value 0]
    (contract : PortContract k Value) (voltage : Vec k Value) : Vec k Value :=
  fun i => matVec contract.Y voltage i + contract.J i

/-- The `i`th formal port name.  `PortBehavior` separately requires the array
to have size `k`, so this total lookup never supplies its fallback there. -/
def Subckt.portName (subckt : Subckt) {k : Nat} (i : Fin k) : String :=
  subckt.ports.getD i.val ""

/-- Flatten a leaf subcircuit body.  Instances cannot be interpreted without
the enclosing definition table, so this operation rejects them loudly rather
than treating them as empty.  It is the M0 entry point for local leaf-contract
certificates. -/
def flattenLeafSubckt (subckt : Subckt) : Except FlattenError FlatNetlist := do
  let mut elements := #[]
  for card in subckt.body do
    match card with
    | .element element => elements := elements.push element
    | .mosfet mosfet =>
        throw (.unsupported "M" s!"MOS transistor {mosfet.name}")
    | .mosModel model =>
        throw (.unsupported ".model" s!"MOS model {model.name}")
    | .op _ => pure ()
    | .xInstance inst => throw (.missingSubckt inst.subckt)
    | .unsupported card => throw (.unsupported card.spiceKind card.text)
    | .subckt nested => throw (.nestedSubckt nested.name)
  pure { elements }

/-! ## Computable leaf reduction -/

/-- Failures while extracting a port contract by exact basis solves. -/
inductive ReductionError where
  | flatten (error : FlattenError)
  | solve (error : SolveError)
  | portArity (expected actual : Nat)
deriving Repr, BEq, DecidableEq, Inhabited

private def portDriveName (index : Nat) : String :=
  "__port_drive_" ++ toString index

private def portDrives (subckt : Subckt) (voltage : Vec k) : Array Element :=
  (List.ofFn fun i : Fin k =>
    { kind := .vsource
      span := ⟨0, 0⟩
      name := portDriveName i.val
      n1 := subckt.portName i
      n2 := "0"
      value := voltage i }).toArray

private def drivenLeaf (subckt : Subckt) (flat : FlatNetlist)
    (voltage : Vec k) : FlatNetlist :=
  { elements := flat.elements ++ portDrives subckt voltage }

private def solveDriven (subckt : Subckt) (flat : FlatNetlist)
    (voltage : Vec k) : Except ReductionError Assignment :=
  match solve (drivenLeaf subckt flat voltage) with
  | .ok assignment => .ok assignment
  | .error error => .error (.solve error)

/-- Current entering the block is the negative of the current through the
ideal voltage source that fixes the corresponding port voltage. -/
private def measuredCurrent (assignment : Assignment) (index : Fin k) : Rat :=
  -assignment.cur (portDriveName index.val)

private def basisVoltage (column : Fin k) : Vec k :=
  fun index => if index = column then 1 else 0

/-- Compute the exact affine port contract of a leaf by `k + 1` rational MNA
solves: one zero drive for `J`, then one unit drive per column of `Y`.

The result is computational evidence, not a trusted theorem.  A caller turns
it into `HasContract` with `hasContract_of_leafCertificate`, whose uniqueness
field proves that the basis-derived relation describes every behavior.
-/
def reduceLeaf (subckt : Subckt) (k : Nat) : Except ReductionError (PortContract k) := do
  if subckt.ports.size != k then
    throw (.portArity k subckt.ports.size)
  let flat ← match flattenLeafSubckt subckt with
    | .ok flat => pure flat
    | .error error => throw (.flatten error)
  let zeroVoltage : Vec k := fun _ => 0
  let zeroAssignment ← solveDriven subckt flat zeroVoltage
  let basisCurrents ← (List.ofFn fun column : Fin k => do
    let assignment ← solveDriven subckt flat (basisVoltage column)
    pure (fun row => measuredCurrent assignment row : Vec k)).mapM id
  let source : Vec k := fun row => measuredCurrent zeroAssignment row
  pure
    { Y := fun row column =>
        basisCurrents[column.val]! row - source row
      J := source }

/-- Whether a node of a leaf block is internal rather than ground or a port. -/
def IsInternalNode (subckt : Subckt) (flat : FlatNetlist) (node : String) : Prop :=
  node ∈ flat.nodes ∧ node != "0" ∧ !subckt.ports.contains node

/-- The exact projected behavior of a leaf subcircuit.

`current i` is oriented into the block from the environment.  Therefore its
sum with the currents contributed into the port node by the block's elements
is zero. -/
def PortBehavior (subckt : Subckt) (voltage current : Vec k) : Prop :=
  subckt.ports.size = k ∧
    ∃ flat, flattenLeafSubckt subckt = .ok flat ∧
    ∃ assignment : Assignment,
      assignment.volt "0" = 0 ∧
      (∀ i, assignment.volt (subckt.portName i) = voltage i) ∧
      (∀ element, element ∈ flat.elements.toList → DeviceLaw assignment element) ∧
      (∀ node, IsInternalNode subckt flat node → kclSum flat assignment node = 0) ∧
      (∀ i, kclSum flat assignment (subckt.portName i) + current i = 0)

/-- A block has a contract exactly when the concrete and affine behavior sets
contain one another.  These are separate fields so neither direction can be
accidentally omitted by a composition proof. -/
structure HasContract (subckt : Subckt) (contract : PortContract k) : Prop where
  /-- Every concrete behavior satisfies the advertised affine relation. -/
  sound : ∀ voltage current,
    PortBehavior subckt voltage current → current = contract.apply voltage
  /-- Every point on the affine relation has a concrete internal realization. -/
  realize : ∀ voltage current,
    current = contract.apply voltage → PortBehavior subckt voltage current

theorem hasContract_iff (subckt : Subckt) (contract : PortContract k) :
    HasContract subckt contract ↔
      ∀ voltage current,
        PortBehavior subckt voltage current ↔ current = contract.apply voltage := by
  constructor
  · intro h voltage current
    exact ⟨h.sound voltage current, h.realize voltage current⟩
  · intro h
    exact ⟨fun voltage current => (h voltage current).mp,
      fun voltage current => (h voltage current).mpr⟩

/-!
## Proof-carrying leaf reduction

Numerically sampling a solver cannot establish an exact affine interface.
`LeafContractCertificate` exposes the honest boundary: `extend` computes an
internal assignment for every port-voltage vector, while `behavior_current`
is the elimination/uniqueness obligation proving that no other current vector
is possible.  Concrete leaf reductions may fill all fields by rational
computation and algebra; the generic theorem below then yields both halves of
`HasContract` without trusting an evaluator.
-/

/-- A kernel-checkable certificate for reducing one leaf subcircuit to an
affine port contract. -/
structure LeafContractCertificate (subckt : Subckt)
    (contract : PortContract k) where
  flat : FlatNetlist
  flat_eq : flattenLeafSubckt subckt = .ok flat
  arity : subckt.ports.size = k
  extend : Vec k → Assignment
  extend_ground : ∀ voltage, (extend voltage).volt "0" = 0
  extend_ports : ∀ voltage i,
    (extend voltage).volt (subckt.portName i) = voltage i
  extend_devices : ∀ voltage element,
    element ∈ flat.elements.toList → DeviceLaw (extend voltage) element
  extend_internal : ∀ voltage node,
    IsInternalNode subckt flat node → kclSum flat (extend voltage) node = 0
  extend_ports_kcl : ∀ voltage i,
    kclSum flat (extend voltage) (subckt.portName i) + contract.apply voltage i = 0
  behavior_current : ∀ voltage current,
    PortBehavior subckt voltage current → current = contract.apply voltage

/-- A checked leaf-reduction certificate proves the full, two-directional
contract, including realizability. -/
theorem hasContract_of_leafCertificate
    (certificate : LeafContractCertificate subckt contract) :
    HasContract subckt contract := by
  constructor
  · exact certificate.behavior_current
  · intro voltage current hcurrent
    subst current
    refine ⟨certificate.arity, certificate.flat, certificate.flat_eq,
      certificate.extend voltage, certificate.extend_ground voltage, ?_, ?_, ?_, ?_⟩
    · exact certificate.extend_ports voltage
    · exact certificate.extend_devices voltage
    · exact certificate.extend_internal voltage
    · exact certificate.extend_ports_kcl voltage

end LeanModels.Spice
