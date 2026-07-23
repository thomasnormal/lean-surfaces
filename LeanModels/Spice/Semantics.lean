import LeanModels.Spice.Ast

/-!
# Exact linear-DC semantics and hierarchy flattening

`Satisfies` is a finite proposition over the nodes and elements of a flat
netlist. Kirchhoff's current law and the supported device laws are therefore
definitions, not axioms. Hierarchical netlists acquire meaning only through
the computable `flatten` function.
-/

namespace LeanModels.Spice

/-- Loud failures produced while removing `.subckt` hierarchy. -/
inductive FlattenError where
  | missingSubckt (name : String)
  | recursion (name : String)
  | portArity (name : String) (expected actual : Nat)
  | nestedSubckt (name : String)
  | unsupported (spiceKind text : String)
  | depth
deriving Repr, BEq, DecidableEq, Inhabited

def findSubckt (defs : Array (SubcktEntry Value))
    (name : String) : Option (Subckt Value) :=
  defs.toList.findSome? fun
    | .definition subckt => if subckt.name == name then some subckt else none
    | .unsupported _ => none

def lookupRename (renames : List (String × String))
    (name : String) : Option String :=
  renames.findSome? fun (localName, actual) =>
    if localName == name then some actual else none

def qualify (path name : String) : String :=
  if path.isEmpty then name else path ++ "." ++ name

def renameNode (path : String) (renames : List (String × String))
    (name : String) : String :=
  if name == "0" then "0"
  else (lookupRename renames name).getD (qualify path name)

def renameElement (path : String)
    (renames : List (String × String)) (element : Element Value) : Element Value :=
  { element with
    name := qualify path element.name
    n1 := renameNode path renames element.n1
    n2 := renameNode path renames element.n2 }

/-- Worker for `flatten`. The first argument bounds hierarchy depth by the
number of top-level definitions; ordinary card traversal is structural.
The active-definition list detects cycles before the depth bound is reached. -/
def flattenCards (defs : Array (SubcktEntry Value)) :
    Nat → List String → String → List (String × String) → List (Card Value) →
      Except FlattenError (List (Element Value))
  | 0, _, _, _, _ => .error .depth
  | _ + 1, _, _, _, [] => .ok []
  | fuel + 1, active, path, renames, card :: rest => do
      let head ← match card with
        | .element element => pure [renameElement path renames element]
        | .mosfet mosfet =>
            throw (.unsupported "M" s!"MOS transistor {mosfet.name}")
        | .mosModel model =>
            throw (.unsupported ".model" s!"MOS model {model.name}")
        | .op _ => pure []
        | .unsupported card => throw (.unsupported card.spiceKind card.text)
        | .subckt subckt => throw (.nestedSubckt subckt.name)
        | .xInstance inst =>
            let subckt ← match findSubckt defs inst.subckt with
              | some subckt => pure subckt
              | none => throw (.missingSubckt inst.subckt)
            if active.contains subckt.name then
              throw (.recursion subckt.name)
            if subckt.ports.size != inst.connections.size then
              throw (.portArity inst.name subckt.ports.size inst.connections.size)
            let actuals := inst.connections.toList.map (renameNode path renames)
            let localRenames := subckt.ports.toList.zip actuals
            let childPrefix := qualify path inst.name
            flattenCards defs fuel (subckt.name :: active) childPrefix
              localRenames subckt.body.toList
      let tail ← flattenCards defs fuel active path renames rest
      pure (head ++ tail)

def flattenBudget (netlist : Netlist Value) : Nat :=
  let cardCount := netlist.cards.size + netlist.subckts.foldl (fun total entry =>
    match entry with
    | .definition subckt => total + subckt.body.size
    | .unsupported _ => total + 1) 0
  (cardCount + 1) ^ (netlist.subckts.size + 2)

/-- Remove hierarchy, rename instance-local nodes/devices, and discard `.op`.
Ground remains global. The definition count is a complete hierarchy-depth
bound because recursive definition paths are rejected. -/
def flatten (netlist : Netlist Value) : Except FlattenError (FlatNetlist Value) := do
  let elements ← flattenCards netlist.subckts (flattenBudget netlist)
    [] "" [] netlist.cards.toList
  pure { elements := elements.toArray }

/-- Nodes mentioned by the flat netlist, without duplicates. -/
def FlatNetlist.nodes (netlist : FlatNetlist Value) : List String :=
  (netlist.elements.toList.flatMap fun element => [element.n1, element.n2]).eraseDups

/-- Branch-current keys introduced by MNA (`V` and `L` elements). -/
def FlatNetlist.branchNames (netlist : FlatNetlist Value) : List String :=
  netlist.elements.toList.filterMap fun element =>
    match element.kind with
    | .vsource | .inductor => some element.name
    | _ => none

/-- Current contributed *into* a node by one oriented element. -/
def currentInto (assignment : Assignment) (node : String) (element : Element) : Rat :=
  let contribution :=
    match element.kind with
    | .resistor => (assignment.volt element.n2 - assignment.volt element.n1) / element.value
    | .vsource | .inductor => -assignment.cur element.name
    | .isource => -element.value
    | .capacitor => 0
  if node == element.n1 then contribution
  else if node == element.n2 then -contribution
  else 0

/-- Kirchhoff sum at one node, using the `currentInto` orientation. -/
def kclSum (netlist : FlatNetlist) (assignment : Assignment) (node : String) : Rat :=
  netlist.elements.foldl (fun total element =>
    total + currentInto assignment node element) 0

/-- Constitutive laws not already encoded by `currentInto`.
Resistor Ohm law is its KCL contribution; capacitors are DC opens. -/
def DeviceLaw (assignment : Assignment) (element : Element) : Prop :=
  match element.kind with
  | .vsource => assignment.volt element.n1 - assignment.volt element.n2 = element.value
  | .inductor => assignment.volt element.n1 = assignment.volt element.n2
  | .resistor | .isource | .capacitor => True

def deviceLawHolds (assignment : Assignment) (element : Element) : Bool :=
  match element.kind with
  | .vsource => assignment.volt element.n1 - assignment.volt element.n2 == element.value
  | .inductor => assignment.volt element.n1 == assignment.volt element.n2
  | .resistor | .isource | .capacitor => true

/-- Linear DC meaning of a hierarchy-free netlist: ground, every separate
device law, and KCL at every mentioned non-ground node. The `List.All`
form makes the proposition decidable for concrete assignments. -/
def Satisfies (netlist : FlatNetlist) (assignment : Assignment) : Prop :=
  (assignment.volt "0" == 0) = true ∧
  netlist.elements.toList.all (deviceLawHolds assignment) = true ∧
  (netlist.nodes.filter (· != "0")).all
    (fun node => kclSum netlist assignment node == 0) = true

instance (netlist : FlatNetlist) (assignment : Assignment) :
    Decidable (Satisfies netlist assignment) := by
  unfold Satisfies
  infer_instance

/-- Hierarchical satisfaction is definitionally mediated by `flatten`. -/
def SatisfiesNetlist (netlist : Netlist) (assignment : Assignment) : Prop :=
  match flatten netlist with
  | .ok flat => Satisfies flat assignment
  | .error _ => False

/-- Equality only on voltages and branch currents constrained by a netlist. -/
def SupportEq (netlist : FlatNetlist) (left right : Assignment) : Prop :=
  netlist.nodes.all (fun node => left.volt node == right.volt node) = true ∧
  netlist.branchNames.all (fun name => left.cur name == right.cur name) = true

/-- Existence and uniqueness on support. Off-support values of total
assignments are deliberately irrelevant. -/
def WellPosed (netlist : Netlist) : Prop :=
  ∃ flat, flatten netlist = .ok flat ∧
    ∃ assignment, Satisfies flat assignment ∧
      ∀ other, Satisfies flat other → SupportEq flat assignment other

/-! ## Closed smoke tests -/

private def dividerFlat : FlatNetlist :=
  { elements := #[
      ⟨.vsource, ⟨1, 1⟩, "v1", "in", "0", 5⟩,
      ⟨.resistor, ⟨2, 2⟩, "r1", "in", "out", 1000⟩,
      ⟨.resistor, ⟨3, 3⟩, "r2", "out", "0", 2000⟩] }

private def dividerAssignment : Assignment :=
  { volt := fun node => if node == "in" then 5 else if node == "out" then 10 / 3 else 0
    cur := fun name => if name == "v1" then -1 / 600 else 0 }

#guard decide (Satisfies dividerFlat dividerAssignment)
#guard dividerFlat.nodes.contains "out"
#guard dividerFlat.branchNames == ["v1"]

end LeanModels.Spice
