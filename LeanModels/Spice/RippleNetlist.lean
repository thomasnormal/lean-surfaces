import LeanModels.Spice.Ripple
import LeanModels.Circuit.Spice

/-!
# Literal hierarchical ripple-adder layouts

This module stops hierarchy expansion at `half_adder` instances. It connects
the calls written in a SPICE deck to `RippleAdderOf` without flattening the
transistor implementation repeated behind every call.
-/

namespace LeanModels.Spice

open LeanModels.Circuit.Spice

/-- The five electrical ports of one literal `half_adder` call. -/
structure HalfAdderCall where
  name : String
  left : String
  right : String
  sum : String
  carry : String
  supply : String
deriving Repr, BEq, DecidableEq, Inhabited

inductive RippleLayoutError where
  | depth
  | missingSubcircuit (name : String)
  | recursion (name : String)
  | portArity (instanceName : String) (expected actual : Nat)
  | unexpectedLeaf (subcircuit : String)
deriving Repr, BEq, DecidableEq, Inhabited

def qualifyLayout (path name : String) : String :=
  if path.isEmpty then name else path ++ "." ++ name

def renameLayoutNode
    (path : String) (renames : List (String × String))
    (name : String) : String :=
  if name == "0" then "0"
  else match renames.lookup name with
    | some renamed => renamed
    | none => qualifyLayout path name

def findSourceSubcircuit
    (definitions : Array SourceSubcircuit) (name : String) :
    Option SourceSubcircuit :=
  definitions.toList.find? (·.name == name)

def halfAdderCallOf (path : String) (inst : SourceInstance)
    (actuals : List String) : Except RippleLayoutError HalfAdderCall :=
  match actuals with
  | [left, right, sum, carry, supply] =>
      .ok {
        name := qualifyLayout path inst.name
        left, right, sum, carry, supply }
  | _ => .error (.portArity inst.name 5 actuals.length)

def expandHalfAdderCallsFrom
    (definitions : Array SourceSubcircuit) :
    Nat → List String → String → List (String × String) →
      List SourceInstance → Except RippleLayoutError (List HalfAdderCall)
  | 0, _, _, _, _ => .error .depth
  | _ + 1, _, _, _, [] => .ok []
  | fuel + 1, active, path, renames, inst :: rest => do
      let subcircuit ←
        match findSourceSubcircuit definitions inst.subcircuit with
        | some subcircuit => pure subcircuit
        | none => throw (.missingSubcircuit inst.subcircuit)
      if active.contains subcircuit.name then
        throw (.recursion subcircuit.name)
      if subcircuit.ports.size != inst.connections.size then
        throw (.portArity inst.name subcircuit.ports.size
          inst.connections.size)
      let actuals :=
        inst.connections.toList.map (renameLayoutNode path renames)
      let head ←
        if subcircuit.name == "half_adder" then
          pure [← halfAdderCallOf path inst actuals]
        else
          if !subcircuit.devices.isEmpty || !subcircuit.mosfets.isEmpty then
            throw (.unexpectedLeaf subcircuit.name)
          let localRenames := subcircuit.ports.toList.zip actuals
          expandHalfAdderCallsFrom definitions fuel
            (subcircuit.name :: active)
            (qualifyLayout path inst.name) localRenames
            subcircuit.instances.toList
      let tail ←
        expandHalfAdderCallsFrom definitions fuel active path renames rest
      pure (head ++ tail)

/-- Expand a hierarchy only far enough to expose its half-adder calls. Any
device above that abstraction boundary is rejected. -/
def expandHalfAdderCalls
    (source : SourceCircuit) :
    Except RippleLayoutError (List HalfAdderCall) :=
  expandHalfAdderCallsFrom source.subcircuits
    (source.instances.size + source.subcircuits.size + 2)
    [] "" [] source.instances.toList

/-- Hierarchy syntax relevant to the reusable half-adder implementation.
Source spans and analysis cards are deliberately absent. -/
inductive HierarchyCardShape where
  | mosfet (name drain gate source bulk model : String)
  | instance (name subckt : String) (connections : List String)
  | model (name : String) (polarity : SourceMosPolarity)
      (parameters : List (String × Rat))
deriving Repr, BEq, DecidableEq, Inhabited

def SourceMosfet.hierarchyShape
    (mosfet : SourceMosfet) : HierarchyCardShape :=
  .mosfet mosfet.name mosfet.drain mosfet.gate mosfet.source
    mosfet.bulk mosfet.model

def SourceInstance.hierarchyShape
    (sourceInstance : SourceInstance) : HierarchyCardShape :=
  .instance sourceInstance.name sourceInstance.subcircuit
    sourceInstance.connections.toList

def SourceMosModel.hierarchyShape
    (model : SourceMosModel) : HierarchyCardShape :=
  .model model.name model.polarity
    [("level", model.level), ("vto", model.threshold),
      ("kp", model.transconductance),
      ("lambda", model.channelLengthModulation),
      ("is", model.junctionSaturation)]

structure SubcktHierarchyShape where
  name : String
  ports : List String
  body : List HierarchyCardShape
deriving Repr, BEq, DecidableEq, Inhabited

def SourceSubcircuit.hierarchyShape
    (subcircuit : SourceSubcircuit) : SubcktHierarchyShape :=
  { name := subcircuit.name
    ports := subcircuit.ports.toList
    body :=
      subcircuit.mosfets.toList.map SourceMosfet.hierarchyShape ++
      subcircuit.instances.toList.map SourceInstance.hierarchyShape }

def subcircuitHierarchyShape?
    (source : SourceCircuit) (name : String) :
    Option SubcktHierarchyShape :=
  (findSourceSubcircuit source.subcircuits name).map
    SourceSubcircuit.hierarchyShape

structure HalfAdderImplementationShape where
  andGate : SubcktHierarchyShape
  orGate : SubcktHierarchyShape
  inverter : SubcktHierarchyShape
  halfAdder : SubcktHierarchyShape
  models : List HierarchyCardShape
deriving Repr, BEq, DecidableEq, Inhabited

private def modelShapes (source : SourceCircuit) :
    List HierarchyCardShape :=
  source.models.toList.map SourceMosModel.hierarchyShape

/-- The named half-adder implementation embedded in a larger hierarchy. -/
def embeddedHalfAdderShape?
    (source : SourceCircuit) : Option HalfAdderImplementationShape := do
  return {
    andGate := ← subcircuitHierarchyShape? source "and2"
    orGate := ← subcircuitHierarchyShape? source "or2"
    inverter := ← subcircuitHierarchyShape? source "inv"
    halfAdder := ← subcircuitHierarchyShape? source "half_adder"
    models := modelShapes source }

/-- Treat the top-level instance calls in the standalone half-adder example
as the body of a reusable `half_adder` subcircuit. -/
def standaloneHalfAdderShape?
    (source : SourceCircuit) : Option HalfAdderImplementationShape := do
  return {
    andGate := ← subcircuitHierarchyShape? source "and2"
    orGate := ← subcircuitHierarchyShape? source "or2"
    inverter := ← subcircuitHierarchyShape? source "inv"
    halfAdder := {
      name := "half_adder"
      ports := ["a", "b", "sum", "carry", "vdd"]
      body := source.instances.toList.map SourceInstance.hierarchyShape }
    models := modelShapes source }

def indexedNodeName (nodePrefix : String) (index : Nat) : String :=
  nodePrefix ++ toString index

def rippleCarryName (width index : Nat) : String :=
  if index == 0 then "cin"
  else if index == width then "cout"
  else indexedNodeName "c" index

def stageLocalName (index : Nat) (localName : String) : String :=
  indexedNodeName "xbit" index ++ "." ++ localName

/-- The three half-adder calls that define our full-adder implementation. -/
def expectedFullAdderCalls (width index : Nat) : List HalfAdderCall :=
  let left := indexedNodeName "a" index
  let right := indexedNodeName "b" index
  let carryIn := rippleCarryName width index
  let sum := indexedNodeName "sum" index
  let carryOut := rippleCarryName width (index + 1)
  let propagate := stageLocalName index "propagate"
  let generated := stageLocalName index "generated"
  let propagatedCarry := stageLocalName index "propagated_carry"
  let unused := stageLocalName index "unused"
  let path := indexedNodeName "xbit" index ++ "."
  [
    { name := path ++ "xfirst", left, right,
      sum := propagate, carry := generated, supply := "vdd" },
    { name := path ++ "xsecond", left := propagate, right := carryIn,
      sum, carry := propagatedCarry, supply := "vdd" },
    { name := path ++ "xcarry", left := generated,
      right := propagatedCarry, sum := carryOut,
      carry := unused, supply := "vdd" }
  ]

def expectedRippleCallsFrom
    (width start count : Nat) : List HalfAdderCall :=
  match count with
  | 0 => []
  | count + 1 =>
      expectedFullAdderCalls width start ++
        expectedRippleCallsFrom width (start + 1) count

def expectedRippleCalls (width : Nat) : List HalfAdderCall :=
  expectedRippleCallsFrom width 0 width

def indexedBitsFrom (levels : String → Bool)
    (nodePrefix : String) (start count : Nat) : List Bool :=
  match count with
  | 0 => []
  | count + 1 =>
      levels (indexedNodeName nodePrefix start) ::
        indexedBitsFrom levels nodePrefix (start + 1) count

@[simp] theorem indexedBitsFrom_length (levels : String → Bool)
    (nodePrefix : String) (start count : Nat) :
    (indexedBitsFrom levels nodePrefix start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [indexedBitsFrom, ih]

def HalfAdderCall.Observes (relation : HalfAdderRelation)
    (levels : String → Bool) (call : HalfAdderCall) : Prop :=
  relation (levels call.left) (levels call.right)
    (levels call.sum) (levels call.carry)

def HalfAdderCallsObserve (relation : HalfAdderRelation)
    (levels : String → Bool) (calls : List HalfAdderCall) : Prop :=
  ∀ call ∈ calls, call.Observes relation levels

/-- The literal three-calls-per-stage layout induces the same recursive
relation consumed by the width-parametric arithmetic proof. -/
theorem expectedRippleCallsFrom_observe
    (relation : HalfAdderRelation) (levels : String → Bool)
    (width start count : Nat)
    (hobserve : HalfAdderCallsObserve relation levels
      (expectedRippleCallsFrom width start count)) :
    RippleAdderOf relation
      (indexedBitsFrom levels "a" start count)
      (indexedBitsFrom levels "b" start count)
      (levels (rippleCarryName width start))
      (indexedBitsFrom levels "sum" start count)
      (levels (rippleCarryName width (start + count))) := by
  induction count generalizing start with
  | zero =>
      simp [indexedBitsFrom, RippleAdderOf]
  | succ count ih =>
      let calls := expectedFullAdderCalls width start
      let first := calls[0]!
      let second := calls[1]!
      let third := calls[2]!
      have hfirst : first.Observes relation levels := by
        apply hobserve
        simp [expectedRippleCallsFrom, calls, first,
          expectedFullAdderCalls]
      have hsecond : second.Observes relation levels := by
        apply hobserve
        simp [expectedRippleCallsFrom, calls, second,
          expectedFullAdderCalls]
      have hthird : third.Observes relation levels := by
        apply hobserve
        simp [expectedRippleCallsFrom, calls, third,
          expectedFullAdderCalls]
      have htail : HalfAdderCallsObserve relation levels
          (expectedRippleCallsFrom width (start + 1) count) := by
        intro call hcall
        apply hobserve call
        simp [expectedRippleCallsFrom, hcall]
      have hrest := ih (start + 1) htail
      simp only [indexedBitsFrom, RippleAdderOf]
      refine ⟨levels (rippleCarryName width (start + 1)), ?_, ?_⟩
      · refine ⟨levels (stageLocalName start "propagate"),
          levels (stageLocalName start "generated"),
          levels (stageLocalName start "propagated_carry"),
          levels (stageLocalName start "unused"), ?_, ?_, ?_⟩
        · simpa [HalfAdderCall.Observes, calls, first,
            expectedFullAdderCalls] using hfirst
        · simpa [HalfAdderCall.Observes, calls, second,
            expectedFullAdderCalls] using hsecond
        · simpa [HalfAdderCall.Observes, calls, third,
            expectedFullAdderCalls] using hthird
      · have hend :
            start + (count + 1) = (start + 1) + count := by omega
        simpa [hend] using hrest

theorem expectedRippleCalls_observe
    (relation : HalfAdderRelation) (levels : String → Bool) (width : Nat)
    (hobserve : HalfAdderCallsObserve relation levels
      (expectedRippleCalls width)) :
    RippleAdderOf relation
      (indexedBitsFrom levels "a" 0 width)
      (indexedBitsFrom levels "b" 0 width)
      (levels "cin")
      (indexedBitsFrom levels "sum" 0 width)
      (levels (rippleCarryName width width)) := by
  simpa [expectedRippleCalls, rippleCarryName] using
    expectedRippleCallsFrom_observe relation levels width 0 width hobserve

end LeanModels.Spice
