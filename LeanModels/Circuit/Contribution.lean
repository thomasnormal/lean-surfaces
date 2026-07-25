import Mathlib.Data.Real.Basic
import LeanModels.Circuit.Behavior

/-!
# Relational analog contribution models

This is the semantic target shared by native Lean components and the minimal
Verilog-A frontend. A contribution is not an imperative assignment. All
contributions to the same branch quantity are summed, and the resulting
equation is imposed relationally.

The first slice is conservative electrical behavior. Port potentials and
oriented branch flows are distinct quantities. Network KCL remains part of
interconnection semantics rather than a component contribution.
-/

namespace LeanModels.Circuit

structure PortId where
  index : Nat
deriving Repr, BEq, DecidableEq, Inhabited

structure ParameterId where
  index : Nat
deriving Repr, BEq, DecidableEq, Inhabited

/-- An oriented conservative electrical branch. Positive flow is from
`positive` to `negative`. -/
structure ElectricalBranch where
  positive : PortId
  negative : PortId
deriving Repr, BEq, DecidableEq, Inhabited

/-- The supported expression language after source names have been resolved.
`potentialRate` is the semantic target of the minimal `ddt(V(...))` subset.
More general differentiation is intentionally rejected by the frontend until
its chain-rule semantics is implemented. -/
inductive ContributionExpr where
  | literal (value : Rat)
  | parameter (id : ParameterId)
  | potential (branch : ElectricalBranch)
  | flow (branch : ElectricalBranch)
  | potentialRate (branch : ElectricalBranch)
  | neg (value : ContributionExpr)
  | add (left right : ContributionExpr)
  | sub (left right : ContributionExpr)
  | mul (left right : ContributionExpr)
  | div (left right : ContributionExpr)
deriving Repr, BEq, DecidableEq, Inhabited

inductive ContributionTarget where
  | potential (branch : ElectricalBranch)
  | flow (branch : ElectricalBranch)
deriving Repr, BEq, DecidableEq, Inhabited

structure Contribution where
  target : ContributionTarget
  expression : ContributionExpr
deriving Repr, BEq, DecidableEq, Inhabited

/-- A typed, source-independent contribution model. Names are retained only
for source diagnostics; semantic expressions use numeric IDs. -/
structure ContributionModel where
  name : String
  portNames : Array String
  parameterNames : Array String
  parameterDefaults : Array Rat
  contributions : Array Contribution
deriving Repr, BEq, Inhabited

/-- One instantaneous interpretation of a contribution model. Potential
derivatives are explicit because transient DAE assembly supplies them.
Parameters are fixed by the run/fabricated instance rather than selected by
the model at each evaluation point. -/
structure AnalogPoint where
  potential : PortId → ℝ
  potentialRate : PortId → ℝ
  flow : ElectricalBranch → ℝ
  parameter : ParameterId → ℝ

def AnalogPoint.branchPotential (point : AnalogPoint)
    (branch : ElectricalBranch) : ℝ :=
  point.potential branch.positive - point.potential branch.negative

def AnalogPoint.branchPotentialRate (point : AnalogPoint)
    (branch : ElectricalBranch) : ℝ :=
  point.potentialRate branch.positive -
    point.potentialRate branch.negative

noncomputable def ContributionExpr.evaluate
    (point : AnalogPoint) : ContributionExpr → ℝ
  | .literal value => value
  | .parameter id => point.parameter id
  | .potential branch => point.branchPotential branch
  | .flow branch => point.flow branch
  | .potentialRate branch => point.branchPotentialRate branch
  | .neg value => -value.evaluate point
  | .add left right => left.evaluate point + right.evaluate point
  | .sub left right => left.evaluate point - right.evaluate point
  | .mul left right => left.evaluate point * right.evaluate point
  | .div left right => left.evaluate point / right.evaluate point

noncomputable def ContributionTarget.value
    (point : AnalogPoint) : ContributionTarget → ℝ
  | .potential branch => point.branchPotential branch
  | .flow branch => point.flow branch

def ElectricalBranch.validFor (portCount : Nat)
    (branch : ElectricalBranch) : Prop :=
  branch.positive.index < portCount ∧
  branch.negative.index < portCount

def ContributionExpr.validFor (portCount parameterCount : Nat) :
    ContributionExpr → Prop
  | .literal _ => True
  | .parameter id => id.index < parameterCount
  | .potential branch
  | .flow branch
  | .potentialRate branch => branch.validFor portCount
  | .neg value => value.validFor portCount parameterCount
  | .add left right
  | .sub left right
  | .mul left right
  | .div left right =>
      left.validFor portCount parameterCount ∧
      right.validFor portCount parameterCount

def ContributionTarget.validFor (portCount : Nat) :
    ContributionTarget → Prop
  | .potential branch
  | .flow branch => branch.validFor portCount

def ContributionModel.Valid (model : ContributionModel) : Prop :=
  model.parameterNames.size = model.parameterDefaults.size ∧
  (∀ contribution ∈ model.contributions,
    contribution.target.validFor model.portNames.size ∧
    contribution.expression.validFor model.portNames.size
      model.parameterNames.size)

noncomputable def ContributionModel.sumFor
    (model : ContributionModel) (point : AnalogPoint)
    (target : ContributionTarget) : ℝ :=
  model.contributions.foldl
    (fun total contribution =>
      if contribution.target == target then
        total + contribution.expression.evaluate point
      else total)
    0

/-- Additive relational contribution semantics. Repeating the equation for
each source contribution is harmless and avoids manufacturing a separate
finite target table; duplicate targets all impose the same summed equation.
-/
noncomputable def ContributionModel.Satisfies
    (model : ContributionModel) (point : AnalogPoint) : Prop :=
  model.Valid ∧
  ∀ contribution ∈ model.contributions,
    contribution.target.value point =
      model.sumFor point contribution.target

noncomputable def ContributionModel.behavior
    (model : ContributionModel) :
    Behavior Unit AnalogPoint Unit :=
  fun _world point _internal => model.Satisfies point

/-- Fix source parameter defaults for a point while preserving all electrical
quantities supplied by the surrounding network. -/
noncomputable def ContributionModel.usesDefaults
    (model : ContributionModel) (point : AnalogPoint) : Prop :=
  ∀ parameter,
    parameter.index < model.parameterDefaults.size →
      point.parameter parameter =
        model.parameterDefaults[parameter.index]!

end LeanModels.Circuit
