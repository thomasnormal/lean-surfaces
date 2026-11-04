import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Semiconductor device-model levels

These definitions state the equation boundaries above compact SPICE models.
They deliberately contain no existence, uniqueness, discretization, or solver
claims. Circuit proofs currently target MOS1; these specifications record what
would have to be refined to justify MOS1 from a more microscopic model.
-/

namespace LeanModels.Spice

/-- An exact vertical refinement. Constructing this structure requires a proof
that every lower-level state satisfying its equations maps to a state
satisfying the upper-level specification. Merely defining both specifications
does not construct a refinement. -/
structure ExactRefinement {LowerState UpperState : Type}
    (lowerSpec : LowerState → Prop) (upperSpec : UpperState → Prop) where
  project : LowerState → UpperState
  sound : ∀ state, lowerSpec state → upperSpec (project state)

def ExactRefinement.trans
    {First Second Third : Type}
    {firstSpec : First → Prop} {secondSpec : Second → Prop}
    {thirdSpec : Third → Prop}
    (lower : ExactRefinement firstSpec secondSpec)
    (upper : ExactRefinement secondSpec thirdSpec) :
    ExactRefinement firstSpec thirdSpec :=
  { project := upper.project ∘ lower.project
    sound := fun state hstate => upper.sound _ (lower.sound state hstate) }

/-- A refinement carrying an observation-error bound. This is the appropriate
shape for compact models such as MOS1, which approximate rather than exactly
equal a transport model. -/
structure BoundedObservableRefinement
    {LowerState UpperState Observation : Type}
    (lowerSpec : LowerState → Prop) (upperSpec : UpperState → Prop)
    (distance : Observation → Observation → ℝ) where
  project : LowerState → UpperState
  lowerObservation : LowerState → Observation
  upperObservation : UpperState → Observation
  error : ℝ
  error_nonnegative : 0 ≤ error
  upper_sound : ∀ state, lowerSpec state → upperSpec (project state)
  observation_bound : ∀ state, lowerSpec state →
    distance (lowerObservation state) (upperObservation (project state)) ≤ error

/-- Material and geometry data for a one-dimensional semiconductor device. -/
structure DriftDiffusionModel where
  length : ℝ
  charge : ℝ
  permittivity : ℝ
  electronMobility : ℝ
  holeMobility : ℝ
  electronDiffusivity : ℝ
  holeDiffusivity : ℝ
  doping : ℝ → ℝ
  recombination : ℝ → ℝ → ℝ
  leftPotential : ℝ
  rightPotential : ℝ
  leftElectrons : ℝ
  rightElectrons : ℝ
  leftHoles : ℝ
  rightHoles : ℝ

/-- Electrostatic potential, carrier densities, and current densities. -/
structure DriftDiffusionState where
  potential : ℝ → ℝ
  electrons : ℝ → ℝ
  holes : ℝ → ℝ
  electronCurrent : ℝ → ℝ
  holeCurrent : ℝ → ℝ

/-- Steady one-dimensional Poisson and carrier-continuity equations with
drift-diffusion constitutive current laws and Dirichlet contact data. -/
def DriftDiffusionSpec
    (model : DriftDiffusionModel) (state : DriftDiffusionState) : Prop :=
  0 < model.length ∧
  0 < model.charge ∧
  0 < model.permittivity ∧
  (∀ x, 0 < x → x < model.length →
    deriv (deriv state.potential) x =
      -(model.charge / model.permittivity) *
        (state.holes x - state.electrons x + model.doping x)) ∧
  (∀ x, 0 < x → x < model.length →
    state.electronCurrent x =
      model.charge *
        (model.electronMobility * state.electrons x *
            (-deriv state.potential x) +
          model.electronDiffusivity * deriv state.electrons x)) ∧
  (∀ x, 0 < x → x < model.length →
    state.holeCurrent x =
      model.charge *
        (model.holeMobility * state.holes x *
            (-deriv state.potential x) -
          model.holeDiffusivity * deriv state.holes x)) ∧
  (∀ x, 0 < x → x < model.length →
    deriv state.electronCurrent x =
      model.charge * model.recombination (state.electrons x) (state.holes x)) ∧
  (∀ x, 0 < x → x < model.length →
    deriv state.holeCurrent x =
      -model.charge * model.recombination
        (state.electrons x) (state.holes x)) ∧
  state.potential 0 = model.leftPotential ∧
  state.potential model.length = model.rightPotential ∧
  state.electrons 0 = model.leftElectrons ∧
  state.electrons model.length = model.rightElectrons ∧
  state.holes 0 = model.leftHoles ∧
  state.holes model.length = model.rightHoles

/-- One-dimensional semiclassical phase-space transport data. The collision
operator is left explicit because choosing it is itself a physical model. -/
structure BoltzmannTransportModel where
  length : ℝ
  velocity : ℝ → ℝ
  force : ℝ → ℝ
  collision : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  leftDistribution : ℝ → ℝ
  rightDistribution : ℝ → ℝ

/-- Steady Boltzmann transport equation with inflow contact distributions. -/
def BoltzmannTransportSpec
    (model : BoltzmannTransportModel)
    (distribution : ℝ → ℝ → ℝ) : Prop :=
  0 < model.length ∧
  (∀ x momentum, 0 < x → x < model.length →
    model.velocity momentum * deriv (fun y => distribution y momentum) x +
      model.force x * deriv (fun p => distribution x p) momentum =
        model.collision distribution x momentum) ∧
  (∀ momentum, 0 < model.velocity momentum →
    distribution 0 momentum = model.leftDistribution momentum) ∧
  (∀ momentum, model.velocity momentum < 0 →
    distribution model.length momentum = model.rightDistribution momentum)

/-- Finite-basis nonequilibrium Green-function data. This is an equation
interface for quantum transport, not a claim that a chosen basis is adequate. -/
structure QuantumTransportModel (orbital : Type)
    [Fintype orbital] [DecidableEq orbital] where
  energy : ℝ
  broadening : ℝ
  hamiltonian : Matrix orbital orbital ℂ
  retardedSelfEnergy : Matrix orbital orbital ℂ
  lesserSelfEnergy : Matrix orbital orbital ℂ

/-- Retarded and lesser Green functions satisfying Dyson and Keldysh
equations in a finite orbital basis. -/
structure QuantumTransportState (orbital : Type)
    [Fintype orbital] [DecidableEq orbital] where
  retarded : Matrix orbital orbital ℂ
  lesser : Matrix orbital orbital ℂ

def QuantumTransportSpec {orbital : Type}
    [Fintype orbital] [DecidableEq orbital]
    (model : QuantumTransportModel orbital)
    (state : QuantumTransportState orbital) : Prop :=
  (((model.energy : ℂ) + model.broadening * Complex.I) • (1 : Matrix orbital orbital ℂ) -
      model.hamiltonian - model.retardedSelfEnergy) * state.retarded = 1 ∧
  state.lesser =
    state.retarded * model.lesserSelfEnergy *
      Matrix.conjTranspose state.retarded

end LeanModels.Spice
