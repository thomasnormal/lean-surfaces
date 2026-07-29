import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import LeanModels.Circuit.Behavior
import LeanModels.Circuit.Time

/-!
# Absolutely-continuous DAE and backward-Euler capabilities

The continuous relation is the model semantics used for physical transient
claims. A physical trajectory is absolutely continuous coordinatewise and
satisfies its residual almost everywhere. This admits the nonsmooth but
finite-energy trajectories that arise at switching instants without requiring
a classical derivative at every time.

`SmoothBehavesOn` is a stronger, solver-friendly capability used for analytic
witnesses and elementary calculus proofs. It refines `ACBehavesOn` only when
absolute continuity is supplied explicitly. Backward Euler is a separate
numerical relation; it does not define the continuous physics.
-/

namespace LeanModels.Circuit

/-- A trace enters and remains in an absolute error band by a deadline. -/
def SettlesWithin (trace : DenseTrace ℝ) (target tolerance deadline horizon : ℝ) : Prop :=
  0 ≤ tolerance ∧ 0 ≤ deadline ∧ deadline ≤ horizon ∧
  ∀ time, deadline ≤ time → time ≤ horizon →
    |trace time - target| ≤ tolerance

/-- A scalar trace stays inside a closed safety interval for the horizon. -/
def NoOvershoot (trace : DenseTrace ℝ) (lower upper horizon : ℝ) : Prop :=
  ∀ time, 0 ≤ time → time ≤ horizon →
    lower ≤ trace time ∧ trace time ≤ upper

/-- A first-order scalar DAE residual relation
`R(world, time, value, derivative) = 0`. -/
structure ScalarDAE (World : Type) where
  residual : World → ℝ → ℝ → ℝ → Prop

/-- A finite-dimensional state indexed by semantic variables rather than
source strings. -/
abbrev VectorState (Index : Type) := Index → ℝ

/-- A dense-time trajectory of a finite-dimensional semantic state. -/
abbrev VectorTrace (Index : Type) := DenseTrace (VectorState Index)

/-- A vector DAE residual. Algebraic coordinates may ignore their derivative;
the relation therefore covers coupled ODEs and index-one DAEs without
pretending that every state coordinate is dynamic. -/
structure VectorDAE (World Index : Type) where
  residual :
    World → ℝ → VectorState Index → VectorState Index → Prop

/-- The physical vector-DAE denotation on a finite horizon.

Every coordinate is absolutely continuous. At almost every time in the closed
horizon there is one simultaneous derivative vector for all coordinates and
the coupled residual holds for that vector. The single simultaneous witness is
important: separate coordinatewise existential derivatives would not justify a
coupled residual. -/
def VectorDAE.ACBehavesOn (dae : VectorDAE World Index)
    (world : World) (horizon : ℝ) (trace : VectorTrace Index) : Prop :=
  0 ≤ horizon ∧
  (∀ index,
    AbsolutelyContinuousOnInterval
      (fun time => trace time index) 0 horizon) ∧
  ∀ᵐ time ∂MeasureTheory.volume.restrict (Set.uIcc 0 horizon),
    ∃ derivative : VectorState Index,
      (∀ index,
        HasDerivAt (fun t => trace t index) (derivative index) time) ∧
      dae.residual world time (trace time) derivative

/-- A stronger pointwise differentiable view of a vector DAE. This is useful
for closed-form witnesses and local algebra, but is not the physical semantic
root because hybrid and piecewise-smooth traces need not be differentiable at
every time. -/
def VectorDAE.SmoothBehavesOn (dae : VectorDAE World Index)
    (world : World) (horizon : ℝ) (trace : VectorTrace Index) : Prop :=
  0 ≤ horizon ∧
  ∀ time, 0 ≤ time → time ≤ horizon →
    ∃ derivative : VectorState Index,
      (∀ index,
        HasDerivAt (fun t => trace t index) (derivative index) time) ∧
      dae.residual world time (trace time) derivative

/-- A smooth vector solution with certified absolute continuity is a physical
almost-everywhere solution. -/
theorem VectorDAE.acBehavesOn_of_smooth
    {dae : VectorDAE World Index} {world : World} {horizon : ℝ}
    {trace : VectorTrace Index}
    (hcontinuous :
      ∀ index,
        AbsolutelyContinuousOnInterval
          (fun time => trace time index) 0 horizon)
    (hsmooth : dae.SmoothBehavesOn world horizon trace) :
    dae.ACBehavesOn world horizon trace := by
  refine ⟨hsmooth.1, hcontinuous, ?_⟩
  exact MeasureTheory.ae_restrict_of_forall_mem
    measurableSet_uIcc fun time htime => by
      rw [Set.uIcc_of_le hsmooth.1] at htime
      exact hsmooth.2 time htime.1 htime.2

/-- A vector equilibrium is a zero-derivative state. -/
def VectorDAE.Equilibrium (dae : VectorDAE World Index)
    (world : World) (state : VectorState Index) : Prop :=
  dae.residual world 0 state (fun _ => 0)

/-- One implicit backward-Euler step for a vector residual. -/
def VectorDAE.BackwardEulerStep (dae : VectorDAE World Index)
    (world : World) (step time : ℝ)
    (previous next : VectorState Index) : Prop :=
  0 < step ∧
  dae.residual world (time + step) next
    (fun index => (next index - previous index) / step)

/-- A finite vector backward-Euler trajectory. -/
def VectorDAE.BackwardEulerTrajectory (dae : VectorDAE World Index)
    (world : World) (step : ℝ) (steps : Nat)
    (trajectory : Nat → VectorState Index) : Prop :=
  0 < step ∧
  ∀ index, index < steps →
    dae.BackwardEulerStep world step (index * step)
      (trajectory index) (trajectory (index + 1))

/-- The physical scalar-DAE denotation: an absolutely-continuous trace whose
residual holds almost everywhere on the finite horizon. -/
def ScalarDAE.ACBehavesOn (dae : ScalarDAE World)
    (world : World) (horizon : ℝ) (trace : DenseTrace ℝ) : Prop :=
  0 ≤ horizon ∧
  AbsolutelyContinuousOnInterval trace 0 horizon ∧
  ∀ᵐ time ∂MeasureTheory.volume.restrict (Set.uIcc 0 horizon),
    ∃ derivative,
      HasDerivAt trace derivative time ∧
      dae.residual world time (trace time) derivative

/-- Strong pointwise differentiable scalar capability. -/
def ScalarDAE.SmoothBehavesOn (dae : ScalarDAE World)
    (world : World) (horizon : ℝ) (trace : DenseTrace ℝ) : Prop :=
  0 ≤ horizon ∧
  ∀ time, 0 ≤ time → time ≤ horizon →
    ∃ derivative,
      HasDerivAt trace derivative time ∧
      dae.residual world time (trace time) derivative

/-- A smooth scalar solution with certified absolute continuity is a physical
almost-everywhere solution. -/
theorem ScalarDAE.acBehavesOn_of_smooth
    {dae : ScalarDAE World} {world : World} {horizon : ℝ}
    {trace : DenseTrace ℝ}
    (hcontinuous : AbsolutelyContinuousOnInterval trace 0 horizon)
    (hsmooth : dae.SmoothBehavesOn world horizon trace) :
    dae.ACBehavesOn world horizon trace := by
  refine ⟨hsmooth.1, hcontinuous, ?_⟩
  exact MeasureTheory.ae_restrict_of_forall_mem
    measurableSet_uIcc fun time htime => by
      rw [Set.uIcc_of_le hsmooth.1] at htime
      exact hsmooth.2 time htime.1 htime.2

/-- If every residual solution has zero derivative, every physical scalar-DAE
trajectory is constant on its horizon. This turns a device/evolution fact into
an endpoint theorem without adding constancy to the behavior relation. -/
theorem ScalarDAE.constant_on_of_residual_forces_zero
    {dae : ScalarDAE World} {world : World} {horizon : ℝ}
    {trace : DenseTrace ℝ}
    (hbehavior : dae.ACBehavesOn world horizon trace)
    (hzero :
      ∀ time value derivative,
        dae.residual world time value derivative → derivative = 0) :
    ∀ time ∈ Set.Icc 0 horizon, trace time = trace 0 := by
  have hzeroDerivativeRestricted :
      ∀ᵐ time ∂MeasureTheory.volume.restrict (Set.uIcc 0 horizon),
        HasDerivAt trace 0 time := by
    filter_upwards [hbehavior.2.2] with time htime
    obtain ⟨derivative, hderivative, hresidual⟩ := htime
    exact hderivative.congr_deriv (hzero time (trace time) derivative hresidual)
  have hzeroDerivative :
      ∀ᵐ time,
        time ∈ Set.uIcc 0 horizon → HasDerivAt trace 0 time :=
    MeasureTheory.ae_imp_of_ae_restrict hzeroDerivativeRestricted
  obtain ⟨constant, hconstant⟩ :=
    hbehavior.2.1.const_of_ae_hasDerivAt_zero hzeroDerivative
  intro time htime
  have htime' : time ∈ Set.uIcc 0 horizon := by
    simpa [Set.uIcc_of_le hbehavior.1] using htime
  have hzero' : (0 : ℝ) ∈ Set.uIcc 0 horizon := by
    simp [hbehavior.1]
  exact (hconstant time htime').trans (hconstant 0 hzero').symm

/-- A DC equilibrium is a zero-derivative point of the transient residual. -/
def ScalarDAE.Equilibrium (dae : ScalarDAE World)
    (world : World) (value : ℝ) : Prop :=
  dae.residual world 0 value 0

/-- One implicit backward-Euler step for the same residual. -/
def ScalarDAE.BackwardEulerStep (dae : ScalarDAE World)
    (world : World) (step time previous next : ℝ) : Prop :=
  0 < step ∧
  dae.residual world (time + step) next ((next - previous) / step)

/-- A finite backward-Euler trajectory. -/
def ScalarDAE.BackwardEulerTrajectory (dae : ScalarDAE World)
    (world : World) (step : ℝ) (steps : Nat)
    (trajectory : Nat → ℝ) : Prop :=
  0 < step ∧
  ∀ index, index < steps →
    dae.BackwardEulerStep world step (index * step)
      (trajectory index) (trajectory (index + 1))

end LeanModels.Circuit
