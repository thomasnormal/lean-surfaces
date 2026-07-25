import Mathlib.Tactic
import LeanModels.Circuit.Behavior

/-!
# Operating-point linearization and exact AC semantics

Physical residuals and their real-valued linearizations are kept separate
from the exact Gaussian-rational procedure used for rational-frequency linear
circuits. An `ExactLinearizationAt` certificate connects the two.
-/

namespace LeanModels.Circuit

/-- Exact complex numbers with rational real and imaginary parts. -/
structure GaussianRat where
  re : Rat
  im : Rat
deriving Repr, BEq, DecidableEq, Inhabited

namespace GaussianRat

@[ext] theorem ext {left right : GaussianRat}
    (hre : left.re = right.re) (him : left.im = right.im) :
    left = right := by
  cases left
  cases right
  simp_all

instance : Zero GaussianRat := ⟨⟨0, 0⟩⟩
instance : One GaussianRat := ⟨⟨1, 0⟩⟩
instance : Add GaussianRat :=
  ⟨fun left right => ⟨left.re + right.re, left.im + right.im⟩⟩
instance : Neg GaussianRat :=
  ⟨fun value => ⟨-value.re, -value.im⟩⟩
instance : Sub GaussianRat := ⟨fun left right => left + -right⟩
instance : Mul GaussianRat :=
  ⟨fun left right =>
    ⟨left.re * right.re - left.im * right.im,
      left.re * right.im + left.im * right.re⟩⟩

def ofRat (value : Rat) : GaussianRat := ⟨value, 0⟩
def j : GaussianRat := ⟨0, 1⟩
def conj (value : GaussianRat) : GaussianRat := ⟨value.re, -value.im⟩
def normSq (value : GaussianRat) : Rat :=
  value.re ^ 2 + value.im ^ 2

@[simp] theorem zero_re : (0 : GaussianRat).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianRat).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussianRat).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussianRat).im = 0 := rfl
@[simp] theorem add_re (left right : GaussianRat) :
    (left + right).re = left.re + right.re := rfl
@[simp] theorem add_im (left right : GaussianRat) :
    (left + right).im = left.im + right.im := rfl
@[simp] theorem neg_re (value : GaussianRat) :
    (-value).re = -value.re := rfl
@[simp] theorem neg_im (value : GaussianRat) :
    (-value).im = -value.im := rfl
@[simp] theorem mul_re (left right : GaussianRat) :
    (left * right).re =
      left.re * right.re - left.im * right.im := rfl
@[simp] theorem mul_im (left right : GaussianRat) :
    (left * right).im =
      left.re * right.im + left.im * right.re := rfl
@[simp] theorem ofRat_re (value : Rat) : (ofRat value).re = value := rfl
@[simp] theorem ofRat_im (value : Rat) : (ofRat value).im = 0 := rfl

end GaussianRat

/-- A scalar physical residual with one driven input. -/
structure DrivenScalarDAE (Parameter : Type) where
  residual :
    Parameter → ℝ → ℝ → ℝ → ℝ → Prop

/-- `d * output' + a * output + b * input = 0`. -/
structure ScalarLinearResidual (Scalar : Type) where
  derivativeCoefficient : Scalar
  valueCoefficient : Scalar
  inputCoefficient : Scalar
deriving Repr, BEq, DecidableEq, Inhabited

noncomputable def ScalarLinearResidual.realResidual
    (linear : ScalarLinearResidual ℝ)
    (input output derivative : ℝ) : Prop :=
  linear.derivativeCoefficient * derivative +
    linear.valueCoefficient * output +
      linear.inputCoefficient * input = 0

/-- Exact affine perturbation equality at one operating point. This is
stronger than a first-order approximation and is appropriate for linear RLC
components. Nonlinear models use a derivative/error-bounded certificate. -/
structure ExactLinearizationAt
    (dae : DrivenScalarDAE Parameter)
    (parameter : Parameter) (input₀ output₀ : ℝ)
    (linear : ScalarLinearResidual ℝ) : Prop where
  equilibrium : dae.residual parameter 0 input₀ output₀ 0
  perturbation :
    ∀ time inputDelta outputDelta outputDerivative,
      dae.residual parameter time
          (input₀ + inputDelta) (output₀ + outputDelta) outputDerivative ↔
        linear.realResidual inputDelta outputDelta outputDerivative

structure ScalarACScenario where
  angularFrequency : Rat
  input : GaussianRat
deriving Repr, BEq, DecidableEq, Inhabited

structure ScalarACBoundary where
  output : GaussianRat
deriving Repr, BEq, DecidableEq, Inhabited

def ScalarLinearResidual.acCoefficient
    (linear : ScalarLinearResidual Rat) (angularFrequency : Rat) :
    GaussianRat :=
  GaussianRat.ofRat linear.valueCoefficient +
    (GaussianRat.j * GaussianRat.ofRat angularFrequency) *
      GaussianRat.ofRat linear.derivativeCoefficient

def ScalarLinearResidual.acResidual
    (linear : ScalarLinearResidual Rat) (scenario : ScalarACScenario)
    (output : GaussianRat) : Prop :=
  linear.acCoefficient scenario.angularFrequency * output +
    GaussianRat.ofRat linear.inputCoefficient * scenario.input = 0

def ScalarACBehavior (linear : ScalarLinearResidual Rat) :
    Behavior ScalarACScenario ScalarACBoundary Unit :=
  fun scenario boundary _ =>
      linear.acResidual scenario boundary.output

/-! ## Certified first-order transfer and stability views -/

/-- `numerator / (denominatorConstant + s * derivativeCoefficient)`.
The transfer is a structured view; its residual remains the semantic
relation used for composition and proof. -/
structure FirstOrderTransfer (Scalar : Type) where
  derivativeCoefficient : Scalar
  denominatorConstant : Scalar
  numerator : Scalar
deriving Repr, BEq, DecidableEq, Inhabited

def FirstOrderTransfer.residual
    (transfer : FirstOrderTransfer Rat) : ScalarLinearResidual Rat :=
  { derivativeCoefficient := transfer.derivativeCoefficient
    valueCoefficient := transfer.denominatorConstant
    inputCoefficient := -transfer.numerator }

/-- Exactness certificate connecting solver-friendly transfer metadata to
the denotational small-signal residual. -/
def HasExactFirstOrderTransfer
    (linear : ScalarLinearResidual Rat)
    (transfer : FirstOrderTransfer Rat) : Prop :=
  linear = transfer.residual

def FirstOrderTransfer.denominatorAt
    (transfer : FirstOrderTransfer Rat) (angularFrequency : Rat) :
    GaussianRat :=
  GaussianRat.ofRat transfer.denominatorConstant +
    (GaussianRat.j * GaussianRat.ofRat angularFrequency) *
      GaussianRat.ofRat transfer.derivativeCoefficient

/-- First-order Routh-Hurwitz certificate. For `d*s + a`, positive `d` and
`a` put the sole pole strictly in the open left half-plane. -/
def FirstOrderStable (transfer : FirstOrderTransfer Rat) : Prop :=
  0 < transfer.derivativeCoefficient ∧
    0 < transfer.denominatorConstant

def FirstOrderTransfer.pole
    (transfer : FirstOrderTransfer Rat) : Rat :=
  -transfer.denominatorConstant / transfer.derivativeCoefficient

theorem FirstOrderStable.pole_negative
    {transfer : FirstOrderTransfer Rat}
    (hstable : FirstOrderStable transfer) :
    transfer.pole < 0 := by
  unfold FirstOrderTransfer.pole
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hstable.2) hstable.1

theorem FirstOrderTransfer.acCoefficient_eq_denominatorAt
    (transfer : FirstOrderTransfer Rat) (angularFrequency : Rat) :
    transfer.residual.acCoefficient angularFrequency =
      transfer.denominatorAt angularFrequency := rfl

/-- Interpret exact rational linear coefficients in the real physical
linearization semantics. -/
noncomputable def ScalarLinearResidual.toReal
    (linear : ScalarLinearResidual Rat) : ScalarLinearResidual ℝ :=
  { derivativeCoefficient := linear.derivativeCoefficient
    valueCoefficient := linear.valueCoefficient
    inputCoefficient := linear.inputCoefficient }

end LeanModels.Circuit
