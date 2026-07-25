import Mathlib.Tactic
import LeanModels.Circuit.DC

/-!
# Exact compositional port contracts

Contracts describe boundary behavior, not implementation syntax. A source
subcircuit can prove that its physical port relation has a contract; composite
proofs then use only that relation and never reopen internal nodes.
-/

namespace LeanModels.Circuit

abbrev Vec (size : Nat) (Value : Type := Rat) := Fin size → Value

abbrev Matrix (rows columns : Nat) (Value : Type := Rat) :=
  Fin rows → Fin columns → Value

def dot {size : Nat} {Value : Type} [Mul Value] [Add Value] [OfNat Value 0]
    (left right : Vec size Value) : Value :=
  (List.ofFn fun index : Fin size => left index * right index).foldl
    (fun total value => total + value) 0

def matVec {rows columns : Nat} {Value : Type}
    [Mul Value] [Add Value] [OfNat Value 0]
    (matrix : Matrix rows columns Value) (vector : Vec columns Value) :
    Vec rows Value :=
  fun row => dot (matrix row) vector

/-- Exact affine boundary relation `I = Y V + J`. -/
structure PortContract (size : Nat) (Value : Type := Rat) where
  Y : Matrix size size Value
  J : Vec size Value

def PortContract.apply {Value : Type}
    [Mul Value] [Add Value] [OfNat Value 0]
    (contract : PortContract size Value) (voltage : Vec size Value) :
    Vec size Value :=
  fun index => matVec contract.Y voltage index + contract.J index

abbrev PortRelation (size : Nat) (Value : Type := Rat) :=
  Vec size Value → Vec size Value → Prop

/-- Both directions are required: `sound` supports universal reasoning and
`realize` prevents composition from inventing impossible boundary points. -/
structure HasExactContract (behavior : PortRelation size Value)
    [Mul Value] [Add Value] [OfNat Value 0]
    (contract : PortContract size Value) : Prop where
  sound : ∀ voltage current,
    behavior voltage current → current = contract.apply voltage
  realize : ∀ voltage current,
    current = contract.apply voltage → behavior voltage current

theorem hasExactContract_iff {Value : Type}
    [Mul Value] [Add Value] [OfNat Value 0]
    (behavior : PortRelation size Value)
    (contract : PortContract size Value) :
    HasExactContract behavior contract ↔
      ∀ voltage current,
        behavior voltage current ↔ current = contract.apply voltage := by
  constructor
  · intro h voltage current
    exact ⟨h.sound voltage current, h.realize voltage current⟩
  · intro h
    exact {
      sound := fun voltage current => (h voltage current).mp
      realize := fun voltage current => (h voltage current).mpr }

private abbrev p0 : Fin 2 := ⟨0, by decide⟩
private abbrev p1 : Fin 2 := ⟨1, by decide⟩

def cascadeLeftVoltage (external : Vec 2) (shared : Rat) : Vec 2
  | index => if index = p0 then external p0 else shared

def cascadeRightVoltage (external : Vec 2) (shared : Rat) : Vec 2
  | index => if index = p0 then shared else external p1

/-- Relational wiring of two two-ports. Port currents are positive into each
block, hence the hidden connection sums to zero. -/
def CascadeRelation (left right : PortRelation 2) :
    PortRelation 2 :=
  fun voltage current =>
    ∃ shared : Rat, ∃ leftCurrent rightCurrent : Vec 2,
      left (cascadeLeftVoltage voltage shared) leftCurrent ∧
      right (cascadeRightVoltage voltage shared) rightCurrent ∧
      leftCurrent p1 + rightCurrent p0 = 0 ∧
      current p0 = leftCurrent p0 ∧
      current p1 = rightCurrent p1

def cascadeDenominator (left right : PortContract 2) : Rat :=
  left.Y p1 p1 + right.Y p0 p0

/-- Schur-complement elimination of the hidden cascade node. -/
def cascade (left right : PortContract 2) : PortContract 2 :=
  let denominator := cascadeDenominator left right
  { Y := fun row column =>
      if row = p0 then
        if column = p0 then
          left.Y p0 p0 - left.Y p0 p1 * left.Y p1 p0 / denominator
        else -(left.Y p0 p1 * right.Y p0 p1 / denominator)
      else if column = p0 then
        -(right.Y p1 p0 * left.Y p1 p0 / denominator)
      else
        right.Y p1 p1 -
          right.Y p1 p0 * right.Y p0 p1 / denominator
    J := fun row =>
      if row = p0 then
        left.J p0 -
          left.Y p0 p1 * (left.J p1 + right.J p0) / denominator
      else
        right.J p1 -
          right.Y p1 p0 * (left.J p1 + right.J p0) / denominator }

def cascadeSharedVoltage (left right : PortContract 2)
    (voltage : Vec 2) : Rat :=
  -(left.Y p1 p0 * voltage p0 + right.Y p0 p1 * voltage p1 +
      left.J p1 + right.J p0) /
    cascadeDenominator left right

private theorem vec2_ext {left right : Vec 2}
    (h0 : left p0 = right p0) (h1 : left p1 = right p1) :
    left = right := by
  funext index
  have hindex : index.val = 0 ∨ index.val = 1 := by omega
  rcases hindex with hindex | hindex
  · have : index = p0 := by apply Fin.ext; exact hindex
    subst index
    exact h0
  · have : index = p1 := by apply Fin.ext; exact hindex
    subst index
    exact h1

private theorem cascade_apply_p0 (left right : PortContract 2)
    (voltage : Vec 2) :
    (cascade left right).apply voltage p0 =
      left.Y p0 p0 * voltage p0 +
        left.Y p0 p1 * cascadeSharedVoltage left right voltage +
        left.J p0 := by
  simp [PortContract.apply, matVec, dot, cascade, cascadeSharedVoltage,
    cascadeDenominator]
  grind

private theorem cascade_apply_p1 (left right : PortContract 2)
    (voltage : Vec 2) :
    (cascade left right).apply voltage p1 =
      right.Y p1 p0 * cascadeSharedVoltage left right voltage +
        right.Y p1 p1 * voltage p1 + right.J p1 := by
  simp [PortContract.apply, matVec, dot, cascade, cascadeSharedVoltage,
    cascadeDenominator]
  grind

private theorem cascade_shared_kcl (left right : PortContract 2)
    (voltage : Vec 2) (hnonzero : cascadeDenominator left right ≠ 0) :
    left.Y p1 p0 * voltage p0 +
        left.Y p1 p1 * cascadeSharedVoltage left right voltage + left.J p1 +
      (right.Y p0 p0 * cascadeSharedVoltage left right voltage +
        right.Y p0 p1 * voltage p1 + right.J p0) = 0 := by
  simp [cascadeSharedVoltage, cascadeDenominator]
  unfold cascadeDenominator at hnonzero
  grind

/-- Exact composition theorem. The reverse direction uses both component
realization fields, so non-vacuity is preserved by construction. -/
theorem compose_contracts
    {leftBehavior rightBehavior : PortRelation 2}
    {leftContract rightContract : PortContract 2}
    (hleft : HasExactContract leftBehavior leftContract)
    (hright : HasExactContract rightBehavior rightContract)
    (hnonzero : cascadeDenominator leftContract rightContract ≠ 0) :
    HasExactContract (CascadeRelation leftBehavior rightBehavior)
      (cascade leftContract rightContract) := by
  constructor
  · intro voltage current behavior
    rcases behavior with
      ⟨shared, leftCurrent, rightCurrent, hleftBehavior,
        hrightBehavior, hshared, hexternal0, hexternal1⟩
    have hl := hleft.sound _ _ hleftBehavior
    have hr := hright.sound _ _ hrightBehavior
    have hsharedValue :
        shared = cascadeSharedVoltage leftContract rightContract voltage := by
      have hl1 := congrFun hl p1
      have hr0 := congrFun hr p0
      simp [PortContract.apply, matVec, dot, cascadeLeftVoltage,
        cascadeRightVoltage] at hl1 hr0
      unfold cascadeSharedVoltage cascadeDenominator
      unfold cascadeDenominator at hnonzero
      grind
    apply vec2_ext
    · rw [hexternal0, congrFun hl p0, cascade_apply_p0]
      simp [PortContract.apply, matVec, dot, cascadeLeftVoltage,
        hsharedValue]
    · rw [hexternal1, congrFun hr p1, cascade_apply_p1]
      simp [PortContract.apply, matVec, dot, cascadeRightVoltage,
        hsharedValue]
  · intro voltage current hcurrent
    let shared := cascadeSharedVoltage leftContract rightContract voltage
    let leftVoltage := cascadeLeftVoltage voltage shared
    let rightVoltage := cascadeRightVoltage voltage shared
    let leftCurrent := leftContract.apply leftVoltage
    let rightCurrent := rightContract.apply rightVoltage
    refine ⟨shared, leftCurrent, rightCurrent,
      hleft.realize leftVoltage leftCurrent rfl,
      hright.realize rightVoltage rightCurrent rfl, ?_, ?_, ?_⟩
    · have hkcl :=
        cascade_shared_kcl leftContract rightContract voltage hnonzero
      simpa [leftCurrent, rightCurrent, leftVoltage, rightVoltage,
        PortContract.apply, matVec, dot, cascadeLeftVoltage,
        cascadeRightVoltage, shared, Rat.zero_add] using hkcl
    · rw [hcurrent, cascade_apply_p0]
      simp [leftCurrent, leftVoltage, PortContract.apply, matVec, dot,
        cascadeLeftVoltage, shared]
    · rw [hcurrent, cascade_apply_p1]
      simp [rightCurrent, rightVoltage, PortContract.apply, matVec, dot,
        cascadeRightVoltage, shared]

/-! ## Error-bounded oriented views

Conservative components remain acausal at the semantic root. After selecting
an excitation/observation partition, a reduced block may expose this scalar
affine view. Unlike `HasExactContract`, its envelope is only an
over-approximation; realizability is therefore carried separately and is
preserved by serial composition.
-/

abbrev ScalarPortRelation := ℝ → ℝ → Prop

structure ScalarErrorContract where
  gain : ℝ
  bias : ℝ
  error : ℝ
  error_nonnegative : 0 ≤ error

def ScalarErrorContract.apply
    (contract : ScalarErrorContract) (input : ℝ) : ℝ :=
  contract.gain * input + contract.bias

def ScalarErrorContract.Admits
    (contract : ScalarErrorContract) (input output : ℝ) : Prop :=
  |output - contract.apply input| ≤ contract.error

/-- Universal error coverage plus input-relative realizability. The
realizability field prevents a reduced contract from certifying an empty
implementation relation. -/
structure HasErrorBoundedContract
    (behavior : ScalarPortRelation)
    (contract : ScalarErrorContract) : Prop where
  sound : ∀ input output,
    behavior input output → contract.Admits input output
  realizable : ∀ input, ∃ output, behavior input output

def SerialScalarRelation
    (left right : ScalarPortRelation) : ScalarPortRelation :=
  fun input output =>
    ∃ shared, left input shared ∧ right shared output

/-- Serial error propagation. The upstream error is amplified by the
absolute downstream gain. -/
def composeErrorContracts
    (left right : ScalarErrorContract) : ScalarErrorContract :=
  {
    gain := right.gain * left.gain
    bias := right.gain * left.bias + right.bias
    error := |right.gain| * left.error + right.error
    error_nonnegative :=
      add_nonneg
        (mul_nonneg (abs_nonneg _) left.error_nonnegative)
        right.error_nonnegative }

theorem compose_error_bounded_contracts
    {leftBehavior rightBehavior : ScalarPortRelation}
    {leftContract rightContract : ScalarErrorContract}
    (hleft : HasErrorBoundedContract leftBehavior leftContract)
    (hright : HasErrorBoundedContract rightBehavior rightContract) :
    HasErrorBoundedContract
      (SerialScalarRelation leftBehavior rightBehavior)
      (composeErrorContracts leftContract rightContract) := by
  constructor
  · intro input output behavior
    rcases behavior with ⟨shared, hleftBehavior, hrightBehavior⟩
    have hleftError := hleft.sound input shared hleftBehavior
    have hrightError := hright.sound shared output hrightBehavior
    have hdecompose :
        output - (composeErrorContracts leftContract rightContract).apply input =
          (output - rightContract.apply shared) +
            rightContract.gain *
              (shared - leftContract.apply input) := by
      simp [ScalarErrorContract.apply, composeErrorContracts]
      ring
    have hscaled :
        |rightContract.gain *
            (shared - leftContract.apply input)| ≤
          |rightContract.gain| * leftContract.error := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hleftError (abs_nonneg _)
    rw [ScalarErrorContract.Admits, hdecompose]
    calc
      |(output - rightContract.apply shared) +
          rightContract.gain *
            (shared - leftContract.apply input)| ≤
        |output - rightContract.apply shared| +
          |rightContract.gain *
            (shared - leftContract.apply input)| := abs_add_le _ _
      _ ≤ rightContract.error +
          |rightContract.gain| * leftContract.error :=
        add_le_add hrightError hscaled
      _ = (composeErrorContracts leftContract rightContract).error := by
        simp [composeErrorContracts, add_comm]
  · intro input
    rcases hleft.realizable input with ⟨shared, hshared⟩
    rcases hright.realizable shared with ⟨output, houtput⟩
    exact ⟨output, shared, hshared, houtput⟩

def ExactScalarRelation (gain bias : ℝ) : ScalarPortRelation :=
  fun input output => output = gain * input + bias

def exactScalarErrorContract (gain bias : ℝ) : ScalarErrorContract :=
  {
    gain
    bias
    error := 0
    error_nonnegative := le_rfl }

theorem exact_scalar_has_error_contract (gain bias : ℝ) :
    HasErrorBoundedContract
      (ExactScalarRelation gain bias)
      (exactScalarErrorContract gain bias) := by
  constructor
  · intro input output houtput
    change output = gain * input + bias at houtput
    rw [ScalarErrorContract.Admits, ScalarErrorContract.apply]
    simp [exactScalarErrorContract, houtput]
  · intro input
    exact ⟨gain * input + bias, rfl⟩

end LeanModels.Circuit
