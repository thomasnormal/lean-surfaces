import LeanModels.Spice.Contract

/-!
# Composing exact linear port contracts

The physical `HasContract` predicate is tied to a leaf `Subckt`.  This module
therefore states wiring independently as a relation on the blocks' projected
`PortBehavior`s.  The cascade theorem below is exact in both directions: its
forward half forgets both implementations through `HasContract.sound`, and its
reverse half reconstructs both implementations through `HasContract.realize`.

For two two-ports, port 1 of the left block is wired to port 0 of the right
block.  The shared voltage is existential and the two currents into the blocks
sum to zero.  The remaining ports retain the order `[left.port0, right.port1]`.
-/

namespace LeanModels.Spice

private abbrev f0 : Fin 2 := ⟨0, by decide⟩
private abbrev f1 : Fin 2 := ⟨1, by decide⟩

/-- Voltages seen by the left block in a two-port cascade. -/
def cascadeLeftVoltage (external : Vec 2) (shared : Rat) : Vec 2
  | i => if i = f0 then external f0 else shared

/-- Voltages seen by the right block in a two-port cascade. -/
def cascadeRightVoltage (external : Vec 2) (shared : Rat) : Vec 2
  | i => if i = f0 then shared else external f1

/-- Concrete behavior of two leaf two-ports wired in cascade.

Currents use the `PortBehavior` convention: positive means into a block.
Consequently the hidden connection obeys `leftCurrent 1 + rightCurrent 0 = 0`.
-/
def CascadeBehavior (left right : Subckt)
    (voltage current : Vec 2) : Prop :=
  ∃ shared : Rat, ∃ leftCurrent rightCurrent : Vec 2,
    PortBehavior left (cascadeLeftVoltage voltage shared) leftCurrent ∧
    PortBehavior right (cascadeRightVoltage voltage shared) rightCurrent ∧
    leftCurrent f1 + rightCurrent f0 = 0 ∧
    current f0 = leftCurrent f0 ∧
    current f1 = rightCurrent f1

/-- The coefficient of the hidden shared voltage in the cascade KCL row. -/
def cascadeDenominator (left right : PortContract 2) : Rat :=
  left.Y f1 f1 + right.Y f0 f0

/-- Eliminate the shared port of two affine two-port contracts.

This is the one-variable Schur complement of the hidden KCL equation.  A zero
`cascadeDenominator` means that this elimination does not determine the shared
voltage; the exact theorem therefore carries its nonzero condition explicitly.
-/
def cascade (left right : PortContract 2) : PortContract 2 :=
  let denominator := cascadeDenominator left right
  { Y := fun row col =>
      if row = f0 then
        if col = f0 then
          left.Y f0 f0 - left.Y f0 f1 * left.Y f1 f0 / denominator
        else -(left.Y f0 f1 * right.Y f0 f1 / denominator)
      else if col = f0 then
        -(right.Y f1 f0 * left.Y f1 f0 / denominator)
      else right.Y f1 f1 - right.Y f1 f0 * right.Y f0 f1 / denominator
  , J := fun row =>
      if row = f0 then
        left.J f0 - left.Y f0 f1 * (left.J f1 + right.J f0) / denominator
      else right.J f1 - right.Y f1 f0 * (left.J f1 + right.J f0) / denominator }

/-- The shared voltage obtained by solving the hidden KCL equation. -/
def cascadeSharedVoltage (left right : PortContract 2)
    (voltage : Vec 2) : Rat :=
  -(left.Y f1 f0 * voltage f0 + right.Y f0 f1 * voltage f1 +
      left.J f1 + right.J f0) / cascadeDenominator left right

private theorem vec2_ext {left right : Vec 2}
    (h0 : left f0 = right f0) (h1 : left f1 = right f1) : left = right := by
  funext i
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · have : i = f0 := by apply Fin.ext; exact hi
    subst i
    exact h0
  · have : i = f1 := by apply Fin.ext; exact hi
    subst i
    exact h1

private theorem cascade_apply_f0 (left right : PortContract 2)
    (voltage : Vec 2) :
    (cascade left right).apply voltage f0 =
      left.Y f0 f0 * voltage f0 +
      left.Y f0 f1 * cascadeSharedVoltage left right voltage + left.J f0 := by
  simp [PortContract.apply, matVec, dot, cascade, cascadeSharedVoltage,
    cascadeDenominator]
  grind

private theorem cascade_apply_f1 (left right : PortContract 2)
    (voltage : Vec 2) :
    (cascade left right).apply voltage f1 =
      right.Y f1 f0 * cascadeSharedVoltage left right voltage +
      right.Y f1 f1 * voltage f1 + right.J f1 := by
  simp [PortContract.apply, matVec, dot, cascade, cascadeSharedVoltage,
    cascadeDenominator]
  grind

private theorem cascade_shared_kcl (left right : PortContract 2)
    (voltage : Vec 2) (hnz : cascadeDenominator left right ≠ 0) :
    left.Y f1 f0 * voltage f0 +
        left.Y f1 f1 * cascadeSharedVoltage left right voltage + left.J f1 +
      (right.Y f0 f0 * cascadeSharedVoltage left right voltage +
        right.Y f0 f1 * voltage f1 + right.J f0) = 0 := by
  simp [cascadeSharedVoltage, cascadeDenominator]
  unfold cascadeDenominator at hnz
  grind

/-- Exact contract-only composition theorem for a two-port cascade.

No internal assignment from either block appears in the resulting affine
relation.  The reverse implication is the crucial realizability statement:
every point admitted by the Schur-complement contract is implemented by both
blocks with a consistent hidden port.
-/
theorem cascade_contracts {left right : Subckt}
    {leftContract rightContract : PortContract 2}
    (hleft : HasContract left leftContract)
    (hright : HasContract right rightContract)
    (hnz : cascadeDenominator leftContract rightContract ≠ 0) :
    ∀ voltage current,
      CascadeBehavior left right voltage current ↔
        current = (cascade leftContract rightContract).apply voltage := by
  intro voltage current
  constructor
  · rintro ⟨shared, leftCurrent, rightCurrent, hleftBehavior,
      hrightBehavior, hshared, hexternal0, hexternal1⟩
    have hl := hleft.sound _ _ hleftBehavior
    have hr := hright.sound _ _ hrightBehavior
    have hsharedValue : shared =
        cascadeSharedVoltage leftContract rightContract voltage := by
      have hl1 := congrFun hl f1
      have hr0 := congrFun hr f0
      simp [PortContract.apply, matVec, dot, cascadeLeftVoltage,
        cascadeRightVoltage] at hl1 hr0
      unfold cascadeSharedVoltage cascadeDenominator
      unfold cascadeDenominator at hnz
      grind
    apply vec2_ext
    · rw [hexternal0, congrFun hl f0, cascade_apply_f0]
      simp [PortContract.apply, matVec, dot, cascadeLeftVoltage, hsharedValue]
      grind
    · rw [hexternal1, congrFun hr f1, cascade_apply_f1]
      simp [PortContract.apply, matVec, dot, cascadeRightVoltage, hsharedValue]
      grind
  · intro hcurrent
    let shared := cascadeSharedVoltage leftContract rightContract voltage
    let leftVoltage := cascadeLeftVoltage voltage shared
    let rightVoltage := cascadeRightVoltage voltage shared
    let leftCurrent := leftContract.apply leftVoltage
    let rightCurrent := rightContract.apply rightVoltage
    refine ⟨shared, leftCurrent, rightCurrent,
      hleft.realize leftVoltage leftCurrent rfl,
      hright.realize rightVoltage rightCurrent rfl, ?_, ?_, ?_⟩
    · have hkcl := cascade_shared_kcl leftContract rightContract voltage hnz
      simpa [leftCurrent, rightCurrent, leftVoltage, rightVoltage,
        PortContract.apply, matVec, dot, cascadeLeftVoltage,
        cascadeRightVoltage, shared, Rat.zero_add] using hkcl
    · rw [hcurrent, cascade_apply_f0]
      simp [leftCurrent, leftVoltage, PortContract.apply, matVec, dot,
        cascadeLeftVoltage, shared, Rat.zero_add]
    · rw [hcurrent, cascade_apply_f1]
      simp [rightCurrent, rightVoltage, PortContract.apply, matVec, dot,
        cascadeRightVoltage, shared, Rat.zero_add]

/-- Public composition theorem under the lane-wide workflow name.

For M0, wiring is the exact `CascadeBehavior` relation and the composed
interface is the Schur complement `cascade`.  This synonym keeps clients
independent of the two-port implementation terminology while retaining both
directions of the behavior equivalence.
-/
theorem compose_contracts {left right : Subckt}
    {leftContract rightContract : PortContract 2}
    (hleft : HasContract left leftContract)
    (hright : HasContract right rightContract)
    (hnz : cascadeDenominator leftContract rightContract ≠ 0) :
    ∀ voltage current,
      CascadeBehavior left right voltage current ↔
        current = (cascade leftContract rightContract).apply voltage :=
  cascade_contracts hleft hright hnz

/-! ## Tellegen's theorem at the semantic boundary -/

/-- The nodal power residual `v(n) * KCL(n)`, summed over every mentioned node.

With the `currentInto` orientation, expanding and regrouping this expression
gives the negative sum of oriented branch powers.  The nodal form is the
primitive Tellegen identity and avoids imposing a separate branch-current
field for resistors and current sources.
-/
def nodalPowerResidual (netlist : FlatNetlist) (assignment : Assignment) : Rat :=
  netlist.nodes.foldl
    (fun total node => total + assignment.volt node * kclSum netlist assignment node) 0

private theorem foldl_zero_terms (term : String → Rat) :
    ∀ nodes : List String, (∀ node, node ∈ nodes → term node = 0) →
      nodes.foldl (fun total node => total + term node) 0 = 0 := by
  intro nodes hzero
  induction nodes with
  | nil => rfl
  | cons node tail ih =>
      simp only [List.foldl_cons]
      have hhead : term node = 0 := hzero node (by simp)
      have htail : ∀ item, item ∈ tail → term item = 0 := by
        intro item hmem
        exact hzero item (by simp [hmem])
      simpa [hhead, Rat.zero_add] using ih htail

/-- Tellegen's theorem in primitive nodal form: every satisfying DC assignment
has zero total voltage-weighted KCL residual.  This uses physical laws only;
no solver or well-posedness assumption is involved. -/
theorem tellegen_nodal {netlist : FlatNetlist} {assignment : Assignment}
    (hsat : Satisfies netlist assignment) :
    nodalPowerResidual netlist assignment = 0 := by
  rcases hsat with ⟨hground, _, hkcl⟩
  have hground' : assignment.volt "0" = 0 := by
    simpa using hground
  have hkcl' : ∀ node, node ∈ netlist.nodes → node ≠ "0" →
      kclSum netlist assignment node = 0 := by
    intro node hmem hne
    have hfiltered : node ∈ netlist.nodes.filter (· != "0") := by
      simp [hmem, hne]
    have hnode := List.all_eq_true.mp hkcl node hfiltered
    simpa using hnode
  unfold nodalPowerResidual
  apply foldl_zero_terms
  intro node hmem
  by_cases hnode : node = "0"
  · simp [hnode, hground']
  · rw [hkcl' node hmem hnode]
    simp

end LeanModels.Spice
