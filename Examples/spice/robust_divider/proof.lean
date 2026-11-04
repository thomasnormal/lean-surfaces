import LeanModels.Circuit

namespace Examples.spice.robust_divider.proof

open LeanModels.Circuit

load_circuit robustDivider from
  "Examples/spice/robust_divider/robust_divider.cir"

abbrev inputNodeRef := node! robustDivider "in"
abbrev groundNodeRef := node! robustDivider "0"
abbrev outputNodeRef := node! robustDivider "out"
abbrev supplySourceRef := device! robustDivider "v1"
abbrev topResistorRef := device! robustDivider "r1"
abbrev bottomResistorRef := device! robustDivider "r2"

abbrev inputNode := inputNodeRef.id
abbrev groundNode := groundNodeRef.id
abbrev outputNode := outputNodeRef.id
abbrev supplySource := supplySourceRef.id
abbrev topResistor := topResistorRef.id
abbrev bottomResistor := bottomResistorRef.id

def SupplyRange : RatInterval := ⟨19 / 4, 21 / 4⟩
def TopResistanceRange : RatInterval := ⟨950, 1050⟩
def BottomResistanceRange : RatInterval := ⟨1900, 2100⟩

#guard dividerOutputInterval SupplyRange TopResistanceRange
    BottomResistanceRange == ⟨361 / 118, 441 / 122⟩

/-- The supply varies per run. The two resistor values are selected once per
fabricated instance, rather than independently at every equation use. -/
noncomputable def RobustDividerAllowed (world : DCRunWorld) : Prop :=
  SupplyRange.Contains (world.environment.sourceVoltage supplySource) ∧
  TopResistanceRange.Contains
    (world.fabricated.resistance topResistor) ∧
  BottomResistanceRange.Contains
    (world.fabricated.resistance bottomResistor)

private theorem allowed_positive {world : DCRunWorld}
    (h : RobustDividerAllowed world) :
  0 < world.fabricated.resistance topResistor ∧
    0 < world.fabricated.resistance bottomResistor := by
  dsimp [RobustDividerAllowed, SupplyRange, TopResistanceRange,
    BottomResistanceRange, RatInterval.Contains] at h
  norm_num at h
  exact ⟨by linarith [h.2.1.1], by linarith [h.2.2.1]⟩

/-- The divider formula follows from the voltage-source law, both resistor
laws, ground, and KCL at `out`. It is not part of the circuit model. -/
theorem output_eq {world : DCRunWorld} {assignment : RealDCAssignment}
    (hpositive :
      0 < world.fabricated.resistance topResistor ∧
      0 < world.fabricated.resistance bottomResistor)
    (h : RealDCSatisfies robustDivider world assignment) :
    assignment.voltage outputNode =
      world.environment.sourceVoltage supplySource *
        world.fabricated.resistance bottomResistor /
          (world.fabricated.resistance topResistor +
            world.fabricated.resistance bottomResistor) := by
  change RawRealDCSatisfies robustDivider_dc world assignment at h
  have hsupply := h.2.2.1
    (.voltageSource supplySource inputNode groundNode 5)
    (by simp [robustDivider_dc,
      supplySource, inputNode, groundNode])
  have htop := h.2.2.1
    (.resistor topResistor inputNode outputNode 1000)
    (by simp [robustDivider_dc,
      topResistor, inputNode, outputNode])
  have hbottom := h.2.2.1
    (.resistor bottomResistor outputNode groundNode 2000)
    (by simp [robustDivider_dc,
      bottomResistor, outputNode, groundNode])
  have hkcl := h.2.2.2 outputNode
    (by simp [robustDivider_dc,
      DCCircuit.nodes, outputNode])
    (by decide)
  simp [robustDivider_dc, DCCircuit.realKcl, DCDevice.realCurrentLeaving,
    DCDevice.positive, DCDevice.negative, DCDevice.id, outputNode] at hkcl
  simp [DCDevice.realLaw] at hsupply htop hbottom
  have hground := h.2.1
  change assignment.voltage groundNode = 0 at hground
  rw [hground] at hsupply hbottom
  rw [htop, hbottom] at hkcl
  have htopNonzero :
      world.fabricated.resistance topResistor ≠ 0 :=
    ne_of_gt hpositive.1
  have hbottomNonzero :
      world.fabricated.resistance bottomResistor ≠ 0 :=
    ne_of_gt hpositive.2
  have hsum :
      world.fabricated.resistance topResistor +
          world.fabricated.resistance bottomResistor ≠ 0 :=
    ne_of_gt (add_pos hpositive.1 hpositive.2)
  field_simp [htopNonzero, hbottomNonzero] at hkcl
  apply (eq_div_iff hsum).2
  nlinarith

/-- Positive-resistance worlds have an explicitly constructed operating
point. This is the non-vacuity theorem used by the robust result. -/
theorem positive_realizable :
    RealizableUnder (RealDCBehavior robustDivider)
      (fun world =>
        0 < world.fabricated.resistance topResistor ∧
        0 < world.fabricated.resistance bottomResistor) := by
  intro world hpositive
  let total :=
    world.fabricated.resistance topResistor +
      world.fabricated.resistance bottomResistor
  let output :=
    world.environment.sourceVoltage supplySource *
      world.fabricated.resistance bottomResistor / total
  let current := world.environment.sourceVoltage supplySource / total
  let assignment : RealDCAssignment :=
    { voltage := fun node =>
        if node = inputNode then
          world.environment.sourceVoltage supplySource
        else if node = outputNode then output
        else 0
      current := fun id =>
        if id = supplySource then -current else current }
  refine ⟨assignment, (), ?_⟩
  change RawRealDCSatisfies robustDivider_dc world assignment
  have htopNonzero :
      world.fabricated.resistance topResistor ≠ 0 :=
    ne_of_gt hpositive.1
  have hbottomNonzero :
      world.fabricated.resistance bottomResistor ≠ 0 :=
    ne_of_gt hpositive.2
  have htotal : total ≠ 0 := by
    dsimp [total]
    exact ne_of_gt (add_pos hpositive.1 hpositive.2)
  have hsum :
      world.fabricated.resistance topResistor +
          world.fabricated.resistance bottomResistor ≠ 0 :=
    ne_of_gt (add_pos hpositive.1 hpositive.2)
  dsimp [topResistor, bottomResistor] at hsum
  constructor
  · exact robustDivider_solution_satisfies.valid
  constructor
  · simp [assignment, robustDivider_dc,
      inputNode, outputNode]
  constructor
  · intro device membership
    simp [robustDivider_dc] at membership
    rcases membership with rfl | rfl | rfl
    · simp [DCDevice.realLaw, assignment, inputNode, outputNode,
        supplySource]
    · simp [DCDevice.realLaw, assignment, inputNode, outputNode,
        topResistor, supplySource, current, output, total]
      dsimp [topResistor, bottomResistor] at htopNonzero hbottomNonzero htotal ⊢
      field_simp [htopNonzero, hbottomNonzero, hsum]
      ring
    · simp [DCDevice.realLaw, assignment, outputNode, bottomResistor,
        inputNode, supplySource,
        current, output, total]
      dsimp [topResistor, bottomResistor] at htopNonzero hbottomNonzero htotal ⊢
      field_simp [htopNonzero, hbottomNonzero, hsum]
  · intro node membership nonground
    rcases node with ⟨index⟩
    simp [robustDivider_dc, DCCircuit.nodes] at membership
    interval_cases index
    · simp [robustDivider_dc, DCCircuit.realKcl,
        DCDevice.realCurrentLeaving, DCDevice.positive,
        DCDevice.negative, DCDevice.id, assignment, supplySource, current]
    · exact absurd rfl nonground
    · simp [robustDivider_dc, DCCircuit.realKcl,
        DCDevice.realCurrentLeaving, DCDevice.positive,
        DCDevice.negative, DCDevice.id, assignment, supplySource, current]

theorem robust_divider_realizable :
    RealizableUnder (RealDCBehavior robustDivider)
      RobustDividerAllowed := by
  intro world hallowed
  exact positive_realizable world (allowed_positive hallowed)

theorem robust_divider_safe :
    SafeUnder (RealDCBehavior robustDivider) RobustDividerAllowed
      (fun _world assignment _internal =>
        (361 / 118 : ℝ) ≤ assignment.voltage outputNode ∧
        assignment.voltage outputNode ≤ 441 / 122) := by
  intro world assignment _internal hallowed hbehavior
  have hformula := output_eq (allowed_positive hallowed) hbehavior
  change
    SupplyRange.Contains (world.environment.sourceVoltage supplySource) ∧
      TopResistanceRange.Contains
        (world.fabricated.resistance topResistor) ∧
      BottomResistanceRange.Contains
        (world.fabricated.resistance bottomResistor) at hallowed
  rcases hallowed with ⟨hsupply, ⟨htop, hbottom⟩⟩
  have hinterval :
      (dividerOutputInterval SupplyRange TopResistanceRange
        BottomResistanceRange).Contains
          (assignment.voltage outputNode) := by
    circuit_enclose [hformula] with
      [SupplyRange, TopResistanceRange, BottomResistanceRange]
  norm_num [RatInterval.Contains, dividerOutputInterval, SupplyRange,
    TopResistanceRange, BottomResistanceRange] at hinterval ⊢
  exact hinterval

/-! ## Observation noise and probabilistic yield -/

/-- Bounded readout noise is adversarial, not probabilistic. It widens the
proved electrical interval by exactly the admitted observation error. -/
theorem robust_divider_bounded_noise
    {world : DCRunWorld} {assignment : RealDCAssignment}
    {noise : ℝ}
    (hallowed : RobustDividerAllowed world)
    (hbehavior : RealDCSatisfies robustDivider world assignment)
    (hnoise : BoundedNoise (1 / 100) noise) :
    (361 / 118 : ℝ) - 1 / 100 ≤
        assignment.voltage outputNode + noise ∧
      assignment.voltage outputNode + noise ≤
        441 / 122 + 1 / 100 := by
  apply bounded_noise_widens_interval (by norm_num)
  · exact robust_divider_safe world assignment () hallowed hbehavior
  · exact hnoise

/-- Two correlated fabrication/run outcomes. Each outcome fixes supply and
both resistors together; parameters are not resampled within a run. -/
noncomputable def lowCornerWorld : DCRunWorld :=
  deterministicWorld
    { resistance := fun id =>
        if id = topResistor then 950
        else if id = bottomResistor then 1900 else 0 }
    { sourceVoltage := fun id =>
        if id = supplySource then 19 / 4 else 0 }

noncomputable def highCornerWorld : DCRunWorld :=
  deterministicWorld
    { resistance := fun id =>
        if id = topResistor then 1050
        else if id = bottomResistor then 2100 else 0 }
    { sourceVoltage := fun id =>
        if id = supplySource then 21 / 4 else 0 }

theorem lowCornerWorld_allowed :
    RobustDividerAllowed lowCornerWorld := by
  norm_num [RobustDividerAllowed, SupplyRange, TopResistanceRange,
    BottomResistanceRange, RatInterval.Contains, lowCornerWorld,
    deterministicWorld, topResistor, bottomResistor, supplySource]

theorem highCornerWorld_allowed :
    RobustDividerAllowed highCornerWorld := by
  norm_num [RobustDividerAllowed, SupplyRange, TopResistanceRange,
    BottomResistanceRange, RatInterval.Contains, highCornerWorld,
    deterministicWorld, topResistor, bottomResistor, supplySource]

noncomputable def DividerCornerDistribution :
    FiniteDistribution DCRunWorld where
  outcomes := [(lowCornerWorld, 1 / 2), (highCornerWorld, 1 / 2)]
  weight_nonnegative := by
    intro outcome weight membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with h | h
    · have houtcome : outcome = lowCornerWorld := by
        simpa using congrArg Prod.fst h
      have hweight : weight = 1 / 2 := by
        simpa using congrArg Prod.snd h
      subst outcome
      subst weight
      norm_num
    · have houtcome : outcome = highCornerWorld := by
        simpa using congrArg Prod.fst h
      have hweight : weight = 1 / 2 := by
        simpa using congrArg Prod.snd h
      subst outcome
      subst weight
      norm_num
  total_weight := by norm_num

def DividerSafeWorld (world : DCRunWorld) : Prop :=
  ∀ assignment, RealDCSatisfies robustDivider world assignment →
    (361 / 118 : ℝ) ≤ assignment.voltage outputNode ∧
      assignment.voltage outputNode ≤ 441 / 122

theorem divider_corner_almost_sure :
    FiniteAlmostSure DividerCornerDistribution DividerSafeWorld := by
  intro world weight membership hpositive
  simp only [DividerCornerDistribution, List.mem_cons,
    List.not_mem_nil, or_false] at membership
  rcases membership with h | h
  · have hworld : world = lowCornerWorld := by
      simpa using congrArg Prod.fst h
    have hweight : weight = 1 / 2 := by
      simpa using congrArg Prod.snd h
    subst world
    subst weight
    intro assignment hbehavior
    exact robust_divider_safe lowCornerWorld assignment ()
      lowCornerWorld_allowed hbehavior
  · have hworld : world = highCornerWorld := by
      simpa using congrArg Prod.fst h
    have hweight : weight = 1 / 2 := by
      simpa using congrArg Prod.snd h
    subst world
    subst weight
    intro assignment hbehavior
    exact robust_divider_safe highCornerWorld assignment ()
      highCornerWorld_allowed hbehavior

/-- For this explicitly chosen correlated distribution, the already-proved
universal circuit property has exact yield one. -/
theorem divider_corner_yield :
    finiteYield DividerCornerDistribution DividerSafeWorld = 1 :=
  divider_corner_almost_sure.yield_eq_one

theorem robust_divider_determinate :
    DeterminateUnder (RealDCBehavior robustDivider)
      RobustDividerAllowed ℝ
      (fun _world assignment _internal =>
        assignment.voltage outputNode) := by
  intro world hallowed left _leftInternal right _rightInternal
    hleft hright
  change left.voltage outputNode = right.voltage outputNode
  rw [output_eq (allowed_positive hallowed) hleft,
    output_eq (allowed_positive hallowed) hright]

def DividerVoltageDomain (_world : DCRunWorld)
    (assignment : RealDCAssignment) (_internal : Unit) : Prop :=
  0 ≤ assignment.voltage inputNode ∧
  assignment.voltage inputNode ≤ 6 ∧
  0 ≤ assignment.voltage outputNode ∧
  assignment.voltage outputNode ≤ 6

theorem robust_divider_domain :
    StaysWithinValidityDomain (RealDCBehavior robustDivider)
      RobustDividerAllowed DividerVoltageDomain := by
  intro world assignment _internal hallowed hbehavior
  have hformula := output_eq (allowed_positive hallowed) hbehavior
  change RawRealDCSatisfies robustDivider_dc world assignment at hbehavior
  have hsupplyLaw := hbehavior.2.2.1
    (.voltageSource supplySource inputNode groundNode 5)
    (by simp [robustDivider_dc,
      supplySource, inputNode, groundNode])
  simp [DCDevice.realLaw] at hsupplyLaw
  have hground := hbehavior.2.1
  change assignment.voltage groundNode = 0 at hground
  rw [hground] at hsupplyLaw
  dsimp [RobustDividerAllowed, SupplyRange, TopResistanceRange,
    BottomResistanceRange, RatInterval.Contains] at hallowed
  rcases hallowed with
    ⟨⟨hsupplyMin, hsupplyMax⟩,
      ⟨⟨htopMin, htopMax⟩, ⟨hbottomMin, hbottomMax⟩⟩⟩
  norm_num at hsupplyMin hsupplyMax htopMin htopMax hbottomMin hbottomMax
  have hsum :
      0 < world.fabricated.resistance topResistor +
        world.fabricated.resistance bottomResistor := by
    linarith
  have hratioNonnegative :
      0 ≤ world.fabricated.resistance bottomResistor /
        (world.fabricated.resistance topResistor +
          world.fabricated.resistance bottomResistor) := by
    positivity
  have hratioAtMostOne :
      world.fabricated.resistance bottomResistor /
          (world.fabricated.resistance topResistor +
            world.fabricated.resistance bottomResistor) ≤ 1 := by
    rw [div_le_one hsum]
    linarith
  have hinput :
      assignment.voltage inputNode =
        world.environment.sourceVoltage supplySource := by
    linarith
  constructor
  · rw [hinput]
    linarith
  constructor
  · rw [hinput]
    linarith
  constructor
  · rw [hformula, mul_div_assoc]
    exact mul_nonneg (by linarith) hratioNonnegative
  · rw [hformula, mul_div_assoc]
    calc
      world.environment.sourceVoltage supplySource *
          (world.fabricated.resistance bottomResistor /
            (world.fabricated.resistance topResistor +
              world.fabricated.resistance bottomResistor)) ≤
          world.environment.sourceVoltage supplySource := by
        nlinarith [
          mul_le_mul_of_nonneg_left hratioAtMostOne
            (show 0 ≤ world.environment.sourceVoltage supplySource by
              linarith)]
      _ ≤ 6 := by linarith

theorem robust_divider_assurance :
    AssuranceCase robustDivider (RealDCBehavior robustDivider)
      RobustDividerAllowed
      (SourceBinding.identity robustDivider
        (fun _circuit => RealDCBehavior robustDivider)
        (fun _circuit => RobustDividerAllowed))
      (fun _world assignment _internal =>
        (361 / 118 : ℝ) ≤ assignment.voltage outputNode ∧
        assignment.voltage outputNode ≤ 441 / 122)
      DividerVoltageDomain :=
  ⟨robust_divider_safe, robust_divider_realizable, robust_divider_domain⟩

end Examples.spice.robust_divider.proof
