import LeanModels.Spice.DramWrite

/-!
# Selected-cell write specifications

This module imports the source-derived write behavior and states engineering
properties of its observations. `DramWrite` does not import this module.
-/

namespace LeanModels.Spice

open LeanModels.Circuit Set

def DramWriteOneNanosecondSpecification
    (world : DramWriteWorld) (boundary : DramWriteBoundary)
    (_internal : Unit) : Prop :=
  SettlesWithin boundary.storageVoltage 4 1
    (1 / 1000000000) world.environment.horizon

def DramWriteRailDomain
    (world : DramWriteWorld) (boundary : DramWriteBoundary)
    (_internal : Unit) : Prop :=
  NoOvershoot boundary.storageVoltage 0 5 world.environment.horizon

/-- The selected storage node charges monotonically from its initial value
toward the threshold-loss boundary and never overshoots it. -/
theorem nominalDramWriteOne_no_overshoot
    {initialStorage horizon : ℝ}
    {boundary : DramWriteBoundary}
    (hinitial4 : initialStorage ≤ 4)
    (hhorizon : 0 ≤ horizon)
    (hbehavior :
      DramWriteBehavior
        (nominalDramWriteOneWorld initialStorage horizon)
        boundary ()) :
    NoOvershoot boundary.storageVoltage initialStorage 4 horizon := by
  intro time htime0 htimeH
  rw [nominalDramWriteOne_behavior_eq_trace
    hinitial4 hhorizon hbehavior time ⟨htime0, htimeH⟩]
  exact
    ⟨nominalDramWriteOneTrace_mono_from_initial hinitial4 htime0,
      nominalDramWriteOneTrace_le_target hinitial4 htime0⟩

/-- A nominal physical write-one trajectory enters any requested positive
voltage band whose rational deadline inequality has been discharged. Exact
`4 V` is deliberately not claimed at finite time. -/
theorem nominalDramWriteOne_settles_within
    {initialStorage horizon : ℝ}
    {boundary : DramWriteBoundary}
    (hinitial : initialStorage ≤ 4) (hhorizon : 0 ≤ horizon)
    (hbehavior :
      DramWriteBehavior
        (nominalDramWriteOneWorld initialStorage horizon)
        boundary ())
    {tolerance deadline : ℝ}
    (htolerance : 0 ≤ tolerance)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineH : deadline ≤ horizon)
    (hdeadline :
      (4 - initialStorage) /
          (1 + nominalDramWriteOneRate *
            (4 - initialStorage) * deadline) ≤
        tolerance) :
    SettlesWithin boundary.storageVoltage 4 tolerance deadline horizon := by
  refine ⟨htolerance, hdeadline0, hdeadlineH, ?_⟩
  intro time hdeadlineTime htimeH
  have htime0 : 0 ≤ time := hdeadline0.trans hdeadlineTime
  rw [nominalDramWriteOne_behavior_eq_trace
    hinitial hhorizon hbehavior time ⟨htime0, htimeH⟩]
  have herror : 0 ≤ 4 - initialStorage := sub_nonneg.mpr hinitial
  have hdeadlineDenominator :=
    nominalDramWriteOneTrace_denominator_pos hinitial hdeadline0
  have htimeDenominator :=
    nominalDramWriteOneTrace_denominator_pos hinitial htime0
  have hdenominatorMono :
      1 + nominalDramWriteOneRate * (4 - initialStorage) * deadline ≤
        1 + nominalDramWriteOneRate * (4 - initialStorage) * time := by
    have hcoefficient :
        0 ≤ nominalDramWriteOneRate * (4 - initialStorage) :=
      mul_nonneg nominalDramWriteOneRate_pos.le herror
    nlinarith
  have hfraction :
      (4 - initialStorage) /
          (1 + nominalDramWriteOneRate * (4 - initialStorage) * time) ≤
        (4 - initialStorage) /
          (1 + nominalDramWriteOneRate *
            (4 - initialStorage) * deadline) := by
    rw [div_le_div_iff₀ htimeDenominator hdeadlineDenominator]
    exact mul_le_mul_of_nonneg_left hdenominatorMono herror
  have hle :=
    nominalDramWriteOneTrace_le_target hinitial htime0
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  change
    -(nominalDramWriteOneTrace initialStorage time - 4) ≤ tolerance
  have hformula :
      -(nominalDramWriteOneTrace initialStorage time - 4) =
        (4 - initialStorage) /
          (1 + nominalDramWriteOneRate *
            (4 - initialStorage) * time) := by
    unfold nominalDramWriteOneTrace
    ring
  rw [hformula]
  exact hfraction.trans hdeadline

/-- From a discharged cell, the nominal primitive model reaches the
`[3 V, 4 V]` write-one band within one nanosecond. -/
theorem nominalDramWriteOne_zero_to_high_by_one_ns
    {horizon : ℝ} {boundary : DramWriteBoundary}
    (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon)
    (hbehavior :
      DramWriteBehavior (nominalDramWriteOneWorld 0 horizon) boundary ()) :
    SettlesWithin boundary.storageVoltage 4 1
      (1 / 1000000000) horizon := by
  apply nominalDramWriteOne_settles_within
    (initialStorage := 0) (horizon := horizon)
    (boundary := boundary)
  · norm_num
  · linarith
  · exact hbehavior
  · norm_num
  · norm_num
  · exact hdeadline
  · norm_num [nominalDramWriteOneRate]

/-- Paired non-vacuity for the concrete one-nanosecond write guarantee. -/
theorem nominalDramWriteOne_zero_to_high_by_one_ns_realizable
    {horizon : ℝ} (hdeadline : (1 / 1000000000 : ℝ) ≤ horizon) :
    ∃ boundary,
      DramWriteBehavior (nominalDramWriteOneWorld 0 horizon) boundary () ∧
        SettlesWithin boundary.storageVoltage 4 1
          (1 / 1000000000) horizon := by
  have hhorizon : 0 ≤ horizon := by linarith
  obtain ⟨boundary, hbehavior⟩ :=
    nominalDramWriteOne_realizable (initialStorage := 0)
      (horizon := horizon) (by norm_num) hhorizon
  exact ⟨boundary, hbehavior,
    nominalDramWriteOne_zero_to_high_by_one_ns hdeadline hbehavior⟩

end LeanModels.Spice
