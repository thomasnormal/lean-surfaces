import LeanModels.Spice.Logic
import LeanModels.Spice.DeviceLevels
import LeanModels.Spice.Mos1Resolved

/-!
# MOS Level 1 compact-model specification

The scalar current below is the long-channel square-law MOS1 channel model
used by the committed ngspice decks. `vgs` and `vds` are polarity-normalized:
for PMOS they mean `Vsg` and `Vsd`. The model currently covers the explicit
deck profile `LEVEL=1`, zero body effect, and no junction-current contribution
to the DC channel equation.
-/

namespace LeanModels.Spice

-- Loudness guard (family-architecture.md §autoImplicit ruling, 2026-08-24):
-- without this a mistyped or unopened name is silently auto-bound as an
-- implicit variable rather than reported. This file is monomorphic --
-- no `Type`/`Sort` binders, no generic type variables -- so the flip is
-- inert here, and it is file-local: importers are unaffected.
set_option autoImplicit false

/-- Real-valued parameters consumed by the channel equation. These are
obtained from the exact validated `Mos1Model`, not from named parameters. -/
structure Mos1Params where
  polarity : LeanModels.Circuit.MosPolarity
  threshold : ℝ
  beta : ℝ
  lambda : ℝ

noncomputable def Mos1Model.params (model : Mos1Model) : Mos1Params :=
  { polarity := model.polarity
    threshold := (model.threshold : ℝ)
    beta := (model.transconductance : ℝ)
    lambda := (model.channelLengthModulation : ℝ) }

/-- Forward channel-current magnitude for normalized terminal voltages.

The three branches are cutoff, triode, and saturation. -/
noncomputable def mos1ForwardCurrent
    (params : Mos1Params) (vgs vds : ℝ) : ℝ :=
  if vgs ≤ params.threshold then 0
  else if vds ≤ vgs - params.threshold then
    params.beta *
      ((vgs - params.threshold) * vds - vds ^ 2 / 2) *
      (1 + params.lambda * vds)
  else
    params.beta / 2 * (vgs - params.threshold) ^ 2 *
      (1 + params.lambda * vds)

/-- A compact-model terminal-current observation. -/
def Mos1ChannelSpec (params : Mos1Params)
    (vgs vds drainCurrent : ℝ) : Prop :=
  0 ≤ vds ∧ drainCurrent = mos1ForwardCurrent params vgs vds

/-- Real-valued DC state for a typed MOS1 circuit. Source current is positive
from the voltage source's positive terminal to its negative terminal. -/
structure Mos1CircuitState where
  voltage : NodeId → ℝ
  sourceCurrent : SourceId → ℝ

/-- Drain-to-source current using the source orientation written in the deck.
PMOS channel current has the opposite conventional sign. -/
noncomputable def mos1DrainCurrent
    (state : Mos1CircuitState) (transistor : Mos1Transistor) : ℝ :=
  let params := transistor.model.params
  match params.polarity with
  | .nmos =>
      mos1ForwardCurrent params
        (state.voltage transistor.gate - state.voltage transistor.source)
        (state.voltage transistor.drain - state.voltage transistor.source)
  | .pmos =>
      -mos1ForwardCurrent params
        (state.voltage transistor.source - state.voltage transistor.gate)
        (state.voltage transistor.source - state.voltage transistor.drain)

/-- Drain-terminal current with dynamic source/drain selection.

Long-channel MOS1 is symmetric in the two channel terminals in the supported
zero-body-effect profile.  For NMOS the lower-potential channel terminal is
the effective source; for PMOS the higher-potential terminal is.  The result
is positive when conventional current leaves the terminal written as
`drain`.  This relation is required by pass devices such as a DRAM access
transistor, whose current direction changes during charge sharing. -/
noncomputable def mos1TerminalCurrent
    (params : Mos1Params) (gate drain source : ℝ) : ℝ :=
  match params.polarity with
  | .nmos =>
      if source ≤ drain then
        mos1ForwardCurrent params (gate - source) (drain - source)
      else
        -mos1ForwardCurrent params (gate - drain) (source - drain)
  | .pmos =>
      if drain ≤ source then
        -mos1ForwardCurrent params (source - gate) (source - drain)
      else
        mos1ForwardCurrent params (drain - gate) (drain - source)

/-- State-level bidirectional channel current for a typed transistor. -/
noncomputable def mos1BidirectionalDrainCurrent
    (state : Mos1CircuitState) (transistor : Mos1Transistor) : ℝ :=
  mos1TerminalCurrent transistor.model.params
    (state.voltage transistor.gate)
    (state.voltage transistor.drain)
    (state.voltage transistor.source)

theorem mos1ForwardCurrent_zero_drop
    (params : Mos1Params) (vgs : ℝ) :
    mos1ForwardCurrent params vgs 0 = 0 := by
  unfold mos1ForwardCurrent
  by_cases hcutoff : vgs ≤ params.threshold
  · simp [hcutoff]
  · have hoverdrive : 0 ≤ vgs - params.threshold := by linarith
    simp [hcutoff, hoverdrive]

/-- A bidirectional NMOS channel is cut off when the gate is below threshold
relative to both channel terminals. The statement is orientation-independent,
which is essential for access and pass transistors. -/
theorem mos1TerminalCurrent_nmos_eq_zero_of_cutoff
    (threshold beta lambda gate drain source : ℝ)
    (hgateDrain : gate - drain ≤ threshold)
    (hgateSource : gate - source ≤ threshold) :
    mos1TerminalCurrent
        { polarity := .nmos, threshold, beta, lambda }
        gate drain source = 0 := by
  unfold mos1TerminalCurrent
  by_cases horder : source ≤ drain
  · simp [horder, mos1ForwardCurrent, hgateSource]
  · simp [horder, mos1ForwardCurrent, hgateDrain]

/-- With positive transconductance, zero channel-length modulation, and a
forward-oriented channel, the MOS1 current magnitude is nonnegative. -/
theorem mos1ForwardCurrent_nonneg
    (polarity : LeanModels.Circuit.MosPolarity) (threshold beta vgs vds : ℝ)
    (hbeta : 0 ≤ beta) (hvds : 0 ≤ vds) :
    0 ≤ mos1ForwardCurrent
      { polarity, threshold, beta, lambda := 0 } vgs vds := by
  unfold mos1ForwardCurrent
  split
  · norm_num
  next hon =>
    split
    next htriode =>
      have hoverdrive : 0 < vgs - threshold := by linarith
      have hshape :
          0 ≤ (vgs - threshold) * vds - vds ^ 2 / 2 := by
        nlinarith [mul_nonneg hvds
          (show 0 ≤ vgs - threshold - vds / 2 by linarith)]
      positivity
    next hsaturation =>
      positivity

/-- A zero-channel-length-modulation NMOS channel is passive: terminal
current has the same sign as the voltage drop from the named drain to the
named source. This statement is invariant under the dynamic source/drain
selection used by pass devices. -/
theorem mos1TerminalCurrent_nmos_mul_drop_nonneg
    (threshold beta gate drain source : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      mos1TerminalCurrent
          { polarity := .nmos, threshold, beta, lambda := 0 }
          gate drain source *
        (drain - source) := by
  unfold mos1TerminalCurrent
  by_cases horder : source ≤ drain
  · rw [if_pos horder]
    exact mul_nonneg
      (mos1ForwardCurrent_nonneg .nmos threshold beta
        (gate - source) (drain - source) hbeta (sub_nonneg.mpr horder))
      (sub_nonneg.mpr horder)
  · rw [if_neg horder]
    have hreverse : drain ≤ source := le_of_not_ge horder
    exact mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr
        (mos1ForwardCurrent_nonneg .nmos threshold beta
          (gate - drain) (source - drain) hbeta
          (sub_nonneg.mpr hreverse)))
      (sub_nonpos.mpr hreverse)

theorem mos1TerminalCurrent_nmos_nonneg_of_source_le_drain
    (threshold beta gate drain source : ℝ)
    (hbeta : 0 ≤ beta) (horder : source ≤ drain) :
    0 ≤
      mos1TerminalCurrent
        { polarity := .nmos, threshold, beta, lambda := 0 }
        gate drain source := by
  simp only [mos1TerminalCurrent, horder, if_true]
  exact mos1ForwardCurrent_nonneg .nmos threshold beta
    (gate - source) (drain - source) hbeta (sub_nonneg.mpr horder)

theorem mos1TerminalCurrent_nmos_nonpos_of_drain_le_source
    (threshold beta gate drain source : ℝ)
    (hbeta : 0 ≤ beta) (horder : drain ≤ source) :
    mos1TerminalCurrent
        { polarity := .nmos, threshold, beta, lambda := 0 }
        gate drain source ≤ 0 := by
  by_cases hequal : source ≤ drain
  · have : drain = source := le_antisymm horder hequal
    subst source
    simp [mos1TerminalCurrent, mos1ForwardCurrent_zero_drop]
  · simp only [mos1TerminalCurrent, hequal, if_false]
    exact neg_nonpos.mpr
      (mos1ForwardCurrent_nonneg .nmos threshold beta
        (gate - drain) (source - drain) hbeta
        (sub_nonneg.mpr horder))

/-- With zero channel-length modulation, forward MOS1 current is monotone in
the drain-source drop. This is a primitive device-law fact used by several
compositional circuit arguments. -/
theorem mos1ForwardCurrent_mono_drop_zero_lambda
    (polarity : LeanModels.Circuit.MosPolarity)
    (threshold beta vgs : ℝ)
    (hbeta : 0 ≤ beta) {vds₁ vds₂ : ℝ} (hle : vds₁ ≤ vds₂) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds₁ ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds₂ := by
  unfold mos1ForwardCurrent
  by_cases hcutoff : vgs ≤ threshold
  · simp [hcutoff]
  · simp only [hcutoff, if_false]
    have hon : threshold < vgs := lt_of_not_ge hcutoff
    by_cases h₂ : vds₂ ≤ vgs - threshold
    · have h₁ : vds₁ ≤ vgs - threshold := le_trans hle h₂
      simp only [h₁, h₂, if_true]
      have hproduct :
          0 ≤ beta * ((vds₂ - vds₁) *
            ((vgs - threshold) - (vds₁ + vds₂) / 2)) :=
        mul_nonneg hbeta
          (mul_nonneg (by linarith) (by linarith))
      nlinarith [hproduct]
    · by_cases h₁ : vds₁ ≤ vgs - threshold
      · simp only [h₁, if_true, h₂, if_false]
        nlinarith [mul_nonneg hbeta
          (sq_nonneg (vgs - threshold - vds₁))]
      · simp only [h₁, h₂, if_false]
        nlinarith

/-- With zero channel-length modulation and a nonnegative forward drop,
forward MOS1 current is monotone in gate drive. -/
theorem mos1ForwardCurrent_mono_gate_zero_lambda
    (polarity : LeanModels.Circuit.MosPolarity)
    (threshold beta vds : ℝ)
    (hbeta : 0 ≤ beta) (hvds : 0 ≤ vds)
    {vgs₁ vgs₂ : ℝ} (hle : vgs₁ ≤ vgs₂) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₁ vds ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₂ vds := by
  by_cases h1 : vgs₁ ≤ threshold
  · have hzero :
        mos1ForwardCurrent
          { polarity, threshold, beta, lambda := 0 } vgs₁ vds = 0 := by
      unfold mos1ForwardCurrent
      rw [if_pos h1]
    rw [hzero]
    exact mos1ForwardCurrent_nonneg polarity threshold beta vgs₂ vds
      hbeta hvds
  · have h2 : ¬ vgs₂ ≤ threshold := fun h => h1 (hle.trans h)
    unfold mos1ForwardCurrent
    rw [if_neg h1, if_neg h2]
    have hon1 : threshold < vgs₁ := lt_of_not_ge h1
    by_cases t1 : vds ≤ vgs₁ - threshold
    · have t2 : vds ≤ vgs₂ - threshold := by linarith
      rw [if_pos t1, if_pos t2]
      nlinarith [mul_nonneg hbeta
        (mul_nonneg hvds (sub_nonneg.mpr hle))]
    · rw [if_neg t1]
      by_cases t2 : vds ≤ vgs₂ - threshold
      · rw [if_pos t2]
        nlinarith [mul_nonneg hbeta
            (mul_nonneg
              (by linarith : (0 : ℝ) ≤
                vds - (vgs₁ - threshold))
              (by linarith : (0 : ℝ) ≤
                vds + (vgs₁ - threshold))),
          mul_nonneg hbeta
            (mul_nonneg
              (by linarith : (0 : ℝ) ≤
                vgs₂ - threshold - vds)
              hvds)]
      · rw [if_neg t2]
        nlinarith [mul_nonneg hbeta
          (mul_nonneg
            (by linarith : (0 : ℝ) ≤ vgs₂ - vgs₁)
            (by linarith : (0 : ℝ) ≤
              vgs₁ + vgs₂ - 2 * threshold))]

/-- For a nonnegative threshold and zero channel-length modulation, assigning
the larger of two nonnegative voltages to the gate and the smaller to the
drain drop cannot reduce the forward current. This is the device-law ordering
used by cross-coupled differential stages. -/
theorem mos1ForwardCurrent_cross_mono_zero_lambda
    (polarity : LeanModels.Circuit.MosPolarity)
    (threshold beta low high : ℝ)
    (hthreshold : 0 ≤ threshold) (hbeta : 0 ≤ beta)
    (hlow : 0 ≤ low) (hle : low ≤ high) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } low high ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } high low := by
  rcases hle.eq_or_lt with hEq | hlt
  · subst high
    exact le_rfl
  unfold mos1ForwardCurrent
  by_cases hlowCutoff : low ≤ threshold
  · rw [if_pos hlowCutoff]
    split
    · exact le_rfl
    · split
      · have hoverdrive : 0 < high - threshold := by linarith
        have hshape :
            0 ≤ (high - threshold) * low - low ^ 2 / 2 := by
          nlinarith [mul_nonneg hlow
            (show 0 ≤ high - threshold - low / 2 by linarith)]
        positivity
      · positivity
  · have hhighCutoff : ¬ high ≤ threshold := by
      linarith
    have hleftSaturation : ¬ high ≤ low - threshold := by linarith
    rw [if_neg hlowCutoff, if_neg hleftSaturation,
      if_neg hhighCutoff]
    by_cases hrightTriode : low ≤ high - threshold
    · rw [if_pos hrightTriode]
      have hshape :
          (low - threshold) ^ 2 / 2 ≤
            (high - threshold) * low - low ^ 2 / 2 := by
        nlinarith [
          mul_nonneg hlow
            (show 0 ≤ high - low - threshold by linarith),
          mul_nonneg hthreshold
            (show 0 ≤ 2 * low - threshold by linarith)]
      nlinarith [mul_nonneg hbeta
        (sub_nonneg.mpr hshape)]
    · rw [if_neg hrightTriode]
      have hsq :
          (low - threshold) ^ 2 ≤
            (high - threshold) ^ 2 := by
        nlinarith [mul_nonneg
          (show 0 ≤ high - low by linarith)
          (show 0 ≤ high + low - 2 * threshold by linarith)]
      nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hsq)]

/-- The cross ordering is strict when the larger gate drive is above
threshold and the smaller drain drop is positive. -/
theorem mos1ForwardCurrent_cross_strict_zero_lambda
    (polarity : LeanModels.Circuit.MosPolarity)
    (threshold beta low high : ℝ)
    (hthreshold : 0 ≤ threshold) (hbeta : 0 < beta)
    (hlow : 0 < low) (hthresholdHigh : threshold < high)
    (hlt : low < high) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } low high <
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } high low := by
  unfold mos1ForwardCurrent
  by_cases hlowCutoff : low ≤ threshold
  · rw [if_pos hlowCutoff, if_neg (not_le.mpr hthresholdHigh)]
    by_cases hrightTriode : low ≤ high - threshold
    · rw [if_pos hrightTriode]
      have hshape :
          0 < (high - threshold) * low - low ^ 2 / 2 := by
        nlinarith [mul_pos hlow
          (show 0 < high - threshold - low / 2 by linarith)]
      positivity
    · rw [if_neg hrightTriode]
      positivity
  · have hleftSaturation : ¬ high ≤ low - threshold := by
      linarith
    rw [if_neg hlowCutoff, if_neg hleftSaturation,
      if_neg (not_le.mpr hthresholdHigh)]
    by_cases hrightTriode : low ≤ high - threshold
    · rw [if_pos hrightTriode]
      have hshape :
          (low - threshold) ^ 2 / 2 <
            (high - threshold) * low - low ^ 2 / 2 := by
        have hproduct :
            threshold ^ 2 < low * (high - low) := by
          rcases hthreshold.eq_or_lt with hthresholdZero
              | hthresholdPositive
          · subst threshold
            simpa using mul_pos hlow (sub_pos.mpr hlt)
          · calc
              threshold ^ 2 = threshold * threshold := by ring
              _ < low * threshold :=
                mul_lt_mul_of_pos_right
                  (show threshold < low by linarith)
                  hthresholdPositive
              _ ≤ low * (high - low) :=
                mul_le_mul_of_nonneg_left
                  (show threshold ≤ high - low by linarith)
                  hlow.le
        nlinarith
      nlinarith [mul_pos hbeta
        (sub_pos.mpr hshape)]
    · rw [if_neg hrightTriode]
      have hsq :
          (low - threshold) ^ 2 <
            (high - threshold) ^ 2 := by
        nlinarith [mul_pos
          (show 0 < high - low by linarith)
          (show 0 < high + low - 2 * threshold by linarith)]
      nlinarith [mul_pos hbeta (sub_pos.mpr hsq)]

/-- Lowering gate drive and drain-source drop by the same nonnegative amount
cannot increase a forward-oriented MOS1 current, provided the lowered drop
remains nonnegative. -/
theorem mos1ForwardCurrent_mono_common_shift
    (polarity : LeanModels.Circuit.MosPolarity)
    (threshold beta vgs vds shift : ℝ)
    (hbeta : 0 ≤ beta) (hshift : 0 ≤ shift)
    (hvds : 0 ≤ vds - shift) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 }
        (vgs - shift) (vds - shift) ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds := by
  calc
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 }
        (vgs - shift) (vds - shift) ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 }
        vgs (vds - shift) :=
      mos1ForwardCurrent_mono_gate_zero_lambda
        polarity threshold beta (vds - shift) hbeta hvds
        (sub_le_self vgs hshift)
    _ ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds :=
      mos1ForwardCurrent_mono_drop_zero_lambda
        polarity threshold beta vgs hbeta
        (sub_le_self vds hshift)

/-- Swapping the written channel terminals reverses the terminal current. -/
theorem mos1TerminalCurrent_swap
    (params : Mos1Params) (gate drain source : ℝ) :
    mos1TerminalCurrent params gate source drain =
      -mos1TerminalCurrent params gate drain source := by
  cases hpolarity : params.polarity <;>
    simp only [mos1TerminalCurrent, hpolarity]
  · by_cases hsd : source ≤ drain
    · by_cases hds : drain ≤ source
      · have heq : drain = source := le_antisymm hds hsd
        subst drain
        simp [mos1ForwardCurrent_zero_drop]
      · simp [hsd, hds]
    · have hds : drain ≤ source := le_of_not_ge hsd
      simp [hsd, hds]
  · by_cases hds : drain ≤ source
    · by_cases hsd : source ≤ drain
      · have heq : drain = source := le_antisymm hds hsd
        subst drain
        simp [mos1ForwardCurrent_zero_drop]
      · simp [hds, hsd]
    · have hsd : source ≤ drain := le_of_not_ge hds
      simp [hds, hsd]

/-- Current leaving one node through one typed device. MOS gate and bulk
currents are zero in this restricted DC channel model. -/
noncomputable def mos1DeviceCurrentLeaving
    (state : Mos1CircuitState) (target : NodeId) : Mos1Device → ℝ
  | .voltageSource source =>
      if target = source.positive then state.sourceCurrent source.id
      else if target = source.negative then -state.sourceCurrent source.id
      else 0
  | .transistor transistor =>
      if target = transistor.drain then mos1DrainCurrent state transistor
      else if target = transistor.source then -mos1DrainCurrent state transistor
      else 0

/-- Device current using bidirectional channel-terminal semantics. -/
noncomputable def mos1BidirectionalDeviceCurrentLeaving
    (state : Mos1CircuitState) (target : NodeId) : Mos1Device → ℝ
  | .voltageSource source =>
      if target = source.positive then state.sourceCurrent source.id
      else if target = source.negative then -state.sourceCurrent source.id
      else 0
  | .transistor transistor =>
      if target = transistor.drain then
        mos1BidirectionalDrainCurrent state transistor
      else if target = transistor.source then
        -mos1BidirectionalDrainCurrent state transistor
      else 0

/-- Total current leaving a named node. -/
noncomputable def mos1Kcl (circuit : Mos1ResolvedCircuit)
    (state : Mos1CircuitState) (target : NodeId) : ℝ :=
  circuit.devices.toList.foldl
    (fun total device => total + mos1DeviceCurrentLeaving state target device) 0

noncomputable def mos1BidirectionalKcl
    (circuit : Mos1ResolvedCircuit)
    (state : Mos1CircuitState) (target : NodeId) : ℝ :=
  circuit.devices.toList.foldl
    (fun total device =>
      total + mos1BidirectionalDeviceCurrentLeaving state target device) 0

/-- Nodes mentioned by one typed device. Duplicates are harmless in the
universal KCL condition. -/
abbrev mos1DeviceNodes := Mos1Device.nodes

abbrev mos1Nodes := Mos1ResolvedCircuit.nodes

/-- Constitutive and operating-orientation requirement for one typed device. -/
noncomputable def Mos1DeviceLaw
    (state : Mos1CircuitState) : Mos1Device → Prop
  | .voltageSource source =>
      state.voltage source.positive - state.voltage source.negative =
        (source.voltage : ℝ)
  | .transistor transistor =>
      match transistor.model.polarity with
      | .nmos =>
          0 ≤ state.voltage transistor.drain - state.voltage transistor.source
      | .pmos =>
          0 ≤ state.voltage transistor.source - state.voltage transistor.drain

/-- On the original forward-oriented domain, dynamic terminal selection is
exactly the established MOS1 drain-current semantics. -/
theorem mos1BidirectionalDrainCurrent_eq_oriented
    (state : Mos1CircuitState) (transistor : Mos1Transistor)
    (horiented : Mos1DeviceLaw state (.transistor transistor)) :
    mos1BidirectionalDrainCurrent state transistor =
      mos1DrainCurrent state transistor := by
  cases hpolarity : transistor.model.polarity with
  | nmos =>
      have hsourceDrain :
          state.voltage transistor.source ≤
            state.voltage transistor.drain := by
        simpa [Mos1DeviceLaw, hpolarity] using horiented
      simp [mos1BidirectionalDrainCurrent, mos1TerminalCurrent,
        mos1DrainCurrent, Mos1Model.params, hpolarity, hsourceDrain]
  | pmos =>
      have hdrainSource :
          state.voltage transistor.drain ≤
            state.voltage transistor.source := by
        simpa [Mos1DeviceLaw, hpolarity] using horiented
      simp [mos1BidirectionalDrainCurrent, mos1TerminalCurrent,
        mos1DrainCurrent, Mos1Model.params, hpolarity, hdrainSource]

/-- The ngspice Level-1 DC semantics used by the proofs:

* hierarchy and model references have already been validated;
* every source and channel satisfies its constitutive equation;
* ground is zero;
* KCL holds at every non-ground terminal node.

Junction currents, body effect, capacitance, and geometry-dependent corrections
are deliberately outside this named profile. -/
noncomputable def Mos1Satisfies
    (circuit : Mos1ResolvedCircuit) (state : Mos1CircuitState) : Prop :=
  state.voltage ground = 0 ∧
  (∀ device ∈ circuit.devices.toList, Mos1DeviceLaw state device) ∧
  ∀ target ∈ mos1Nodes circuit, target ≠ ground →
    mos1Kcl circuit state target = 0

/-- Open-component semantics. Nodes in `driven` are boundary ports whose
voltages and supplied currents are controlled by the surrounding circuit.
Every other non-ground terminal node still obeys KCL. -/
noncomputable def Mos1ComponentSatisfies
    (circuit : Mos1ResolvedCircuit) (driven : List NodeId)
    (state : Mos1CircuitState) : Prop :=
  state.voltage ground = 0 ∧
  (∀ device ∈ circuit.devices.toList, Mos1DeviceLaw state device) ∧
  ∀ target ∈ mos1Nodes circuit,
    target ≠ ground → target ∉ driven →
      mos1Kcl circuit state target = 0

/-- Source/drain-symmetric MOS1 DC semantics.  Voltage sources retain their
constitutive laws; transistor orientation is no longer an admissibility
condition because `mos1TerminalCurrent` selects it dynamically. -/
noncomputable def Mos1BidirectionalSatisfies
    (circuit : Mos1ResolvedCircuit) (state : Mos1CircuitState) : Prop :=
  state.voltage ground = 0 ∧
  (∀ device ∈ circuit.devices.toList,
    match device with
    | .voltageSource source =>
        state.voltage source.positive - state.voltage source.negative =
          (source.voltage : ℝ)
    | .transistor _ => True) ∧
  ∀ target ∈ mos1Nodes circuit, target ≠ ground →
    mos1BidirectionalKcl circuit state target = 0

noncomputable def Mos1BidirectionalComponentSatisfies
    (circuit : Mos1ResolvedCircuit) (driven : List NodeId)
    (state : Mos1CircuitState) : Prop :=
  state.voltage ground = 0 ∧
  (∀ device ∈ circuit.devices.toList,
    match device with
    | .voltageSource source =>
        state.voltage source.positive - state.voltage source.negative =
          (source.voltage : ℝ)
    | .transistor _ => True) ∧
  ∀ target ∈ mos1Nodes circuit,
    target ≠ ground → target ∉ driven →
      mos1BidirectionalKcl circuit state target = 0

private theorem bidirectional_device_current_eq_oriented
    (state : Mos1CircuitState) (target : NodeId) (device : Mos1Device)
    (hlaw : Mos1DeviceLaw state device) :
    mos1BidirectionalDeviceCurrentLeaving state target device =
      mos1DeviceCurrentLeaving state target device := by
  cases device with
  | voltageSource source =>
      rfl
  | transistor transistor =>
      simp only [mos1BidirectionalDeviceCurrentLeaving,
        mos1DeviceCurrentLeaving]
      rw [mos1BidirectionalDrainCurrent_eq_oriented state transistor hlaw]

private theorem bidirectional_kcl_eq_oriented
    {circuit : Mos1ResolvedCircuit} {state : Mos1CircuitState}
    (hlaws : ∀ device ∈ circuit.devices.toList,
      Mos1DeviceLaw state device) (target : NodeId) :
    mos1BidirectionalKcl circuit state target =
      mos1Kcl circuit state target := by
  unfold mos1BidirectionalKcl mos1Kcl
  have hfold :
      ∀ (devices : List Mos1Device),
        (∀ device ∈ devices, Mos1DeviceLaw state device) →
        ∀ initial : ℝ,
          devices.foldl
              (fun total device =>
                total +
                  mos1BidirectionalDeviceCurrentLeaving state target device)
              initial =
            devices.foldl
              (fun total device =>
                total + mos1DeviceCurrentLeaving state target device)
              initial := by
    intro devices hdevices
    induction devices with
    | nil =>
        intro initial
        rfl
    | cons head tail ih =>
        intro initial
        simp only [List.foldl_cons]
        rw [bidirectional_device_current_eq_oriented state target head
          (hdevices head (by simp))]
        exact ih
          (fun device hdevice =>
            hdevices device (by simp [hdevice]))
          _
  exact hfold circuit.devices.toList hlaws 0

/-- Every state admitted by the original oriented semantics is admitted by
the bidirectional semantics with identical KCL equations.  This is the
statement-preservation gate for the existing logic and inverter library. -/
theorem Mos1Satisfies.toBidirectional
    {circuit : Mos1ResolvedCircuit} {state : Mos1CircuitState}
    (h : Mos1Satisfies circuit state) :
    Mos1BidirectionalSatisfies circuit state := by
  refine ⟨h.1, ?_, ?_⟩
  · intro device hdevice
    have hlaw := h.2.1 device hdevice
    cases device <;> simpa [Mos1DeviceLaw] using hlaw
  · intro target htarget hnonground
    rw [bidirectional_kcl_eq_oriented h.2.1 target]
    exact h.2.2 target htarget hnonground

theorem Mos1ComponentSatisfies.toBidirectional
    {circuit : Mos1ResolvedCircuit} {driven : List NodeId}
    {state : Mos1CircuitState}
    (h : Mos1ComponentSatisfies circuit driven state) :
    Mos1BidirectionalComponentSatisfies circuit driven state := by
  refine ⟨h.1, ?_, ?_⟩
  · intro device hdevice
    have hlaw := h.2.1 device hdevice
    cases device <;> simpa [Mos1DeviceLaw] using hlaw
  · intro target htarget hnonground hnotDriven
    rw [bidirectional_kcl_eq_oriented h.2.1 target]
    exact h.2.2 target htarget hnonground hnotDriven

/-- An operating envelope for static CMOS proofs. This is a named theorem
precondition, not an axiom: all observed nodes must remain between the supply
rails. -/
def Mos1WithinSupply
    (circuit : Mos1ResolvedCircuit) (state : Mos1CircuitState) : Prop :=
  ∀ target ∈ mos1Nodes circuit,
    0 ≤ state.voltage target ∧ state.voltage target ≤ 5

/-- Extract KCL at a circuit-checked non-ground node. -/
theorem Mos1Satisfies.kclAt
    {circuit : Mos1ResolvedCircuit} {state : Mos1CircuitState}
    (hsatisfies : Mos1Satisfies circuit state)
    (target : circuit.Node) (hnonground : target.1 ≠ ground) :
    mos1Kcl circuit state target.1 = 0 := by
  exact hsatisfies.2.2 target.1 target.2 hnonground

/-- Extract KCL at a checked internal or output node of an open component. -/
theorem Mos1ComponentSatisfies.kclAt
    {circuit : Mos1ResolvedCircuit} {driven : List NodeId}
    {state : Mos1CircuitState}
    (hsatisfies : Mos1ComponentSatisfies circuit driven state)
    (target : circuit.Node) (hnonground : target.1 ≠ ground)
    (hnotDriven : target.1 ∉ driven) :
    mos1Kcl circuit state target.1 = 0 := by
  exact hsatisfies.2.2 target.1 target.2 hnonground hnotDriven

/-- Extract the supply bounds at a circuit-checked node. -/
theorem Mos1WithinSupply.boundsAt
    {circuit : Mos1ResolvedCircuit} {state : Mos1CircuitState}
    (hbounded : Mos1WithinSupply circuit state)
    (target : circuit.Node) :
    0 ≤ state.voltage target.1 ∧ state.voltage target.1 ≤ 5 := by
  exact hbounded target.1 target.2

/-- Exact voltage associated with a Boolean input or output. -/
def logicVoltage : Bool → ℝ
  | false => 0
  | true => 5

/-- Ideal external voltage drivers for a two-input MOS1 block. -/
def Mos1DrivesTwo (state : Mos1CircuitState)
    (leftNode rightNode : NodeId) (left right : Bool) : Prop :=
  state.voltage ground = 0 ∧
  state.voltage supply = 5 ∧
  state.voltage leftNode = logicVoltage left ∧
  state.voltage rightNode = logicVoltage right

/-- Soundness contract for an extracted two-input block under the MOS1
equations and the explicitly named static-CMOS supply envelope. -/
noncomputable def Mos1BinaryGateContract (circuit : Mos1ResolvedCircuit)
    (leftNode rightNode outputNode : NodeId)
    (operation : Bool → Bool → Bool) : Prop :=
  ∀ left right state,
    Mos1ComponentSatisfies circuit [supply, leftNode, rightNode] state →
    Mos1WithinSupply circuit state →
    Mos1DrivesTwo state leftNode rightNode left right →
    state.voltage outputNode = logicVoltage (operation left right)

/-- Soundness contract for a MOS1 half-adder. -/
noncomputable def Mos1HalfAdderContract (circuit : Mos1ResolvedCircuit)
    (leftNode rightNode sumNode carryNode : NodeId) : Prop :=
  ∀ left right state,
    Mos1ComponentSatisfies circuit [supply, leftNode, rightNode] state →
    Mos1WithinSupply circuit state →
    Mos1DrivesTwo state leftNode rightNode left right →
    state.voltage sumNode = logicVoltage (Bool.xor left right) ∧
      state.voltage carryNode = logicVoltage (Bool.and left right)

/-- One rail-valued observation of a physical MOS1 half-adder instance. -/
noncomputable def Mos1HalfAdderObservation (circuit : Mos1ResolvedCircuit)
    (leftNode rightNode sumNode carryNode : NodeId)
    (left right sum carry : Bool) : Prop :=
  ∃ state,
    Mos1ComponentSatisfies circuit [supply, leftNode, rightNode] state ∧
    Mos1WithinSupply circuit state ∧
    Mos1DrivesTwo state leftNode rightNode left right ∧
    state.voltage sumNode = logicVoltage sum ∧
    state.voltage carryNode = logicVoltage carry

theorem logicVoltage_injective : Function.Injective logicVoltage := by
  intro left right h
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [logicVoltage] at h ⊢

/-- A proved physical half-adder contract refines each observable instance to
the implementation-independent Boolean half-adder behavior. -/
theorem Mos1HalfAdderContract.observation_sound
    {circuit : Mos1ResolvedCircuit} {leftNode rightNode sumNode carryNode : NodeId}
    (hcontract :
      Mos1HalfAdderContract circuit leftNode rightNode sumNode carryNode)
    {left right sum carry : Bool}
    (hobservation :
      Mos1HalfAdderObservation circuit leftNode rightNode sumNode carryNode
        left right sum carry) :
    HalfAdderBehavior left right sum carry := by
  rcases hobservation with
    ⟨state, hsatisfies, hbounded, hdrives, hsum, hcarry⟩
  have houtputs :=
    hcontract left right state hsatisfies hbounded hdrives
  constructor
  · apply logicVoltage_injective
    exact hsum.symm.trans houtputs.1
  · apply logicVoltage_injective
    exact hcarry.symm.trans houtputs.2

/-- One rail-valued observation of a physical MOS1 two-input gate instance.

The two-input analogue of `Mos1HalfAdderObservation`, and it exists for the
same reason: `Mos1BinaryGateContract` is universally quantified over every
state satisfying the component equations, the supply envelope and the input
drivers, so it says nothing at all if no such state exists.  A contract
without a companion observation is a claim that cannot be contradicted by
this deck. -/
noncomputable def Mos1BinaryGateObservation (circuit : Mos1ResolvedCircuit)
    (leftNode rightNode outputNode : NodeId)
    (left right output : Bool) : Prop :=
  ∃ state,
    Mos1ComponentSatisfies circuit [supply, leftNode, rightNode] state ∧
    Mos1WithinSupply circuit state ∧
    Mos1DrivesTwo state leftNode rightNode left right ∧
    state.voltage outputNode = logicVoltage output

/- NO `observation_sound` COMPANION HERE, DELIBERATELY.  The half-adder's
version refines an observation into `HalfAdderBehavior`, a separate
implementation-independent predicate.  A binary gate's corresponding
conclusion would be `output = operation left right`, which is definitionally
trivial once `output` is instantiated -- a lemma that could not fail, added
only for symmetry.  Symmetry is not a consumer.

AND THIS IS A PLAIN BLOCK COMMENT, NOT A DOC COMMENT, ON PURPOSE.  A doc
comment is GRAMMAR: it must attach to a declaration, so it is exactly the
wrong form for marking a declaration's ABSENCE -- it occupies the slot it is
trying to say is empty.  The first draft of this note was a doc comment and
cost a tenure (unexpected token; expected 'lemma').

AND IT CANNOT QUOTE THE DELIMITERS IT DESCRIBES.  Lean block comments NEST,
so writing an opener without its closer -- even as an example inside
backticks -- leaves this comment open and swallows the rest of the file.
The second draft did that and was caught by a depth count before it reached
the queue.  Name the delimiters; never spell them. -/

/-- In the explicit deck profile (`VTO=1`, `LAMBDA=0`, positive beta), a
strongly-on forward channel carrying zero current has zero drain-source
voltage. This is the local fact later used to derive switch behavior. -/
theorem mos1_on_zero_current_iff
    (polarity : LeanModels.Circuit.MosPolarity) (beta vds : ℝ)
    (hbeta : 0 < beta) (hvds0 : 0 ≤ vds) (hvds5 : vds ≤ 5) :
    mos1ForwardCurrent
        { polarity, threshold := 1, beta, lambda := 0 } 5 vds = 0 ↔
      vds = 0 := by
  unfold mos1ForwardCurrent
  simp only [show ¬(5 : ℝ) ≤ 1 by norm_num, if_false]
  by_cases hregion : vds ≤ 5 - 1
  · simp [hregion]
    constructor
    · intro hzero
      have : beta * (4 * vds - vds ^ 2 / 2) = 0 := by
        norm_num at hzero ⊢
        exact hzero
      rcases mul_eq_zero.mp this with hbeta0 | hshape
      · exact False.elim (ne_of_gt hbeta hbeta0)
      · nlinarith
    · rintro rfl
      norm_num
  · simp [hregion]
    constructor
    · intro hzero
      norm_num at hzero
      nlinarith
    · intro hvds
      subst vds
      norm_num at hregion

/-- A strongly-on, forward-oriented MOS1 channel with positive `KP` and
`LAMBDA=0` carries zero current exactly when its terminal voltage drop is
zero. -/
theorem mos1ForwardCurrent_eq_zero_iff
    (polarity : LeanModels.Circuit.MosPolarity) (threshold beta vgs vds : ℝ)
    (hbeta : 0 < beta) (hon : threshold < vgs) (hvds : 0 ≤ vds) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds = 0 ↔
      vds = 0 := by
  unfold mos1ForwardCurrent
  simp only [if_neg (not_le.mpr hon)]
  split
  next htriode =>
    constructor
    · intro hzero
      have hfactor :
          beta * ((vgs - threshold) * vds - vds ^ 2 / 2) = 0 := by
        norm_num at hzero ⊢
        exact hzero
      rcases mul_eq_zero.mp hfactor with hbeta0 | hshape
      · exact False.elim (ne_of_gt hbeta hbeta0)
      · nlinarith
    · rintro rfl
      norm_num
  next hsaturation =>
    constructor
    · intro hzero
      norm_num at hzero
      rcases hzero with hbeta0 | hoverdrive0 <;> linarith
    · rintro rfl
      exact False.elim (hsaturation (by linarith))

end LeanModels.Spice
