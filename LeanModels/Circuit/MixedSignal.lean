import LeanModels.Circuit.Time
import LeanModels.Sv.Surface
import Mathlib.Tactic

/-!
# Sampled mixed-signal connection to the SV scheduler

Continuous settling remains a circuit theorem. This module only states the
typed boundary contract at a superdense sample time and composes it with an
actual all-schedule `LeanModels.Sv.Runs` trace.
-/

namespace LeanModels.Circuit

open LeanModels.Sv

structure LogicElectricalLevels where
  lowMaximum : ℝ
  highMinimum : ℝ
  supply : ℝ
deriving Inhabited

def LogicElectricalLevels.Valid
    (levels : LogicElectricalLevels) : Prop :=
  0 ≤ levels.lowMaximum ∧
  levels.lowMaximum < levels.highMinimum ∧
  levels.highMinimum ≤ levels.supply

noncomputable def logicDrive
    (levels : LogicElectricalLevels) (bit : Bool) : ℝ :=
  if bit then levels.supply else 0

def ElectricalToLogic
    (levels : LogicElectricalLevels) (voltage : ℝ) (bit : Bool) : Prop :=
  if bit then levels.highMinimum ≤ voltage
  else voltage ≤ levels.lowMaximum

theorem logicDrive_decodes
    {levels : LogicElectricalLevels} (hvalid : levels.Valid) (bit : Bool) :
    ElectricalToLogic levels (logicDrive levels bit) bit := by
  rcases bit with _ | _
  · simpa [ElectricalToLogic, logicDrive] using hvalid.1
  · simpa [ElectricalToLogic, logicDrive] using hvalid.2.2

structure AnalogSample where
  sampleTime : HybridTime
  voltage : ℝ

def SvStateCarriesBool
    (state : SvState) (signal : String) (bit : Bool) : Prop :=
  SvState.lookup state signal =
    some (LVec.ofNat 1 (if bit then 1 else 0))

/-- One settled analog sample decodes to the same bit as a scalar SV
snapshot. The analog proof owns the fact that the sample was taken after
the required settling deadline. -/
def SampleConnects
    (levels : LogicElectricalLevels) (signal : String)
    (state : SvState) (sample : AnalogSample) : Prop :=
  ∃ bit,
    SvStateCarriesBool state signal bit ∧
    ElectricalToLogic levels sample.voltage bit

/-- A mixed behavior relates a completed digital trace to analog samples.
This is where a transient DAE model or a future connect-module interpretation
is plugged in. -/
abbrev MixedBehavior :=
  List SvState → List AnalogSample → Prop

def SampledRefinement
    (levels : LogicElectricalLevels) (signal : String)
    (behavior : MixedBehavior) : Prop :=
  ∀ digital analog, behavior digital analog →
    List.Forall₂ (SampleConnects levels signal) digital analog

def MixedRuns
    (design : Design) (behavior : MixedBehavior)
    (schedule : ScheduleOracle) (stimulus : List SvState)
    (analog : List AnalogSample) : Prop :=
  ∃ digital,
    Runs design schedule stimulus digital ∧ behavior digital analog

/-- An SV property and a sampled analog-refinement certificate compose
without introducing a second digital scheduler. -/
theorem mixed_refines_sv_runs
    {design : Design} {property : TraceProp}
    {levels : LogicElectricalLevels} {signal : String}
    {behavior : MixedBehavior}
    (hdigital : Models design property)
    (hrefinement : SampledRefinement levels signal behavior)
    {schedule : ScheduleOracle} {stimulus : List SvState}
    {analog : List AnalogSample}
    (hmixed : MixedRuns design behavior schedule stimulus analog) :
    ∃ digital,
      property design stimulus digital ∧
      List.Forall₂ (SampleConnects levels signal) digital analog := by
  rcases hmixed with ⟨digital, hrun, hbehavior⟩
  exact ⟨digital, hdigital schedule stimulus digital hrun,
    hrefinement digital analog hbehavior⟩

/-- Executable rail-driving connect behavior used to validate the abstract
connection rule. Production analog blocks normally replace equality with a
proved settling band. -/
noncomputable def RailSampleBehavior
    (levels : LogicElectricalLevels) (signal : String) :
    MixedBehavior :=
  List.Forall₂ fun state sample =>
    ∃ bit,
      SvStateCarriesBool state signal bit ∧
      sample.voltage = logicDrive levels bit

theorem railSample_refines
    {levels : LogicElectricalLevels} (hvalid : levels.Valid)
    (signal : String) :
    SampledRefinement levels signal
      (RailSampleBehavior levels signal) := by
  intro digital analog hbehavior
  apply hbehavior.imp
  intro state sample hsample
  rcases hsample with ⟨bit, hstate, hvoltage⟩
  exact ⟨bit, hstate, hvoltage.symm ▸ logicDrive_decodes hvalid bit⟩

end LeanModels.Circuit
