import LeanModels.Circuit.MixedSignal
import Examples.«system-verilog».counter.proof

namespace Examples.«mixed-signal».counter_connect.proof

open LeanModels.Circuit LeanModels.Sv
open Examples.«system-verilog».counter.proof

noncomputable def logicLevels : LogicElectricalLevels :=
  { lowMaximum := 1 / 2
    highMinimum := 9 / 2
    supply := 5 }

theorem logicLevels_valid : logicLevels.Valid := by
  norm_num [LogicElectricalLevels.Valid, logicLevels]

/-- The bridge consumes the actual schedule-quantified counter trace. It
does not define or replace the SystemVerilog scheduler. -/
theorem counter_reset_connect_refines :
    SampledRefinement logicLevels "rst"
      (RailSampleBehavior logicLevels "rst") :=
  railSample_refines logicLevels_valid "rst"

theorem counter_mixed_run_preserves
    {property : TraceProp}
    (hdigital : Models counterDesign property)
    {schedule : ScheduleOracle} {stimulus : List SvState}
    {analog : List AnalogSample}
    (hmixed :
      MixedRuns counterDesign (RailSampleBehavior logicLevels "rst")
        schedule stimulus analog) :
    ∃ digital,
      property counterDesign stimulus digital ∧
      List.Forall₂ (SampleConnects logicLevels "rst") digital analog :=
  mixed_refines_sv_runs hdigital counter_reset_connect_refines hmixed

end Examples.«mixed-signal».counter_connect.proof
