import LeanModels.Python.Surface
import Examples.«mixed-signal».counter_connect.proof

open LeanModels.Circuit LeanModels.Sv
open Examples.«system-verilog».counter.proof
open Examples.«mixed-signal».counter_connect.proof

theorem counter_reset_connect_refines :
    SampledRefinement logicLevels "rst"
      (RailSampleBehavior logicLevels "rst") := by proofs

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
      List.Forall₂ (SampleConnects logicLevels "rst") digital analog := by proofs

#print axioms counter_reset_connect_refines
#print axioms counter_mixed_run_preserves
