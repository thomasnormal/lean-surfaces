import LeanModels.Circuit.AC
import LeanModels.Spice.LoadedRC

/-!
# Loaded-RC operating-point linearization

The driven residual is the same KCL relation used by the loaded-RC transient
model, with supply voltage exposed as the input. Because the circuit is
linear, its perturbation relation is exact at every operating point.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

noncomputable def loadedRCDrivenDAE :
    DrivenScalarDAE LoadedRCInstance where
  residual parameter _time input output derivative :=
    parameter.capacitance * derivative +
      (output - input) / parameter.seriesResistance +
      output / parameter.loadResistance = 0

noncomputable def loadedRCLinearResidual
    (parameter : LoadedRCInstance) : ScalarLinearResidual ℝ :=
  { derivativeCoefficient := parameter.capacitance
    valueCoefficient :=
      1 / parameter.seriesResistance + 1 / parameter.loadResistance
    inputCoefficient := -(1 / parameter.seriesResistance) }

theorem loadedRC_exact_linearization
    (parameter : LoadedRCInstance)
    (hseries : parameter.seriesResistance ≠ 0)
    (hload : parameter.loadResistance ≠ 0)
    (hsum :
      parameter.seriesResistance + parameter.loadResistance ≠ 0)
    (input₀ : ℝ) :
    ExactLinearizationAt loadedRCDrivenDAE parameter input₀
      (input₀ * parameter.loadResistance /
        (parameter.seriesResistance + parameter.loadResistance))
      (loadedRCLinearResidual parameter) := by
  constructor
  · simp only [loadedRCDrivenDAE]
    field_simp [hseries, hload, hsum]
    ring
  · intro time inputDelta outputDelta outputDerivative
    have hbase :
        (input₀ * parameter.loadResistance /
              (parameter.seriesResistance + parameter.loadResistance) -
            input₀) /
            parameter.seriesResistance +
          (input₀ * parameter.loadResistance /
              (parameter.seriesResistance + parameter.loadResistance)) /
            parameter.loadResistance = 0 := by
      field_simp [hseries, hload, hsum]
      ring
    change
      (parameter.capacitance * outputDerivative +
          ((input₀ * parameter.loadResistance /
                (parameter.seriesResistance +
                  parameter.loadResistance) +
              outputDelta) -
            (input₀ + inputDelta)) /
              parameter.seriesResistance +
          (input₀ * parameter.loadResistance /
                (parameter.seriesResistance +
                  parameter.loadResistance) +
              outputDelta) /
            parameter.loadResistance = 0) ↔
        (parameter.capacitance * outputDerivative +
          (1 / parameter.seriesResistance +
              1 / parameter.loadResistance) * outputDelta +
          -(1 / parameter.seriesResistance) * inputDelta = 0)
    have hequations :
        parameter.capacitance * outputDerivative +
            ((input₀ * parameter.loadResistance /
                  (parameter.seriesResistance +
                    parameter.loadResistance) +
                outputDelta) -
              (input₀ + inputDelta)) /
                parameter.seriesResistance +
            (input₀ * parameter.loadResistance /
                  (parameter.seriesResistance +
                    parameter.loadResistance) +
                outputDelta) /
              parameter.loadResistance =
          parameter.capacitance * outputDerivative +
            (1 / parameter.seriesResistance +
                1 / parameter.loadResistance) * outputDelta +
            -(1 / parameter.seriesResistance) * inputDelta := by
      calc
        _ =
            ((input₀ * parameter.loadResistance /
                  (parameter.seriesResistance +
                    parameter.loadResistance) -
                input₀) /
                parameter.seriesResistance +
              (input₀ * parameter.loadResistance /
                  (parameter.seriesResistance +
                    parameter.loadResistance)) /
                parameter.loadResistance) +
              (parameter.capacitance * outputDerivative +
                (1 / parameter.seriesResistance +
                    1 / parameter.loadResistance) * outputDelta +
                -(1 / parameter.seriesResistance) * inputDelta) := by ring
        _ = _ := by rw [hbase]; ring
    rw [hequations]

end LeanModels.Spice
