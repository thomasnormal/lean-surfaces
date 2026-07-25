/-!
# Structured uncertainty over fabricated instances and runs

Process and mismatch choices live in `instance` and are therefore fixed for
one fabricated circuit.  Time-varying environment, noise, and model
discrepancy live in the run world instead of being resampled pointwise by a
device relation.
-/

namespace LeanModels.Circuit

/-- The semantic world for one run of one fabricated instance. -/
structure RunWorld
    (Instance Environment Noise Discrepancy : Type) where
  fabricated : Instance
  environment : Environment
  noise : Noise
  discrepancy : Discrepancy

/-- A run world without stochastic noise or model discrepancy. -/
def deterministicWorld (fabricated : Instance) (environment : Environment) :
    RunWorld Instance Environment Unit Unit :=
  ⟨fabricated, environment, (), ()⟩

end LeanModels.Circuit
