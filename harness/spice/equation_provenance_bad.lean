import LeanModels.Circuit.Surface

namespace LeanModels.Circuit.EquationProvenanceAdversarial

def ForbiddenSpecification (_world _boundary _internal : Unit) : Prop :=
  True

def physicalProgram : EquationProgram Unit Unit Unit Unit where
  origin := fun _ => .deviceLaw "test resistor"
  equation := fun _ _ _ _ => True

#equation_guard physicalProgram forbids [ForbiddenSpecification]

def bakedProgram : EquationProgram Unit Unit Unit Unit where
  origin := fun _ => .deviceLaw "dishonestly tagged equation"
  equation := fun _ world boundary internal =>
    ForbiddenSpecification world boundary internal

-- This command must fail. The Python harness checks the diagnostic.
#equation_guard bakedProgram forbids [ForbiddenSpecification]

end LeanModels.Circuit.EquationProvenanceAdversarial
