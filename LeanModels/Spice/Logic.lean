/-! Implementation-independent Boolean contracts used by physical blocks. -/

namespace LeanModels.Spice

def HalfAdderBehavior
    (left right sum carry : Bool) : Prop :=
  sum = Bool.xor left right ∧ carry = Bool.and left right

end LeanModels.Spice
