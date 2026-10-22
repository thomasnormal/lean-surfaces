import LeanModels.Cpp.ScalarTypes
import LeanModels.Cpp.Integral

namespace LeanModels.Cpp.ScalarRung2Tests

open LeanModels.Cpp

def scalarConversionWitness : Bool :=
  (TargetProfile.lp64.format .short matches .ok (.signed 16)) &&
    (scalarWidthBits ScalarProfile.lp64 (.integral .unsignedChar) matches .ok 8) &&
    (integralConvert (.unsigned 8) ⟨.signed 16, -1⟩ matches
      .ok ⟨.unsigned 8, 255⟩) &&
    (integralPromotion TargetProfile.lp64 .short matches .ok .int) &&
    (usualArithmeticType TargetProfile.lp64 .short .unsignedInt matches .ok .unsignedInt)

#guard scalarConversionWitness

theorem scalar_conversion_witness : scalarConversionWitness = true := by
  rfl

#print axioms scalar_conversion_witness

end LeanModels.Cpp.ScalarRung2Tests
