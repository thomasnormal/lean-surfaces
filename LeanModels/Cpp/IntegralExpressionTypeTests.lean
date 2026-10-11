import LeanModels.Cpp.IntegralExpressionTypes

namespace LeanModels.Cpp.IntegralExpressionTypeTests

#guard integralUnaryType .lp64 .plus .short matches .ok .int
#guard integralUnaryType .lp64 .minus .unsignedShort matches .ok .int
#guard integralUnaryType .lp64 .bitNot .char matches .ok .int
#guard integralUnaryType .lp64 .logicalNot .long matches .ok .boolean

#guard integralBinaryType .lp64 .add .short .short matches .ok .int
#guard integralBinaryType .lp64 .multiply .int .unsignedInt matches .ok .unsignedInt
#guard integralBinaryType .lp64 .equal .long .longLong matches .ok .boolean
#guard integralBinaryType .lp64 .less .unsignedLong .long matches .ok .boolean
#guard integralBinaryType .lp64 .shiftLeft .short .longLong matches .ok .int
#guard integralBinaryType .lp64 .shiftRight .unsignedShort .int matches .ok .int

def narrowIntProfile : TargetProfile := {TargetProfile.lp64 with intWidth := 16}

#guard integralUnaryType narrowIntProfile .plus .unsignedShort matches .ok .unsignedInt
#guard integralBinaryType narrowIntProfile .shiftLeft .unsignedShort .int matches .ok .unsignedInt
#guard integralBinaryType narrowIntProfile .equal .short .short matches .ok .boolean

#guard inferIntegralBinary .lp64 .add .short .short matches
  .ok {type := .scalar (.integral .int), category := .prvalue}
#guard inferIntegralUnary .lp64 .logicalNot .int matches
  .ok {type := .scalar (.integral .boolean), category := .prvalue}
#guard integralBinaryType .lp64 .add .boolean .boolean matches .ok .int
#guard integralBinaryType narrowIntProfile .add .int .int matches .ok .int

def invalidProfile : TargetProfile := {TargetProfile.lp64 with intWidth := 8}

#guard integralUnaryType invalidProfile .plus .int matches .error .invalidProfile
#guard integralBinaryType invalidProfile .add .int .int matches .error .invalidProfile
#guard integralBinaryType invalidProfile .shiftLeft .int .int matches .error .invalidProfile

end LeanModels.Cpp.IntegralExpressionTypeTests
