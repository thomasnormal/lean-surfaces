import LeanModels.Cpp.Capture

namespace LeanModels.Cpp.CaptureTests

#guard parseCaptureRawString "-0" matches .ok (.number "-0")
#guard parseCaptureRawString "9007199254740993" matches
  .ok (.number "9007199254740993")
#guard parseCaptureRawString "0.125" matches .ok (.number "0.125")
#guard parseCaptureRawString "1.25e+02" matches .ok (.number "1.25e+02")
#guard parseCaptureRawString "-1E-02" matches .ok (.number "-1E-02")
#guard parseCaptureRawString "\"\\uD83D\\uDE00\"" matches .ok (.string "😀")
#guard parseCaptureRawString "{\"outer\":[{\"x\":1,\"x\":2}]}" matches .error _
#guard parseCaptureRawString "{\"x\":1,\"\\u0078\":2}" matches .error _
#guard parseCaptureRawString "{\"x\":1,\"nested\":{\"x\":2}}" matches .ok _
#guard parseCaptureRawString "\"\\ud800\"" matches .error _
#guard parseCaptureRawString "\"\\udfff\"" matches .error _
#guard parseCaptureRawString "\"\\ud800x\"" matches .error _
#guard parseCaptureRawString "\"\\ud800\\u0061\"" matches .error _
#guard ["NaN", "Infinity", "-Infinity", "01", "-01", "+1", ".5", "1.",
  "1e", "1e+", "null false", "[1,]", "{\"x\":1,}"].all
  fun contents => match parseCaptureRawString contents with
    | .error _ => true
    | .ok _ => false
#guard parseCaptureReceiptString "null" matches .error _
#guard parseCaptureReceiptString "[]" matches .error _
#guard parseCaptureReceiptString "{}" matches .error _
#guard parseCaptureReceiptString "{\"schema_version\":\"cpp-probe-capture-0.1\"}"
  matches .error _
#guard validateCaptureRaw (.number "1.250e+02") matches .ok _
#guard validateCaptureRaw (.object [("elapsed_seconds", .number "1e+")]) matches .error _
#guard validateCaptureRaw (.array [.number "01"]) matches .error _
#guard validateCaptureRaw (.object [("outer", .object [
  ("key", .number "1"), ("key", .number "2")])]) matches .error _
#guard captureNat (.object [("byte_count", .number "0")]) "byte_count" matches .ok 0
#guard captureNat (.object [("byte_count", .number "-0")]) "byte_count" matches .error _
#guard captureNat (.object [("byte_count", .number "1e0")]) "byte_count" matches .error _

end LeanModels.Cpp.CaptureTests
