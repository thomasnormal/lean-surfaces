import LeanModels.Cpp.MemberCalls

open Lean LeanModels.Cpp

/- A source-backed syntax census only. It validates the complete probe, walks
   retained AST children, and never executes a call or constructs a receiver. -/

private def jsonObject := Json.mkObj

private partial def memberCalls (raw : Raw) : List Raw :=
  let nested := (((raw.field "inner").bind Raw.array?).getD []).flatMap memberCalls
  if raw.text "kind" == some "CXXMemberCallExpr" then raw :: nested else nested

private def errorName : IntegralMemberCallSyntaxError → String
  | .notMemberCall => "not-member-call"
  | .malformedChildren => "malformed-children"
  | .unsupportedReceiver => "unsupported-receiver"
  | .unsupportedArguments => "unsupported-arguments"
  | .missingMethodHandle => "missing-method-handle"
  | .unsupportedMethod => "unsupported-method"
  | .canonicalMethodMissing => "canonical-method-missing"
  | .canonicalMethodAmbiguous => "canonical-method-ambiguous"
  | .canonicalMethodTargetMissing => "canonical-method-target-missing"
  | .canonicalMethodTargetMismatch => "canonical-method-target-mismatch"
  | .missingReceiverHandle => "missing-receiver-handle"
  | .malformedReceiverType => "malformed-receiver-type"
  | .malformedResultType => "malformed-result-type"
  | .malformedName => "malformed-name"

private def counts (values : List String) : Json :=
  jsonObject (values.eraseDups.map fun value => (value, toJson (values.count value)))

private def argumentShape (raw : Raw) : String :=
  match raw.field "inner" with
  | some (.array (_ :: arguments)) =>
      String.intercalate "," (arguments.map (fun argument => argument.text "kind" |>.getD "<missing>"))
  | _ => "<malformed>"

private partial def baseTree (raw : Raw) : String :=
  let kind := raw.text "kind" |>.getD "<missing>"
  let cast := raw.text "castKind" |>.map (fun value => ":" ++ value) |>.getD ""
  let children := match raw.field "inner" with
    | some (.array values) => values
    | _ => []
  if children.isEmpty then kind ++ cast
  else kind ++ cast ++ "(" ++ String.intercalate "," (children.map baseTree) ++ ")"

private def receiverShape (raw : Raw) : String :=
  match raw.field "inner" with
  | some (.array (member :: _)) =>
      let kind := member.text "kind" |>.getD "<missing>"
      let arrow := match member.field "isArrow" with
        | some (.bool true) => "arrow"
        | some (.bool false) => "dot"
        | _ => "arrow-missing"
      let category := member.text "valueCategory" |>.getD "<missing>"
      let bases := match member.field "inner" with
        | some (.array children) => String.intercalate "," (children.map baseTree)
        | _ => "<missing>"
      s!"{kind}|{arrow}|{category}|{bases}"
  | _ => "<malformed>"

private def emit (value : Json) : IO Unit := IO.println value.compress

private def refuse (stage reason : String) : IO UInt32 := do
  emit (jsonObject [
    ("format", toJson "cpp-member-call-census-1"),
    ("status", toJson "REFUSE"),
    ("stage", toJson stage),
    ("reason", toJson reason),
    ("execution", toJson "not-attempted")])
  return 2

private def census (probe : DeclarationProbe) : IO UInt32 := do
  let calls := memberCalls probe.ast
  let mut admitted := 0
  let mut refusals : List String := []
  let mut argumentShapes : List String := []
  let mut receiverShapes : List String := []
  let mut reports : List Json := []
  for (raw, ordinal) in calls.zipIdx do
    match IntegralMemberCallSyntax.admitResolved probe raw with
    | .ok evidence =>
        admitted := admitted + 1
        reports := jsonObject [
          ("ordinal", toJson ordinal),
          ("status", toJson "ADMIT"),
          ("method", toJson evidence.method.value),
          ("canonical_method", toJson evidence.canonicalMethod.value),
          ("receiver", toJson evidence.receiver.value),
          ("name", toJson evidence.name)] :: reports
    | .error reason =>
        let name := errorName reason
        refusals := name :: refusals
        if reason == .unsupportedArguments then
          argumentShapes := argumentShape raw :: argumentShapes
        if reason == .unsupportedReceiver then
          receiverShapes := receiverShape raw :: receiverShapes
        reports := jsonObject [
          ("ordinal", toJson ordinal),
          ("status", toJson "REFUSE"),
          ("reason", toJson name)] :: reports
  emit (jsonObject [
    ("format", toJson "cpp-member-call-census-1"),
    ("status", toJson "COMPLETE"),
    ("execution", toJson "not-attempted"),
    ("counting_basis", toJson "every retained CXXMemberCallExpr inner-tree occurrence"),
    ("call_sites", toJson calls.length),
    ("admitted", toJson admitted),
    ("refused", toJson refusals.length),
    ("first_refusals", counts refusals),
    ("unsupported_argument_shapes", counts argumentShapes),
    ("unsupported_receiver_shapes", counts receiverShapes),
    ("calls", toJson reports.reverse)])
  return 0

def main (arguments : List String) : IO UInt32 := do
  let [input] := arguments
    | IO.eprintln "usage: lake env lean --run extractors/cpp/census_member_calls.lean PROBE"; return 1
  try
    let before ← (System.FilePath.mk input).metadata
    unless before.type == .file do
      return ← refuse "input-io" "probe must be a regular file"
    if before.byteSize > 128 * 1024 * 1024 then
      return ← refuse "input-byte-bound" "probe exceeds 128 MiB runtime census bound"
    let bytes ← IO.FS.readBinFile input
    let after ← (System.FilePath.mk input).metadata
    unless before.byteSize == after.byteSize && before.modified == after.modified &&
        after.byteSize.toNat == bytes.size do
      return ← refuse "input-read" "probe changed while reading"
    let some contents := String.fromUTF8? bytes
      | return ← refuse "probe-format" "invalid UTF-8"
    let probe ← match parseDeclarationProbeString contents with
      | .ok probe => pure probe
      | .error reason => return ← refuse "probe-format" reason
    census probe
  catch error => refuse "input-io" error.toString
