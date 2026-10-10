import LeanModels.Cpp.Evidence

namespace LeanModels.Cpp

structure CapturePayload where
  key : String
  path : String
  byteCount : Nat
  sha256 : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure CaptureReceipt where
  raw : Raw
  payloads : List CapturePayload
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure DeclarationCapture where
  receipt : CaptureReceipt
  probe : DeclarationProbe
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def captureObject (raw : Raw) : Except String (List (String × Raw)) :=
  match raw with
  | .object fields => .ok fields
  | _ => .error "capture: expected object"

def captureNonempty (raw : Raw) (name : String) : Except String String := do
  let value ← evidenceText raw name
  if value.isEmpty || value.toList.contains '\x00' then
    throw s!"capture field {name}: expected nonempty NUL-free string"
  return value

def captureAbsolute (raw : Raw) (name : String) : Except String String := do
  let value ← captureNonempty raw name
  unless value.startsWith "/" do throw s!"capture field {name}: expected absolute path"
  return value

def captureHash (raw : Raw) : Except String String := do
  let value ← evidenceText raw "sha256"
  unless value.length == 64 && value.toList.all (fun character =>
      ('0' ≤ character && character ≤ '9') || ('a' ≤ character && character ≤ 'f')) do
    throw "capture: expected lowercase SHA-256 digest"
  return value

def captureNat (raw : Raw) (name : String) : Except String Nat := do
  match ← evidenceField raw name with
  | .number token =>
    unless !token.isEmpty && token.toList.all (fun character =>
        '0' ≤ character && character ≤ '9') do
      throw s!"capture field {name}: expected unsigned integer token"
    match token.toNat? with
    | some value => return value
    | none => throw s!"capture field {name}: invalid integer"
  | _ => throw s!"capture field {name}: expected integer token"

def captureNumber (raw : Raw) (name : String) (positive : Bool := false) :
    Except String String := do
  match ← evidenceField raw name with
  | .number token =>
    if token.startsWith "-" then throw s!"capture field {name}: expected nonnegative number"
    let mantissa := token.toList.takeWhile (fun character => character != 'e' && character != 'E')
    if positive && !mantissa.any (fun character => '1' ≤ character && character ≤ '9') then
      throw s!"capture field {name}: expected positive number"
    return token
  | _ => throw s!"capture field {name}: expected numeric token"

def captureBool (raw : Raw) (name : String) (expected : Bool) : Except String Unit := do
  unless (← evidenceBool raw name) == expected do
    throw s!"capture field {name}: inconsistent Boolean observation"

def captureNull (raw : Raw) (name : String) : Except String Unit := do
  unless (← evidenceField raw name) == .null do
    throw s!"capture field {name}: expected null"

def captureStrings (raw : Raw) (name : String) : Except String (List String) := do
  let values ← evidenceArray raw name
  values.mapM fun value => match value with
    | .string text =>
      if text.toList.contains '\x00' then throw s!"capture field {name}: NUL in string"
      else return text
    | _ => throw s!"capture field {name}: expected string array"

def captureArgv (raw : Raw) (name : String := "argv") : Except String (List String) := do
  let values ← captureStrings raw name
  if values.isEmpty then throw s!"capture field {name}: empty command"
  return values

def captureBasename (value : String) : Except String Unit := do
  if value.isEmpty || value == "." || value == ".." ||
      value.toList.any (fun character => character == '/' || character == '\\' || character == '\x00') then
    throw "capture: unsafe bundle-relative payload basename"

def parseCapturePayload (key : String) (raw : Raw) : Except String CapturePayload := do
  let _ ← captureObject raw
  let path ← captureNonempty raw "path"
  captureBasename path
  return {key, path, byteCount := ← captureNat raw "byte_count", sha256 := ← captureHash raw}

def capturePayloads (raw : Raw) : Except String (List CapturePayload) := do
  let fields ← captureObject (← evidenceField raw "payloads")
  let payloads ← fields.mapM fun (key, value) => parseCapturePayload key value
  let mut paths : List String := []
  for payload in payloads do
    if paths.contains payload.path then throw "capture: duplicate bound payload path"
    paths := payload.path :: paths
  for (key, path) in [("probe", "probe.json"), ("stderr", "stderr.txt"),
      ("dependencies", "inputs.d"), ("discovery_dependencies", "discovery.d")] do
    unless payloads.any (fun payload => payload.key == key && payload.path == path) do
      throw s!"capture: missing or misnamed required payload {key}"
  return payloads

def captureImage (raw : Raw) : Except String Unit := do
  let _ ← captureObject raw
  let _ ← captureAbsolute raw "path"
  let _ ← captureAbsolute raw "resolved_path"
  let _ ← captureHash raw
  let _ ← captureNat raw "byte_count"

def captureImages (raw : Raw) (name : String) : Except String Unit := do
  let values ← evidenceArray raw name
  let mut paths : List String := []
  for value in values do
    captureImage value
    let path ← evidenceText value "resolved_path"
    if paths.contains path then throw s!"capture field {name}: duplicate image path"
    paths := path :: paths

def captureProducer (raw : Raw) : Except String Unit := do
  requireEvidenceText raw "version" "leancpp-probe-capture-0.1"
  captureImage (← evidenceField raw "interpreter")
  captureImages raw "sources"
  unless (← evidenceArray raw "sources").length == 3 do
    throw "capture: expected three producer source-image observations"

def captureEnvironment (raw : Raw) : Except String Unit := do
  let fields ← captureObject raw
  for (key, value) in fields do
    unless ["PATH", "LC_ALL", "TZ", "CPATH", "CPLUS_INCLUDE_PATH", "C_INCLUDE_PATH",
        "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "SOURCE_DATE_EPOCH"].contains key do
      throw s!"capture: environment key outside declared policy: {key}"
    match value with
    | .string text =>
      if text.toList.contains '\x00' then throw "capture: NUL in environment value"
    | _ => throw "capture: environment value must be a string"
  requireEvidenceText raw "LC_ALL" "C"
  requireEvidenceText raw "TZ" "UTC"
  requireEvidenceText raw "PATH" "/bin:/usr/bin"
  let _ ← evidenceText raw "SOURCE_DATE_EPOCH"

def captureLaunch (raw : Raw) (frontend : Raw) : Except String Unit := do
  let executable ← captureAbsolute raw "executable"
  let resolved ← captureAbsolute raw "resolved_executable"
  let compiler ← evidenceField frontend "compiler"
  unless executable == (← evidenceText compiler "path") &&
      resolved == (← evidenceText compiler "resolved_path") do
    throw "capture: launch/compiler image disagreement"
  let argv ← captureArgv raw
  unless argv.head? == some executable do throw "capture: launch executable/argv disagreement"
  let _ ← captureAbsolute raw "cwd"
  requireEvidenceText raw "environment_policy" "controlled-clang-environment-0.1"
  captureEnvironment (← evidenceField raw "environment")

def captureResourceEntry (raw : Raw) : Except String Unit := do
  let path ← captureNonempty raw "path"
  if path.startsWith "/" || (path.splitOn "/").any (fun part =>
      part.isEmpty || part == "." || part == "..") then
    throw "capture: unsafe relative resource-tree path"
  match ← evidenceText raw "kind" with
  | "file" =>
    let _ ← captureHash raw
    let _ ← captureNat raw "byte_count"
    pure ()
  | "directory" => pure ()
  | "symlink" =>
    let _ ← evidenceText raw "target"
    pure ()
  | _ => throw "capture: unsupported resource-tree entry kind"

def captureResource (raw : Raw) : Except String Unit := do
  let _ ← captureAbsolute raw "path"
  let _ ← captureAbsolute raw "resolved_path"
  requireEvidenceText raw "scope" "observed-tree-without-symlink-directory-traversal"
  requireEvidenceText raw "closure" "unestablished"
  let before ← evidenceArray raw "before"
  let after ← evidenceArray raw "after"
  unless before == after do throw "capture: resource-tree before/after disagreement"
  let mut paths : List String := []
  for entry in before do
    captureResourceEntry entry
    let path ← evidenceText entry "path"
    if paths.contains path then throw "capture: duplicate resource-tree path"
    paths := path :: paths

def captureFrontend (raw : Raw) : Except String Unit := do
  captureImage (← evidenceField raw "compiler")
  captureImage (← evidenceField raw "plugin")
  captureImages raw "declared_runtime_libraries"
  captureResource (← evidenceField raw "resource_directory")
  requireEvidenceText raw "compiled_frontend" "21.1.8"
  requireEvidenceText raw "llvm_headers" "21.1.8"
  requireEvidenceText raw "image_closure" "unestablished"
  for name in ["version", "runtime_frontend"] do
    let version ← captureNonempty raw name
    unless version == "clang version 21.1.8" || version.startsWith "clang version 21.1.8 " ||
        (name == "version" && version.startsWith "clang version 21.1.8\n") do
      throw s!"capture: unsupported frontend {name}"
  let _ ← captureNonempty raw "target"
  let _ ← evidenceArray raw "processes"

def captureDependency (raw : Raw) : Except String (String × String) := do
  return (← captureAbsolute raw "path", ← captureHash raw)

def captureDependencies (raw : Raw) (name : String) : Except String (List (String × String)) := do
  let dependencies ← (← evidenceArray raw name).mapM captureDependency
  let mut paths : List String := []
  for (path, _) in dependencies do
    if paths.contains path then throw s!"capture field {name}: duplicate dependency path"
    paths := path :: paths
  return dependencies

def capturePositiveInputs (raw source : Raw) (payloads : List CapturePayload) :
    Except String Unit := do
  let before ← captureDependencies raw "before"
  let after ← captureDependencies raw "after"
  let discovered ← captureStrings raw "discovery_manifest"
  let actual ← captureStrings raw "actual_manifest"
  unless !before.isEmpty && before == after && discovered == actual &&
      before.map Prod.fst == discovered do
    throw "capture: positive-input manifests disagree"
  captureBool raw "paths_equal" true
  captureBool raw "hashes_equal" true
  let _ ← captureArgv raw "discovery_command"
  let sourcePath ← captureAbsolute source "path"
  let sourceHash ← captureHash source
  let _ ← captureNonempty source "logical_command_path"
  unless before.contains (sourcePath, sourceHash) do
    throw "capture: main source/hash absent from positive inputs"
  let binding ← parseCapturePayload "discovery_dependencies" (← evidenceField raw "discovery_payload")
  unless payloads.contains binding do throw "capture: discovery payload binding disagreement"

def captureBounds (raw : Raw) : Except String Unit := do
  let _ ← captureNumber raw "timeout_seconds" true
  unless (← captureNat raw "memory_mib") > 0 do throw "capture: nonpositive memory limit"
  unless (← captureNat raw "file_size_bytes") == 4294967296 do
    throw "capture: unsupported per-file size limit"
  requireEvidenceText raw "scope" "frontend-subprocess-only"
  requireEvidenceText raw "memory_scope" "inherited-per-process-address-space-limit"
  requireEvidenceText raw "file_size_scope" "inherited-per-file-size-limit"

def captureProcess (raw : Raw) (payloads : List CapturePayload) : Except String Unit := do
  let _ ← captureArgv raw
  let _ ← captureAbsolute raw "cwd"
  captureBool raw "launched" true
  unless (← captureNat raw "exit_status") == 0 do throw "capture: unsuccessful subprocess"
  captureNull raw "signal"
  captureNull raw "observation_error"
  captureBool raw "timed_out" false
  let _ ← captureNumber raw "elapsed_seconds"
  let _ ← captureNat raw "max_rss_kib"
  requireEvidenceText raw "measurement_scope"
    "linux-wait4-child-resource-usage-including-reaped-descendants"
  captureBounds (← evidenceField raw "bounds")
  for name in ["stdout", "stderr"] do
    let path ← captureNonempty raw name
    captureBasename path
    unless payloads.any (fun payload => payload.path == path) do
      throw s!"capture: subprocess {name} has no payload binding"

def captureProcessLinks (processes : List Raw) (launch frontend inputs : Raw) :
    Except String Unit := do
  unless processes.length == 6 do throw "capture: expected six observed subprocesses"
  unless (← evidenceArray frontend "processes") == processes.take 4 do
    throw "capture: frontend/completion subprocess disagreement"
  let labels := [("version.stdout", "version.stderr"), ("target.stdout", "target.stderr"),
    ("resource.stdout", "resource.stderr"), ("predefines.stdout", "predefines.stderr"),
    ("discovery.stdout", "discovery.stderr"), ("probe.json", "stderr.txt")]
  for (process, (stdout, stderr)) in processes.zip labels do
    requireEvidenceText process "stdout" stdout
    requireEvidenceText process "stderr" stderr
    unless (← evidenceText process "cwd") == (← evidenceText launch "cwd") do
      throw "capture: subprocess cwd disagreement"
    let argv ← captureArgv process
    unless argv.take 2 == [← evidenceText launch "executable", "--no-default-config"] do
      throw "capture: subprocess executable/default-config disagreement"
  match processes[4]?, processes[5]? with
  | some discovery, some probe =>
    unless (← captureArgv discovery) == (← captureArgv inputs "discovery_command") do
      throw "capture: discovery command disagreement"
    unless (← captureArgv probe) == (← captureArgv launch) do
      throw "capture: probe launch command disagreement"
  | _, _ => throw "capture: missing discovery/probe subprocess"

def captureCompletion (raw launch frontend inputs : Raw) (payloads : List CapturePayload) :
    Except String Unit := do
  unless (← captureNat raw "exit_status") == 0 do throw "capture: unsuccessful completion"
  captureBool raw "timed_out" false
  requireEvidenceText raw "bounds_scope" "frontend-subprocesses-only"
  let processes ← evidenceArray raw "processes"
  for process in processes do captureProcess process payloads
  let bounds ← processes.mapM (fun process => evidenceField process "bounds")
  unless bounds.all (fun bound => some bound == bounds.head?) do
    throw "capture: subprocess resource bounds disagree"
  captureProcessLinks processes launch frontend inputs

def captureClosureLimits (raw : Raw) : Except String Unit := do
  for name in ["input_world", "runtime_image_closure", "effective_cc1", "ordinary_source_profile"] do
    requireEvidenceText raw name "unestablished"
  requireEvidenceText raw "guarantee" "observed-positive-input-stability"
  captureBool raw "semantic_admission" false
  captureBool raw "runtime_admission" false

def parseCaptureReceipt (raw : Raw) : Except String CaptureReceipt := do
  validateCaptureRaw raw
  let _ ← captureObject raw
  requireEvidenceText raw "schema_version" "cpp-probe-capture-0.1"
  requireEvidenceText raw "profile_id" "cpp23-clang-probe-capture-0.1"
  requireEvidenceText raw "edition" "c++23"
  requireEvidenceText raw "probe_schema" "cpp-canonical-probe-0.3"
  let payloads ← capturePayloads raw
  captureProducer (← evidenceField raw "producer")
  let frontend ← evidenceField raw "frontend"
  captureFrontend frontend
  let launch ← evidenceField raw "launch"
  captureLaunch launch frontend
  let source ← evidenceField raw "source"
  unless (← captureArgv launch).getLast? == some (← evidenceText source "logical_command_path") do
    throw "capture: logical source/probe command disagreement"
  let inputs ← evidenceField raw "positive_inputs"
  capturePositiveInputs inputs source payloads
  captureCompletion (← evidenceField raw "completion") launch frontend inputs payloads
  captureClosureLimits (← evidenceField raw "closure_limits")
  return {raw, payloads}

def parseCaptureReceiptString (contents : String) : Except String CaptureReceipt := do
  parseCaptureReceipt (← parseCaptureRawString contents)

def validateCaptureProbe (receipt : CaptureReceipt) (probe : DeclarationProbe) :
    Except String Unit := do
  let frontend ← evidenceField receipt.raw "frontend"
  for name in ["compiled_frontend", "llvm_headers", "runtime_frontend"] do
    unless (← evidenceText frontend name) == (← evidenceText probe.metadata name) do
      throw s!"capture: receipt/probe {name} disagreement"

end LeanModels.Cpp
