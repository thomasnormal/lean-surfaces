import LeanModels.Cpp.Capture

namespace LeanModels.Cpp

/--
Literal capture loading trusts Lean's filesystem/process interfaces and the executable
`/usr/bin/sha256sum`. It hashes the same in-memory bytes that the probe parser receives,
not a separately reopened filename. The named hashing program is not a kernel proof of
SHA-256, and digest agreement does not authenticate the capture producer or its claims.

The bundle must be a quiescent directory owned by the caller. Ordinary symlink and path
escapes are refused before and after reads; these checks are not an adversarial concurrent
filesystem-mutation guarantee. Source files and toolchain images referenced by the receipt
need not remain installed. No translation, identity, ISO, or execution admission is added.
Bundle paths must end in an ordinary basename, without trailing separators, `.` or `..`,
except for the exact root path `/`. Ancestor aliases are resolved to a canonical directory.
-/
private def captureLoadBoundary : String :=
  "Literal observational capture; exact-byte binding trusts /usr/bin/sha256sum and IO; no authenticated provenance, semantic or execution admission."

private def captureIOExcept (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| .userError error

private def captureText (label : String) (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => throw <| .userError s!"{label}: invalid UTF-8"

private def captureLoadBasename (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." &&
    name.toList.all (fun character =>
      character != '/' && character != '\\' && character != '\x00')

private def captureDirectory (path : System.FilePath) : IO System.FilePath := do
  unless path.toString == "/" || captureLoadBasename (path.fileName.getD "") do
    throw <| .userError "capture bundle path requires an ordinary final basename or exact '/'"
  unless (← path.symlinkMetadata).type == .dir do
    throw <| .userError "capture bundle must be a directory, not a symlink"
  let directory ← IO.FS.realPath path
  unless (← directory.symlinkMetadata).type == .dir do
    throw <| .userError "capture bundle directory changed during resolution"
  return directory

private def captureFileMetadata (directory : System.FilePath) (name : String) :
    IO IO.FS.Metadata := do
  unless captureLoadBasename name do
    throw <| .userError s!"unsafe capture payload path: {name}"
  let path := directory / name
  let metadata ← path.symlinkMetadata
  unless metadata.type == .file do
    throw <| .userError s!"capture payload must be an ordinary file, not a symlink: {name}"
  unless (← IO.FS.realPath path) == path do
    throw <| .userError s!"capture payload escapes its bundle directory: {name}"
  return metadata

private def captureReadBytes (directory : System.FilePath) (name : String) :
    IO ByteArray := do
  let before ← captureFileMetadata directory name
  let bytes ← IO.FS.readBinFile (directory / name)
  let after ← captureFileMetadata directory name
  unless before.byteSize == after.byteSize && before.modified == after.modified &&
      after.byteSize.toNat == bytes.size do
    throw <| .userError s!"capture payload changed during read: {name}"
  return bytes

private def captureSha256 (bytes : ByteArray) : IO String := do
  let child ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := "/usr/bin/sha256sum", args := #["--binary", "-"],
      stdin := .piped, stdout := .piped, stderr := .piped,
      inheritEnv := false, env := #[("LC_ALL", some "C")] }).takeStdin
    stdin.write bytes
    stdin.flush
    pure child
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  unless exitCode == 0 && stderr.isEmpty do
    throw <| .userError s!"/usr/bin/sha256sum failed with exit {exitCode}: {stderr}"
  let digest := String.ofList (stdout.toList.take 64)
  unless digest.length == 64 && digest.toList.all (fun character =>
      ('0' ≤ character && character ≤ '9') || ('a' ≤ character && character ≤ 'f')) &&
      stdout == digest ++ " *-\n" do
    throw <| .userError "unexpected /usr/bin/sha256sum output"
  return digest

private def captureRequireCore (receipt : CaptureReceipt) : Except String Unit := do
  for key in ["probe", "stderr", "dependencies", "discovery_dependencies"] do
    unless receipt.payloads.any (fun payload => payload.key == key) do
      throw s!"missing required capture payload: {key}"

private def captureRequireProcessOutputs (receipt : CaptureReceipt) : Except String Unit := do
  let completion ← evidenceField receipt.raw "completion"
  let processes ← evidenceArray completion "processes"
  for process in processes do
    for stream in ["stdout", "stderr"] do
      let path ← evidenceText process stream
      unless receipt.payloads.any (fun payload => payload.path == path) do
        throw s!"unbound capture process {stream}: {path}"

private def captureReadPayload (directory : System.FilePath) (payload : CapturePayload) :
    IO ByteArray := do
  let bytes ← captureReadBytes directory payload.path
  unless bytes.size == payload.byteCount do
    throw <| .userError s!"capture payload byte count mismatch: {payload.key}"
  unless (← captureSha256 bytes) == payload.sha256 do
    throw <| .userError s!"capture payload SHA-256 mismatch: {payload.key}"
  return bytes

def readDeclarationCapture (path : System.FilePath) : IO DeclarationCapture := do
  let directory ← captureDirectory path
  let receiptBytes ← captureReadBytes directory "capture.json"
  let receiptText ← captureText "capture.json" receiptBytes
  let receipt ← captureIOExcept (parseCaptureReceiptString receiptText)
  captureIOExcept (captureRequireCore receipt)
  captureIOExcept (captureRequireProcessOutputs receipt)
  let mut probeBytes : Option ByteArray := none
  for payload in receipt.payloads do
    let bytes ← captureReadPayload directory payload
    if payload.key == "probe" then probeBytes := some bytes
  let bytes ← match probeBytes with
    | some bytes => pure bytes
    | none => throw <| .userError "missing required capture probe payload"
  let text ← captureText "probe payload" bytes
  let probe ← captureIOExcept (parseDeclarationProbeString text)
  captureIOExcept (validateCaptureProbe receipt probe)
  return {receipt, probe}

open Lean Elab Command in
elab "load_cpp_capture " name:ident " from " path:str : command => do
  let capture ← try
      readDeclarationCapture ⟨path.getString⟩
    catch error => throwErrorAt path "load_cpp_capture: {error.toMessageData}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name "load_cpp_capture: '{declarationName}' already declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName, levelParams := []
      type := Lean.mkConst ``LeanModels.Cpp.DeclarationCapture
      value := Lean.toExpr capture, hints := .abbrev, safety := .safe }
    enableRealizationsForConst declarationName
    addDocStringCore declarationName captureLoadBoundary
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

end LeanModels.Cpp
