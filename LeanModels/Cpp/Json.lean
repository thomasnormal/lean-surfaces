import LeanModels.Cpp.Ast

namespace LeanModels.Cpp

def acceptedProfile : String := "cpp23-clang-json-0.1"

partial def rawOfJson : Lean.Json → Raw
  | .null => .null
  | .bool value => .bool value
  | .num value => .number value.toString
  | .str value => .string value
  | .arr values => .array (values.toList.map rawOfJson)
  | .obj fields => .object (fields.toArray.toList.map fun (name, value) => (name, rawOfJson value))

def textField (json : Lean.Json) (name : String) : Except String String :=
  json.getObjValAs? String name

def requireText (json : Lean.Json) (name expected : String) : Except String Unit := do
  let actual ← textField json name
  unless actual == expected do
    throw s!"{name}: expected '{expected}', got '{actual}'"

def requireHash (value : String) : Except String Unit := do
  unless value.length == 64 && value.toList.all (fun character =>
      character.isDigit || ('a' ≤ character && character ≤ 'f')) do
    throw "expected a lowercase SHA-256 digest"

def parseDependency (json : Lean.Json) : Except String Dependency := do
  let path ← textField json "path"
  let sha256 ← textField json "sha256"
  unless path.startsWith "/" do throw "dependency path must be absolute"
  requireHash sha256
  return {path, sha256}

def validateFrontend (json : Lean.Json) : Except String Unit := do
  for name in ["path", "version", "target", "cwd", "predefined_macros", "diagnostics"] do
    let _ ← textField json name
  for name in ["path", "cwd"] do
    unless (← textField json name).startsWith "/" do
      throw s!"frontend {name} must be absolute"
  requireHash (← textField json "sha256")
  let argv ← (← json.getObjVal? "argv").getArr?
  unless !argv.isEmpty do throw "frontend argv must not be empty"
  for argument in argv do
    let _ ← argument.getStr?
  let environment ← (← json.getObjVal? "environment").getObj?
  for (_, value) in environment.toArray do
    let _ ← value.getStr?

def validateDependencies (dependencies : List Dependency) : Except String Unit := do
  let mut paths : List String := []
  for dependency in dependencies do
    if paths.contains dependency.path then
      throw s!"duplicate dependency path: {dependency.path}"
    paths := dependency.path :: paths

def parseArtifact (json : Lean.Json) : Except String Artifact := do
  requireText json "schema_version" "cpp-0.1"
  requireText json "language" "cpp"
  requireText json "edition" "c++23"
  requireText json "profile_id" acceptedProfile
  let sourceFile ← textField json "source_file"
  let sourceSha256 ← textField json "source_sha256"
  requireHash sourceSha256
  let dependencies ← ((← (← json.getObjVal? "dependencies").getArr?).toList.mapM parseDependency)
  validateDependencies dependencies
  unless dependencies.any (fun dependency =>
      dependency.path == sourceFile && dependency.sha256 == sourceSha256) do
    throw "source and hash must occur in dependency manifest"
  let frontend ← json.getObjVal? "frontend"
  validateFrontend frontend
  let ast ← json.getObjVal? "ast"
  requireText ast "kind" "TranslationUnitDecl"
  let _ ← textField ast "id"
  return {sourceFile, sourceSha256, frontend := rawOfJson frontend,
          dependencies, ast := rawOfJson ast}

def parseArtifactString (contents : String) : Except String Artifact := do
  parseArtifact (← Lean.Json.parse contents)

end LeanModels.Cpp
