import Lean

open Lean

def main (args : List String) : IO Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let modules := if args.isEmpty then ["LeanModels"] else args
  let imports := modules.toArray.map fun moduleName =>
    { module := moduleName.toName : Import }
  let environment ← importModules imports {}
  let mut artifacts : Array Json := #[]
  for moduleName in environment.allImportedModuleNames do
    let path ← findOLean moduleName
    for candidate in #[path, path.addExtension "server", path.addExtension "private",
        path.withExtension "ir.sig", path.withExtension "ir"] do
      if ← candidate.pathExists then
        artifacts := artifacts.push (.str candidate.toString)
  for directory in #[sysroot / "lib", sysroot / "lib" / "lean", sysroot / "bin"] do
    for entry in ← directory.readDir do
      let filename := entry.fileName
      if filename.endsWith ".so" || (filename.splitOn ".so.").length > 1 ||
          filename.endsWith ".dylib" || filename.endsWith ".dll" then
        artifacts := artifacts.push (.str entry.path.toString)
  IO.println (Json.arr artifacts).compress
