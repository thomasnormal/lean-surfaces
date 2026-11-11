import LeanModels.C.Torture

open LeanModels.C LeanModels.C.C23 LeanModels.C.C23.Torture

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "expected one C envelope"; return 2
  let contents ← IO.FS.readFile path
  match parseEnvelopeString contents with
  | .error reason => IO.eprintln s!"ingestion: {reason}"; return 2
  | .ok envl =>
      let lay := layoutFor envl
      let prog : Program := {fns := envl.unit.functionDefns, layout := lay}
      let run : ExecM CVal := do
        let globals ← setupGlobals 512 lay envl.unit.fileScopeObjects []
        callByName 512 {prog with globals} "main" []
      match ExecM.verdict Mem.empty run with
      | .ok (.int _ value) => IO.println s!"{value}"; return 0
      | outcome => IO.eprintln s!"model refused: {repr outcome}"; return 3
