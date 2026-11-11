import LeanModels.C.Torture

open LeanModels.C LeanModels.C.C23 LeanModels.C.C23.Torture

/-- Observe the actual return value; the torture scoreboard currently drops it. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "expected one C envelope"; return 2
  let contents ← IO.FS.readFile path
  match parseEnvelopeString contents with
  | .error reason => IO.eprintln s!"ingestion: {reason}"; return 2
  | .ok envl =>
      let lay := layoutFor envl
      let prog : Program := {fns := envl.unit.functionDefns}
      let prog := {prog with layout := lay}
      let prog := {prog with enumIds := envl.unit.enumBindings}
      let run : ExecM CVal := do
        let globals ← setupGlobalsWithIds 512 lay envl.unit.fileScopeObjects [] []
        callByName 512 {prog with globals := globals.1, globalIds := globals.2} "main" []
      match ExecM.verdict Mem.empty run with
      | .ok (.int _ value) => IO.println s!"{value}"; return 0
      | outcome => IO.eprintln s!"model refused: {repr outcome}"; return 3
