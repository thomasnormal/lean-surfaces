import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.localArrays.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The cell initializer used on each automatic block entry. -/
def automaticEntry (name : String) : SStmt :=
  .localDecl name 32 true (some (.squash2 (.m0 (.lit (.ofNat 32 4)))))

/-- A static array cell survives each repeat-body entry. -/
def staticBody (name : String) : SStmt :=
  .assign false name (.squash2
    (.m0 (.binary .add (.ident name) (.lit (.ofNat 32 1)))))

private theorem squash_ofNat (width value : Nat) :
    squash2v (.ofNat width value) = .ofNat width value := by
  simp [squash2v, LVec.toTwoState, LVec.ofNat]
  apply congrArg (fun f : Fin width → Logic => Array.ofFn f)
  funext i
  simp only [Function.comp_apply]
  split <;> rfl

theorem automatic_reinitializes (name : String) (old : LVec) :
    execSStmt 8 [(name, old)] [] {} (automaticEntry name) =
      .ok ([(name, .ofNat 32 4)], [], {}) := by
  simp [automaticEntry, execSStmt, evalSExpr, evalExpr, SvState.set,
    Bind.bind, Pure.pure, squash_ofNat]

theorem static_persists (name : String) (old : LVec) :
    execSStmt 8 [(name, old)] [] {} (staticBody name) =
      .ok ([(name, squash2v (old.add (.ofNat 32 1)))], [], {}) := by
  simp [staticBody, execSStmt, evalSExpr, evalExpr, evalBinOp,
    readSignal, SvState.lookup, SvState.set, Bind.bind, Pure.pure]

#print axioms automatic_reinitializes
#print axioms static_persists

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/local_arrays/local_arrays.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "local-array fixture failed to load")
  let some declaration := design.decls.find? (·.name.endsWith ":saved[0]")
    | throw (IO.userError "static cell was not hoisted")
  let some (SProc.initial (.block statements)) := design.procs[0]?
    | throw (IO.userError "local-array process shape changed")
  let some (SStmt.repeatLoop _ _ (.block body)) := statements[0]?
    | throw (IO.userError "local-array repeat shape changed")
  let some (SStmt.block automatic) := body[1]?
    | throw (IO.userError "automatic array declaration shape changed")
  let some (SStmt.localDecl name _ _ _) := automatic[0]?
    | throw (IO.userError "automatic cell missing")
  unless body[0]? == some .skip &&
      automatic[0]? == some (automaticEntry name) &&
      body[3]? == some (staticBody declaration.name) do
    throw (IO.userError "local-array certificates differ from extracted source")
  unless runSelfCheck design 4096 ==
      Res.ok ["entry 4 4", "entry 5 4", "entry 6 4"] do
    throw (IO.userError "local-array static/automatic lifetime disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.localArrays.proof
