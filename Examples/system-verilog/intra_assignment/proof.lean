import LeanModels.Sv.Load

namespace Examples.systemVerilog.intraAssignment.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- The fixture receipt binds both definitions to the actual compiled capture.
def capturedName : String := "$intra:163"
def copyback : SStmt := .packedAssign
  [.selected "word" 8 false true false (.m0 (.ident "index"))]
  (.m0 (.ident capturedName))
def captureWait : SStmt := .block #[
  .localDecl capturedName 8 false (some (.m0 (.ident "source"))),
  .delay 3, copyback]
def waitEdge : SStmt := .waitEvent "clk" .pos

/-- Source evaluation happens before the wait and retains all previous effects. -/
theorem capture_before_wait (source word index : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false)
    (normal : output.transfer = .normal) :
    stepSStmt (fuel + 12) [("source",source),("word",word),("index",index)] pending output
      captureWait =
      .ok ([("source",source),("word",word),("index",index),(capturedName,source)],
        pending, output, .suspended (.atTime 3) [copyback]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer, _⟩
  change halted = false at running
  change transfer = .normal at normal
  subst halted
  subst transfer
  rfl

/-- Copyback reads the resumed index, using saved data despite a changed source. -/
theorem copyback_uses_resumed_index (word resumedIndex changedSource : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8)
      [("source",changedSource),("word",word),("index",resumedIndex),
        (capturedName,.ofNat 8 165)] pending output copyback =
      .ok ([("source",changedSource),
        ("word",selectedWrite 8 false true word resumedIndex (.ofNat 8 165)),
        ("index",resumedIndex),(capturedName,.ofNat 8 165)], pending, output) := by
  simp [copyback, capturedName, execSStmt, execPackedTargets, packedTargetSlices,
    rightToLeftAssignmentOrder, validAssignmentOrder, evalSExpr, evalExpr,
    readSignal, SvState.lookup, SvState.set, PackedTarget.width, List.eraseDups, running] <;> rfl

/-- After one event, the saved repeat count controls the next wait without a reread. -/
theorem repeat_retains_count (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false)
    (normal : output.transfer = .normal) :
    stepSStmt (fuel + 8) state pending output (.repeatAfterBody 2 waitEdge) =
      .ok (state,pending,{ output with transfer := .normal },
        .suspended (.atEdge "clk" .pos) [.repeatAfterBody 1 waitEdge]) := by
  simp [waitEdge, stepSStmt, stepRepeatLoop, running, normal]

#print axioms capture_before_wait
#print axioms copyback_uses_resumed_index
#print axioms repeat_retains_count

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- Complete independent source transcripts, 2026-10-20.
-- capture.sv SHA-256: cc2074123fa85c182443b0d5fba523a1a9254aff291cb002fe79d031e4c4546b
-- zero.sv SHA-256: f1caa8257f100ede19528dc811d4a289b6eba1a18469e1b3cf83c7bdb6806ec8
-- counts.sv SHA-256: 2a2074ee7986ea7031c6426d37178a0dee2f42549784d359131173100d0ff59d
-- events.sv SHA-256: 5325753d6b956826ca6251658f06214e3f9b4e89fa92cdd68b8bc87b64684423
-- reentry.sv SHA-256: 7278694aface38eb3691c2f7e5c6012704fa4e918cc68769ea1854b94e677707
def fixtureReceipt : IO Unit := do
  for (name, expected, limit) in [
      ("reentry", ["concat 0100 10xzxz10zx0110xz source 9",
        "reentry 10xz101110101001 12 12"], 4),
      ("capture", ["changed z10xzzzzxxxxxz10",
        "selected z10x10100101xz10 source 3c index 4"], 3),
      ("counts", ["negative 2a", "zero 35", "unknown_x 46", "unknown_z 57",
        "parked 57 source 99 count 0"], 2)] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/intra_assignment/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "capture" then
      let some (SProc.initial body) := design.procs[0]?
        | throw (IO.userError "capture process shape changed")
      unless containsStatement captureWait body do
        throw (IO.userError "capture certificate differs from source")
    if name == "counts" then
      let some (SProc.initial body) := design.procs[0]?
        | throw (IO.userError "repeat process shape changed")
      unless containsStatement (.repeatLoop (.m0 (.ident "count")) true waitEdge) body do
        throw (IO.userError "repeat event certificate differs from source")
    for oracle in [ρ_src,ρ_rev] do
      let .ok world := elabTimedDesign 4096 design
        | throw (IO.userError s!"{name} timed design refused")
      let .ok (.ok _,world) := SvM.exec (slotStep oracle 4096) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range limit do
        let .ok (.ok _,next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.flush == expected do
        throw (IO.userError s!"{name} transcript differs")
  let .ok zero := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/intra_assignment/zero.sv.json")
    | throw (IO.userError "zero-delay fixture failed to load")
  let .ok zeroWorld := elabTimedDesign 4096 zero
    | throw (IO.userError "zero-delay design failed to elaborate")
  -- SYNTHETIC-ORACLE: tests=intra-assignment-zero-delay | origin=spec | authority=timed-slot-contract | map=zero-delay:requires-inactive-delivery-rule
  match SvM.exec (slotStep ρ_src 4096) zeroWorld with
  | .error (.unsupported (.unsupported clause) _ _) =>
      unless clause.clause == "9.4.1" do
        throw (IO.userError "zero delay refused under a different clause")
  | _ => throw (IO.userError "zero-delay delivery boundary disappeared")
  let .ok internalEdges := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/intra_assignment/events.sv.json")
    | throw (IO.userError "event fixture failed to load")
  -- SYNTHETIC-ORACLE: tests=intra-assignment-edge-publication | origin=spec | authority=timed-slot-contract | map=procedural-clock-write:published-edge-wakes-retained-wait
  unless requiresInternalEdges internalEdges do
    throw (IO.userError "internal edge census disappeared")
  for oracle in [ρ_src, ρ_rev] do
    let .ok world := elabTimedDesign 4096 internalEdges
      | throw (IO.userError "event fixture failed to elaborate")
    let .ok (.ok _, world) := SvM.exec (slotStep oracle 4096) world
      | throw (IO.userError "event fixture initial slot refused")
    let mut world := world
    for _ in List.range 4 do
      if world.out.halted then break
      let .ok (.ok _, next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
        | throw (IO.userError "event fixture resumed slot refused")
      world := next
    unless world.out.halted do
      throw (IO.userError "event fixture did not finish after four ticks")

#eval fixtureReceipt

end Examples.systemVerilog.intraAssignment.proof
