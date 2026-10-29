import LeanModels.Sv.Load

namespace Examples.systemVerilog.always.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def trueCondition : SExpr := .m0 (.lit (.ofNat 1 1))
def increment (name : String) : SStmt :=
  .assign false name (.squash2 (.m0 (.binary .add (.ident name) (.lit (.ofNat 32 1)))))
-- Exact compiled bodies from independent.sv and events.sv; checked below.
def delayedBody : SStmt := .block #[.delay 2, increment "fast"]
def eventBody : SStmt := .block #[.waitEvent "trigger" .any, increment "changes"]
def loop (body : SStmt) : SStmt := .forLoop #[] trueCondition #[] body

/-- One plain source process becomes one ready loop, with no separate arm. -/
theorem one_process (body : SStmt) :
    timedProcOf (.alwaysBody body) =
      .ok { residual := [loop body], status := .ready, arm := none } := by
  rfl

private theorem true_test : (LVec.ofNat 1 1).condTrue = true := by
  simp only [LVec.condTrue, LVec.ofNat, ← Array.any_toList]
  simp [Array.toList_ofFn, List.ofFn_succ]

/-- The source delay retains its unfinished increment before the loop boundary. -/
theorem delay_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 12) state pending output (loop delayedBody) =
      .ok (state, pending, output, .suspended (.atTime 2)
        [increment "fast", .forAfterBody trueCondition #[] delayedBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer⟩
  change halted = false at running
  subst halted
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := transfer }
    trueCondition #[] delayedBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

/-- A bare event keeps its tail and repeats only after the current body completes. -/
theorem event_retains (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 12) state pending output (loop eventBody) =
      .ok (state, pending, output, .suspended (.atEdge "trigger" .any)
        [increment "changes", .forAfterBody trueCondition #[] eventBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer⟩
  change halted = false at running
  subst halted
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := transfer }
    trueCondition #[] eventBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

/-- Reaching the saved boundary enters the next body and registers its wait. -/
theorem event_rearms (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false)
    (normal : output.transfer = .normal) :
    stepSStmt (fuel + 12) state pending output
        (.forAfterBody trueCondition #[] eventBody) =
      .ok (state, pending, { output with transfer := .normal },
        .suspended (.atEdge "trigger" .any)
          [increment "changes", .forAfterBody trueCondition #[] eventBody]) := by
  rcases output with ⟨lines, current, strobes, halted, transfer⟩
  change halted = false at running
  subst halted
  change transfer = .normal at normal
  subst transfer
  change stepForLoop (fuel + 11) state pending
    { lines := lines, cur := current, pending := strobes, halted := false, transfer := .normal }
    trueCondition #[] eventBody = _
  rw [stepForLoop.eq_def]
  simp only [Bool.false_eq_true, if_false, evalForCondition, trueCondition,
    evalSExpr, evalExpr, Res.ok_bind, true_test, if_true]
  rfl

#print axioms one_process
#print axioms delay_retains
#print axioms event_retains
#print axioms event_rearms

-- SYNTHETIC-ORACLE: tests=always-fuel | origin=spec | authority=fueled-executor-contract | map=non-suspending-repetition:timeout
#guard stepSStmt 64 [] [] {} (loop .skip) matches .timeout

-- REFERENCE: 0dea8a26464790315cd479cc 24.03-s004 2026-10-20 | tests=independent | source=Examples/system-verilog/always/independent.sv@sha256:8c82e0192d915d990d83d0c84c336f792097f0ee7dc7b952f85ceb3a4b87786e | top=top | args=["-ii_val"] | map=README.md#plain-always-source-repetition
-- REFERENCE: 0196e2d900f93c2f1c4dca6c 24.03-s004 2026-10-20 | tests=tails | source=Examples/system-verilog/always/tails.sv@sha256:d5f97f1fde25f7089d87a1bffa212e7b55b45da9295ad5c7a52607bca5702fdf | top=top | args=["-ii_val"] | map=README.md#plain-always-source-repetition
-- REFERENCE: 44bce854e7c5758f6c631639 24.03-s004 2026-10-20 | tests=automatic | source=Examples/system-verilog/always/automatic.sv@sha256:0d32348a7a3c221f68970488164ce2702409434ec15837741496b797a51221d5 | top=top | args=["-ii_val"] | map=README.md#plain-always-source-repetition
-- REFERENCE: 6061f51049fb20d422397f3b 24.03-s004 2026-10-20 | tests=events | source=Examples/system-verilog/always/events.sv@sha256:a2f691c92fabdda73de26dc956c83fd3f0844be101b6160e308a0c23d07aef94 | top=top | args=["-ii_val"] | map=README.md#plain-always-source-repetition
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-mechanism-boundaries | origin=spec | authority=docs/sv-always.md | map=certificates:parsed-body-equality;process-count:one-per-source;initial-only:reject-Always;internal-edges:require-publication;early-finish:cannot-hide-Always
def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("independent", ["independent 3 2"]),
      ("tails", ["retained 4 3 z01x"]),
      ("automatic", ["automatic 3 9"]),
      ("events", ["waiting 0 0"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/always/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "independent" || name == "events" then
      let wanted := if name == "independent" then delayedBody else eventBody
      unless design.procs.any (fun process => match process with
          | .alwaysBody body => body == wanted
          | _ => false) do
        throw (IO.userError s!"{name} certificate differs from compiled source")
    unless match runSelfCheck design 32768 with
        | .unsupported _ => true
        | _ => false do
      throw (IO.userError s!"{name} entered initial-only runner")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      unless world.procs.size == design.procs.size do
        throw (IO.userError s!"{name} process count changed")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 8 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  let .ok edges := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/always/internal_edges.sv.json")
    | throw (IO.userError "edge source failed to load")
  unless requiresInternalEdges edges do
    throw (IO.userError "plain always lost internal-edge barrier")
  unless match elabTimedDesign 32768 edges with
      | .error "timed design requires procedural edge publication" => true
      | _ => false do
    throw (IO.userError "internal procedural edge silently admitted")
  -- Even an earlier initial $finish must not hide the source Always kind.
  let stopped : SelfCheck.Design := { edges with procs := #[.initial .finish, .alwaysBody eventBody] }
  unless match runSelfCheck stopped 32768 with
      | .unsupported _ => true
      | _ => false do
    throw (IO.userError "early finish concealed a non-initial process")

#eval fixtureReceipt

end Examples.systemVerilog.always.proof
