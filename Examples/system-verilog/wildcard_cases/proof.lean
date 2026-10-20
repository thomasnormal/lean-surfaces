import LeanModels.Sv.Load

namespace Examples.systemVerilog.wildcardCases.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- The receipt below binds these terms to the actual timed source's first case.
def choose (value : Nat) : SStmt :=
  .assign false "choice" (.squash2 (.m0 (.lit (.ofNat 32 value))))
def writeChoice : SStmt := choose 1
def selectedBody : SStmt := .block #[.delay 2, writeChoice]
def selectedCase : SStmt :=
  .ifStmt (.caseMatch false (.m0 (.ident "selector")) (.m0 (.lit (.lit "1zz0"))))
    selectedBody (some (
      .ifStmt (.caseMatch false (.m0 (.ident "selector")) (.m0 (.lit (.lit "x1z0"))))
        (.block #[.delay 2, choose 2])
        (some (choose 3))))

/-- The expression bridge uses the same symmetric value predicate as the spec. -/
theorem match_evaluates (wildX : Bool) (a b : LVec) (fuel : Nat) :
    evalSExpr (fuel + 4) [("subject",a),("item",b)]
      (.caseMatch wildX (.m0 (.ident "subject")) (.m0 (.ident "item"))) =
      .ok (.ofLogic (if LVec.matchesCase wildX a b then .l1 else .l0)) := by
  rfl

/-- The ignored positions belong to either operand, including dynamic items. -/
theorem match_symmetric (wildX : Bool) (a b : LVec) :
    LVec.matchesCase wildX a b = LVec.matchesCase wildX b a :=
  LVec.matchesCase_comm wildX a b

/-- Once selected, the wait retains only the selected arm's copyback. -/
theorem selection_retained (selector previous : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false)
    (selected : LVec.matchesCase false selector (.lit "1zz0") = true) :
    stepSStmt (fuel + 16) [("selector",selector),("choice",previous)] pending output
      selectedCase =
      .ok ([("selector",selector),("choice",previous)],pending,output,
        .suspended (.atTime 2) [writeChoice]) := by
  have gate : evalSExpr (fuel + 15) [("selector",selector),("choice",previous)]
      (.caseMatch false (.m0 (.ident "selector")) (.m0 (.lit (.lit "1zz0")))) =
      .ok (.ofLogic .l1) := by
    change Res.ok (LVec.ofLogic (if LVec.matchesCase false selector (.lit "1zz0")
      then .l1 else .l0)) = _
    rw [selected]
    rfl
  unfold selectedCase
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, gate, Res.ok_bind]
  rw [show (LVec.ofLogic .l1).condTrue = true by simp [LVec.ofLogic, LVec.condTrue]]
  simp only [if_true]
  change stepSStmt (fuel + 15) [("selector",selector),("choice",previous)]
    pending output selectedBody = _
  rcases output with ⟨lines, current, halted, transfer⟩
  change halted = false at running
  subst halted
  rfl

#print axioms match_evaluates
#print axioms match_symmetric
#print axioms selection_retained

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- Complete independent source transcripts, 2026-10-20.
-- table.sv SHA-256: 96720616f170f2c968f1f5c8582381ff990f8c1e00bf852c692d89bf121bf9d0
-- contexts.sv SHA-256: b1ffa129a6205d0c10c0f56645b0a0ff29fb05aa3f42e0da7228a11e922ac357
-- timers.sv SHA-256: 8256c3d44561d0f514fa9f30ffb72e5b81e2b1974f85b9ad1cfabd397bcddfc8
def fixtureReceipt : IO Unit := do
  for (name,expected) in [
      ("table", ["row 00 z 9009 x dd0d", "row 01 z a00a x ee0e",
        "row 0x z c00c x ff0f", "row 0z z f00f x ff0f",
        "row 10 z 9090 x ddd0", "row 11 z a0a0 x eee0",
        "row 1x z c0c0 x fff0", "row 1z z f0f0 x fff0",
        "row x0 z 9900 x dddd", "row x1 z aa00 x eeee",
        "row xx z cc00 x ffff", "row xz z ff00 x ffff",
        "row z0 z 9999 x dddd", "row z1 z aaaa x eeee",
        "row zx z cccc x ffff", "row zz z ffff x ffff"]),
      ("contexts", ["signed 2", "mixed 5", "exact_x 7", "dynamic_z 9",
        "dynamic_x 11", "wide 13", "no_match 16", "first_nested 19"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/wildcard_cases/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    unless runSelfCheck design 32768 == .ok expected do
      throw (IO.userError s!"{name} complete transcript differs")
  let .ok design := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/wildcard_cases/timers.sv.json")
    | throw (IO.userError "timers failed to load")
  let some (SProc.initial body) := design.procs[0]?
    | throw (IO.userError "timer process shape changed")
  unless containsStatement selectedCase body do
    throw (IO.userError "selected-case certificate differs from source")
  for oracle in [ρ_src,ρ_rev] do
    let .ok world := elabTimedDesign 32768 design
      | throw (IO.userError "timed design refused")
    let .ok (.ok _,world) := SvM.exec (slotStep oracle 32768) world
      | throw (IO.userError "initial slot refused")
    let mut world := world
    for _ in List.range 4 do
      let .ok (.ok _,next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
        | throw (IO.userError "resumed slot refused")
      world := next
    unless world.out.flush == ["casez 1 live x101", "casex 4 live 1110"] do
      throw (IO.userError "timed transcript differs")

#eval fixtureReceipt

end Examples.systemVerilog.wildcardCases.proof
