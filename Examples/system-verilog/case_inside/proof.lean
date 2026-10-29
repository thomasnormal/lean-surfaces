import LeanModels.Sv.Load

namespace Examples.systemVerilog.caseInside.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact compiled subtrees from timers.sv, certified by the receipt below.
def choose (value : Nat) : SStmt :=
  .assign false "choice" (.squash2 (.m0 (.lit (.ofNat 32 value))))
def comparison (item : String) : SExpr :=
  .m0 (.binary .wildEq (.ident "selector") (.ident item))
def selectedBody : SStmt := .block #[.delay 2, choose 2]
def selectedCase : SStmt :=
  .ifStmt (comparison "candidate") (choose 1)
    (some (.ifStmt (comparison "mask") selectedBody (some (choose 3))))
def interval : SExpr :=
  .logAnd (.scmp .ge (.m0 (.ident "value")) (.m0 (.ident "lo")))
    (.scmp .le (.m0 (.ident "value")) (.m0 (.ident "hi")))
def intervalCase : SStmt :=
  .ifStmt interval (.block #[.delay 2, choose 4]) (some (choose 5))

/-- Scalar labels use the existing asymmetric membership equality. -/
theorem guard_evaluates (subject item : LVec) (fuel : Nat) :
    evalSExpr (fuel + 5) [("selector",subject),("candidate",item)]
      (comparison "candidate") = .ok (.ofLogic (subject.eqWildcard item)) := by
  rfl

/-- An ambiguous earlier item is skipped; the selected later arm retains only its tail. -/
theorem ambiguous_then_match (subject candidate mask previous : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat)
    (running : output.halted = false)
    (ambiguous : subject.eqWildcard candidate = .lx)
    (matched : subject.eqWildcard mask = .l1) :
    stepSStmt (fuel + 16)
      [("selector",subject),("candidate",candidate),("mask",mask),("choice",previous)]
      pending output selectedCase =
      .ok ([("selector",subject),("candidate",candidate),("mask",mask),("choice",previous)],
        pending,output,.suspended (.atTime 2) [choose 2]) := by
  have firstGate : evalSExpr (fuel + 15)
      [("selector",subject),("candidate",candidate),("mask",mask),("choice",previous)]
      (comparison "candidate") = .ok (.ofLogic .lx) := by
    simp [comparison, evalSExpr, evalExpr, evalBinOp, readSignal, SvState.lookup, ambiguous]
  have secondGate : evalSExpr (fuel + 14)
      [("selector",subject),("candidate",candidate),("mask",mask),("choice",previous)]
      (comparison "mask") = .ok (.ofLogic .l1) := by
    simp [comparison, evalSExpr, evalExpr, evalBinOp, readSignal, SvState.lookup, matched]
  unfold selectedCase
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, firstGate, Res.ok_bind]
  rw [show (LVec.ofLogic .lx).condTrue = false by simp [LVec.ofLogic, LVec.condTrue]]
  simp only [Bool.false_eq_true, if_false]
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, secondGate, Res.ok_bind]
  rw [show (LVec.ofLogic .l1).condTrue = true by simp [LVec.ofLogic, LVec.condTrue]]
  simp only [if_true]
  change stepSStmt (fuel + 14)
    [("selector",subject),("candidate",candidate),("mask",mask),("choice",previous)]
    pending output selectedBody = _
  rcases output with ⟨lines,current,strobes,halted,transfer⟩
  change halted = false at running
  subst halted
  rfl

private theorem truthy_one : truthy (.ofLogic .l1) = .l1 := by
  simp [truthy, LVec.ofLogic, LVec.condTrue]

/-- Both inclusive signed comparisons are required by the actual interval guard. -/
theorem interval_evaluates (subject lower upper : LVec) (fuel : Nat)
    (atLeast : evalScmp .ge subject lower = .l1)
    (atMost : evalScmp .le subject upper = .l1) :
    evalSExpr (fuel + 8) [("value",subject),("lo",lower),("hi",upper)] interval =
      .ok (.ofLogic .l1) := by
  simp [interval, evalSExpr, evalExpr, readSignal, SvState.lookup,
    atLeast, atMost, truthy_one, Logic.and]

#print axioms guard_evaluates
#print axioms ambiguous_then_match
#print axioms interval_evaluates

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body => containsStatement wanted body
  | _ => false

-- Complete independently observed source transcripts, 2026-10-20.
-- table.sv SHA-256: e5eb027ea999484515a328651d01ccc09c0707c2cd4ebc4aee7c84ce39026637
-- contexts.sv SHA-256: 652ba4d90708947ff104c042f1799f160713a48f186051a78e0cdb4c5ba93d25
-- timers.sv SHA-256: d31b6889891075023ba6597c823cc63f4b7485f937e293c947a5b2ade1206e1e
-- array_widening.sv SHA-256: a2d77bdd0a931b2ee9c5ecebf38795703ab7bddb31696d844fdd025bf16ede16
def fixtureReceipt : IO Unit := do
  for (name, expected) in [
    ("table", ["row 00 dd0d", "row 01 ee0e", "row 0x cc0c", "row 0z cc0c", "row 10 ddd0", "row 11 eee0", "row 1x ccc0", "row 1z ccc0", "row x0 dd00", "row x1 ee00", "row xx cc00", "row xz cc00", "row z0 dd00", "row z1 ee00", "row zx cc00", "row zz cc00"]),
    ("contexts", ["signed 1", "mixed 4", "wide 5", "range 7", "reversed 10", "dynamic 12", "ambiguous 14", "bounds 17", "signed_cells 19", "unsigned_cells 22", "slice 24", "first_nested 26"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/case_inside/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    unless runSelfCheck design 32768 == .ok expected do
      throw (IO.userError s!"{name} complete transcript differs")
  let .ok design := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/case_inside/timers.sv.json")
    | throw (IO.userError "timer source failed to load")
  let some (SProc.initial body) := design.procs[0]?
    | throw (IO.userError "timer source process shape changed")
  unless containsStatement selectedCase body && containsStatement intervalCase body do
    throw (IO.userError "case-inside certificates differ from compiled source")
  for oracle in [ρ_src,ρ_rev] do
    let .ok world := elabTimedDesign 32768 design
      | throw (IO.userError "timer source refused")
    let .ok (.ok _,world) := SvM.exec (slotStep oracle 32768) world
      | throw (IO.userError "initial slot refused")
    let mut world := world
    for _ in List.range 4 do
      let .ok (.ok _,next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
        | throw (IO.userError "resumed slot refused")
      world := next
    unless world.out.halted && world.out.flush == ["wildcard 2 live 1110", "range 4 live 20 30 40", "reentry 7"] do
      throw (IO.userError "timed case-inside complete transcript differs")
#eval fixtureReceipt

end Examples.systemVerilog.caseInside.proof
