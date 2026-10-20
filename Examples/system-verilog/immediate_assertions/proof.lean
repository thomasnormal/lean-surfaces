import LeanModels.Sv.Load

namespace Examples.systemVerilog.immediateAssertions.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact compiled subtrees, certified against timers.sv and table.sv below.
def condition : SExpr := .m0 (.ident "gate")
def choose (name : String) (value : Nat) : SStmt :=
  .assign false name (.squash2 (.m0 (.lit (.ofNat 32 value))))
def successBody : SStmt := .block #[.delay 2, choose "choice" 11]
def failureBody : SStmt := .block #[.delay 3, choose "choice" 22]
def checked : SStmt := .ifStmt condition successBody (some failureBody)
def covered : SStmt := .ifStmt condition (choose "covered" 1) none

/-- Evaluation reads the current vector, preserving all four-state bits. -/
theorem current_condition (value : LVec) (state : SvState) (fuel : Nat) :
    evalSExpr (fuel + 3) (("gate",value) :: state) condition = .ok value := by
  rfl

/-- A false or wholly ambiguous condition retains only the failure action's tail. -/
theorem failure_retains (value : LVec) (state : SvState) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false)
    (failed : value.condTrue = false) :
    stepSStmt (fuel + 12) (("gate",value) :: state) pending output checked =
      .ok (("gate",value) :: state, pending, output,
        .suspended (.atTime 3) [choose "choice" 22]) := by
  have evaluation : evalSExpr (fuel + 11) (("gate",value) :: state) condition = .ok value := by rfl
  unfold checked
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, evaluation, Res.ok_bind, failed]
  rcases output with ⟨lines, current, halted, transfer⟩
  change halted = false at running
  subst halted
  rfl

/-- A logically true vector retains only the selected success action's tail. -/
theorem success_retains (value : LVec) (state : SvState) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false)
    (passed : value.condTrue = true) :
    stepSStmt (fuel + 12) (("gate",value) :: state) pending output checked =
      .ok (("gate",value) :: state, pending, output,
        .suspended (.atTime 2) [choose "choice" 11]) := by
  have evaluation : evalSExpr (fuel + 11) (("gate",value) :: state) condition = .ok value := by rfl
  unfold checked
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, evaluation, Res.ok_bind, passed, if_true]
  rcases output with ⟨lines, current, halted, transfer⟩
  change halted = false at running
  subst halted
  rfl

/-- An unsuccessful cover has no failure action or diagnostic. -/
theorem cover_skips (value : LVec) (state : SvState) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false)
    (missed : value.condTrue = false) :
    stepSStmt (fuel + 12) (("gate",value) :: state) pending output covered =
      .ok (("gate",value) :: state, pending, output, .done) := by
  have evaluation : evalSExpr (fuel + 11) (("gate",value) :: state) condition = .ok value := by rfl
  unfold covered
  rw [stepSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, evaluation, Res.ok_bind, missed]

#print axioms current_condition
#print axioms failure_retains
#print axioms success_retains
#print axioms cover_skips

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: 38f1514ba7d4d6d38b91c02d 24.03-s004 2026-10-20 | tests=table | source=Examples/system-verilog/immediate_assertions/table.sv@sha256:52e41b370b9ee5717cfb768c780c9836625a0e41e180cc966570267b6e7e763d | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#simple-immediate-assertion-actions
-- REFERENCE: 947ee5a5190a7cc012a08b1d 24.03-s004 2026-10-20 | tests=actions | source=Examples/system-verilog/immediate_assertions/actions.sv@sha256:987dbf6e0f00408da5a62a854d78ebcd65868fe4d57a6eee9379c0ab03be32e6 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#simple-immediate-assertion-actions
-- REFERENCE: 4bc1e870d9652702ae42e273 24.03-s004 2026-10-20 | tests=timers | source=Examples/system-verilog/immediate_assertions/timers.sv@sha256:a7011aff4b9ef1a704e5a6ab6a9796458e87ec20e612ead3ae8c5e4ab85f067c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#simple-immediate-assertion-actions
-- REFERENCE: a21d9a1135f3230a6666a0b7 24.03-s004 2026-10-20 | tests=implicit_pass | source=Examples/system-verilog/immediate_assertions/implicit_pass.sv@sha256:0774e140a77be01f8f23f6001c1c30b0cf10131480820caa1fa929ef5a26e06e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#simple-immediate-assertion-actions
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-immediate-assertions.md | map=certificates:parsed-body-equality;implicit-error:requires-diagnostics;deferred:requires-observation-regions;null-failure:unvalidated-parser-disagreement
def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("table", ["row 00 2 2 0", "row 01 1 1 1", "row 0x 2 2 0", "row 0z 2 2 0",
        "row 10 1 1 1", "row 11 1 1 1", "row 1x 1 1 1", "row 1z 1 1 1",
        "row x0 2 2 0", "row x1 1 1 1", "row xx 2 2 0", "row xz 2 2 0",
        "row z0 2 2 0", "row z1 1 1 1", "row zx 2 2 0", "row zz 2 2 0"]),
      ("actions", ["actions 15"]), ("implicit_pass", ["implicit_pass"]),
      ("timers", ["failure_tail 22 live 1", "success_tail 33 live 0"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/immediate_assertions/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "table" || name == "timers" then
      let certificate := if name == "table" then covered else checked
      unless design.procs.any (fun process => match process with
          | .initial body => containsStatement certificate body
          | _ => false) do
        throw (IO.userError s!"{name} certificate differs from compiled source")
    if name != "timers" then
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 6 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete timed transcript differs")
  for name in ["implicit_error", "deferred", "null_failure"] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/immediate_assertions/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    unless match runSelfCheck design 32768 with
        | .unsupported _ => true
        | _ => false do
      throw (IO.userError s!"{name} silently crossed its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.immediateAssertions.proof
