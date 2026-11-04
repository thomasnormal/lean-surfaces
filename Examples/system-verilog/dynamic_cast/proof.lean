import LeanModels.Sv.Load

namespace Examples.systemVerilog.dynamicCast.proof
open LeanModels.Sv LeanModels.Sv.SelfCheck
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- REFERENCE: df57813163e4b8a357005397 24.03-s004 2026-10-20 | tests=cast-source-bound-theorems | source=Examples/system-verilog/dynamic_cast/certificate.sv@sha256:cde576e1db69ee705208f4bb9e4b564d9ca3100f25ce0703b81de97d341c80c7 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: a63f4905d24fda41bc5a69bf 24.03-s004 2026-10-20 | tests=cast-source-bound-theorems | source=Examples/system-verilog/dynamic_cast/selected.sv@sha256:de26b062014cf5b52e4504925a081d39e395a6b16cd782fe69503f8ed940b02e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- SYNTHETIC-ORACLE: tests=closed-table-facts | origin=literal | authority=certificate.sv | map=members:declared-1-and-8;nonmember:selected.sv-invalid-source-7;preservation:existing-store-and-conditional-contract
def sampled : SExpr := .m0 (.ident "$cast:2")
def sourceValue : SExpr := .resize 4 (.m0 (.ident "source"))
def valid : SExpr := .logOr
  (.logOr (.m0 (.lit (.lit "0"))) (.caseEq sampled (.m0 (.lit (.lit "0001")))))
  (.caseEq sampled (.m0 (.lit (.lit "1000"))))
def copyback : SStmt := .m0 (.block #[
  .blockingAssign "destination" (.ident "$cast:2"),
  .blockingAssign "$cast:1" (.lit (.lit "00000000000000000000000000000001"))])
def decision : SStmt := .ifStmt valid copyback none
def frame (state : SvState) (old value : LVec) : SvState :=
  ("$cast:2", value) :: ("destination", old) :: state

private theorem literal_zero : LVec.lit "0" = ⟨#[.l0]⟩ := by rfl
private theorem literal_one : LVec.lit "1" = ⟨#[.l1]⟩ := by rfl
-- Closed four-bit table facts use kernel reduction; no native decision tactic.
private theorem neq18 : LVec.lit "0001" ≠ LVec.lit "1000" := by decide
private theorem neq81 : LVec.lit "1000" ≠ LVec.lit "0001" := by decide
private theorem neq71 : LVec.lit "0111" ≠ LVec.lit "0001" := by decide
private theorem neq78 : LVec.lit "0111" ≠ LVec.lit "1000" := by decide

/-- The parsed source is converted once to its destination width. -/
theorem samples_source (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 16) (("source", value) :: state) sourceValue = .ok (resizeV 4 value) := by
  rfl

/-- Exact membership accepts the first bound member. -/
theorem member_one (state : SvState) (old : LVec) (fuel : Nat) :
    evalSExpr (fuel + 32) (frame state old (.lit "0001")) valid = .ok (.lit "1") := by
  simp [evalSExpr, valid, sampled, frame, evalExpr, SvState.lookup, readSignal, LVec.eqCase, truthy, LVec.condTrue, LVec.isKnownZero,
    LVec.ofLogic, Logic.or, literal_zero, literal_one, neq18]

/-- Exact membership also accepts the sparse second member. -/
theorem member_eight (state : SvState) (old : LVec) (fuel : Nat) :
    evalSExpr (fuel + 32) (frame state old (.lit "1000")) valid = .ok (.lit "1") := by
  simp [evalSExpr, valid, sampled, frame, evalExpr, SvState.lookup, readSignal, LVec.eqCase, truthy, LVec.condTrue, LVec.isKnownZero,
    LVec.ofLogic, Logic.or, literal_zero, literal_one, neq81]

/-- A failed membership branch preserves all storage, pending work and output. -/
theorem failure_preserves (state : SvState) (old : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false) :
    execSStmt (fuel + 64) (frame state old (.lit "0111")) pending output decision =
      .ok (frame state old (.lit "0111"), pending, output) := by
  unfold decision
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  simp [evalSExpr, valid, sampled, frame, evalExpr, SvState.lookup, readSignal, LVec.eqCase, truthy, LVec.condTrue, LVec.isKnownZero,
    LVec.ofLogic, Logic.or, literal_zero, neq71, neq78]

/-- The real success body writes the snapshot and success code only. -/
theorem success_stores (state : SvState) (old value : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false) :
    execSStmt (fuel + 64) (frame state old value) pending output copyback =
      .ok (SvState.set (SvState.set (frame state old value) "destination" value)
        "$cast:1" (.lit "00000000000000000000000000000001"), pending, output) := by
  unfold copyback
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- Later source writes cannot change the saved converted value. -/
theorem snapshot_stable (state : SvState) (old value replacement : LVec) (fuel : Nat) :
    evalSExpr (fuel + 16) (SvState.set (frame state old value) "source" replacement) sampled =
      .ok value := by
  rfl

#print axioms samples_source
#print axioms member_one
#print axioms member_eight
#print axioms failure_preserves
#print axioms success_stores
#print axioms snapshot_stable

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | _ => false

partial def containsCapture (statement : SStmt) : Bool :=
  match statement with
  | .localDecl "$cast:2" 4 false (some value) => value == sourceValue
  | .block statements => statements.any containsCapture
  | _ => false

-- REFERENCE: 0e7730bbab791e971ef72672 24.03-s004 2026-10-20 | tests=conditional | source=Examples/system-verilog/dynamic_cast/conditional.sv@sha256:89d9118dcca1c24febecb24e7c81f6936afcaf2213161d788fcae67790568bfa | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: 72538893c3532a3a40c98a5c 24.03-s004 2026-10-20 | tests=control | source=Examples/system-verilog/dynamic_cast/control.sv@sha256:22caebe43141a5e12e73de25f3866f8016dc7c5e942d8265047ccec06586a707 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: 70711ef71e50f92b905b84c3 24.03-s004 2026-10-20 | tests=rules | source=Examples/system-verilog/dynamic_cast/rules.sv@sha256:8f8c9d0efd54fde3155c299e0f4e3558c6d43a10746559b409336a83a1525e28 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: a63f4905d24fda41bc5a69bf 24.03-s004 2026-10-20 | tests=selected | source=Examples/system-verilog/dynamic_cast/selected.sv@sha256:de26b062014cf5b52e4504925a081d39e395a6b16cd782fe69503f8ed940b02e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: f8d31e2830d3b79ac35fade6 24.03-s004 2026-10-20 | tests=source_effect | source=Examples/system-verilog/dynamic_cast/source_effect.sv@sha256:8104aca35b66cb89ce78f923baf3221c0233a3646108a72ff6dc1b595c4f50c2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: 548b04125236309016eb2002 24.03-s004 2026-10-20 | tests=task_failure | source=Examples/system-verilog/dynamic_cast/task_failure.sv@sha256:a63600a4a35c4faf4cd6f7f8f70b2015357d20221629d8851a744a99d87b2f62 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: 563759e330aef53817a0fe18 24.03-s004 2026-10-20 | tests=task_success | source=Examples/system-verilog/dynamic_cast/task_success.sv@sha256:99d5762c9fa25a8c44cac877815a8f91cfb8d580f97f0713c86c8cad5fef8cd4 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: ecedfe9e5fd0bbb1fec98568 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/dynamic_cast/timing.sv@sha256:5ad43f4ac4ec844e15185a6c66db652db1c094ae3ac24ecf3ebdd8218babeceb | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: c3032fe3eacc1abe09b978a8 24.03-s004 2026-10-20 | tests=unordered | source=Examples/system-verilog/dynamic_cast/unordered.sv@sha256:d81576dc0e8c4eb1faaa725bde1c5ac32e93c8dc39459a78d76771f0e2fa32c7 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- REFERENCE: df57813163e4b8a357005397 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/dynamic_cast/certificate.sv@sha256:cde576e1db69ee705208f4bb9e4b564d9ca3100f25ce0703b81de97d341c80c7 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=README.md#dynamic-integral-casts
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-admission | origin=spec | authority=docs/sv-dynamic-cast.md#dynamic-integral-casts | map=certificates:parsed-capture-and-guard-equality;refusals:documented-effect-and-diagnostic-boundaries
def fixtureReceipt : IO Unit := do
  let .ok design := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/dynamic_cast/certificate.sv.json")
    | throw (IO.userError "certificate failed to load")
  unless design.procs.any (fun process => match process with
      | .initial body => containsStatement decision body && containsCapture body
      | _ => false) do
    throw (IO.userError "certificates differ from actual parsed cast")

  for (name, expected) in [
      ("control", ["and-skip 0 01", "or-skip 1 01", "and-write 1 10", "fallback 01", "unknown-fail 0 01", "comparison 1 10"]),
      ("rules", ["wide 1 01", "ones 0 01", "x 1 x1", "z 1 z0", "two 1 00", "two1 1 01", "sign 1 110", "unsigned 1 110", "u32 1 110", "u32n 1 110", "selfinvalid 0 11", "int 1 00000000"]),
      ("selected", ["cell 1 1 8", "retain 0 1 8", "outside 1 1 8", "window 1 ab6d", "member 1 3f"]),
      ("task_success", ["task 110 f"]),
      ("timing", ["capture 1 8 8 7", "failure 0 8 8"]),
      ("certificate", ["certificate 1 8"])] do
    let .ok d := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/dynamic_cast/{name}.sv.json")
      | throw (IO.userError s!"{name} load failed")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 d
        | throw (IO.userError s!"{name} timed load failed")
      let mut world := initial
      for _ in List.range 12 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (slotStep oracle 32768) world
          | throw (IO.userError s!"{name} slot refused")
        world := next
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (do advanceTime 1; wakeTimers) world
          | throw (IO.userError s!"{name} advance refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["conditional", "source_effect", "unordered", "task_failure"] do
    let .ok d := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/dynamic_cast/{name}.sv.json")
      | throw (IO.userError s!"{name} load failed")
    let .ok world := elabTimedDesign 32768 d
      | throw (IO.userError s!"{name} timed load failed")
    match SvM.exec (slotStep ρ_src 32768) world with
    | .ok (.ok _, _) => throw (IO.userError s!"{name} lost its refusal")
    | _ => pure ()

#eval fixtureReceipt
end Examples.systemVerilog.dynamicCast.proof
