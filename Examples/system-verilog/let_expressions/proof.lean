import LeanModels.Sv.Load
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.letExpressions.proof
open LeanModels.Sv LeanModels.Sv.SelfCheck
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- REFERENCE: b03b0a3b73727ba781dd4d7a 24.03-s004 2026-10-20 | tests=binding | source=Examples/system-verilog/let_expressions/binding.sv@sha256:75ce296763a0c23b0ef9aa989e3703fe5d00bf7d43fab02f455ca52eb435f57e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: dd359c6ae6a63f1283f53c17 24.03-s004 2026-10-20 | tests=call | source=Examples/system-verilog/let_expressions/call.sv@sha256:e9b97df59c248d2b2e253878951977cf9a5bf25073957843fb4010c3b62a50f3 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: d131ac0601814c4465fbf855 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/let_expressions/certificate.sv@sha256:17f5597e37b25f42a237a95ab6d29ab7cde82ccc2015fbe4acbb5d538e9be59a | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: 528421725d2b3a50177f573c 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/let_expressions/effects.sv@sha256:5ee81e71294b540e08ce72971f9e8f2482b6b531752765aa650292c6fbdcca1c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: 9e29b5de4163af92fb63e6a5 24.03-s004 2026-10-20 | tests=local | source=Examples/system-verilog/let_expressions/local.sv@sha256:bc065ab862053db508afdd460895367de43089665db2f06e3b06d1dce0987b98 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: f15f532a1ceb1ee3a1fdb244 24.03-s004 2026-10-20 | tests=program | source=Examples/system-verilog/let_expressions/program.sv@sha256:af52324ce6c3eac8b76f2e61a0cdec2f568c56490ee8e0c1cd7c0be8ced82911 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: 49383f3eb729b467587c94dd 24.03-s004 2026-10-20 | tests=sizing | source=Examples/system-verilog/let_expressions/sizing.sv@sha256:2cc1da1a70aa06e76b0dc57276c9bb08b85f50c0376af42f5e4bf5974c00c6a2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: 9c5fd762733e0f5f2bbc4b92 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/let_expressions/structure.sv@sha256:19ead2ca28de495bf38017cab0cceff22a670236fb44513d68ce7d439694b140 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: 60a678378f8e897c3abebf09 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/let_expressions/timing.sv@sha256:ee50869ba77f49dfd5ba65ec75840593d9e740d5f9c2def33caddaaa86f7fed2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- REFERENCE: f177e74e6c20640c68fc43ff 24.03-s004 2026-10-20 | tests=unused | source=Examples/system-verilog/let_expressions/unused.sv@sha256:ab0dffd96ad1882b35fa5ac036f95d2cd6b2d3219a24ed8a754e4a568e0ae017 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
-- SYNTHETIC-ORACLE: tests=admission-and-binding | origin=spec | authority=docs/sv-let-expressions.md#let-expressions | map=binding:actual-symbol;order:declaration-before-use;invalid:whole-design;nonmodule:scheduling-barrier;typed-default:structural-only

/-- The actual expansion of plus(actual) in certificate.sv. -/
def templateExpression : SExpr := .m0 (.binary .add (.ident "held") (.ident "actual"))
def assignment : SStmt := .m0 (.blockingAssign "result"
  (.binary .add (.ident "held") (.ident "actual")))
def shadowName : String := "$local:3:top:0:110:held"
def bindings (state : SvState) (held actual shadow : LVec) : SvState :=
  (shadowName, shadow) :: ("held", held) :: ("actual", actual) :: state

/-- Expansion reads the current declaration-scope and actual values. -/
theorem live_template (state : SvState) (held actual shadow : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state held actual shadow) templateExpression =
      .ok (held.add actual) := by
  rfl

/-- A same-spelled invocation local cannot capture the declaration's read. -/
theorem shadow_independent (state : SvState) (held actual first second : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state held actual first) templateExpression =
    evalSExpr (fuel + 8) (bindings state held actual second) templateExpression := by
  rfl

/-- The source's four-bit addition retains ordinary modular arithmetic. -/
theorem modular_template (state : SvState) (held actual : BitVec 4) (shadow : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state (.ofBitVec held) (.ofBitVec actual) shadow)
      templateExpression = .ok (.ofBitVec (held + actual)) := by
  rw [live_template, LVec.add_ofBitVec]

/-- Copyback retains earlier output and queued nonblocking publications. -/
theorem stored_template (state : SvState) (held actual shadow : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false) :
    execSStmt (fuel + 16) (bindings state held actual shadow) pending output assignment =
      .ok (SvState.set (bindings state held actual shadow) "result" (held.add actual),
           pending, output) := by
  unfold assignment
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

#print axioms live_template
#print axioms shadow_independent
#print axioms modular_template
#print axioms stored_template

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | _ => false

def fixtureReceipt : IO Unit := do
  let .ok certificate := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/let_expressions/certificate.sv.json")
    | throw (IO.userError "certificate failed to load")
  unless certificate.procs.any (fun process => match process with
      | .initial body => containsStatement assignment body
      | _ => false) do
    throw (IO.userError "let theorem differs from actual parsed source")
  unless certificate.decls.any (fun declaration =>
      declaration.name == shadowName && declaration.width == 4 && declaration.init.isNone) do
    throw (IO.userError "local binding differs from parsed source")
  for (name, expected) in [("binding", ["binding 4 15 9", "nested 4 27", "restored 4 9"]),
      ("certificate", ["certificate 1"]),
      ("local", ["local 14", "live-local 36"]),
      ("sizing", ["width 24 24 24", "state 1xz1 xxxx 0001"]),
      ("structure", ["structure 12 5 5", "live 17"]),
      ("timing", ["captured 7 14", "live-timing 16"]),
      ("unused", ["unused 5 42"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/let_expressions/{name}.sv.json")
      | throw (IO.userError s!"{name} load failed")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed load failed")
      let mut world := initial
      for _ in List.range 12 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (slotStep oracle 32768) world
          | throw (IO.userError s!"{name} slot refused")
        world := next
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (do advanceTime 1; wakeTimers) world
          | throw (IO.userError s!"{name} timer refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["effects", "call", "program"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/let_expressions/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
      match elabTimedDesign 32768 design with
      | .error _ => pure ()
      | .ok world =>
        match SvM.exec (slotStep ρ_src 32768) world with
        | .ok (.ok _, _) => throw (IO.userError s!"{name} lost refusal")
        | _ => pure ()

#eval fixtureReceipt
end Examples.systemVerilog.letExpressions.proof
