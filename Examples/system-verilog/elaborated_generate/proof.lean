import LeanModels.Sv.Load

namespace Examples.systemVerilog.elaboratedGenerate.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact generated declarations and selected write in scopes.sv.
def selectedName : String := "$generate:3:top:1:5:8:selected:340:value"
def innerName : String := "$generate:3:top:1:7:5:outer:1:1:5:inner:554:value"
def selectedRead : SExpr := .m0 (.ident selectedName)
def innerRead : SExpr := .m0 (.ident innerName)
def selectedWrite : SStmt := .m0 (.blockingAssign selectedName (.lit (.lit "1100")))

/-- A hierarchical source read sees the current selected scope's slot. -/
theorem current_selected (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 3) ((selectedName, value) :: state) selectedRead = .ok value := by
  rfl

/-- Updating the selected branch cannot overwrite the nested same-named declaration. -/
theorem scopes_separate (state : SvState) (nested replacement : LVec) (fuel : Nat) :
    evalSExpr (fuel + 3)
      (SvState.set ((innerName, nested) :: state) selectedName replacement) innerRead =
      .ok nested := by
  rfl

/-- The real generated initial statement uses the existing blocking-store rule. -/
theorem selected_store (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) state pending output selectedWrite =
      .ok (SvState.set state selectedName (.lit "1100"), pending, output) := by
  unfold selectedWrite
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

#print axioms current_selected
#print axioms scopes_separate
#print axioms selected_store

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

partial def containsRead (wanted : SExpr) (statement : SStmt) : Bool :=
  match statement with
  | .sysCall _ _ arguments => arguments.any (fun pair => pair.1 == wanted)
  | .block statements => statements.any (containsRead wanted)
  | _ => false

-- REFERENCE: fc136cfbf90bab730f8bc5c7 24.03-s004 2026-10-20 | tests=scopes | source=Examples/system-verilog/elaborated_generate/scopes.sv@sha256:731c8cdfeee28725d8dda239052265bb510673d24791924f877b274d458998c2 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: 311ec1cae87faabe5f32f495 24.03-s004 2026-10-20 | tests=loops | source=Examples/system-verilog/elaborated_generate/loops.sv@sha256:40791035a957f142aaa4e68753e287a5dc135309780d15e23b772fac6fd1a4d8 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: ed65b8cd91f52c01b476ae70 24.03-s004 2026-10-20 | tests=locals | source=Examples/system-verilog/elaborated_generate/locals.sv@sha256:1d3fcb36a549d5efb7ddda7b17cb7750ac5a08095d41dc1fcfd33224683214a2 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: f9a869bfebf2c592152915d9 24.03-s004 2026-10-20 | tests=captures | source=Examples/system-verilog/elaborated_generate/captures.sv@sha256:19285e28b06e77e510bbabf5ea6a60ac26957b651b3530eb1989c864e94da8d5 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: c79b8b4c56b4709eeb9895fd 24.03-s004 2026-10-20 | tests=imports | source=Examples/system-verilog/elaborated_generate/imports.sv@sha256:d6e3729343932f827dcd6c662dd7f21ad0536c35815c88f3f9eba9efe05f275d | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: a2670b6a5f84739295c7524e 24.03-s004 2026-10-20 | tests=parameters | source=Examples/system-verilog/elaborated_generate/parameters.sv@sha256:6f62e6bc89795379d3687d75d332c983ae8c93580cb6a97614178d2f9c87e112 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: b87baebe0d77de845059fe60 24.03-s004 2026-10-20 | tests=choices | source=Examples/system-verilog/elaborated_generate/choices.sv@sha256:abc0b9f2c9c4ad03acff8f3998d860bd795ac21b4ef5a99972bbc70dd73cc130 | top=top | args=["-ii_val"] | map=README.md#elaborated-generate-scopes
-- REFERENCE: d5eafc43f849efb620a0d48c 24.03-s004 2026-10-20 | tests=hierarchy | source=Examples/system-verilog/elaborated_generate/hierarchy.sv@sha256:d66d2003bc747d98520d1f95ee3a638df1f375862085570e409bdc0bfae0badb | top=top | args=["-ii_val"] | map=../module_hierarchy/README.md#static-module-hierarchy
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-elaborated-generate.md | map=certificates:parsed-source-subtrees;member:subroutine-frame-required;dependent:initialization-order-oracle

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("scopes", ["scopes 22 c 55 aa"]),
      ("loops", ["up 3 13 23", "down 6 7 8"]),
      ("locals", ["locals 16 19"]),
      ("captures", ["pending 0 0", "captured 30 31"]),
      ("imports", ["cells 2 8 3 9"]),
      ("parameters", ["parameters 10xz -3 c7 -3"]),
      ("choices", ["choices 1 2 3"]),
      ("hierarchy", ["instance 5"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/elaborated_generate/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "scopes" then
      unless design.decls.any (fun d => d.name == selectedName) &&
          design.decls.any (fun d => d.name == innerName) do
        throw (IO.userError "scope certificate differs from parsed declarations")
      unless design.procs.any (fun process => match process with
          | .initial body => containsStatement selectedWrite body
          | _ => false) do
        throw (IO.userError "selected write differs from source")
      for expression in [selectedRead, innerRead] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsRead expression body
            | _ => false) do
          throw (IO.userError "hierarchical read differs from source")
    if name == "parameters" || name == "choices" || name == "hierarchy" then
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 5 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete timed transcript differs")
  for name in ["member", "dependent"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/elaborated_generate/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
        unless match runSelfCheck design 32768 with
            | .unsupported _ => true
            | _ => false do
          throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.elaboratedGenerate.proof
