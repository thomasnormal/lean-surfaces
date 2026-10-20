import LeanModels.Sv.Load

namespace Examples.systemVerilog.moduleHierarchy.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- The actual distinct instance storage and parsed assignments in isolation.sv.
def leftName : String := "$hierarchy:3:top:10:$hierarchy:1:0:4:left:58:value"
def rightName : String := "$hierarchy:3:top:10:$hierarchy:1:1:5:right:58:value"
def bindings (state : SvState) (left right : LVec) : SvState :=
  (leftName, left) :: (rightName, right) :: state

def blocking : SStmt := .m0 (.blockingAssign leftName (.lit (.lit "00110011")))
def nba : SStmt := .m0 (.nbaAssign rightName (.ident leftName))

/-- A hierarchical read sees the current value of its actual instance slot. -/
theorem live_value (state : SvState) (left right : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state left right) (.m0 (.ident leftName)) = .ok left := by
  rfl

/-- The parsed blocking assignment changes only its original destination. -/
theorem blocking_store (state : SvState) (left right : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (bindings state left right) pending output blocking =
      .ok (SvState.set (bindings state left right) leftName (.lit "00110011"), pending, output) := by
  unfold blocking
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- Updating one instance does not change its same-definition sibling. -/
theorem sibling_preserved (state : SvState) (left right replacement : LVec) :
    SvState.lookup (SvState.set (bindings state left right) leftName replacement) rightName =
      some right := by
  rfl

/-- A cross-instance NBA captures the source now and preserves current storage. -/
theorem nba_captures (state : SvState) (left right : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (bindings state left right) pending output nba =
      .ok (bindings state left right, pending ++ [(rightName, left)], output) := by
  unfold nba
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- Later source changes cannot alter the value already captured for its sibling. -/
theorem captured_after_change (state : SvState) (left right replacement : LVec) :
    commitNba (SvState.set (bindings state left right) leftName replacement) [(rightName, left)] =
      (leftName, replacement) :: (rightName, left) :: state := by
  rfl

#print axioms live_value
#print axioms blocking_store
#print axioms sibling_preserved
#print axioms nba_captures
#print axioms captured_after_change

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: b05b086e84da0718bb4efd59 24.03-s004 2026-10-20 | tests=isolation | source=Examples/system-verilog/module_hierarchy/isolation.sv@sha256:58f1de79feab7c676401bdd7ca41bf17c57efd0f772733286ba4fb545ea15f02 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: 2baf3fa00845f0d6726cf5e2 24.03-s004 2026-10-20 | tests=nested | source=Examples/system-verilog/module_hierarchy/nested.sv@sha256:7599f454d9166acc336c927061835a147224c6799967485caabff896ae5f310d | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: 75385d02e64d838f328846a4 24.03-s004 2026-10-20 | tests=arrays | source=Examples/system-verilog/module_hierarchy/arrays.sv@sha256:2f4664d266dc515662fb9a843cfcef3d837e8c4cd3b4d2b3b07f7b3cbf0cca65 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: 6056c5d8241d48f9d912f18d 24.03-s004 2026-10-20 | tests=locals_timing | source=Examples/system-verilog/module_hierarchy/locals_timing.sv@sha256:88f8dd387784b7a6504f5aa8c5774bd6898ec17ed1aacb57b25b2b95810990c5 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: dc2f06ab607035ca9459bb25 24.03-s004 2026-10-20 | tests=shared_package | source=Examples/system-verilog/module_hierarchy/shared_package.sv@sha256:fbefc7ee9d232cdc73f2114f0b5ba00a4d016adc92e110126f92bc5fdf7605e8 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: c26913132f0e3cb1ae8a4313 24.03-s004 2026-10-20 | tests=parameters | source=Examples/system-verilog/module_hierarchy/parameters.sv@sha256:ca6bfad08382fdfd73fda6e712c4296155ea59268b7c7ed7e95fa4861a1b0350 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: f554919f814b768c951ce265 24.03-s004 2026-10-20 | tests=ports | source=Examples/system-verilog/module_hierarchy/ports.sv@sha256:2a3714921a7c2714392c5402a6c299262e6f2a16bed19a99cfe0762187745dad | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: c5c847a2dc72bfe3d1b5cc96 24.03-s004 2026-10-20 | tests=program_kind | source=Examples/system-verilog/module_hierarchy/program_kind.sv@sha256:d1d3d64558ecc4dafe7734dcb2e0e5a0e0c307fbd59a441286dab7766d70eaa4 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: ee8714f2a4cf6e37caa01906 24.03-s004 2026-10-20 | tests=initializer | source=Examples/system-verilog/module_hierarchy/initializer.sv@sha256:b2c565aa68bb9c8609deb4055fd892f7933f0b479f6318b0ee3a6ba0e7d69b9c | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: 0963959003dff2b501ae4b57 24.03-s004 2026-10-20 | tests=timescale | source=Examples/system-verilog/module_hierarchy/timescale.sv@sha256:23ee1928880921ed2b076a5571c852053a347937ae4d1ec9de3e0a78678c8bb3 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- REFERENCE: 9f39189729f25f270a2890d3 24.03-s004 2026-10-20 | tests=storage | source=Examples/system-verilog/module_hierarchy/storage.sv@sha256:8cb77f64a1b76e6d308f8a65da3358ab2764afc20bbc7a4873ac8641aa0c78e7 | top=top | args=["-ii_val"] | map=README.md#static-module-hierarchy
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-module-hierarchy.md | map=certificates:actual-parsed-statement-and-distinct-declarations;ports:unmodelled-propagation;program:module-only;initializer:order-oracle-required;timescale:no-rescaling

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
    ("storage", ["storage 32 32 32 13", "separate 33 22"]),
    ("isolation", ["before 11 11", "blocking 21 11", "captured 33 21"]),
    ("nested", ["nested 5 02 12"]),
    ("arrays", ["array 11 3 3 22", "grid 3 3 3 33"]),
    ("locals_timing", ["locals 6 6 9"]),
    ("shared_package", ["shared 3"]),
    ("parameters", ["parameters 4 f 8 ff 12 fff"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/module_hierarchy/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "isolation" then
      unless design.decls.any (fun declaration => declaration.name == leftName) &&
          design.decls.any (fun declaration => declaration.name == rightName) && leftName != rightName do
        throw (IO.userError "instance storage differs from parsed declarations")
      for statement in [blocking, nba] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "hierarchy certificate differs from parsed source")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, first) := SvM.exec (slotStep oracle 32768) initial
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := first
      for _ in List.range 8 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["ports", "program_kind", "initializer", "timescale"] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/module_hierarchy/{name}.sv.json")
      | throw (IO.userError s!"{name} lost its executable refusal")
    match elabTimedDesign 32768 design with
    | .error _ => pure ()
    | _ => throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.moduleHierarchy.proof
