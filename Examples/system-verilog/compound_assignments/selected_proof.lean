import LeanModels.Sv.Load

namespace Examples.systemVerilog.compoundAssignments.selectedProof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact capture, read and store in runtime.sv's delayed operator assignment.
def address : String := "$compound:182:index"
def indexExpr : SExpr := .m0 (.ident address)
def current : SExpr := .compoundRead 2 false true (.m0 (.ident "data")) indexExpr
def rhs : SExpr := .binary .add current (.m0 (.lit (.lit "10")))
def capture : SStmt := .localDecl address 32 false (some (.m0 (.ident "index")))
def store : SStmt := .selectedAssign "data" 2 false true false indexExpr rhs

def addressed (state : SvState) (value position : LVec) : SvState :=
  (address, position) :: ("data", value) :: state

def replacement (value position : LVec) : LVec :=
  (selectedRead 2 false true value position).add (.lit "10")

/-- The dynamic address is evaluated once into the source's scoped temporary. -/
theorem capture_address (state : SvState) (position : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false) :
    execSStmt (fuel + 8) (("index", position) :: state) pending output capture =
      .ok (SvState.set (("index", position) :: state) address position, pending, output) := by
  unfold capture
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- The bound RMW reads live selected bits at the captured address. -/
theorem current_value (state : SvState) (value position : LVec) (fuel : Nat)
    (admitted : partialCompoundSelection 2 false true value position = false) :
    evalSExpr (fuel + 12) (addressed state value position) rhs =
      .ok (replacement value position) := by
  simp [rhs, current, indexExpr, addressed, address, evalSExpr, evalExpr,
    readSignal, SvState.lookup, compoundRead, admitted, replacement, evalBinOp]

/-- The blocking store preserves all pending NBA work and prior output. -/
theorem read_modify_store (state : SvState) (value position : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false)
    (admitted : partialCompoundSelection 2 false true value position = false) :
    execSStmt (fuel + 16) (addressed state value position) pending output store =
      .ok (SvState.set (addressed state value position) "data"
        (selectedWrite 2 false true value position (replacement value position)),
        pending, output) := by
  unfold store
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  simp [rhs, current, indexExpr, addressed, address, evalSExpr, evalExpr,
    readSignal, SvState.lookup, compoundRead, admitted, replacement, evalBinOp]

/-- An unknown captured address cannot update any packed bit. -/
theorem unknown_no_write (value replacement : LVec) :
    selectedWrite 2 false true value (.xVec 32) replacement = value := by
  have bitsUnknown : (LVec.xVec 32).allKnown = false := by
    change (Array.replicate 32 Logic.lx).all Logic.isKnown = false
    rw [Array.all_replicate]
    rfl
  have unknown : selectedIndex true (.xVec 32) = none := by
    simp [selectedIndex, toIntS?, LVec.toNat?, bitsUnknown]
  simp only [selectedWrite, unknown]

/-- A partial range refuses before claiming disputed copyback behavior. -/
theorem partial_refuses (state : SvState) (value position : LVec) (fuel : Nat)
    (partialRange : partialCompoundSelection 2 false true value position = true) :
    evalSExpr (fuel + 12) (addressed state value position) rhs =
      .unsupported "AssignmentExpression:compound-partial-range" := by
  simp [rhs, current, indexExpr, addressed, address, evalSExpr, evalExpr,
    readSignal, SvState.lookup, compoundRead, partialRange]

#print axioms capture_address
#print axioms current_value
#print axioms read_modify_store
#print axioms unknown_no_write
#print axioms partial_refuses

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: 3b0da8567885b6e7b1c9d487 24.03-s004 2026-10-20 | tests=scalars | source=Examples/system-verilog/compound_assignments/scalars.sv@sha256:6c8e2f06a4e96bc58f30a5ad7afa88f914626715d15987bebc30aa22d54508a1 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 54d45c124aece58b6e11c5b6 24.03-s004 2026-10-20 | tests=arrays | source=Examples/system-verilog/compound_assignments/arrays.sv@sha256:82132abad52f7ceec8fe2e1dac8d13e053b63df7c1bf1d89e332c7049f9d1164 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 6056c0c43fe579703fb21158 24.03-s004 2026-10-20 | tests=windows | source=Examples/system-verilog/compound_assignments/windows.sv@sha256:1bf58671eff37bd902e564a4289f17b588059bb99704f722a7305457d1c89d83 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 5100bbc95f5e99e41e34cdb1 24.03-s004 2026-10-20 | tests=members | source=Examples/system-verilog/compound_assignments/members.sv@sha256:849dd5b286e59718fa065ce0192826d8928c2a71a158c3ddc484de8cdd58611f | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 03628779cd44cd176d4fac09 24.03-s004 2026-10-20 | tests=two_state | source=Examples/system-verilog/compound_assignments/two_state.sv@sha256:17728831da41182dc30a11e5297aa87f5c4a92d2520348ec1bfd5f76e77df2e4 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: e34fc1a81396d088b6247fab 24.03-s004 2026-10-20 | tests=indices | source=Examples/system-verilog/compound_assignments/indices.sv@sha256:eb7b2c9ae131bd1f86bd7d2f96dbd32c51de77804ae777a595895554e919cee9 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: bd25eca831cc5c3fcf21bdce 24.03-s004 2026-10-20 | tests=runtime | source=Examples/system-verilog/compound_assignments/runtime.sv@sha256:d97828a9ff0515f62728763d9d6590bbd64ca113688b61f6e339b90206c6f172 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 325bc16153eb77200def554d 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/compound_assignments/effects.sv@sha256:9eface904611c385631bb770add88214e30f90b309dd9613b736d2d55907aea1 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 4e23194c885816e1b7f1c595 24.03-s004 2026-10-20 | tests=dynamic_rhs | source=Examples/system-verilog/compound_assignments/dynamic_rhs.sv@sha256:33d40cc91f06a0b150bf920437bcd24174aa7bb224deeb11868c13f0659308ec | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: c46010c8c83d0580650545ec 24.03-s004 2026-10-20 | tests=partial_windows | source=Examples/system-verilog/compound_assignments/partial_windows.sv@sha256:4c856d59fe8efb532ebf8e35877a16ab23dd9d1a24f478661739930681ec7c4d | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- REFERENCE: 8f68759e3e29235e636695f0 24.03-s004 2026-10-20 | tests=partial_members | source=Examples/system-verilog/compound_assignments/partial_members.sv@sha256:6cb037dae4a6f1cadba9a4a3d2196e877b9fb61efeb116150faf1160d0e736f5 | top=top | args=["-ii_val"] | map=README.md#selected-compound-assignments
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-compound-assignments.md | map=certificates:parsed-source;effects:pure-source;partial-range:measured-refusal;unknown-RHS:evaluate-before-no-store

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
    ("scalars", ["wide 8", "signed -42 -1", "operators 13"]),
    ("arrays", ["arrays 3 42 22 15 e0 48"]),
    ("windows", ["windows d2cc", "invalid d2cc"]),
    ("members", ["members 36e2", "invalid 36e2"]),
    ("two_state", ["two-state 3ae2 a b"]),
    ("indices", ["indices 10 23"]),
    ("runtime", ["before a3", "after 30"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/compound_assignments/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "runtime" then
      for statement in [capture, store] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "compound certificate differs from parsed source")
    else
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, first) := SvM.exec (slotStep oracle 32768) initial
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := first
      for _ in List.range 4 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["effects", "dynamic_rhs", "partial_windows", "partial_members"] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/compound_assignments/{name}.sv.json")
      | throw (IO.userError s!"{name} lost its executable refusal")
    match runSelfCheck design 32768 with
    | .unsupported message =>
        if name.startsWith "partial_" then
          unless message == "AssignmentExpression:compound-partial-range" do
            throw (IO.userError s!"{name} refused for a different reason")
    | _ => throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.compoundAssignments.selectedProof
