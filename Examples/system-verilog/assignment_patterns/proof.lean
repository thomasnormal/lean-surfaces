import LeanModels.Sv.Load

namespace Examples.systemVerilog.assignmentPatterns.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact keyed RHS and both assignments certified against runtime.sv below.
def pattern : SExpr := .m0 (.concat #[
  .ident "source", .lit (.lit "x"), .lit (.lit "z"), .lit (.lit "1")])
def blockingPattern : SStmt := .m0 (.blockingAssign "bus" (.concat #[
  .ident "source", .lit (.lit "x"), .lit (.lit "z"), .lit (.lit "1")]))
def nbaPattern : SStmt := .m0 (.nbaAssign "bus" (.concat #[
  .ident "source", .lit (.lit "x"), .lit (.lit "z"), .lit (.lit "1")]))
def packed (value : LVec) : LVec :=
  LVec.concatMany #[value, .lit "x", .lit "z", .lit "1"]

/-- Pattern operands read current storage, retaining the declared bit order. -/
theorem live_value (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 12) (("source", value) :: state) pattern = .ok (packed value) := by
  rfl

/-- A whole packed pattern is evaluated before its one blocking store. -/
theorem blocking_store (state : SvState) (value : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (("source", value) :: state) pending output blockingPattern =
      .ok (SvState.set (("source", value) :: state) "bus" (packed value), pending, output) := by
  unfold blockingPattern
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- An NBA captures every pattern bit now and leaves the current store intact. -/
theorem nba_captures (state : SvState) (value : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (("source", value) :: state) pending output nbaPattern =
      .ok (("source", value) :: state, pending ++ [("bus", packed value)], output) := by
  unfold nbaPattern
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

private theorem lookup_set_self (state : SvState) (name : String) (value : LVec) :
    SvState.lookup (SvState.set state name value) name = some value := by
  induction state with
  | nil => simp [SvState.set, SvState.lookup]
  | cons binding rest ih =>
    rcases binding with ⟨key, old⟩
    simp only [SvState.set]
    split <;> simp_all [SvState.lookup]

/-- Changing the source after capture cannot change the committed pattern. -/
theorem captured_after_change (state : SvState) (old replacement : LVec) (fuel : Nat) :
    evalSExpr (fuel + 3)
      (commitNba (SvState.set state "source" replacement) [("bus", packed old)])
      (.m0 (.ident "bus")) = .ok (packed old) := by
  simp [commitNba, evalSExpr, evalExpr, readSignal, lookup_set_self]

#print axioms live_value
#print axioms blocking_store
#print axioms nba_captures
#print axioms captured_after_change

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: 1842a47481c2d070a61097b6 24.03-s004 2026-10-20 | tests=keys | source=Examples/system-verilog/assignment_patterns/keys.sv@sha256:bcd982ec66249bae5119b7d56d8e38a8888d6c29fd39d15d344fe55fb48e09e9 | top=top | args=["-ii_val"] | map=README.md#integral-assignment-patterns
-- REFERENCE: 53f556301c09b00c5be308c6 24.03-s004 2026-10-20 | tests=structs | source=Examples/system-verilog/assignment_patterns/structs.sv@sha256:427ec1fd61fffc782a3645477239b2f700e7193b429fc13d6c507904ddbb635e | top=top | args=["-ii_val"] | map=README.md#integral-assignment-patterns
-- REFERENCE: 5d13b1492210d37b8a0885a2 24.03-s004 2026-10-20 | tests=runtime | source=Examples/system-verilog/assignment_patterns/runtime.sv@sha256:2ad9b3d943f6abc376b90c5c5108712217f828dc9977cf43283da1e2138ab2f3 | top=top | args=["-ii_val"] | map=README.md#integral-assignment-patterns
-- REFERENCE: 188772ccb43e73965ca6cf35 24.03-s004 2026-10-20 | tests=arrays | source=Examples/system-verilog/assignment_patterns/arrays.sv@sha256:09b3c14612ccedb48530c6fba4e9f051afb00975d06263f1a267f60a85f74fb2 | top=top | args=["-ii_val"] | map=README.md#integral-assignment-patterns
-- REFERENCE: 1de368cf665a451a686f34b5 24.03-s004 2026-10-20 | tests=replicated | source=Examples/system-verilog/assignment_patterns/replicated.sv@sha256:a1f14a900966afa0ed420c15d5e94a67ee12f2584827f161300f3bcd439b93cf | top=top | args=["-ii_val"] | map=README.md#integral-assignment-patterns
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-assignment-patterns.md | map=certificates:parsed-source-subtrees;effects:pure-operand-contract;multidim:existing-storage-boundary;self-alias:split-cell-RHS-capture-required

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("keys", ["keys 80808100 0xx1 1zz0"]),
      ("structs", ["structs 39a5 12345 -2 1001"]),
      ("arrays", ["arrays 30 20 10 7 8 9 34 12", "updated 60 50 40 78 56"]),
      ("replicated", ["repeated 10101010 xz01xz01"]),
      ("runtime", ["live 1xz1 9 2", "captured 1xz1 0"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/assignment_patterns/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "runtime" then
      for statement in [blockingPattern, nbaPattern] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "pattern certificate differs from source")
      unless blockingPattern == SStmt.mkAssign false "bus" pattern &&
          nbaPattern == SStmt.mkAssign true "bus" pattern do
        throw (IO.userError "certified RHS differs from pattern")
    else
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 4 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["effects", "multidim", "self_alias"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/assignment_patterns/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
        unless match runSelfCheck design 32768 with
            | .unsupported _ => true
            | _ => false do
          throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.assignmentPatterns.proof
