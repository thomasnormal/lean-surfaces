import LeanModels.Sv.Load

namespace Examples.systemVerilog.replication.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact replicated RHS and both assignments certified against runtime.sv below.
def group : Expr := .concat #[.ident "source"]
def pattern : SExpr := .m0 (.concat #[group, group, group])
def blockingPattern : SStmt := .m0 (.blockingAssign "bus" (.concat #[group, group, group]))
def nbaPattern : SStmt := .m0 (.nbaAssign "bus" (.concat #[group, group, group]))
def packed (value : LVec) : LVec :=
  LVec.concatMany #[LVec.concatMany #[value], LVec.concatMany #[value], LVec.concatMany #[value]]
def zeroMember : SExpr := .m0 (.concat #[.concat #[], .ident "tail"])

/-- A legal zero-count member adds no bits to the following live value. -/
theorem zero_identity (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 12) (("tail", value) :: state) zeroMember = .ok value := by
  simp [zeroMember, evalSExpr, evalExpr, evalExprs, readSignal, SvState.lookup,
    LVec.concatMany, Array.foldl, Array.append_empty]

/-- Replicated operands read current storage, retaining the declared bit order. -/
theorem live_value (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 12) (("source", value) :: state) pattern = .ok (packed value) := by
  rfl

/-- A whole packed replication is evaluated before its one blocking store. -/
theorem blocking_store (state : SvState) (value : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (("source", value) :: state) pending output blockingPattern =
      .ok (SvState.set (("source", value) :: state) "bus" (packed value), pending, output) := by
  unfold blockingPattern
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- An NBA captures every replicated bit now and leaves the current store intact. -/
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

/-- Changing the source after capture cannot change the committed replication. -/
theorem captured_after_change (state : SvState) (old replacement : LVec) (fuel : Nat) :
    evalSExpr (fuel + 3)
      (commitNba (SvState.set state "source" replacement) [("bus", packed old)])
      (.m0 (.ident "bus")) = .ok (packed old) := by
  simp [commitNba, evalSExpr, evalExpr, readSignal, lookup_set_self]

#print axioms zero_identity
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

-- REFERENCE: dd367f1c9930ad9ef818423b 24.03-s004 2026-10-20 | tests=groups | source=Examples/system-verilog/replication/groups.sv@sha256:442b5401adea5224ce478f0ffea3656231dcbceece29ced2d2758aee5e9749a3 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: ea3b24bcb0d74abf044527f8 24.03-s004 2026-10-20 | tests=contexts | source=Examples/system-verilog/replication/contexts.sv@sha256:73ca9bb2a20f6ccb4c3b0a098b5d0bc1f557c3a6d56f1b6bc54304f3677fc411 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 76ce4aafb8af810e6be3857e 24.03-s004 2026-10-20 | tests=zero | source=Examples/system-verilog/replication/zero.sv@sha256:b61afd8778978789acc82d140c874319093381e4e061c697b1fc205b70517076 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: eedfdc7b0ac8d953960f0a45 24.03-s004 2026-10-20 | tests=strings | source=Examples/system-verilog/replication/strings.sv@sha256:3250aa61d8f05cec3c2d74d8383922f30f8404fb8a0ea086ff3483480929abfa | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 92279376873ff5f7762286cd 24.03-s004 2026-10-20 | tests=runtime | source=Examples/system-verilog/replication/runtime.sv@sha256:3898bc7423c60255b3a2cf069fb2ac7e236c3a88c324099e4149b9e3febb8c4c | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 2dfaf773edef406694df62f5 24.03-s004 2026-10-20 | tests=composition | source=Examples/system-verilog/replication/composition.sv@sha256:58da8b985e7a99af509f2787d5149f8e45513bfb26cbbd4f98967b81e16e92dc | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 93f2b3254957c874835794a4 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/replication/effects.sv@sha256:577d4b5b807688b26805e13c17b07696e58ac2c67bebf2c3c8146c1dd9f014b2 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 82f4f2f0cc4388ec09b60d4e 24.03-s004 2026-10-20 | tests=dynamic_string | source=Examples/system-verilog/replication/dynamic_string.sv@sha256:97dcf8b72b43cef6c039b9dcf80d1964ab3175c1f8890ce45dc4eb5464972433 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: e120f6565740df8b0fcb3de5 24.03-s004 2026-10-20 | tests=based | source=Examples/system-verilog/replication/based.sv@sha256:64f8bfef9e338e70508eb36e99850d0c6e82eb659f244cbfa7219b71a81d0d35 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- REFERENCE: 149cc761ac4e0d96194c8bdb 24.03-s004 2026-10-20 | tests=constant_based | source=Examples/system-verilog/replication/constant_based.sv@sha256:1fe28d681247b220ea20bfed0a7f3f1d3d39852ec5746773bcec67fcb3eac944 | top=top | args=["-ii_val"] | map=README.md#integral-replication
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-replication.md | map=certificates:parsed-source-subtrees;effects:pure-operand-contract;strings:integral-only;elaboration:known-frontend-widening-gap

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("groups", ["groups 10xz10xz 101010101010 933a"]),
      ("contexts", ["contexts 0ff 9 00000000 1111 abab"]),
      ("zero", ["zero a5 3c3c"]),
      ("strings", ["strings 414142 410a410a"]),
      ("runtime", ["before xzxzxz", "after xzxzxz 101010"]),
      ("composition", ["composed a xzxz a a"]),
      ("based", ["based xxxxxxxxxxxxxxxxxxxxxx zzzzzzzzzzzzzzzzzzzzzz xxxxxxxxxxxxxxxxxxxxx1", "contexts 00000000000000xxxxxxxx xxxxxxxxxxxxxxxxxxxxxx 00000000000000xxxxxxxx 0000000000000000000000"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/replication/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "runtime" then
      for statement in [blockingPattern, nbaPattern] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "replication certificate differs from source")
      unless blockingPattern == SStmt.mkAssign false "bus" pattern &&
          nbaPattern == SStmt.mkAssign true "bus" pattern do
        throw (IO.userError "certified RHS differs from pattern")
    if name == "zero" then
      unless design.procs.any (fun process => match process with
          | .initial body => containsStatement (SStmt.mkAssign false "empty_then_tail" zeroMember) body
          | _ => false) do
        throw (IO.userError "empty-member certificate differs from source")
    if name != "runtime" then
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
  for name in ["effects", "dynamic_string", "constant_based"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/replication/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
        unless match runSelfCheck design 32768 with
            | .unsupported _ => true
            | _ => false do
          throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.replication.proof
