import LeanModels.Sv.Load

namespace Examples.systemVerilog.runtimeClog2.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Exact runtime.sv RHS and both source assignments, checked below.
def expression : SExpr := .squash2 (.clog2 (.m0 (.ident "source")))
def blocking : SStmt := .assign false "captured" expression
def nba : SStmt := .assign true "captured" expression
def result (n : Nat) : LVec := .ofNat 32 (LeanModels.Sv.clog2 n)

private theorem squash_nat (width n : Nat) :
    squash2v (LVec.ofNat width n) = LVec.ofNat width n := by
  simp only [squash2v, LVec.toTwoState, LVec.ofNat, Array.map_ofFn]
  congr 1
  apply congrArg Array.ofFn
  funext i
  by_cases h : n.testBit i
  all_goals simp [Function.comp_apply, h]

/-- Every call reads the current finite-width bits as unsigned. -/
theorem live_value (state : SvState) (value : LVec) (n fuel : Nat)
    (known : value.toNat? = some n) :
    evalSExpr (fuel + 8) (("source", value) :: state) expression = .ok (result n) := by
  simp [expression, evalSExpr, evalExpr, readSignal, SvState.lookup, evalClog2, known, result, squash_nat]

/-- The source's one blocking store uses that current numeric result. -/
theorem blocking_store (state : SvState) (value : LVec) (n fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false)
    (known : value.toNat? = some n) :
    execSStmt (fuel + 12) (("source", value) :: state) pending output blocking =
      .ok (SvState.set (("source", value) :: state) "captured" (result n), pending, output) := by
  unfold blocking
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  simp [expression, evalSExpr, evalExpr, readSignal, SvState.lookup, evalClog2, known, result, squash_nat]

/-- The NBA keeps the current store and captures the computed integer now. -/
theorem nba_captures (state : SvState) (value : LVec) (n fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false)
    (known : value.toNat? = some n) :
    execSStmt (fuel + 12) (("source", value) :: state) pending output nba =
      .ok ((("source", value) :: state), pending ++ [("captured", result n)], output) := by
  unfold nba
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  simp [expression, evalSExpr, evalExpr, readSignal, SvState.lookup, evalClog2, known, result, squash_nat]

private theorem lookup_set_self (state : SvState) (name : String) (value : LVec) :
    SvState.lookup (SvState.set state name value) name = some value := by
  induction state with
  | nil => simp [SvState.set, SvState.lookup]
  | cons binding rest ih =>
    rcases binding with ⟨key, old⟩
    simp only [SvState.set]
    split <;> simp_all [SvState.lookup]

/-- A later source change cannot alter the already captured logarithm. -/
theorem captured_after_change (state : SvState) (replacement : LVec) (n fuel : Nat) :
    evalSExpr (fuel + 3)
      (commitNba (SvState.set state "source" replacement) [("captured", result n)])
      (.m0 (.ident "captured")) = .ok (result n) := by
  simp [commitNba, evalSExpr, evalExpr, readSignal, lookup_set_self]

/-- Unknown bits refuse before inventing a numeric result. -/
theorem unknown_refuses (state : SvState) (value : LVec) (fuel : Nat)
    (unknown : value.toNat? = none) :
    evalSExpr (fuel + 8) (("source", value) :: state) expression =
      .unsupported "$clog2 requires a fully known integral argument" := by
  simp [expression, evalSExpr, evalExpr, readSignal, SvState.lookup, evalClog2, unknown]

#print axioms live_value
#print axioms blocking_store
#print axioms nba_captures
#print axioms captured_after_change
#print axioms unknown_refuses

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: 75fcbe23ae3287ee1d4e265c 24.03-s004 2026-10-20 | tests=boundaries | source=Examples/system-verilog/runtime_clog2/boundaries.sv@sha256:8ca8c0743af11fdcfa4acb072c8f9432f3457bd767ff09e5b243c4d0ecc25cca | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: ee9dee815c79d790a755f320 24.03-s004 2026-10-20 | tests=widths | source=Examples/system-verilog/runtime_clog2/widths.sv@sha256:9579f87ddf2c5b37f34e1c38ad0d976b3d83a3730d0bca6d53b562e89bc9c49b | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: 095399d4f51567c5d5f07bb3 24.03-s004 2026-10-20 | tests=runtime | source=Examples/system-verilog/runtime_clog2/runtime.sv@sha256:91a76f3b708075d5563e0a9f0d20f59503a286e3b83e1531fef886fc43bc8997 | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: f81259281e8bd8de532f2d57 24.03-s004 2026-10-20 | tests=composition | source=Examples/system-verilog/runtime_clog2/composition.sv@sha256:1709f22fddc5a12151c89153ac2a301f44862f9563dff8c658dc9fa15e8d722c | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: 13a7eaa7ef3bf5385e485887 24.03-s004 2026-10-20 | tests=unknown | source=Examples/system-verilog/runtime_clog2/unknown.sv@sha256:c916bc02036eb8d368573372f9ca89948a4b3eb33accdfe6e1ce5c89d3a4b45f | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: 95758aa620f574674d9fcf15 24.03-s004 2026-10-20 | tests=constant_unknown | source=Examples/system-verilog/runtime_clog2/constant_unknown.sv@sha256:c3471514f62741b154e1f8d0b2d36cc7595b0cab95158510e6f678729159b400 | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: a6019d8fbd3a55391123361c 24.03-s004 2026-10-20 | tests=elaboration_unknown | source=Examples/system-verilog/runtime_clog2/elaboration_unknown.sv@sha256:a15af3c5e30a1fa77f901e6ab0c269c99fe95909e67a817f15e47263e8190652 | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- REFERENCE: 3c8737dc735a2b41c71840ea 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/runtime_clog2/effects.sv@sha256:b07f085ac67cbb82b5213204c1d00da65aa82a745c2bd10621cb1acc5d098797 | top=top | args=["-ii_val"] | map=README.md#runtime-integral-clog2
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-runtime-clog2.md | map=certificates:actual-parsed-statements;unknown:explicit-refusal;effects:pure-operand-contract;elaboration:no-approximate-bound-constant

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("boundaries", ["0:0 1:0 2:1 3:2 4:2 5:3 6:3 7:3 8:3 9:4 10:4 11:4 12:4 13:4 14:4 15:4 16:4 17:5 ", "neighbors 8 8 9"]),
      ("widths", ["unsigned 8 32 127", "contexts 128 0 128 32"]),
      ("runtime", ["before 4", "after 4 8"]),
      ("composition", ["composed 0803 0808 30", "selected"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/runtime_clog2/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "runtime" then
      for statement in [blocking, nba] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "clog2 statement certificate differs from source")
      unless blocking == SStmt.mkAssign false "captured" expression &&
          nba == SStmt.mkAssign true "captured" expression do
        throw (IO.userError "clog2 RHS certificate differs from source")
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
  for name in ["unknown", "constant_unknown", "elaboration_unknown", "effects"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/runtime_clog2/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
        unless match runSelfCheck design 32768 with
            | .unsupported _ => true
            | _ => false do
          throw (IO.userError s!"{name} lost its refusal boundary")

#eval fixtureReceipt

end Examples.systemVerilog.runtimeClog2.proof
