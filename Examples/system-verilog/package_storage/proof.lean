import LeanModels.Sv.Load

namespace Examples.systemVerilog.packageStorage.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Certified against the exact imported write / qualified read in timers.sv.
def packageName : String := "$package:6:Shared:value"
def qualifiedRead : SExpr := .m0 (.ident packageName)
def importedWrite : SStmt :=
  .assign false packageName (.squash2 (.m0 (.lit (.ofNat 32 8))))
def importedNba : SStmt :=
  .assign true packageName (.squash2 (.m0 (.lit (.ofNat 32 13))))

private theorem lookup_set_self (state : SvState) (name : String) (value : LVec) :
    SvState.lookup (SvState.set state name value) name = some value := by
  induction state with
  | nil => simp [SvState.set, SvState.lookup]
  | cons binding rest ih =>
    rcases binding with ⟨key, old⟩
    simp only [SvState.set]
    split
    · simp_all [SvState.lookup]
    · simp_all [SvState.lookup]

/-- Every qualified/imported spelling reads the one current package slot. -/
theorem shared_read (state : SvState) (value : LVec) (fuel : Nat) :
    evalSExpr (fuel + 3) (SvState.set state packageName value) qualifiedRead = .ok value := by
  simp [qualifiedRead, evalSExpr, evalExpr, readSignal, lookup_set_self]

/-- The real imported blocking assignment immediately changes the shared slot. -/
theorem blocking_store (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) state pending output importedWrite =
      .ok (SvState.set state packageName (.ofNat 32 8), pending, output) := by
  have squashed : squash2v (.ofNat 32 8) = .ofNat 32 8 := by
    simp only [squash2v, LVec.toTwoState, LVec.ofNat, Array.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_def]
    split <;> rfl
  have evaluated : evalSExpr (fuel + 7) state (.squash2 (.m0 (.lit (.ofNat 32 8)))) =
      .ok (.ofNat 32 8) := by
    change Res.ok (squash2v (.ofNat 32 8)) = _
    rw [squashed]
  unfold importedWrite
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, evaluated, Res.ok_bind]
  rfl

/-- The real NBA captures its value without changing the package store early. -/
theorem nba_captures (state : SvState) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) state pending output importedNba =
      .ok (state, pending ++ [(packageName, .ofNat 32 13)], output) := by
  have squashed : squash2v (.ofNat 32 13) = .ofNat 32 13 := by
    simp only [squash2v, LVec.toTwoState, LVec.ofNat, Array.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_def]
    split <;> rfl
  have evaluated : evalSExpr (fuel + 7) state (.squash2 (.m0 (.lit (.ofNat 32 13)))) =
      .ok (.ofNat 32 13) := by
    change Res.ok (squash2v (.ofNat 32 13)) = _
    rw [squashed]
  unfold importedNba
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false, evaluated, Res.ok_bind]
  rfl

/-- Committing that captured update is visible to the qualified source read. -/
theorem committed_read (state : SvState) (fuel : Nat) :
    evalSExpr (fuel + 3) (commitNba state [(packageName, .ofNat 32 13)]) qualifiedRead =
      .ok (.ofNat 32 13) := by
  exact shared_read state (.ofNat 32 13) fuel

#print axioms shared_read
#print axioms blocking_store
#print axioms nba_captures
#print axioms committed_read

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

-- REFERENCE: 2843b0aede4a9eab93ee2521 24.03-s004 2026-10-20 | tests=identity | source=Examples/system-verilog/package_storage/identity.sv@sha256:0d7964f750258c288cecb9ef086e0af8b6e3d2926d6f31395837910ec51caf27 | top=top | args=["-ii_val"] | map=README.md#package-integral-singleton-storage
-- REFERENCE: 8f2ec4d535024ddcb5a22160 24.03-s004 2026-10-20 | tests=defaults | source=Examples/system-verilog/package_storage/defaults.sv@sha256:510ab4f197de034be2c8e17e4bce9f56592ede59d9f187912ed5ddb7efa8349a | top=top | args=["-ii_val"] | map=README.md#package-integral-singleton-storage
-- REFERENCE: e0a493f2f140ef2ada26881e 24.03-s004 2026-10-20 | tests=packed | source=Examples/system-verilog/package_storage/packed.sv@sha256:63ed7b450e19700b4f6d4f0bd87f38c9abc438de729afc1b1c71097869660a55 | top=top | args=["-ii_val"] | map=README.md#package-integral-singleton-storage
-- REFERENCE: fc2ea104ab01a2d6e0e51ffc 24.03-s004 2026-10-20 | tests=timers | source=Examples/system-verilog/package_storage/timers.sv@sha256:d48ab7996a04b86762a95aecc0c47849bcc1ebb2e917193aedf84db13ddf6905 | top=top | args=["-ii_val"] | map=README.md#package-integral-singleton-storage
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-boundaries | origin=spec | authority=docs/sv-package-storage.md | map=certificates:parsed-source-subtrees;dependent:initialization-order-contract;array:package-storage-type;subroutine:call-frame-contract

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
      ("identity", ["bound 4 4 20 boot 10", "shadow 11 6", "distinct 6 22"]),
      ("defaults", ["defaults xxxx 0000 1000 number 7", "constants 4 2 1001"]),
      ("packed", ["packed 9 6", "updated dc d d2"]),
      ("timers", ["before 5", "after 8", "later 13"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/package_storage/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "timers" then
      for certificate in [importedWrite, importedNba] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement certificate body
            | _ => false) do
          throw (IO.userError "assignment certificate differs from source")
      unless design.procs.any (fun process => match process with
          | .initial body => containsRead qualifiedRead body
          | _ => false) do
        throw (IO.userError "read certificate differs from source")
    if name != "timers" then
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok world := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, world) := SvM.exec (slotStep oracle 32768) world
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := world
      for _ in List.range 8 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} timed transcript differs")
  for name in ["dependent", "array", "subroutine"] do
    unless match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/package_storage/{name}.sv.json") with
        | .error _ => true
        | .ok _ => false do
      throw (IO.userError s!"{name} lost its design-level boundary")

#eval fixtureReceipt

end Examples.systemVerilog.packageStorage.proof
