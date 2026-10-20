import LeanModels.Sv.Load
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.plusargs.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- These are bound to the actual loaded fixture by fixtureReceipt below.
def selectedCopyback : SStmt := .packedAssign
  [.selected "word" 8 false true false (.m0 (.lit (.ofNat 32 4)))]
  (.m0 (.lit (.ofNat 8 165)))
def absentCopyback : SStmt := .m0 (.block #[
  .blockingAssign "$plusargs:8" (.lit (.ofNat 32 0))])

/-- The fixture's earlier COUNT argument wins for every later argument list. -/
theorem first_count (later : List String) :
    Plusargs.first ("COUNT=7" :: later) "COUNT=" = some "COUNT=7" := by
  exact Plusargs.first_cons_hit _ _ _ (by decide)

/-- Absence retains every bit of the selected word, prior NBA work and output. -/
theorem absence_retains_state (word oldResult : LVec) (pending : NbaQueue)
    (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) [("word", word), ("$plusargs:8", oldResult)] pending output
      absentCopyback =
      .ok ([("word", word), ("$plusargs:8", .ofNat 32 0)], pending, output) := by
  simp [absentCopyback, execSStmt, execStmt, execStmts, evalExpr, SvState.set, running]

/-- The extracted selected copyback uses the same selected write for any word. -/
theorem selected_copyback (word : LVec) (pending : NbaQueue) (output : Out)
    (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 8) [("word", word)] pending output selectedCopyback =
      .ok ([("word", selectedWrite 8 false true word (.ofNat 32 4) (.ofNat 8 165))],
        pending, output) := by
  simp [selectedCopyback, execSStmt, execPackedTargets, packedTargetSlices,
    rightToLeftAssignmentOrder, validAssignmentOrder, evalSExpr, evalExpr,
    SvState.lookup, SvState.set, PackedTarget.width, List.eraseDups, running] <;> rfl

#print axioms first_count
#print axioms absence_retains_state
#print axioms selected_copyback

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | _ => false

-- Complete independent source transcripts, 2026-10-20.
-- values.sv SHA-256: 009aee618cb61087cb1f8d9c48a9ffa29c572748d766824363d52f87aca05766
-- timers.sv SHA-256: dd22d31d326481b04233f1f0ce8e4ca242891e7c79a51e1f2d146615ef25fbc4
-- numeric.sv SHA-256: f147107c51f30e39eb082389f66e5ce22e2f5c8d0aa2bf82d1816cd9a5b9fc21
-- diagnostic.sv SHA-256: feefe5af77db4ded9ae58c02f072f86481cf4feeccf82199faf38e14605f585d
def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/plusargs/values.sv.json"
  -- SYNTHETIC-ORACLE: tests=explicit-plusarg-environment | origin=spec | authority=IEEE-1800-2023#21.6 | map=missing-environment:refusal
  if (loadEnvelopeDesign text).isOk then
    throw (IO.userError "input-dependent fixture accepted an unspecified environment")
  let .ok values := loadEnvelopeDesignWithPlusargs
      ["COUNT=7", "COUNT=9", "NEG=-17", "MASK=10xz", "OCT=777", "HEX=a5"] text
    | throw (IO.userError "plusargs values failed to load")
  let some (SProc.initial body) := values.procs[0]?
    | throw (IO.userError "plusargs process shape changed")
  unless containsStatement selectedCopyback body && containsStatement absentCopyback body do
    throw (IO.userError "plusargs copyback certificates differ from source")
  unless runSelfCheck values 4096 == Res.ok [
      "prefix 1 1 0 1", "first 1 7", "signed 1 -17", "unknown 1 000010xz",
      "octal 1 ff", "hex 1 a5", "two_state 1 00001000", "selected 1 10xz1010010101zx",
      "absent 0 10xz1010010101zx", "ordered yes", "short 77",
      "unknown_left 00000000000000000000000000000000 -17", "left_write 1 -17"] do
    throw (IO.userError "plusargs values transcript differs")
  let .ok numbers := loadEnvelopeDesignWithPlusargs
      ["DEC=255", "SMALL=5", "NEG=-17", "DSEP=_1_2_", "BSEP=_1_0xz", "HSEP=1__a"]
      (← IO.FS.readFile "Examples/system-verilog/plusargs/numeric.sv.json")
    | throw (IO.userError "plusargs numeric fixture refused")
  unless runSelfCheck numbers 4096 == Res.ok [
      "truncated 1 f", "padded 1 0000000000000005", "negative 1 ef",
      "decimal_separators 1 12", "binary_separators 1 000010xz", "hex_separators 1 1a"] do
    throw (IO.userError "plusargs numeric transcript differs")
  -- SYNTHETIC-ORACLE: tests=diagnostic-plusarg-conversion | origin=spec | authority=plusargs-admission-contract | map=unresolved-diagnostic-observations:refusal
  if (loadEnvelopeDesignWithPlusargs ["BAD=12q"]
      (← IO.FS.readFile "Examples/system-verilog/plusargs/diagnostic.sv.json")).isOk then
    throw (IO.userError "malformed conversion silently accepted")
  let .ok timers := loadEnvelopeDesignWithPlusargs ["BYTE=a5"]
      (← IO.FS.readFile "Examples/system-verilog/plusargs/timers.sv.json")
    | throw (IO.userError "plusargs timers failed to load")
  for oracle in [ρ_src, ρ_rev] do
    let .ok world := elabTimedDesign 4096 timers
      | throw (IO.userError "plusargs timed design refused")
    let .ok (.ok _, world) := SvM.exec (slotStep oracle 4096) world
      | throw (IO.userError "plusargs initial slot refused")
    let mut world := world
    for _ in List.range 4 do
      let .ok (.ok _, next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
        | throw (IO.userError "plusargs resumed slot refused")
      world := next
    unless world.out.flush == ["write 1 10xz1010010101zx", "absent 0 z10xzzzzxxxxxz10",
        "write 1 z10x10100101xz10", "absent 0 z10xzzzzxxxxxz10"] do
      throw (IO.userError "plusargs timer transcript differs")

#eval fixtureReceipt

end Examples.systemVerilog.plusargs.proof
