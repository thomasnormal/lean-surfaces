import LeanModels.Sv.Load
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.foreach.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- The certificate below binds these expressions to the actual mixed-dimension loop.
def cursor : String := "$foreach:237:$ordinal"
def offset (stride : Nat) : Expr :=
  .binary .rem (.binary .div (.ident cursor) (.lit (.ofNat 32 stride)))
    (.lit (.ofNat 32 3))
def condition : SExpr := .m0 (.binary .lt (.ident cursor) (.lit (.ofNat 32 9)))
def steps : Array SStmt := #[.m0 (.blockingAssign cursor
  (.binary .add (.ident cursor) (.lit (.ofNat 32 1))))]

/-- The extracted ordinal offsets compute the unsigned quotient and remainder. -/
theorem offset_evaluates (ordinal : BitVec 32) (fuel : Nat) (stride : Nat)
    (nonzero : (BitVec.ofNat 32 stride).toNat ≠ 0) :
    evalExpr (fuel + 8) [(cursor, .ofBitVec ordinal)] (offset stride) =
      .ok (.ofBitVec ((ordinal / BitVec.ofNat 32 stride) % BitVec.ofNat 32 3)) := by
  have literal (n : Nat) : LVec.ofNat 32 n = LVec.ofBitVec (BitVec.ofNat 32 n) := by
    simp only [LVec.ofBitVec, BitVec.toNat_ofNat, LVec.ofNat_emod]
  simp only [offset, evalExpr, readSignal, SvState.lookup, beq_self_eq_true,
    ↓reduceIte, Res.ok_bind, evalBinOp]
  rw [literal stride, LVec.div_ofBitVec _ _ nonzero, literal 3]
  change Res.ok ((LVec.ofBitVec (ordinal / BitVec.ofNat 32 stride)).rem
    (LVec.ofBitVec (BitVec.ofNat 32 3))) = _
  rw [LVec.rem_ofBitVec _ _ (by decide)]

/-- The admitted nine tuples cover the index space in rightmost-first order. -/
theorem tuple_coordinates (ordinal : Nat) (admitted : ordinal < 9) :
    ordinal / 3 % 3 < 3 ∧ ordinal / 1 % 3 < 3 ∧
      3 * (ordinal / 3 % 3) + ordinal / 1 % 3 = ordinal := by
  omega

/-- A break at the saved body boundary exits all dimensions without stepping. -/
theorem break_exits_all (state : SvState) (pending : NbaQueue) (output : Out)
    (body : SStmt) (fuel : Nat) (running : output.halted = false) :
    stepSStmt (fuel + 8) state pending { output with transfer := .breakLoop }
      (.forAfterBody condition steps body) =
      .ok (state, pending, { output with transfer := .normal }, .done) := by
  simp [stepSStmt, running]

#print axioms offset_evaluates
#print axioms tuple_coordinates
#print axioms break_exits_all

-- Complete independent source transcripts, 2026-10-20.
-- indices.sv SHA-256: 052c852abcc131fef789191e2d45fa754cebabdcb543834e96805ce3eeb236d9
-- signed_indices.sv SHA-256: 7c5d68d207d156cf0995c9c8e0cb480402a8c5aa41af0553e1349715b4ddbead
-- timers.sv SHA-256: 6df024822de11722c1b2a6c8092f425fd8b0f5d1acf0ccd90c4a07f4e1597be7
-- values.sv SHA-256: 2fb9ce74d65b9fce68fd4267a6f5ce40d49ca86a3a769daa73833f6d53e6524f
def fixtureReceipt : IO Unit := do
  let .ok values := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/foreach/values.sv.json")
    | throw (IO.userError "foreach values failed to load")
  let some (SProc.initial (.block statements)) := values.procs[0]?
    | throw (IO.userError "foreach process shape changed")
  let some (SStmt.block scope) := statements[1]?
    | throw (IO.userError "foreach implicit scope changed")
  let some (SStmt.block lowered) := scope[0]?
    | throw (IO.userError "foreach scope shape changed")
  let some (.forLoop _ test increment (.block bindings)) := lowered.back?
    | throw (IO.userError "foreach tuple loop shape changed")
  unless test == condition && increment == steps &&
      bindings[0]? == some (.m0 (.blockingAssign "$foreach:249:i"
        (.binary .sub (.lit (.ofNat 32 2)) (offset 3)))) &&
      bindings[1]? == some (.m0 (.blockingAssign "$foreach:251:j"
        (.binary .sub (.lit (.ofNat 32 3)) (offset 1)))) do
    throw (IO.userError "foreach coordinate certificate differs from extracted source")
  unless runSelfCheck values 4096 == Res.ok [
      "unpacked -1 1", "unpacked 0 2", "unpacked 1 3", "multi 4 221 outer 99 88",
      "skip 3", "skip 2", "skip 1", "empty 1", "tuple 2 3", "tuple 2 2", "tuple 2 1",
      "tuple 1 3", "tuple 1 2", "tuple 1 1", "tuple 0 3", "tuple 0 2", "tuple 0 1",
      "tuples 9", "nested_reentry 6", "packed 3 1", "packed 2 0", "packed 1 0",
      "invalid_negative 0", "invalid_min 0", "invalid_max 0", "invalid_unknown 0"] do
    throw (IO.userError "foreach values transcript disagrees")
  let .ok indices := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/foreach/signed_indices.sv.json")
    | throw (IO.userError "foreach signed indices failed to load")
  unless runSelfCheck indices 4096 == Res.ok [
      "negative -1 1", "negative -2 x", "negative -3 z", "positive 1 z",
      "positive 2 1", "positive 3 0", "minimum x x", "maximum x x", "unknown x x"] do
    throw (IO.userError "foreach signed-index transcript disagrees")
  let .ok wide := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/foreach/indices.sv.json")
    | throw (IO.userError "foreach wide indices failed to load")
  -- SYNTHETIC-ORACLE: tests=wide-index-admission | origin=spec | authority=sv-loops-contract | map=unresolved-wide-index:unsupported-class
  unless match runSelfCheck wide 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "unresolved wide unsigned index was silently admitted")
  let .ok timers := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/foreach/timers.sv.json")
    | throw (IO.userError "foreach timers failed to load")
  for oracle in [ρ_src, ρ_rev] do
    let .ok world := elabTimedDesign 4096 timers
      | throw (IO.userError "foreach timers refused")
    let .ok (.ok _, world) := SvM.exec (slotStep oracle 4096) world
      | throw (IO.userError "foreach initial slot refused")
    let mut world := world
    for _ in List.range 10 do
      let .ok (.ok _, next) := SvM.exec
          (do advanceTime 1; wakeTimers; slotStep oracle 4096) world
        | throw (IO.userError "foreach resumed slot refused")
      world := next
    unless world.out.flush == [
        "descending 4 1 1xz", "descending 3 0 z01", "descending 2 1 z01",
        "ascending 1 z", "ascending 2 1", "ascending 3 0", "outer 99 visits 3"] do
      throw (IO.userError "foreach timer transcript disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.foreach.proof
