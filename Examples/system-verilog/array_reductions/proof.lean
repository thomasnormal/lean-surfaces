import LeanModels.Sv.Load
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.arrayReductions.proof
open LeanModels.Sv LeanModels.Sv.SelfCheck
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- REFERENCE: 20342820699402559b0932d2 24.03-s004 2026-10-20 | tests=automatic | source=Examples/system-verilog/array_reductions/automatic.sv@sha256:0a84696634115fb9899678a93e4b0b1fa0aad2bb09d43e7c804c74a4a4e15d2f | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: 27f88ac7e35aa6420a9a16cc 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/array_reductions/certificate.sv@sha256:2a712f2333e66dde2a1f17f0adc36cf244cab94b273564c85ff2cc389c7d2397 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: 358a4cf082915bd4bd384e91 24.03-s004 2026-10-20 | tests=effect | source=Examples/system-verilog/array_reductions/effect.sv@sha256:49d0492c529634c3636ea44e8a499623994c947aa977dc5b32b85f23113165e5 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: 1bcd6d321b3b28a57409497c 24.03-s004 2026-10-20 | tests=iterator_index | source=Examples/system-verilog/array_reductions/iterator_index.sv@sha256:48e2c7d3c948b0a0a622930ac5048ccf17d094c833bc484ef9a7306ae2529e4c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: 19fe8d2083e458b2a9c0abe2 24.03-s004 2026-10-20 | tests=nested | source=Examples/system-verilog/array_reductions/nested.sv@sha256:a9755dd4e0b09ea7a29a0c9aedf91444e42681a4791970e20e605366eeeeab57 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: d98ddf292ef8f4197be1b0bd 24.03-s004 2026-10-20 | tests=rules | source=Examples/system-verilog/array_reductions/rules.sv@sha256:6fa2f5b8b605ba88d7424382532150b6edc04ad8ce80e63f83277149b05f0477 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: bf01345e37e9a61d5be348c4 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/array_reductions/structure.sv@sha256:7e29e2cf3e0decae5679f41ba0cec29525b6e3b44b40a502fbc5e1fbde6ce557 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- REFERENCE: 5560a8c58d2746d40128c5b3 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/array_reductions/timing.sv@sha256:b8e49ae2b87e6ea172fe13f2d3f219ae83a6695cb0d61dc244c1b390b4f44cf0 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
-- SYNTHETIC-ORACLE: tests=binding-and-admission | origin=spec | authority=docs/sv-array-reductions.md#fixed-array-reduction-methods | map=width:intrinsic-element-or-with;binding:actual-symbol;depth:balanced-pure-operators;barriers:storage-effects-types-invalid;certificates:actual-parsed-assignment

/-- The actual two-cell sum in certificate.sv, in declared index order. -/
def sumExpression : SExpr := .m0 (.binary .add (.ident "cells[1]") (.ident "cells[0]"))
def assignment : SStmt := .m0 (.blockingAssign "result"
  (.binary .add (.ident "cells[1]") (.ident "cells[0]")))
def bindings (state : SvState) (left right : LVec) : SvState :=
  ("cells[1]", left) :: ("cells[0]", right) :: state

/-- Reduction reads the current values of both original array cells. -/
theorem live_sum (state : SvState) (left right : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state left right) sumExpression =
      .ok (left.add right) := by
  rfl

/-- The four-bit source sum wraps modulo its intrinsic width. -/
theorem modular_sum (state : SvState) (left right : BitVec 4) (fuel : Nat) :
    evalSExpr (fuel + 8) (bindings state (.ofBitVec left) (.ofBitVec right)) sumExpression =
      .ok (.ofBitVec (left + right)) := by
  rw [live_sum, LVec.add_ofBitVec]

/-- Copyback changes the result while retaining pending work and output. -/
theorem stored_sum (state : SvState) (left right : LVec) (fuel : Nat)
    (pending : NbaQueue) (output : Out) (running : output.halted = false) :
    execSStmt (fuel + 16) (bindings state left right) pending output assignment =
      .ok (SvState.set (bindings state left right) "result" (left.add right), pending, output) := by
  unfold assignment
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- The reduction assignment does not mutate either source array cell. -/
theorem preserves_sources (state : SvState) (left right : LVec) :
    SvState.lookup (SvState.set (bindings state left right) "result" (left.add right)) "cells[1]" =
      some left ∧
    SvState.lookup (SvState.set (bindings state left right) "result" (left.add right)) "cells[0]" =
      some right := by
  exact ⟨rfl, rfl⟩

#print axioms live_sum
#print axioms modular_sum
#print axioms stored_sum
#print axioms preserves_sources

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | _ => false

def fixtureReceipt : IO Unit := do
  let .ok certificate := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/array_reductions/certificate.sv.json")
    | throw (IO.userError "certificate failed to load")
  unless certificate.procs.any (fun process => match process with
      | .initial body => containsStatement assignment body
      | _ => false) do
    throw (IO.userError "reduction theorem differs from actual parsed source")
  for (name, expected) in [
      ("automatic", ["automatic 5 -6"]),
      ("certificate", ["certificate 1"]),
      ("nested", ["nested 20 100 200", "live-with 23"]),
      ("rules", ["sum 4 20 50", "product 10 90", "signed -6 -6", "bits 0x0x 1111 0x0x", "map 2 3"]),
      ("structure", ["instances 11 8", "fields 6 80"]),
      ("timing", ["snapshot 9 26 9", "live 34 24"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/array_reductions/{name}.sv.json")
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
  for name in ["effect", "iterator_index"] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/array_reductions/{name}.sv.json")
      | throw (IO.userError s!"{name} load failed")
    let .ok world := elabTimedDesign 32768 design
      | throw (IO.userError s!"{name} timed load failed")
    match SvM.exec (slotStep ρ_src 32768) world with
    | .ok (.ok _, _) => throw (IO.userError s!"{name} lost refusal")
    | _ => pure ()

#eval fixtureReceipt
end Examples.systemVerilog.arrayReductions.proof
