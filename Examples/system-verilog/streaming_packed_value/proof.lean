import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.streamingPackedValue.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

def packetUnpack : SStmt :=
  .packedAssign [.whole "packet" 8 false, .whole "tail" 1 false]
    (.m0 (.lit (.lit "10110xz01")))

/-- The real fixture's unpack preserves x/z and leaves the other value alone. -/
theorem packet_unpack :
    execSStmt 32
      [("packet", .lit "xxxxxxxx"), ("tail", .lit "x"), ("shared", .lit "xxxx")]
      [] {} packetUnpack =
    .ok ([("packet", .lit "10110xz0"), ("tail", .lit "1"),
           ("shared", .lit "xxxx")], [], {}) := by
  rfl

#print axioms packet_unpack

def leadingUnpack : SStmt :=
  .packedAssign [.whole "shared" 4 false, .whole "tail" 1 false]
    (.selectRead 5 false false (.m0 (.lit (.lit "10xz1011")))
      (.m0 (.lit (.lit "00000000000000000000000000000011"))))

theorem leading_bits_unpack :
    execSStmt 32 [("shared", .lit "xxxx"), ("tail", .lit "x")]
      [] {} leadingUnpack =
    .ok ([("shared", .lit "10xz"), ("tail", .lit "1")], [], {}) := by
  have z1 : (Logic.l0 == Logic.l1) = false := by rfl
  have o1 : (Logic.l1 == Logic.l1) = true := by rfl
  have index : selectedIndex false (.lit "00000000000000000000000000000011") =
      some 3 := by
    change selectedIndex false
      ⟨#[.l1, .l1, .l0, .l0, .l0, .l0, .l0, .l0,
          .l0, .l0, .l0, .l0, .l0, .l0, .l0, .l0,
          .l0, .l0, .l0, .l0, .l0, .l0, .l0, .l0,
          .l0, .l0, .l0, .l0, .l0, .l0, .l0, .l0]⟩ = some 3
    simp [selectedIndex, LVec.toNat?, LVec.allKnown, LVec.toNat, Logic.isKnown,
      z1, o1]
  have selected : selectedRead 5 false false (.lit "10xz1011")
      (.lit "00000000000000000000000000000011") = .lit "10xz1" := by
    rw [selectedRead, index]
    simp [Array.ofFn_succ, LVec.lit, LVec.ofString?, Logic.ofChar?]
  simp [leadingUnpack, execSStmt, evalSExpr, evalExpr, selected,
    Bind.bind, Pure.pure]
  rfl

#print axioms leading_bits_unpack

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/streaming_packed_value/streaming_packed_value.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "whole packed streaming fixture failed to load")
  let some (SProc.initial (SStmt.block statements)) := design.procs[0]?
    | throw (IO.userError "whole packed streaming process shape changed")
  unless statements[3]? == some packetUnpack do
    throw (IO.userError "proved unpack differs from the extracted fixture")
  unless statements[9]? == some leadingUnpack do
    throw (IO.userError "proved leading-bit unpack differs from the fixture")
  unless runSelfCheck design 4096 ==
      .ok ["101 10xz0 1", "0110 0110", "PASS", "10xz 1"] do
    throw (IO.userError "whole packed streaming fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.streamingPackedValue.proof
