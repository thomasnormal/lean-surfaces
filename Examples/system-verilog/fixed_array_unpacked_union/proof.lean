import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.fixedArrayUnpackedUnion.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/fixed_array_unpacked_union/fixed_array_unpacked_union.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "fixed-array-unpacked-union fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS"] do
    throw (IO.userError "fixed-array-unpacked-union self-check disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.fixedArrayUnpackedUnion.proof
