import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.packedUnionReshapedMember.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/packed_union_reshaped_member/packed_union_reshaped_member.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "packed-union-reshaped-member fixture failed to load")
  unless SelfCheck.runSelfCheck design 8192 == .ok ["PASS"] do
    throw (IO.userError "packed-union-reshaped-member fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.packedUnionReshapedMember.proof
