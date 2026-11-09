import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.netAlias.proof

open LeanModels.Sv

set_option autoImplicit false

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/net_alias/net_alias.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "net-alias fixture failed to load")
  unless match SelfCheck.runSelfCheck design 16384 with
    | .unsupported msg => msg.startsWith "Initial:order:"
    | _ => false do
    throw (IO.userError "net_alias fixture disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.netAlias.proof
