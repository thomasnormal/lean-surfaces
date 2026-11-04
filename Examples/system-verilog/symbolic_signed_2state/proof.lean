import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.Sem2

namespace Examples.systemVerilog.symbolicSignedTwoState.proof

open LeanModels.Sv

load_design_sv2 symbolic_signed_2state from
  "Examples/system-verilog/symbolic_signed_2state/symbolic_signed_2state.sv.json"

#guard symbolic_signed_2state.pdesign.params.length == 1
#guard (symbolic_signed_2state.pdesign.instantiateD2 [4]).hasUnsupported == false
#guard (((symbolic_signed_2state.pdesign.instantiateD2 [4]).decls[0]?.getD default).isSigned) == true
#guard (((symbolic_signed_2state.pdesign.instantiateD2 [4]).decls[0]?.getD default).twoState) == true
#guard (run2 (symbolic_signed_2state.pdesign.instantiateD2 [4]) σ_src 64
    [[("a", .lit "1000"), ("b", .lit "0001")]]).toOption.map
  (fun ts => (ts[0]?.getD []).lookup "y") == some (some (.lit "1000"))

end Examples.systemVerilog.symbolicSignedTwoState.proof
