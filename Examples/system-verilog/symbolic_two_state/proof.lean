import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.Sem2

namespace Examples.systemVerilog.symbolicTwoState.proof

open LeanModels.Sv

load_design_sv2 symbolic_two_state from
  "Examples/system-verilog/symbolic_two_state/symbolic_two_state.sv.json"

#guard symbolic_two_state.pdesign.params == []
#guard (symbolic_two_state.pdesign.instantiateD2 []).hasUnsupported == false
#guard (((symbolic_two_state.pdesign.instantiateD2 []).decls[0]?.getD default).twoState) == true
#guard (((symbolic_two_state.pdesign.instantiateD2 []).decls[1]?.getD default).twoState) == true
#guard (run2 (symbolic_two_state.pdesign.instantiateD2 []) σ_src 64
    [[("a", .lit "x")]]).toOption.map
  (fun ts => (ts[0]?.getD []).lookup "y") == some (some (.lit "0"))

end Examples.systemVerilog.symbolicTwoState.proof
