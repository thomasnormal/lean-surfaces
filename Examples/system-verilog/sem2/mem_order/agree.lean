import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».sem2.mem_order.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 memOrder from
  "Examples/system-verilog/sem2/mem_order/mem_order.sv.json"

#guard match (memOrder.pdesign.instantiateMemD2 []).memoryOrderReport with
  | some (k, msg) => k == "Schedule:comb-source-order" &&
      msg.startsWith "comb process 0 reads a signal written by later comb process 1"
  | none => false

end Examples.«system-verilog».sem2.mem_order.agree
