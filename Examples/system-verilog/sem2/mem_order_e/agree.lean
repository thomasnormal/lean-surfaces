import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! E admission guard for an out-of-order continuous-driver chain beside memory.
The source simulator settles `b = a` before observing `y = b`; MemE's one-pass
profile refuses the shape instead of returning a stale `y`. -/
namespace Examples.«system-verilog».sem2.mem_order_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 orderE
  from "Examples/system-verilog/sem2/mem_order_e/mem_order_e.sv.json"

private def twoStateProbe : MemEDesign :=
  { name := "two_state_start"
    env := {}
    decls := [⟨"q", 2, false, true, false, false, false,
      some (LVec.lit "xz")⟩]
    memDecls := []
    processes := [] }

-- IEEE 1800-2023 §6.8: x/z at startup converts to zero for a two-state declaration.
#guard (MemEDesign.init twoStateProbe).scalar == [("q", LVec.ofNat 2 0)]

#guard match MemEDesign.ofPDesign orderE.pdesign [] with
  | .unsupported msg =>
      msg == "Schedule:comb-source-order: comb process 0 reads a signal written by later comb process 1; the source-order memory pass would need a second settle pass under IEEE 1800-2023 §10.3/§4.5"
  | _ => false

end Examples.«system-verilog».sem2.mem_order_e
