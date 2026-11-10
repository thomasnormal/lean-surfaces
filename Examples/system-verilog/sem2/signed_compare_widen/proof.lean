import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.RunEArray

namespace Examples.«system-verilog».sem2.signed_compare_widen

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 signedCompareWiden
  from "Examples/system-verilog/sem2/signed_compare_widen/signed_compare_widen.sv.json"

-- Keep the parser's sign extension and signed comparison visible in E's input.
#guard match signedCompareWiden.sem.processes.toList with
  | [.assign (.ident "y") (.scmp .ge (.resizeSigned 32 (.ident "x")) (.lit _))] => true
  | _ => false

private def e : Elab := Elab.ofDesign2 signedCompareWiden.sem

-- Four points straddling signed zero and the sign bit, executed through E.
#guard (runE0Array e σ_src 100 [
    [("x", .ofNat 8 0)], [("x", .ofNat 8 127)],
    [("x", .ofNat 8 128)], [("x", .ofNat 8 255)] ]).toOption.map
    (fun rows => rows.map (fun row => SvState.showSignal (e.view row.2.store) "y")) ==
  some ["1", "1", "0", "0"]

end Examples.«system-verilog».sem2.signed_compare_widen
