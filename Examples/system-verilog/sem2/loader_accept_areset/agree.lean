/- Clean-room active-high asynchronous-reset fixture. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.loader_accept_areset.agree
open LeanModels.Sv
load_design_sv2 loader_accept_areset from
  "Examples/system-verilog/sem2/loader_accept_areset/loader_accept_areset.sv.json"
#guard !loader_accept_areset.sem.hasUnsupported
end Examples.«system-verilog».sem2.loader_accept_areset.agree
