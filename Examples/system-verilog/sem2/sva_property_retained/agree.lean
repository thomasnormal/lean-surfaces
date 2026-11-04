/- The SVA members are envelope metadata; the retained sequential process
   remains loadable by the semantic tier. -/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.sva_property_retained.agree

open LeanModels.Sv

load_design_sv2 sva_property_retained from
  "Examples/system-verilog/sem2/sva_property_retained/sva_property_retained.sv.json"

end Examples.«system-verilog».sem2.sva_property_retained.agree
