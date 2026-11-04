/-
A known one-bit replication in a typed integer localparam is evaluated in the
constant tier at its source replication width, then assigned to the integer.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.constant_replication.agree

open LeanModels.Sv

load_design_sv2 constant_replication from
  "Examples/system-verilog/sem2/constant_replication/constant_replication.sv.json"

#guard !(constant_replication.sem 4).hasUnsupported
#guard !(constant_replication.sem 8).hasUnsupported
#guard !(constant_replication.sem 12).hasUnsupported

end Examples.«system-verilog».sem2.constant_replication.agree
