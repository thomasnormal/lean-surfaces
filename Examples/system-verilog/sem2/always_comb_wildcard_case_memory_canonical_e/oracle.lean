import Examples.«system-verilog».sem2.always_comb_wildcard_case_memory_canonical_e.agree
open LeanModels.Sv
open Examples.«system-verilog».sem2.always_comb_wildcard_case_memory_canonical_e
#eval match outputs with | .ok rows => rows | .timeout => [] | .unsupported m => [("ERR", m)]
