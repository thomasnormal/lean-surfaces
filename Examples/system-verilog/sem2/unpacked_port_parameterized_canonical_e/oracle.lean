import Examples.«system-verilog».sem2.unpacked_port_parameterized_canonical_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.unpacked_port_parameterized_canonical_e

def main : IO Unit := do
  for n in [2, 3] do
    match outputs n with
    | .ok rows =>
        for (row, i) in rows.zipIdx do
          IO.println s!"ROW N={n} i={i} y={row}"
    | .timeout => throw (IO.userError s!"E timed out at N={n}")
    | .unsupported msg => throw (IO.userError s!"E unsupported at N={n}: {msg}")
