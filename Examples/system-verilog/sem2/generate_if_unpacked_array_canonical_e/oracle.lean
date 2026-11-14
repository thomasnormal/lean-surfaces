import Examples.«system-verilog».sem2.generate_if_unpacked_array_canonical_e.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.generate_if_unpacked_array_canonical_e

def main : IO Unit := do
  for N in [1, 2] do
    match outputs N with
    | .ok rows =>
        for (row, i) in rows.zipIdx do
          IO.println s!"ROW N={N} i={i} y={row}"
    | .timeout => throw (IO.userError s!"E timed out at N={N}")
    | .unsupported msg => throw (IO.userError s!"E refusal at N={N}: {msg}")
