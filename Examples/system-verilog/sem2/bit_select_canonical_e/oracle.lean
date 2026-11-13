import Examples.«system-verilog».sem2.bit_select_canonical_e.agree

open Examples.«system-verilog».sem2.bit_select_canonical_e

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println s!"ROW i={i} q0={row.1} qidx={row.2}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
