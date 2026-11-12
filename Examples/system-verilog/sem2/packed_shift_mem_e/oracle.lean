import Examples.«system-verilog».sem2.packed_shift_mem_e.agree
open Examples.«system-verilog».sem2.packed_shift_mem_e
def main : IO Unit := do
  for (n, tag) in [ (4, "N=4"), (8, "N=8") ] do
    match outputs n with | .ok rows => for (row,i) in rows.zipIdx do IO.println s!"ROW {tag} i={i} q={row}" | .error m => throw (IO.userError m)
