import Examples.«system-verilog».sem2.memory_edge_casez_casex_canonical_e.agree

open Examples.«system-verilog».sem2.memory_edge_casez_casex_canonical_e

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for ((qz, qx, plain), i) in rows.zipIdx do
        IO.println s!"ROW i={i} qz={qz} qx={qx} plain={plain}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
