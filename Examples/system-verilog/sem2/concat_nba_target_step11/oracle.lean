import Examples.«system-verilog».sem2.concat_nba_target_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel

open Examples.«system-verilog».sem2.concat_nba_target_step11.agree

def main : IO Unit := do
  match Examples.«system-verilog».sem2.concat_nba_target_step11.agree.trace
      (Config1.init Examples.«system-verilog».sem2.concat_nba_target_step11.agree.edge)
      Examples.«system-verilog».sem2.concat_nba_target_step11.agree.inputs with
  | some rows =>
      for row in Examples.«system-verilog».sem2.case_always_ff_step11.agree.showRow
          Examples.«system-verilog».sem2.concat_nba_target_step11.agree.edge
          Examples.«system-verilog».sem2.concat_nba_target_step11.agree.names
          (Config1.init Examples.«system-verilog».sem2.concat_nba_target_step11.agree.edge) :: rows do
        IO.println ("ROW " ++ String.intercalate " " row)
  | none =>
      IO.println "E REFUSED"
