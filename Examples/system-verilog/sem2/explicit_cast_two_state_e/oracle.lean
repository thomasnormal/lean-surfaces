import Examples.«system-verilog».sem2.explicit_cast_two_state_e.agree
open Examples.«system-verilog».sem2.explicit_cast_two_state_e
def main : IO Unit := do
  for row in rows 8 do IO.println s!"ROW W=8 y={row}"
  for row in rows 2 do IO.println s!"ROW W=2 y={row}"
