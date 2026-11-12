import Examples.«system-verilog».sem2.memory_shape_c_e.agree
open Examples.«system-verilog».sem2.memory_shape_c_e
def main : IO Unit := do
  if refusal then IO.println "REFUSAL E memory route does not yet admit generate items"
  else throw (IO.userError "generate-item refusal disappeared")
