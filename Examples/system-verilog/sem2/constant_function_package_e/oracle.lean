import Examples.«system-verilog».sem2.constant_function_package_e.agree
open Examples.«system-verilog».sem2.constant_function_package_e

def emit (n : Int) : IO Unit := do
  match widthAt n with
  | .ok w => IO.println s!"ROW N={n} W={w}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
def main : IO Unit := do
  emit 1
  emit 8
  emit 16
