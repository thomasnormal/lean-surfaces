import Examples.«system-verilog».sem2.generate_if_initial_canonical_e.agree
open LeanModels.Sv
open Examples.«system-verilog».sem2.generate_if_initial_canonical_e
#eval do
  for (n, label) in [(1, "n=1"), (0, "n=0")] do
    match outputAt n with
    | .ok q => IO.println s!"ROW {label} q={q}"
    | .timeout => throw (IO.userError "E timed out")
    | .unsupported m => throw (IO.userError m)

def main : IO Unit := pure ()
