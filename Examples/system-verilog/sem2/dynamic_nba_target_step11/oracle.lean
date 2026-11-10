import Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree
open Examples.«system-verilog».sem2.plain_always_posedge_step11.agree
open Examples.«system-verilog».sem2.dynamic_nba_target_step11.agree

private def emit (tag : String) (E : Elab1) (names : List String)
    (entries : List (SvState × Bool)) : IO Unit := do
  let started ← IO.monoMsNow
  let initial := Config1.init E
  let some rows := sampledSlotsCached E names initial entries
    | throw (IO.userError s!"{tag}: E refused or exhausted the test budget")
  for row in showRow E names initial :: rows do
    IO.println s!"ROW {tag} {String.intercalate " " row}"
  IO.println s!"E {tag}: {(← IO.monoMsNow) - started} ms"
  (← IO.getStdout).flush

def main : IO Unit := do
  emit "target" targetEdge targetNames (targetInputs.flatMap fun entry =>
    [(SvState.set entry "clk" (.ofNat 1 0), false), ([("clk", .ofNat 1 1)], true)])
  emit "issue" issueEdge issueNames issueSlots
