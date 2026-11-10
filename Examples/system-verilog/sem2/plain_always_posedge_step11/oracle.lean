import Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree
open Examples.«system-verilog».sem2.plain_always_posedge_step11.agree

private def emit (tag : String) (E : Elab1) (names : List String)
    (entries : List SvState) : IO Unit := do
  let started ← IO.monoMsNow
  let initial := Config1.init E
  let some rows := trace E names initial entries
    | throw (IO.userError s!"{tag}: E refused or exhausted the test budget")
  for row in showRow E names initial :: rows do
    IO.println s!"ROW {tag} {String.intercalate " " row}"
  IO.println s!"E {tag}: {(← IO.monoMsNow) - started} ms"
  (← IO.getStdout).flush

def main : IO Unit := do
  emit "plainedge" plainEdge plainNames plainInputs
  let started ← IO.monoMsNow
  let initial := Config1.init kindsEdge
  let some rows := sampledSlotsCached kindsEdge kindsNames initial kindsSlots
    | throw (IO.userError "kinds: E refused or exhausted the test budget")
  for row in showRow kindsEdge kindsNames initial :: rows do
    IO.println s!"ROW kinds {String.intercalate " " row}"
  IO.println s!"E kinds: {(← IO.monoMsNow) - started} ms"
  (← IO.getStdout).flush
