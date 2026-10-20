import LeanModels.Sv.Load

namespace Examples.systemVerilog.timeBoundary.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

#print axioms elabTimedDesign_requiresTimeZero

def loadFixture (name : String) : IO SelfCheck.Design := do
  let text ← IO.FS.readFile ("Examples/system-verilog/" ++ name ++ ".sv.json")
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "time-boundary fixture failed to load")
  return design

def requireRejected (design : SelfCheck.Design) : IO Unit := do
  unless design.requiresTimeZero do
    throw (IO.userError "time-zero provenance disappeared during ingestion")
  match elabTimedDesign 4096 design with
  | .error "timed design rejects time-zero-only $time lowering" => pure ()
  | _ => throw (IO.userError "time-zero-only literal escaped into the timed executor")

def fixtureReceipt : IO Unit := do
  let zero ← loadFixture "time_zero/time_zero"
  unless runSelfCheck zero 4096 == .ok ["PASS"] do
    throw (IO.userError "time-zero query no longer executes at time zero")
  requireRejected zero
  for name in ["delayed", "nested", "initializer"] do
    requireRejected (← loadFixture ("time_boundary/" ++ name))
  let literal ← loadFixture "time_boundary/literal"
  unless !literal.requiresTimeZero do
    throw (IO.userError "ordinary zero was mistaken for a query")
  let .ok world := elabTimedDesign 4096 literal
    | throw (IO.userError "ordinary literal failed to enter the timed executor")
  let .ok (.ok _, world) := SvM.exec (slotStep ρ_src 4096) world
    | throw (IO.userError "literal fixture failed in its first slot")
  let .ok (.ok _, world) := SvM.exec
      (do advanceTime 2; wakeTimers; slotStep ρ_src 4096) world
    | throw (IO.userError "literal fixture failed after its delay")
  unless world.time == 2 && world.out.flush == ["literal 0"] do
    throw (IO.userError "ordinary literal timed execution disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.timeBoundary.proof
