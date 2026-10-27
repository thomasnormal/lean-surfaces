import LeanModels.Sv.Load

namespace Examples.systemVerilog.qExamTimedStatistics.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile
    "Examples/system-verilog/q_exam_timed_statistics/q_exam_timed_statistics.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "timed queue-exam fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "timed queue-exam fixture failed to elaborate")
  let .ok (.ok _, world) := SvM.exec (slotStep ρ_src 4096) world
    | throw (IO.userError "timed queue-exam initial slot refused")
  let .ok (.ok _, world) := SvM.exec
      (do advanceTime 4; wakeTimers; slotStep ρ_src 4096) world
    | throw (IO.userError "timed queue-exam first delay refused")
  let .ok (.ok _, world) := SvM.exec
      (do advanceTime 6; wakeTimers; slotStep ρ_src 4096) world
    | throw (IO.userError "timed queue-exam second delay refused")
  unless world.out.flush == ["PASS q_exam_timed_statistics"] do
    throw (IO.userError "timed queue-exam transcript disagrees")

#eval fixtureReceipt

end Examples.systemVerilog.qExamTimedStatistics.proof
