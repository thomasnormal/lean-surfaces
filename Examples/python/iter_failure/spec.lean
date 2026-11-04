import LeanModels.Python.Logic
import LeanModels.Python.Monadic.Eval

open LeanModels LeanModels.Python

namespace Examples.python.iter_failure

load_program iter_failure from "Examples/python/iter_failure/iter_failure.json"

private def runFunction (functionName : String) : Res Val :=
  Run.toPublic 32
    (Monadic.callInMono iter_failure 32 (initWorld iter_failure) functionName #[])

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem native_failure_with_default :
    runFunction "native_failure_with_default" =
      .exn (.runtimeError "dictionary changed size during iteration") := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).refl false

theorem native_restored_failure :
    runFunction "native_restored_failure" = .ok (.int 4) := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).refl false

theorem enumerate_restored_failure :
    runFunction "enumerate_restored_failure" = .ok (.int 4) := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).refl false

theorem generator_closed_default :
    runFunction "generator_closed_default" = .ok (.tuple #[.int 99, .int 99]) := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).refl false

theorem generator_closed_without_default :
    runFunction "generator_closed_without_default" = .exn .stopIteration := by
  run_tac (← Lean.Elab.Tactic.getMainGoal).refl false

#print axioms native_failure_with_default
#print axioms native_restored_failure
#print axioms enumerate_restored_failure
#print axioms generator_closed_default
#print axioms generator_closed_without_default

end Examples.python.iter_failure
