/-
Proof module for `Examples/python/tut_03/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.tut_03.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.tut_03.proof

open LeanModels LeanModels.Python

load_program tut_03 from "Examples/python/tut_03/tut_03.json"

/-- Unconditional total correctness: split the symbolic `if x < 0:`
branch explicitly, simplify the depth-aware public result in each arm,
and discharge the `Int.max` equations with fresh `Int` arithmetic. -/
theorem relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0 := by
  refine ⟨32, ?_⟩
  by_cases h : x < 0
  · let xi : Int := x
    have hxi : xi < 0 := by simpa [xi] using h
    have hle : xi ≤ 0 := by omega
    have hmxi : max xi 0 = 0 := by simp [Int.max_def, hle]
    have hm : max x 0 = 0 := by simpa [xi] using hmxi
    rw [hm]
    py_simp [callFunction, callIn, tut_03, h, pythonTopCallDepth,
      pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
      Run.toPublic, Run.toPublic_ok, RVal.freezeB]
  · let xi : Int := x
    have hxi : ¬ xi < 0 := by simpa [xi] using h
    have hmxi : max xi 0 = xi := by
      rw [Int.max_def]
      by_cases hc : xi ≤ 0
      · have hz : xi = 0 := by omega
        simp [hz]
      · simp [hc]
    have hm : max x 0 = x := by simpa [xi] using hmxi
    rw [hm]
    py_simp [callFunction, callIn, tut_03, h, pythonTopCallDepth,
      pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
      Run.toPublic, Run.toPublic_ok, RVal.freezeB]

/-- With a precondition: re-land `hx` at `Int`, derive the branch guard,
and simplify the depth-aware public result directly (docs/tutorial/
06-when-proofs-fail.md, failure mode 5). -/
theorem relu_of_nonneg (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  have hnot : ¬ x < 0 := by
    intro hneg
    let xi : Int := x
    have hxi0 : 0 ≤ xi := by simpa [xi] using hx'
    have hxineg : xi < 0 := by simpa [xi] using hneg
    omega
  refine ⟨32, ?_⟩
  py_simp [callFunction, callIn, tut_03, hx', hnot, pythonTopCallDepth,
    pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
    Run.toPublic, Run.toPublic_ok, RVal.freezeB]

/-- The same theorem with the proof spelled out, for reading goal states
(docs/tutorial/03-branching-and-preconditions.md walks through each
step's goal). -/
theorem relu_of_nonneg' (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  have hnot : ¬ x < 0 := by
    intro hneg
    let xi : Int := x
    have hxi0 : 0 ≤ xi := by simpa [xi] using hx'
    have hxineg : xi < 0 := by simpa [xi] using hneg
    omega
  refine ⟨32, ?_⟩
  py_simp [callFunction, callIn, tut_03, hnot, pythonTopCallDepth,
    pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
    Run.toPublic, Run.toPublic_ok, RVal.freezeB, hx']

end Examples.python.tut_03.proof
