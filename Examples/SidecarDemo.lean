/-
Hand-written sidecar spec file (NOT generated — the exception among
`Examples/*.lean`, which are otherwise extractor-generated companions).
Demonstrates the two sidecar patterns of docs/howto/add-a-spec-to-existing-code.md:
theorems about an already-extracted program without touching its `.py` source.
-/
import Examples.MyAbs

open LeanModels LeanModels.Python

/-- Sidecar pattern 1 — import the generated companion and state more
theorems about the program constant it defines (`my_abs`, loaded by
`Examples/MyAbs.lean`). Note the `Int` (not `PyInt`) binders: this proof
ends in `omega`, whose syntactic atom matching does not see through the
`PyInt` brand outside `py_begin` (which unbrands hypotheses for you). -/
theorem my_abs_nonneg (x r : Int) (h : my_abs(x) ⇓ r) : 0 ≤ r := by
  have hr : r = |x| := by py_corollary [my_abs_spec]
  omega

/- Sidecar pattern 2 — no companion at all: load the envelope yourself
under a name of your choosing and write dotted-callee specs against it.
The dotted identifier `my_abs_again.my_abs` splits into the module constant
`my_abs_again` and the Python function name `"my_abs"`. (Plain comment:
`load_program` is a command, so it takes no doc comment.) -/
load_program my_abs_again from "Examples/python/my_abs.json"

theorem my_abs_again_total (x : PyInt) : my_abs_again.my_abs(x) ==> |x| := by
  py_prove [my_abs_again]
