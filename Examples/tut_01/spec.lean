/-
Examples/tut_01 — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): tut_01.py (pure Python), tut_01.json
(generated envelope), THIS FILE (the non-vacuity checks). No theorems yet
— tutorial 01 runs the pipeline, tutorial 02 proves — so there is no
proof.lean either (a spec file only imports its sibling when it has
`:= by proofs` statements to close).
-/
import LeanModels

open LeanModels LeanModels.Python

load_program tut_01 from "Examples/tut_01/tut_01.json"

/-! Tutorial 01 (docs/tutorial/01-first-run.md): the whole pipeline on a
three-line file. Non-vacuity checks only — the theorems start in
tutorial 02. -/
#py_check tut_01.double(21) = 42
#py_check tut_01.double(0) = 0
#py_check tut_01.double(-7) = -14
