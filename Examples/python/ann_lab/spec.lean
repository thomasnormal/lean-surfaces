import Examples.python.ann_lab.proof

open LeanModels LeanModels.Python

load_program ann_lab from "Examples/python/ann_lab/ann_lab.json"

#py_check ann_lab.ann_module_global(1) = 6
#py_check ann_lab.ann_module_global(0) = 5
#py_check ann_lab.ann_module_global(-5) = 0

load_program annotation_effect from "harness/scripts/ann_module_effect_script.json"

#guard callFunction annotation_effect "read_target" #[] 4096 matches .unsupported _

theorem ann_module_global_total (offset : PyInt) :
    ann_lab.ann_module_global(offset) ==> 5 + offset := by proofs

#print axioms ann_module_global_total
