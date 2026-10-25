import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.ann_lab.proof

open LeanModels LeanModels.Python

load_program ann_lab from "Examples/python/ann_lab/ann_lab.json"

private theorem add_ne_bitAnd : (BinOp.add == BinOp.bitAnd) = false := by
  decide

theorem ann_module_global_total (offset : PyInt) :
    ann_lab.ann_module_global(offset) ==> 5 + offset := by
  py_prove [ann_lab, hasUnboundLocal, unboundLocalMarker, add_ne_bitAnd]

#print axioms ann_module_global_total

end Examples.python.ann_lab.proof
