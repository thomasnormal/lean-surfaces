import LeanModels.Python.Surface

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

load_program round_lab from "Examples/python/round_lab/round_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem round_ne_fstring : ("round" == fstringFormatBuiltinName) = false := by decide
private theorem round_ne_lenMult : ("round" == lenMultBuiltinName) = false := by decide
private theorem round_ne_starArg : ("round" == starArgBuiltinName) = false := by decide
private theorem round_ne_starTuple : ("round" == starTupleBuiltinName) = false := by decide
private theorem round_ne_starList : ("round" == starListBuiltinName) = false := by decide
