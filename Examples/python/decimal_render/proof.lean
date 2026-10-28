import LeanModels.Python.Surface

namespace Examples.python.decimal_render.proof

open LeanModels LeanModels.Python

load_program decimal_render from "Examples/python/decimal_render/decimal_render.json"

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4300

private def scalarFunction : FunctionDefn :=
  { name := "scalar_str"
    params := #[{ arg := "value", span := ⟨6, 15, 6, 20⟩ }]
    argsOk := true
    body := #[.ret
      (some (.call (.name "str" ⟨7, 11, 7, 14⟩)
        #[.name "value" ⟨7, 15, 7, 20⟩] #[] none ⟨7, 11, 7, 21⟩))
      ⟨7, 4, 7, 21⟩]
    span := ⟨6, 0, 7, 21⟩ }

private theorem scalar_literal_actual :
    decimal_render.functions[0]! = scalarFunction := by rfl

private theorem initial_world : initWorld decimal_render = (⟨#[], [], [], []⟩ : World) := by
  rfl

private theorem globals_empty : moduleGlobals decimal_render = ([], true) := by
  rfl

private theorem scalar_found :
    findFunction decimal_render "scalar_str" = some scalarFunction := by
  rfl

private theorem builtin_not_function : findFunction decimal_render "str" = none := by
  rfl

private theorem builtin_not_class : findClass decimal_render "str" = none := by
  rfl

private theorem builtin_not_namedtuple : findNamedTuple decimal_render "str" = none := by
  rfl

private theorem str_ne_fstring : ("str" == fstringFormatBuiltinName) = false := by decide
private theorem str_ne_lenMult : ("str" == lenMultBuiltinName) = false := by decide
private theorem str_ne_starTuple : ("str" == starTupleBuiltinName) = false := by decide
private theorem str_ne_starArg : ("str" == starArgBuiltinName) = false := by decide
private theorem str_ne_starList : ("str" == starListBuiltinName) = false := by decide

private theorem scalar_decimal (value : PyInt)
    (valueBound : value.natAbs < 10 ^ 4300) :
    intDecimal value = some (toString value) := by
  unfold intDecimal
  change (if value.natAbs < 10 ^ 4300 then some (toString value) else none) = _
  exact if_pos valueBound

private theorem scalar_call (value : PyInt) (text : String)
    (scalarOk : intDecimal value = some text) :
    CallsTo decimal_render "scalar_str" #[.int value] (.str text) := by
  have rendered : strOfVal (.int value) = .ok (.str text) := by
    simp only [strOfVal, scalarOk]
  have renderedHeap (heap : Heap) :
      strOfValH heap (.int value) = Res.ok (RVal.str text) := by
    change strOfVal (.int value) = _
    exact rendered
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  simp (config := { maxSteps := 200000 })
    [scalarFunction, globals_empty, scalar_found,
      builtin_not_function, builtin_not_class, builtin_not_namedtuple,
      str_ne_fstring, str_ne_lenMult, str_ne_starTuple, str_ne_starArg, str_ne_starList,
      execStmts, execStmt, evalExpr, evalExprs, mkCallEnv, arityOk,
      defaultBindings, Env.lookup, lookupG, hasUnboundLocal, unboundLocalMarker,
      markUnboundLocals, hasLateRaiseNames, lateRaiseNames, stmtUnboundLocalNames,
      stmtUnboundLocalNamesList, directRaiseName, directAssignName, hasDirectAssignAfter,
      markUnboundLocals_noop, stmtHasUnboundLocal, stmtHasUnboundLocalList,
      isBuiltinName, isPyBuiltinName, isLoweredBuiltinName,
      flattenStarRun, flattenStarCallArgs, strOfValH, strOfVal,
      Run.bind, Run.liftRes, RVal.thaw, RVal.thawList, RVal.thawArgs,
      RVal.freezeB, renderedHeap]
  rw [scalarOk]
  rfl

theorem scalar_str_total (value : PyInt)
    (valueBound : value.natAbs < 10 ^ 4300) :
    decimal_render.scalar_str(value) ==> toString value := by
  exact scalar_call value (toString value) (scalar_decimal value valueBound)

#print axioms scalar_str_total

end Examples.python.decimal_render.proof
