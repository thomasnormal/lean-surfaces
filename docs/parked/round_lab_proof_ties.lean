import Examples.python.round_lab.proof_part1

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem round_init :
    initWorld round_lab = {heap := #[], globals := [], stdout := [], clock := [], callDepth := 0} := by
  rfl

private theorem round_lookup :
    ∃ f, findFunction round_lab "round_float_ties" = some f := by
  simp [findFunction, round_lab]

private theorem round_global_none :
    lookupG (globalsFold #[] [] true false round_lab.topLevel.toList).snd.fst "round" = none := by
  rfl

private theorem round_class_none :
    findClassAux round_lab.classes.toList "round" 0 = none := by
  rfl

private theorem round_nt_none :
    findNamedTupleAux round_lab.namedtuples.toList "round" = none := by
  rfl

private theorem round_heapfree : funsHeapFree round_lab.functions.toList = true := by
  decide

private theorem round_def_free : Stmt.defFreeList round_lab.topLevel.toList = true := by
  decide

private theorem round_no_round :
    ¬ ∃ x, x ∈ round_lab.functions ∧ x.name = "round" := by
  decide

private theorem round_ne_fstring : ("round" == fstringFormatBuiltinName) = false := by decide
private theorem round_ne_lenMult : ("round" == lenMultBuiltinName) = false := by decide
private theorem round_ne_starArg : ("round" == starArgBuiltinName) = false := by decide
private theorem round_ne_starTuple : ("round" == starTupleBuiltinName) = false := by decide
private theorem round_ne_starList : ("round" == starListBuiltinName) = false := by decide

private theorem round_zero : roundFloatVal {bits := 0x3fe0000000000000} = .ok (.int 0) := by rfl
private theorem round_one : roundFloatVal {bits := 0x3ff8000000000000} = .ok (.int 2) := by rfl
private theorem round_two : roundFloatVal {bits := 0x4004000000000000} = .ok (.int 2) := by rfl
private theorem round_neg_zero :
    roundFloatVal ({bits := 0x3fe0000000000000} : Float64).neg = .ok (.int 0) := by rfl
private theorem round_neg_one :
    roundFloatVal ({bits := 0x3ff8000000000000} : Float64).neg = .ok (.int (-2)) := by rfl
private theorem round_neg_two :
    roundFloatVal ({bits := 0x4004000000000000} : Float64).neg = .ok (.int (-2)) := by rfl

theorem round_float_ties :
    round_lab.round_float_ties() ==>
      Val.tuple #[Val.int 0, Val.int 2, Val.int 2, Val.int 0, Val.int (-2), Val.int (-2)] := by
  obtain ⟨f, hf⟩ := round_lookup
  refine ⟨256, ?_⟩
  unfold callFunction
  rw [round_init]
  rw [callIn.eq_2]
  rw [hf]
  simp [findFunction, round_lab] at hf
  subst f
  py_simp [round_global_none, round_class_none, round_nt_none,
    round_heapfree, round_def_free, round_no_round,
    round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList,
    round_zero, round_one, round_two, round_neg_zero,
    round_neg_one, round_neg_two,
    isPyBuiltinName, isLoweredBuiltinName, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFree, Stmt.heapFreeList,
    Expr.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.leaveCallDepth, Run.liftRes, Run.toPublic,
    Run.toPublic_ok, RVal.freezeB, pythonTopCallDepth,
    pythonRecursionLimit, builtinRoundRecursionCheck, Run.withLocals,
    Run.toWorld, Run.finishCallAt, execStmts, execStmt, evalExpr,
    evalExprs, Run.bindE]
