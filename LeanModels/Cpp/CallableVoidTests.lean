import LeanModels.Cpp.CallableObjectEvaluation
import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableVoidTests

open CallableObjectEvaluation

private def intType : CppTypeEvidence := .builtin .int
private def bareReturn : Raw := .object [("kind", .string "ReturnStmt")]
#guard parseCallableStatement .lp64 [] [] .void bareReturn matches .ok .returnVoid
#guard parseCallableStatement .lp64 [] [] intType bareReturn matches .error _
private def h (name : String) : FrontendHandle := ⟨name⟩
private def value (n : Int) : IntegralValue := ⟨.signed 32, n⟩
private def literal (n : Nat) : TypedCallableExpression := ⟨.integer n, intType, intType⟩
private def function (result : CppTypeEvidence) (body : CallableStatement) : CallableFunction := {
  occurrence := {
    id := "void", kind := "FunctionDecl", path := [], name := some "void",
    lexicalParents := [], semanticParent := none, previousDecl := none,
    mangledName := none, type := none, location := none, range := none},
  signature := {result, parameters := [.lvalueReference intType, intType], variadic := false},
  parameters := [{declaration := h "ref", name := none, type := .lvalueReference intType},
    {declaration := h "copy", name := none, type := intType}], body}
private def caller : IntegralObjectFrame :=
  let empty := (IntegralObjectFrame.empty .lp64).toOption.getD default
  (empty.enterScope.frame.declareParameter (h "caller") intType (value 2)).frame
private def arguments : List CallableArgument := [.lvalue ⟨0, intType⟩, .value (value 3)]

private def checkVoid (body : CallableStatement) : Bool :=
  let f := function .void body
  let result := evaluateCallableObjectResultInStore 32 caller.store f arguments
  (result.result matches .ok (.ok none)) && result.frame.scopes.isEmpty &&
    result.frame.store.values == [some (value 7), none] &&
    result.frame.store.objects.objects.map (·.phase) == [.aliveInitialized, .ended]

private def returnAndFallthrough : Bool :=
  checkVoid (.assign (h "ref") (literal 7)) &&
  checkVoid (.sequence (.assign (h "ref") (literal 7))
    (.sequence .returnVoid (.assign (h "ref") (literal 99)))) &&
  checkVoid (.block (.sequence (.assign (h "ref") (literal 7)) .returnVoid))

def callableVoidWitness : Bool := returnAndFallthrough

private def failureAndLegacy : Bool :=
  let body := CallableStatement.sequence (.assign (h "ref") (literal 7))
    (.assign (h "missing") (literal 9))
  let f := function .void body
  let failed := evaluateCallableObjectResultInStore 32 caller.store f arguments
  let legacy := evaluateCallableObjectInStore 32 caller.store f arguments
  let missing := evaluateCallableObjectResultInStore 32 caller.store (function intType .skip) arguments
  let bad := evaluateCallableObjectResultInStore 32 caller.store (function intType .returnVoid) arguments
  let badValue := evaluateCallableObjectResultInStore 32 caller.store
    (function .void (.return_ (literal 9))) arguments
  (failed.result matches .error (.frameError (.missingBinding _))) &&
    failed.frame.store.values == [some (value 7), some (value 3)] &&
    failed.frame.scopes.length == 1 &&
    (legacy.result matches .error .voidResultRequiresResultAPI) && legacy.frame.store == caller.store &&
    (missing.result matches .error .missingReturn) &&
    (bad.result matches .error .returnTypeMismatch) &&
    (badValue.result matches .error .returnTypeMismatch) &&
    (evaluateCallable 32 .lp64 f [value 2, value 3] matches .error (.unsupportedType .void))

private def undefinedIsNotVoid : Bool :=
  let divide : TypedCallableExpression := ⟨.binary "/" (literal 1) (literal 0), intType, intType⟩
  let f := function .void (.sequence (.assign (h "ref") (literal 7)) (.expression divide))
  let result := evaluateCallableObjectResultInStore 32 caller.store f arguments
  let integer := function intType (.return_ (literal 5))
  let integralResult := evaluateCallableObjectResultInStore 32 caller.store integer arguments
  (result.result matches .ok (.undefined .divisionByZero)) &&
    result.frame.store.values == [some (value 7), some (value 3)] &&
    result.frame.scopes.length == 1 &&
    (integralResult.result matches .ok (.ok (some ⟨.signed 32, 5⟩))) &&
    integralResult.frame.scopes.isEmpty

private def emptyFunction : CallableFunction :=
  {function .void .skip with
    parameters := [],
    signature := {result := .void, parameters := [], variadic := false}}

#guard evaluateCallableObjectResult 1 .lp64 emptyFunction [] matches .ok (.ok none)
#guard evaluateCallableObjectResult 0 .lp64 emptyFunction [] matches .error (.frameError .fuelExhausted)
#guard evaluateCallableObject 1 .lp64 emptyFunction [] matches .error .voidResultRequiresResultAPI
#guard callableVoidWitness

private theorem voidKernelChecks : (returnAndFallthrough && failureAndLegacy && undefinedIsNotVoid) = true := by decide

theorem callable_void_witness : callableVoidWitness = true := by
  rfl

#print axioms voidKernelChecks
#print axioms callable_void_witness
#print axioms CallableObjectEvaluation.void_fallthrough_eq_return

end LeanModels.Cpp.CallableVoidTests
