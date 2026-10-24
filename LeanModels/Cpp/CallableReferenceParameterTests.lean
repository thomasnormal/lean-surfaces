import LeanModels.Cpp.CallableObjectEvaluation
import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableReferenceParameterTests

open CallableObjectEvaluation

private def intType : CppTypeEvidence := .builtin .int
private def h (name : String) : FrontendHandle := ⟨name⟩
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def expression (name : String) : TypedCallableExpression :=
  ⟨.parameter (h name), intType, intType⟩
private def literal (value : Nat) : TypedCallableExpression :=
  ⟨.integer value, intType, intType⟩
private def function (types : List CppTypeEvidence) (body : CallableStatement) : CallableFunction := {
  occurrence := {
    id := "f", kind := "FunctionDecl", path := [], name := some "f", lexicalParents := [],
    semanticParent := none, previousDecl := none, mangledName := none,
    type := none, location := none, range := none},
  signature := {result := intType, parameters := types, variadic := false},
  parameters := types.zipIdx |>.map fun (type, index) =>
    {declaration := h (toString index), name := none, type},
  body}

private def caller : IntegralObjectFrame :=
  let empty := (IntegralObjectFrame.empty .lp64).toOption.getD default
  let opened := empty.enterScope.frame
  let first := opened.declareParameter (h "caller") intType (signed 2)
  (first.frame.declareParameter (h "other") intType (signed 3)).frame

private def ref (object : Nat) (type : CppTypeEvidence := intType) : CallableArgument :=
  .lvalue ⟨object, type⟩

private def aliasing : Bool :=
  let f := function [.lvalueReference intType, .lvalueReference intType]
    (.sequence (.assign (h "0") (literal 7))
      (.sequence (.assign (h "1") (literal 9)) (.return_ (expression "0"))))
  let alias := evaluateCallableObjectInStore 32 caller.store f [ref 0, ref 0]
  let distinct := evaluateCallableObjectInStore 32 caller.store f [ref 0, ref 1]
  (alias.result matches .ok (.ok ⟨.signed 32, 9⟩)) &&
    (distinct.result matches .ok (.ok ⟨.signed 32, 7⟩)) &&
    alias.frame.scopes.isEmpty && distinct.frame.scopes.isEmpty &&
    alias.frame.store.values == [some (signed 9), some (signed 3)] &&
    distinct.frame.store.values == [some (signed 7), some (signed 9)] &&
    alias.frame.store.objects.objects.all (fun object => object.phase == .aliveInitialized) &&
    (({caller with store := alias.frame.store}.read (h "caller")).result matches .ok ⟨.signed 32, 9⟩)

def callableReferenceParameterWitness : Bool := aliasing

private def valueCopyAndIsolation : Bool :=
  let f := function [.lvalueReference intType, intType]
    (.sequence (.assign (h "0") (literal 7)) (.return_ (expression "1")))
  let result := evaluateCallableObjectInStore 32 caller.store f [ref 0, ref 0]
  let started := CallableObjectFrame.startInStore caller.store f [ref 0, ref 0]
  (result.result matches .ok (.ok ⟨.signed 32, 2⟩)) &&
    result.frame.store.values == [some (signed 7), some (signed 3), none] &&
    result.frame.store.objects.objects.map (·.phase) ==
      [.aliveInitialized, .aliveInitialized, .ended] && result.frame.scopes.isEmpty &&
    !started.frame.bound (h "caller") && started.frame.store.objects.objects.length == 3

def callableValueParameterIsolationWitness : Bool := valueCopyAndIsolation

#guard callableValueParameterIsolationWitness

private def constAndLifetime : Bool :=
  let mutable := function [.lvalueReference intType] (.return_ (expression "0"))
  let constant := function [.lvalueReference (.qualified true false intType)]
    (.return_ ⟨.convert ⟨.parameter (h "0"), .qualified true false intType,
      .qualified true false intType⟩, .qualified true false intType, intType⟩)
  let drop := CallableObjectFrame.startInStore caller.store mutable
    [ref 0 (.qualified true false intType)]
  let added := evaluateCallableObjectInStore 32 caller.store constant [ref 0]
  let ended := (caller.store.endLifetime 0).toOption.getD default
  let stale := CallableObjectFrame.startInStore ended mutable [ref 0]
  let temporary := CallableObjectFrame.startInStore caller.store constant [.value (signed 2)]
  (drop.result matches .error (.object (.object .referenceQualification))) &&
    drop.frame.store == caller.store && (added.result matches .ok (.ok ⟨.signed 32, 2⟩)) &&
    (stale.result matches .error (.object (.object (.lifetime .lifetimeEnded)))) &&
    stale.frame.store == ended && (temporary.result matches .error (.argumentTypeMismatch _))

def callableConstReferenceWitness : Bool := constAndLifetime

#guard callableConstReferenceWitness

private def uninitializedBinding : Bool :=
  let empty := (IntegralObjectFrame.empty .lp64).toOption.getD default
  let uninitialized := empty.enterScope.frame.declareLocalDefault (h "caller") intType
  let f := function [.lvalueReference intType]
    (.sequence (.assign (h "0") (literal 7)) (.return_ (expression "0")))
  let result := evaluateCallableObjectInStore 32 uninitialized.frame.store f [ref 0]
  (result.result matches .ok (.ok ⟨.signed 32, 7⟩)) &&
    result.frame.store.values == [some (signed 7)] &&
    result.frame.store.objects.objects.map (·.phase) == [.aliveInitialized]

def callableUninitializedBindingWitness : Bool := uninitializedBinding

private def failureRetainsPrefix : Bool :=
  let f := function [intType, .lvalueReference intType] (.return_ (literal 0))
  let result := CallableObjectFrame.startInStore caller.store f
    [.value (signed 4), .value (signed 5)]
  (result.result matches .error (.argumentTypeMismatch _)) &&
    result.frame.store.values == [some (signed 2), some (signed 3), some (signed 4)] &&
    result.frame.scopes.length == 1 && result.frame.bound (h "0") &&
    !result.frame.bound (h "1") &&
    (evaluateCallable 16 .lp64 f [signed 4, signed 5] matches .error (.unsupportedType _))

private def unreadableValueAndActualConst : Bool :=
  let opened := (IntegralObjectFrame.empty .lp64).toOption.getD default |>.enterScope.frame
  let uninitialized := opened.declareLocalDefault (h "caller") intType
  let byValue := function [intType] (.return_ (literal 0))
  let unreadable := CallableObjectFrame.startInStore uninitialized.frame.store byValue [ref 0]
  let constant := opened.declareParameter (h "constant")
    (.qualified true false intType) (signed 2)
  let byReference := function [.lvalueReference intType] (.return_ (expression "0"))
  let forged := CallableObjectFrame.startInStore constant.frame.store byReference [ref 0]
  (unreadable.result matches .error (.object (.object (.lifetime .notInitialized)))) &&
    unreadable.frame.store == uninitialized.frame.store &&
    (forged.result matches .error (.object (.object .referenceQualification))) &&
    forged.frame.store == constant.frame.store &&
    (CallableObjectFrame.start .lp64 byReference [signed 2] matches .error _)

private def executionFailureRetainsMutation : Bool :=
  let division : TypedCallableExpression :=
    ⟨.binary "/" (literal 1) (literal 0), intType, intType⟩
  let f := function [.lvalueReference intType, intType]
    (.sequence (.assign (h "0") (literal 7)) (.expression division))
  let result := evaluateCallableObjectInStore 32 caller.store f [ref 0, .value (signed 4)]
  (result.result matches .ok (.undefined .divisionByZero)) &&
    result.frame.store.values == [some (signed 7), some (signed 3), some (signed 4)] &&
    result.frame.store.objects.objects.all (fun object => object.phase == .aliveInitialized) &&
    result.frame.scopes.length == 1

private def futureArgumentIdentityRefuses : Bool :=
  let f := function [intType, .lvalueReference intType] (.return_ (expression "1"))
  let future := CallableObjectFrame.startInStore caller.store f [.value (signed 4), ref 2]
  (future.result matches .error (.object (.object (.lifetime (.missing 2))))) &&
    future.frame.store == caller.store && future.frame.scopes.isEmpty

private def staticLocalAcrossStarts : Bool :=
  let f := function [intType] (.return_ (expression "0"))
  let first := CallableObjectFrame.startInStore caller.store f [ref 0]
  match first.result with
  | .error _ => false
  | .ok callable =>
      let declared := callable.frame.declareStaticInitialized 8 (h "static") intType intType
        (.literal (signed 3))
      match declared.result with
      | .error _ => false
      | .ok object =>
          let closed := declared.frame.leaveFrame
          match closed.result with
          | .error _ => false
          | .ok _ =>
              let second := CallableObjectFrame.startInStore closed.frame.store f [ref 0]
              match second.result with
              | .error _ => false
              | .ok callable2 =>
                  let reused := callable2.frame.declareStaticInitialized 8 (h "static")
                    intType intType (.literal (signed 9))
                  match reused.result with
                  | .ok object2 =>
                      object == object2 &&
                        (reused.frame.read (h "static")).result matches .ok ⟨.signed 32, 3⟩ &&
                        reused.frame.store.staticBindings.length == 1
                  | .error _ => false

private def threadLocalAcrossStarts : Bool :=
  let f := function [intType] (.return_ (expression "0"))
  let first := CallableObjectFrame.startInStore caller.store f [ref 0]
  match first.result with
  | .error _ => false
  | .ok callable =>
      let declared := callable.frame.declareThreadInitialized 8 (h "thread") intType intType
        (.literal (signed 5))
      match declared.result with
      | .error _ => false
      | .ok object =>
          let closed := declared.frame.leaveFrame
          match closed.result with
          | .error _ => false
          | .ok _ =>
              let second := CallableObjectFrame.startInStore closed.frame.store f [ref 0]
              match second.result with
              | .error _ => false
              | .ok callable2 =>
                  let reused := callable2.frame.declareThreadInitialized 8 (h "thread")
                    intType intType (.literal (signed 11))
                  match reused.result with
                  | .ok object2 =>
                      object == object2 &&
                        (reused.frame.read (h "thread")).result matches .ok ⟨.signed 32, 5⟩ &&
                        reused.frame.store.threadBindings.length == 1
                  | .error _ => false

#guard aliasing
#guard callableReferenceParameterWitness
#guard valueCopyAndIsolation
#guard constAndLifetime
#guard uninitializedBinding
#guard callableUninitializedBindingWitness
#guard failureRetainsPrefix
#guard unreadableValueAndActualConst
#guard executionFailureRetainsMutation
#guard futureArgumentIdentityRefuses
#guard staticLocalAcrossStarts
#guard threadLocalAcrossStarts

-- Kernel reduction controls for identity, ownership and state retention.
private theorem kernelReferenceParameters :
    (aliasing && valueCopyAndIsolation && constAndLifetime &&
      uninitializedBinding && failureRetainsPrefix && unreadableValueAndActualConst &&
      executionFailureRetainsMutation && futureArgumentIdentityRefuses &&
      staticLocalAcrossStarts && threadLocalAcrossStarts) = true := rfl

theorem callable_reference_parameter_witness : callableReferenceParameterWitness = true := by
  rfl

#print axioms kernelReferenceParameters
#print axioms callable_reference_parameter_witness
#print axioms IntegralObjectFrame.bindReferenceParameter_store

end LeanModels.Cpp.CallableReferenceParameterTests
