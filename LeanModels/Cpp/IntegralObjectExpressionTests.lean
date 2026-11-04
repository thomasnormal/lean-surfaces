import LeanModels.Cpp.IntegralObjectExpressions

namespace LeanModels.Cpp.IntegralObjectExpressionTests

open LeanModels.Cpp

private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

private def ready : Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let store ← IntegralObjectStore.empty .lp64
  let (store, object) ← store.allocate .automatic (.builtin .int)
  let store ← store.initializeValue object (signed 7)
  pure (store, object)

private def valueIs (expected : IntegralValue)
    (result : Except IntegralObjectExpressionError (IntegralResult IntegralValue)) : Bool :=
  match result with
  | .ok (.ok value) => value == expected
  | _ => false

private def readReady (fuel : Nat) : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access => valueIs (signed 7)
          (evaluateIntegralObjectExpression fuel store (.read access))
      | .error _ => false
  | .error _ => false

private def addReady : Bool :=
  match ready with
  | .ok (store, left) =>
      match store.allocate .automatic (.builtin .int) with
      | .ok (store, right) =>
          match store.initializeValue right (signed 9) with
          | .ok store =>
              match store.borrow left, store.borrow right with
              | .ok leftAccess, .ok rightAccess => valueIs (signed 16)
                  (evaluateIntegralObjectExpression 6 store
                    (.binary .add (.read leftAccess) (.read rightAccess)))
              | _, _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def negateReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access => valueIs (signed (-7))
          (evaluateIntegralObjectExpression 3 store (.unary .negate (.read access)))
      | .error _ => false
  | .error _ => false

private def complementReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access => valueIs (signed (-8))
          (evaluateIntegralObjectExpression 3 store (.unary .complement (.read access)))
      | .error _ => false
  | .error _ => false

private def logicalNotReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access => valueIs ⟨.boolean, 0⟩
          (evaluateIntegralObjectExpression 3 store (.unary .logicalNot (.read access)))
      | .error _ => false
  | .error _ => false

private def assignReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let expression := .binary .add (.read access) (.literal (signed 2))
          match assignIntegralObjectExpression 5 store access (.builtin .int) expression with
          | .ok store => valueIs (signed 9)
              (evaluateIntegralObjectExpression 3 store (.read access))
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def defaultAssign : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .ok store =>
      match store.allocate .automatic (.builtin .int) with
      | .ok (store, object) =>
          match store.defaultInitialize object with
          | .ok store =>
              match store.borrow object with
              | .ok access =>
                  match assignIntegralObjectExpression 2 store access (.builtin .int)
                      (.literal (signed 40000)) with
                  | .ok store => valueIs (signed 40000)
                      (evaluateIntegralObjectExpression 2 store (.read access))
                  | .error _ => false
              | .error _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def staleRead : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match store.endLifetime object with
          | .ok store =>
              match evaluateIntegralObjectExpression 3 store (.read access) with
              | .error (.object (.lifetime .lifetimeEnded)) => true
              | _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def constWrite : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object true with
      | .ok access =>
          match assignIntegralObjectExpression 3 store access (.builtin .int)
              (.literal (signed 1)) with
          | .error (.object .constWrite) => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard readReady 3
#guard addReady
#guard negateReady
#guard complementReady
#guard logicalNotReady
#guard assignReady
#guard defaultAssign
#guard staleRead
#guard constWrite

#guard match ready with
  | .ok (store, _) =>
      match evaluateIntegralObjectExpression 3 store (.literal ⟨.signed 0, 1⟩) with
      | .ok (.invalid .zeroWidth) => true
      | _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match evaluateIntegralObjectExpression 0 store (.read access) with
          | .error .fuelExhausted => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match evaluateIntegralObjectExpression 1 store
              (.binary .add (.read access) (.literal (signed 1))) with
          | .error .fuelExhausted => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match evaluateIntegralObjectExpression 1 store (.unary .negate (.read access)) with
          | .error .fuelExhausted => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok _ =>
          match evaluateIntegralObjectExpression 3 store
              (.unary .plus (.literal ⟨.boolean, 1⟩)) with
          | .ok (.unsupported .unpromotedBoolean) => true
          | _ => false
      | .error _ => false
  | .error _ => false

end LeanModels.Cpp.IntegralObjectExpressionTests
