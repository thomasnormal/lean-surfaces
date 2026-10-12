import LeanModels.Cpp.IntegralObjectStatements

namespace LeanModels.Cpp.IntegralObjectStatementTests

open LeanModels.Cpp

private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

private def ready : Except IntegralObjectError (IntegralObjectStore × ObjectId) := do
  let store ← IntegralObjectStore.empty .lp64
  let (store, object) ← store.allocate .automatic (.builtin .int)
  let store ← store.initializeValue object (signed 7)
  pure (store, object)

private def readValue (expected : IntegralValue) (store : IntegralObjectStore)
    (access : IntegralObjectRef) : Bool :=
  match store.read access with
  | .ok value => value == expected
  | .error _ => false

private def sequenceReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let statement := .sequence
            (.assign access (.builtin .int)
              (.binary .add (.read access) (.literal (signed 2))))
            (.expression (.unary .negate (.read access)))
          match executeIntegralObjectStatement 8 store statement with
          | .ok store => readValue (signed 9) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def initializeReady : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .ok store =>
      match store.allocate .automatic (.builtin .int) with
      | .ok (store, object) =>
          let statement := .initialize object (.builtin .int) (.literal (signed 13))
          match executeIntegralObjectStatement 4 store statement with
          | .ok store =>
              match store.borrow object with
              | .ok access => readValue (signed 13) store access
              | .error _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def defaultInitializeReady : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .ok store =>
      match store.allocate .automatic (.builtin .int) with
      | .ok (store, object) =>
          match executeIntegralObjectStatement 2 store (.defaultInitialize object) with
          | .ok store =>
              match store.borrow object with
              | .ok access =>
                  match store.read access with
                  | .error (.lifetime .notInitialized) => true
                  | _ => false
              | .error _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def aliasOrder : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object, store.borrow object with
      | .ok first, .ok second =>
          let statement := .sequence
            (.assign first (.builtin .int) (.literal (signed 12)))
            (.expression (.read second))
          match executeIntegralObjectStatement 5 store statement with
          | .ok store => readValue (signed 12) store second
          | .error _ => false
      | _, _ => false
  | .error _ => false

private def conditionalTrue : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let statement := .conditional (.read access)
            (.assign access (.builtin .int) (.literal (signed 11)))
            (.assign access (.builtin .int) (.literal (signed 22)))
          match executeIntegralObjectStatement 6 store statement with
          | .ok store => readValue (signed 11) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def conditionalFalse : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let statement := .conditional (.literal ⟨.boolean, 0⟩)
            (.assign access (.builtin .int) (.literal (signed 11)))
            (.assign access (.builtin .int) (.literal (signed 22)))
          match executeIntegralObjectStatement 6 store statement with
          | .ok store => readValue (signed 22) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def whileReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let body := .assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1)))
          match executeIntegralObjectStatement 20 store (.whileLoop (.read access) body) with
          | .ok store => readValue (signed 0) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def whileEmpty : Bool :=
  match IntegralObjectStore.empty .lp64 with
  | .ok store =>
      match store.allocate .automatic (.builtin .int) with
      | .ok (store, object) =>
          match store.initializeValue object (signed 0) with
          | .ok store =>
              match store.borrow object with
              | .ok access =>
                  let body := .assign access (.builtin .int) (.literal (signed 99))
                  match executeIntegralObjectStatement 4 store
                      (.whileLoop (.read access) body) with
                  | .ok store => readValue (signed 0) store access
                  | .error _ => false
              | .error _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def forReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let initializer := .assign access (.builtin .int) (.literal (signed 3))
          let condition := .binary .greater (.read access) (.literal (signed 0))
          let step := .assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1)))
          match executeIntegralObjectStatement 24 store
              (.forLoop initializer condition step (.expression (.read access))) with
          | .ok store => readValue (signed 0) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def breakReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let decrement := .assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1)))
          let body := .sequence decrement .break_
          let condition := .binary .greater (.read access) (.literal (signed 0))
          match executeIntegralObjectStatement 12 store (.whileLoop condition body) with
          | .ok store => readValue (signed 6) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def continueReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let decrement := .assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1)))
          let body := .sequence decrement .continue_
          let condition := .binary .greater (.read access) (.literal (signed 0))
          match executeIntegralObjectStatement 16 store (.whileLoop condition body) with
          | .ok store => readValue (signed 0) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def forContinueReady : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let decrement := .assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1)))
          let body := .sequence decrement .continue_
          let condition := .binary .greater (.read access) (.literal (signed 0))
          match executeIntegralObjectStatement 16 store
              (.forLoop (.assign access (.builtin .int) (.literal (signed 3)))
                condition decrement body) with
          | .ok store => readValue (signed (-1)) store access
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def divisionError : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          let expression := .binary .divide (.read access) (.literal (signed 0))
          match executeIntegralObjectStatement 4 store (.expression expression) with
          | .error (.undefined .divisionByZero) => true
          | _ => false
      | .error _ => false
  | .error _ => false

private def staleError : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match store.endLifetime object with
          | .ok store =>
              match executeIntegralObjectStatement 3 store (.expression (.read access)) with
              | .error (.object (.lifetime .lifetimeEnded)) => true
              | _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def constError : Bool :=
  match ready with
  | .ok (store, object) =>
      match store.borrow object true with
      | .ok access =>
          match executeIntegralObjectStatement 3 store
              (.assign access (.builtin .int) (.literal (signed 1))) with
          | .error (.object .constWrite) => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard sequenceReady
#guard initializeReady
#guard defaultInitializeReady
#guard aliasOrder
#guard conditionalTrue
#guard conditionalFalse
#guard whileReady
#guard whileEmpty
#guard forReady
#guard breakReady
#guard continueReady
#guard forContinueReady
#guard divisionError
#guard staleError
#guard constError

#guard match ready with
  | .ok (store, _) =>
      match executeIntegralObjectStatement 0 store (.expression (.literal (signed 1))) with
      | .error .fuelExhausted => true
      | _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, _) =>
      match executeIntegralObjectStatement 2 store .break_ with
      | .error .breakOutsideLoop => true
      | _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, _) =>
      match executeIntegralObjectStatement 2 store .continue_ with
      | .error .continueOutsideLoop => true
      | _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match executeIntegralObjectStatement 3 store
              (.whileLoop (.literal ⟨.boolean, 1⟩) (.expression (.read access))) with
          | .error .fuelExhausted => true
          | _ => false
      | .error _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, _) =>
      let condition := .binary .divide (.literal (signed 1)) (.literal (signed 0))
      match executeIntegralObjectStatement 4 store
          (.conditional condition (.expression (.literal (signed 1)))
            (.expression (.literal (signed 2)))) with
      | .error (.undefined .divisionByZero) => true
      | _ => false
  | .error _ => false

#guard match ready with
  | .ok (store, object) =>
      match store.borrow object with
      | .ok access =>
          match executeIntegralObjectStatement 1 store
              (.sequence (.expression (.read access)) (.expression (.read access))) with
          | .error .fuelExhausted => true
          | _ => false
      | .error _ => false
  | .error _ => false

end LeanModels.Cpp.IntegralObjectStatementTests
