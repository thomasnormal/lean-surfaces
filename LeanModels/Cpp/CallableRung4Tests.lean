import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableRung4Tests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int
def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
def parameter : FrontendHandle := {value := "0x10"}

def switchFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [intType], variadic := false}
  parameters := [{declaration := parameter, name := some "value", type := intType}]
  body := .block (.switch_
    {expression := .parameter parameter, sourceType := intType, type := intType}
    [
      {label := some 1, body := .return_ {
        expression := .integer 10, sourceType := intType, type := intType}},
      {label := some 2, body := .return_ {
        expression := .integer 20, sourceType := intType, type := intType}},
      {label := none, body := .return_ {
        expression := .integer 30, sourceType := intType, type := intType}}])
}

def callableSwitchWitness : Bool :=
  match evaluateCallable 32 .lp64 switchFunction [signed 1],
        evaluateCallable 32 .lp64 switchFunction [signed 2],
        evaluateCallable 32 .lp64 switchFunction [signed 7] with
  | .ok (.ok one), .ok (.ok two), .ok (.ok other) =>
      one == signed 10 && two == signed 20 && other == signed 30
  | _, _, _ => false

def ifFunction : CallableFunction := {
  switchFunction with
  body := .block (.conditional
    {expression := .parameter parameter, sourceType := intType, type := intType}
    (.return_ {expression := .integer 10, sourceType := intType, type := intType})
    (.return_ {expression := .integer 20, sourceType := intType, type := intType}))
}

def callableIfWitness : Bool :=
  match evaluateCallable 16 .lp64 ifFunction [signed 1],
        evaluateCallable 16 .lp64 ifFunction [signed 0] with
  | .ok (.ok positive), .ok (.ok zero) => positive == signed 10 && zero == signed 20
  | _, _ => false

def whileFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    (.whileLoop
      {expression := .parameter parameter, sourceType := intType, type := intType}
      (.expression {
        expression := .increment "--" false parameter,
        sourceType := intType,
        type := intType}))
    (.return_ {expression := .integer 0, sourceType := intType, type := intType}))
}

def callableWhileWitness : Bool :=
  match evaluateCallable 32 .lp64 whileFunction [signed 3],
        evaluateCallable 16 .lp64 whileFunction [signed 0] with
  | .ok (.ok three), .ok (.ok zero) => three == signed 0 && zero == signed 0
  | _, _ => false

def doFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    (.doWhile
      (.expression {
        expression := .increment "++" false parameter,
        sourceType := intType,
        type := intType})
      {expression := .integer 0, sourceType := intType, type := intType})
    (.return_ {expression := .parameter parameter, sourceType := intType, type := intType}))
}

def callableDoWitness : Bool :=
  match evaluateCallable 16 .lp64 doFunction [signed 0] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def forFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    (.forLoop
      (.assign parameter {expression := .integer 0, sourceType := intType, type := intType})
      {expression := .binary "<"
        {expression := .parameter parameter, sourceType := intType, type := intType}
        {expression := .integer 3, sourceType := intType, type := intType},
        sourceType := intType, type := .builtin .boolean}
      (.expression {
        expression := .increment "++" false parameter,
        sourceType := intType,
        type := intType})
      (.compoundAssign "+=" parameter
        {expression := .integer 1, sourceType := intType, type := intType}))
    (.return_ {expression := .parameter parameter, sourceType := intType, type := intType}))
}

def callableForWitness : Bool :=
  match evaluateCallable 64 .lp64 forFunction [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def breakFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    (.whileLoop
      {expression := .parameter parameter, sourceType := intType, type := intType}
      .break_)
    (.return_ {expression := .parameter parameter, sourceType := intType, type := intType}))
}

def callableBreakWitness : Bool :=
  match evaluateCallable 16 .lp64 breakFunction [signed 3] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def continueFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    (.forLoop
      (.assign parameter {expression := .integer 0, sourceType := intType, type := intType})
      {expression := .binary "<"
        {expression := .parameter parameter, sourceType := intType, type := intType}
        {expression := .integer 3, sourceType := intType, type := intType},
        sourceType := intType, type := .builtin .boolean}
      (.expression {
        expression := .increment "++" false parameter,
        sourceType := intType,
        type := intType})
      (.sequence
        (.compoundAssign "+=" parameter
          {expression := .integer 1, sourceType := intType, type := intType})
        (.sequence .continue_
          (.compoundAssign "+=" parameter
            {expression := .integer 100, sourceType := intType, type := intType}))))
    (.return_ {expression := .parameter parameter, sourceType := intType, type := intType}))
}

def callableContinueWitness : Bool :=
  match evaluateCallable 64 .lp64 continueFunction [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def nullFunction : CallableFunction := {
  switchFunction with
  body := .block (.sequence
    .skip
    (.return_ {expression := .parameter parameter, sourceType := intType, type := intType}))
}

def callableNullWitness : Bool :=
  match evaluateCallable 16 .lp64 nullFunction [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

#guard callableSwitchWitness
#guard callableIfWitness
#guard callableWhileWitness
#guard callableDoWitness
#guard callableForWitness
#guard callableBreakWitness
#guard callableContinueWitness
#guard callableNullWitness

theorem callable_switch_witness : callableSwitchWitness = true := by
  rfl

theorem callable_if_witness : callableIfWitness = true := by
  rfl

theorem callable_while_witness : callableWhileWitness = true := by
  rfl

theorem callable_do_witness : callableDoWitness = true := by
  rfl

theorem callable_for_witness : callableForWitness = true := by
  rfl

theorem callable_break_witness : callableBreakWitness = true := by
  rfl

theorem callable_continue_witness : callableContinueWitness = true := by
  rfl

theorem callable_null_witness : callableNullWitness = true := by
  rfl

#print axioms callable_switch_witness
#print axioms callable_if_witness
#print axioms callable_while_witness
#print axioms callable_do_witness
#print axioms callable_for_witness
#print axioms callable_break_witness
#print axioms callable_continue_witness
#print axioms callable_null_witness

end LeanModels.Cpp.CallableRung4Tests
