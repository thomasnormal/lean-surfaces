import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableRung3Tests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int
def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
def parameter : FrontendHandle := {value := "0x10"}

def incrementFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [intType], variadic := false}
  parameters := [{declaration := parameter, name := some "value", type := intType}]
  body := .block (.return_ {
    expression := .increment "++" false parameter
    sourceType := intType
    type := intType})
}

def callableIncrementWitness : Bool :=
  match evaluateCallable 16 .lp64 incrementFunction [signed 4] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def postfixFunction : CallableFunction := {
  incrementFunction with
  body := .block (.return_ {
    expression := .comma
      {expression := .increment "++" true parameter, sourceType := intType, type := intType}
      {expression := .parameter parameter, sourceType := intType, type := intType}
    sourceType := intType
    type := intType})
}

def callablePostfixWitness : Bool :=
  match evaluateCallable 16 .lp64 postfixFunction [signed 4] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def compoundAssignmentFunction : CallableFunction := {
  incrementFunction with
  body := .block (.sequence
    (.compoundAssign "+=" parameter
      {expression := .integer 3, sourceType := intType, type := intType})
    (.return_ {
      expression := .parameter parameter
      sourceType := intType
      type := intType}))
}

def callableCompoundAssignmentWitness : Bool :=
  match evaluateCallable 16 .lp64 compoundAssignmentFunction [signed 4] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def conditionalFunction : CallableFunction := {
  incrementFunction with
  body := .block (.return_ {
    expression := .conditional
      {expression := .parameter parameter, sourceType := intType, type := intType}
      {expression := .integer 7, sourceType := intType, type := intType}
      {expression := .integer 8, sourceType := intType, type := intType}
    sourceType := intType
    type := intType})
}

def callableConditionalWitness : Bool :=
  match evaluateCallable 16 .lp64 conditionalFunction [signed 1],
        evaluateCallable 16 .lp64 conditionalFunction [signed 0] with
  | .ok (.ok positive), .ok (.ok zero) => positive == signed 7 && zero == signed 8
  | _, _ => false

#guard callableIncrementWitness
#guard callablePostfixWitness
#guard callableCompoundAssignmentWitness
#guard callableConditionalWitness

theorem callable_increment_witness : callableIncrementWitness = true := by
  rfl

theorem callable_postfix_witness : callablePostfixWitness = true := by
  rfl

theorem callable_compound_assignment_witness : callableCompoundAssignmentWitness = true := by
  rfl

theorem callable_conditional_witness : callableConditionalWitness = true := by
  rfl

#print axioms callable_increment_witness
#print axioms callable_postfix_witness
#print axioms callable_compound_assignment_witness
#print axioms callable_conditional_witness

end LeanModels.Cpp.CallableRung3Tests
