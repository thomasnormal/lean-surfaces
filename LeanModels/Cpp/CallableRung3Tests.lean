import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableRung3Tests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int
def shortType : CppTypeEvidence := .builtin .short
def unsignedIntType : CppTypeEvidence := .builtin .unsignedInt
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

def assignmentFunction : CallableFunction := {
  incrementFunction with
  body := .block (.sequence
    (.assign parameter
      {expression := .binary "+"
        {expression := .parameter parameter, sourceType := intType, type := intType}
        {expression := .integer 3, sourceType := intType, type := intType},
        sourceType := intType, type := intType})
    (.return_ {
      expression := .parameter parameter
      sourceType := intType
      type := intType}))
}

def callableAssignmentWitness : Bool :=
  match evaluateCallable 16 .lp64 assignmentFunction [signed 4] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def mixedLeftParameter : FrontendHandle := {value := "0x30"}
def mixedRightParameter : FrontendHandle := {value := "0x31"}

def mixedArithmeticFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedIntType, parameters := [shortType, unsignedIntType], variadic := false}
  parameters := [
    {declaration := mixedLeftParameter, name := some "left", type := shortType},
    {declaration := mixedRightParameter, name := some "right", type := unsignedIntType}]
  body := .block (.return_ {
    expression := .binary "+"
      {expression := .parameter mixedLeftParameter, sourceType := shortType, type := unsignedIntType}
      {expression := .parameter mixedRightParameter, sourceType := unsignedIntType, type := unsignedIntType},
    sourceType := unsignedIntType
    type := unsignedIntType})
}

def callableMixedArithmeticWitness : Bool :=
  match evaluateCallable 16 .lp64 mixedArithmeticFunction
      [⟨.signed 16, -1⟩, ⟨.unsigned 32, 1⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 32, 0⟩
  | _ => false

def mixedCompoundFunction : CallableFunction := {
  occurrence := default
  signature := {result := shortType, parameters := [shortType, unsignedIntType], variadic := false}
  parameters := [
    {declaration := mixedLeftParameter, name := some "left", type := shortType},
    {declaration := mixedRightParameter, name := some "right", type := unsignedIntType}]
  body := .block (.sequence
    (.compoundAssign "+=" mixedLeftParameter
      {expression := .parameter mixedRightParameter
       sourceType := unsignedIntType
       type := unsignedIntType})
    (.return_ {
      expression := .parameter mixedLeftParameter
      sourceType := shortType
      type := shortType}))
}

def callableMixedCompoundWitness : Bool :=
  match evaluateCallable 16 .lp64 mixedCompoundFunction
      [⟨.signed 16, -1⟩, ⟨.unsigned 32, 1⟩] with
  | .ok (.ok value) => value == ⟨.signed 16, 0⟩
  | _ => false

def mixedComparisonFunction : CallableFunction := {
  occurrence := default
  signature := {result := .builtin .boolean, parameters := [shortType, unsignedIntType], variadic := false}
  parameters := [
    {declaration := mixedLeftParameter, name := some "left", type := shortType},
    {declaration := mixedRightParameter, name := some "right", type := unsignedIntType}]
  body := .block (.return_ {
    expression := .binary "<"
      {expression := .parameter mixedLeftParameter, sourceType := shortType, type := unsignedIntType}
      {expression := .parameter mixedRightParameter, sourceType := unsignedIntType, type := unsignedIntType},
    sourceType := .builtin .boolean
    type := .builtin .boolean})
}

def callableMixedComparisonWitness : Bool :=
  match evaluateCallable 16 .lp64 mixedComparisonFunction
      [⟨.signed 16, -1⟩, ⟨.unsigned 32, 1⟩] with
  | .ok (.ok value) => value == integralBoolean false
  | _ => false

def calleeParameter : FrontendHandle := {value := "0x20"}

def addThreeCallee : CallableCallee := {
  signature := {result := intType, parameters := [intType], variadic := false}
  parameters := [{declaration := calleeParameter, name := some "value", type := intType}]
  body := .block (.return_ {
    expression := .binary "+"
      {expression := .parameter calleeParameter, sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType},
    sourceType := intType, type := intType})
}

def callFunction : CallableFunction := {
  incrementFunction with
  body := .block (.return_ {
    expression := .call addThreeCallee [{
      expression := .parameter parameter
      sourceType := intType
      type := intType}]
    sourceType := intType
    type := intType})
}

def callableCallWitness : Bool :=
  match evaluateCallable 32 .lp64 callFunction [signed 4] with
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

def logicalExpression : TypedCallableExpression := {
  expression := .logical "&&"
    {expression := .parameter parameter, sourceType := intType, type := intType}
    {expression := .increment "++" false parameter, sourceType := intType, type := intType}
  sourceType := .builtin .boolean
  type := .builtin .boolean}

def logicalFunction : CallableFunction := {
  incrementFunction with
  body := .block (.return_ {
    expression := .comma logicalExpression
      {expression := .parameter parameter, sourceType := intType, type := intType}
    sourceType := intType
    type := intType})
}

def callableLogicalWitness : Bool :=
  match evaluateCallable 16 .lp64 logicalFunction [signed 0],
        evaluateCallable 16 .lp64 logicalFunction [signed 1] with
  | .ok (.ok zero), .ok (.ok one) => zero == signed 0 && one == signed 2
  | _, _ => false

def logicalOrExpression : TypedCallableExpression := {
  expression := .logical "||"
    {expression := .parameter parameter, sourceType := intType, type := intType}
    {expression := .increment "++" false parameter, sourceType := intType, type := intType}
  sourceType := .builtin .boolean
  type := .builtin .boolean}

def logicalOrFunction : CallableFunction := {
  incrementFunction with
  body := .block (.return_ {
    expression := .comma logicalOrExpression
      {expression := .parameter parameter, sourceType := intType, type := intType}
    sourceType := intType
    type := intType})
}

def callableLogicalOrWitness : Bool :=
  match evaluateCallable 16 .lp64 logicalOrFunction [signed 1],
        evaluateCallable 16 .lp64 logicalOrFunction [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 1 && zero == signed 1
  | _, _ => false

#guard callableIncrementWitness
#guard callablePostfixWitness
#guard callableCompoundAssignmentWitness
#guard callableAssignmentWitness
#guard callableMixedArithmeticWitness
#guard callableMixedCompoundWitness
#guard callableMixedComparisonWitness
#guard callableCallWitness
#guard callableConditionalWitness
#guard callableLogicalWitness
#guard callableLogicalOrWitness

theorem callable_increment_witness : callableIncrementWitness = true := by
  rfl

theorem callable_postfix_witness : callablePostfixWitness = true := by
  rfl

theorem callable_compound_assignment_witness : callableCompoundAssignmentWitness = true := by
  rfl

theorem callable_assignment_witness : callableAssignmentWitness = true := by
  rfl

theorem callable_mixed_arithmetic_witness : callableMixedArithmeticWitness = true := by
  rfl

theorem callable_mixed_compound_witness : callableMixedCompoundWitness = true := by
  rfl

theorem callable_mixed_comparison_witness : callableMixedComparisonWitness = true := by
  rfl

theorem callable_call_witness : callableCallWitness = true := by
  rfl

theorem callable_conditional_witness : callableConditionalWitness = true := by
  rfl

theorem callable_logical_witness : callableLogicalWitness = true := by
  rfl

theorem callable_logical_or_witness : callableLogicalOrWitness = true := by
  rfl

#print axioms callable_increment_witness
#print axioms callable_postfix_witness
#print axioms callable_compound_assignment_witness
#print axioms callable_assignment_witness
#print axioms callable_mixed_arithmetic_witness
#print axioms callable_mixed_compound_witness
#print axioms callable_mixed_comparison_witness
#print axioms callable_call_witness
#print axioms callable_conditional_witness
#print axioms callable_logical_witness
#print axioms callable_logical_or_witness

end LeanModels.Cpp.CallableRung3Tests
