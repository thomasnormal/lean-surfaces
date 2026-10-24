import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableRung3Tests

open LeanModels.Cpp

def intType : CppTypeEvidence := .builtin .int
def shortType : CppTypeEvidence := .builtin .short
def unsignedCharType : CppTypeEvidence := .builtin .unsignedChar
def unsignedShortType : CppTypeEvidence := .builtin .unsignedShort
def unsignedIntType : CppTypeEvidence := .builtin .unsignedInt
def unsignedLongType : CppTypeEvidence := .builtin .unsignedLong
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

def narrowParameter : FrontendHandle := {value := "0x11"}

def narrowIncrementFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedShortType, parameters := [unsignedShortType], variadic := false}
  parameters := [{declaration := narrowParameter, name := some "value", type := unsignedShortType}]
  body := .block (.return_ {
    expression := .increment "++" false narrowParameter
    sourceType := unsignedShortType
    type := unsignedShortType})
}

def callableNarrowIncrementWitness : Bool :=
  match evaluateCallable 16 .lp64 narrowIncrementFunction [⟨.unsigned 16, 65535⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 16, 0⟩
  | _ => false

def narrowDecrementFunction : CallableFunction := {
  narrowIncrementFunction with
  body := .block (.return_ {
    expression := .increment "--" false narrowParameter
    sourceType := unsignedShortType
    type := unsignedShortType})
}

def callableNarrowDecrementWitness : Bool :=
  match evaluateCallable 16 .lp64 narrowDecrementFunction [⟨.unsigned 16, 0⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 16, 65535⟩
  | _ => false

def unaryNarrowFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [shortType], variadic := false}
  parameters := [{declaration := narrowParameter, name := some "value", type := shortType}]
  body := .block (.return_ {
    expression := .unary "-"
      {expression := .parameter narrowParameter, sourceType := shortType, type := intType}
    sourceType := intType
    type := intType})
}

def callableUnaryNarrowWitness : Bool :=
  match evaluateCallable 16 .lp64 unaryNarrowFunction [⟨.signed 16, -32768⟩] with
  | .ok (.ok value) => value == signed 32768
  | _ => false

def sizeOfFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedLongType, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .sizeOf shortType
    sourceType := unsignedLongType
    type := unsignedLongType})
}

def callableSizeOfWitness : Bool :=
  match evaluateCallable 16 .lp64 sizeOfFunction [] with
  | .ok (.ok value) => value == ⟨.unsigned 64, 2⟩
  | _ => false

def alignOfFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedLongType, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .alignOf shortType
    sourceType := unsignedLongType
    type := unsignedLongType})
}

def callableAlignOfWitness : Bool :=
  match evaluateCallable 16 .lp64 alignOfFunction [] with
  | .ok (.ok value) => value == ⟨.unsigned 64, 2⟩
  | _ => false

def boolLiteralFunction : CallableFunction := {
  occurrence := default
  signature := {result := .builtin .boolean, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .integer 1
    sourceType := .builtin .boolean
    type := .builtin .boolean})
}

def callableBoolLiteralWitness : Bool :=
  match evaluateCallable 16 .lp64 boolLiteralFunction [] with
  | .ok (.ok value) => value == integralBoolean true
  | _ => false

def characterLiteralFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .convert {
      expression := .integer 65
      sourceType := .builtin .char
      type := .builtin .char}
    sourceType := intType
    type := intType})
}

def callableCharacterLiteralWitness : Bool :=
  match evaluateCallable 16 .lp64 characterLiteralFunction [] with
  | .ok (.ok value) => value == signed 65
  | _ => false

def constantExpressionFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .integer 7
    sourceType := intType
    type := intType})
}

def callableConstantExpressionWitness : Bool :=
  match evaluateCallable 16 .lp64 constantExpressionFunction [] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def nullPointerComparisonFunction : CallableFunction := {
  occurrence := default
  signature := {result := .builtin .boolean, parameters := [], variadic := false}
  parameters := []
  body := .block (.return_ {
    expression := .nullComparison "=="
    sourceType := .builtin .boolean
    type := .builtin .boolean})
}

def callableNullPointerWitness : Bool :=
  match evaluateCallable 16 .lp64 nullPointerComparisonFunction [] with
  | .ok (.ok value) => value == integralBoolean true
  | _ => false

def nullPointerInequalityFunction : CallableFunction := {
  nullPointerComparisonFunction with
  body := .block (.return_ {
    expression := .nullComparison "!="
    sourceType := .builtin .boolean
    type := .builtin .boolean})
}

def callableNullPointerInequalityWitness : Bool :=
  match evaluateCallable 16 .lp64 nullPointerInequalityFunction [] with
  | .ok (.ok value) => value == integralBoolean false
  | _ => false

def castFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [shortType], variadic := false}
  parameters := [{declaration := narrowParameter, name := some "value", type := shortType}]
  body := .block (.return_ {
    expression := .convert {
      expression := .parameter narrowParameter
      sourceType := shortType
      type := shortType}
    sourceType := shortType
    type := intType})
}

def callableCastWitness : Bool :=
  match evaluateCallable 16 .lp64 castFunction [⟨.signed 16, -7⟩] with
  | .ok (.ok value) => value == signed (-7)
  | _ => false

def narrowCastFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedCharType, parameters := [shortType], variadic := false}
  parameters := [{declaration := narrowParameter, name := some "value", type := shortType}]
  body := .block (.return_ {
    expression := .convert {
      expression := .parameter narrowParameter
      sourceType := shortType
      type := shortType}
    sourceType := shortType
    type := unsignedCharType})
}

def callableNarrowCastWitness : Bool :=
  match evaluateCallable 16 .lp64 narrowCastFunction [⟨.signed 16, -7⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 8, 249⟩
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

def mixedShiftFunction : CallableFunction := {
  occurrence := default
  signature := {result := intType, parameters := [shortType, unsignedIntType], variadic := false}
  parameters := [
    {declaration := mixedLeftParameter, name := some "left", type := shortType},
    {declaration := mixedRightParameter, name := some "right", type := unsignedIntType}]
  body := .block (.return_ {
    expression := .binary ">>"
      {expression := .parameter mixedLeftParameter, sourceType := shortType, type := intType}
      {expression := .parameter mixedRightParameter, sourceType := unsignedIntType, type := unsignedIntType},
    sourceType := intType
    type := intType})
}

def callableMixedShiftWitness : Bool :=
  match evaluateCallable 16 .lp64 mixedShiftFunction
      [⟨.signed 16, -1⟩, ⟨.unsigned 32, 1⟩] with
  | .ok (.ok value) => value == signed (-1)
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

def convertingCalleeParameter : FrontendHandle := {value := "0x21"}

def convertingCallee : CallableCallee := {
  signature := {result := unsignedIntType, parameters := [unsignedIntType], variadic := false}
  parameters := [{declaration := convertingCalleeParameter, name := some "value", type := unsignedIntType}]
  body := .block (.return_ {
    expression := .parameter convertingCalleeParameter
    sourceType := unsignedIntType, type := unsignedIntType})
}

def callConversionFunction : CallableFunction := {
  occurrence := default
  signature := {result := unsignedIntType, parameters := [shortType], variadic := false}
  parameters := [{declaration := narrowParameter, name := some "value", type := shortType}]
  body := .block (.return_ {
    expression := .call convertingCallee [{
      expression := .parameter narrowParameter
      sourceType := shortType
      type := shortType}]
    sourceType := unsignedIntType
    type := unsignedIntType})
}

def callableCallConversionWitness : Bool :=
  match evaluateCallable 32 .lp64 callConversionFunction [⟨.signed 16, -1⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 32, 4294967295⟩
  | _ => false

def parsedCallRaw : Raw := .object [
  ("id", .string "0x90"), ("kind", .string "CallExpr"),
  ("inner", .array [
    .object [("id", .string "0x91"), ("kind", .string "DeclRefExpr"),
      ("referencedDecl", .object [("id", .string "0x20"),
        ("kind", .string "FunctionDecl"), ("name", .string "add_three")])],
    .object [("id", .string "0x92"), ("kind", .string "DeclRefExpr"),
      ("referencedDecl", .object [("id", .string "0x10"),
        ("kind", .string "ParmVarDecl"), ("name", .string "value")])]])]

def parsedCallExpression : Except String TypedCallableExpression :=
  parseCallableDirectCallExpression .lp64 [
    {declaration := parameter, name := some "value", type := intType}]
    [] none [{declaration := calleeParameter, callee := addThreeCallee}]
    parsedCallRaw (some intType)

def callableParsedCallWitness : Bool :=
  match parsedCallExpression with
  | .ok expression =>
      let function : CallableFunction := {
        occurrence := default
        signature := {result := intType, parameters := [intType], variadic := false}
        parameters := [{declaration := parameter, name := some "value", type := intType}]
        body := .block (.return_ expression)}
      match evaluateCallable 32 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

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
#guard callableNarrowIncrementWitness
#guard callableNarrowDecrementWitness
#guard callableUnaryNarrowWitness
#guard callableSizeOfWitness
#guard callableAlignOfWitness
#guard callableBoolLiteralWitness
#guard callableCharacterLiteralWitness
#guard callableConstantExpressionWitness
#guard callableNullPointerWitness
#guard callableNullPointerInequalityWitness
#guard callableCastWitness
#guard callableNarrowCastWitness
#guard callablePostfixWitness
#guard callableCompoundAssignmentWitness
#guard callableAssignmentWitness
#guard callableMixedArithmeticWitness
#guard callableMixedCompoundWitness
#guard callableMixedComparisonWitness
#guard callableMixedShiftWitness
#guard callableCallWitness
#guard callableCallConversionWitness
#guard callableConditionalWitness
#guard callableLogicalWitness
#guard callableLogicalOrWitness

theorem callable_increment_witness : callableIncrementWitness = true := by
  rfl

theorem callable_narrow_increment_witness : callableNarrowIncrementWitness = true := by
  rfl

theorem callable_narrow_decrement_witness : callableNarrowDecrementWitness = true := by
  rfl

theorem callable_unary_narrow_witness : callableUnaryNarrowWitness = true := by
  rfl

theorem callable_size_of_witness : callableSizeOfWitness = true := by
  rfl

theorem callable_align_of_witness : callableAlignOfWitness = true := by
  rfl

theorem callable_bool_literal_witness : callableBoolLiteralWitness = true := by
  rfl

theorem callable_character_literal_witness : callableCharacterLiteralWitness = true := by
  rfl

theorem callable_constant_expression_witness : callableConstantExpressionWitness = true := by
  rfl

theorem callable_null_pointer_witness : callableNullPointerWitness = true := by
  rfl

theorem callable_null_pointer_inequality_witness : callableNullPointerInequalityWitness = true := by
  rfl

theorem callable_cast_witness : callableCastWitness = true := by
  rfl

theorem callable_narrow_cast_witness : callableNarrowCastWitness = true := by
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

theorem callable_mixed_shift_witness : callableMixedShiftWitness = true := by
  rfl

theorem callable_call_witness : callableCallWitness = true := by
  rfl

theorem callable_call_conversion_witness : callableCallConversionWitness = true := by
  rfl

theorem callable_conditional_witness : callableConditionalWitness = true := by
  rfl

theorem callable_logical_witness : callableLogicalWitness = true := by
  rfl

theorem callable_logical_or_witness : callableLogicalOrWitness = true := by
  rfl

#print axioms callable_increment_witness
#print axioms callable_narrow_increment_witness
#print axioms callable_narrow_decrement_witness
#print axioms callable_unary_narrow_witness
#print axioms callable_size_of_witness
#print axioms callable_align_of_witness
#print axioms callable_bool_literal_witness
#print axioms callable_character_literal_witness
#print axioms callable_constant_expression_witness
#print axioms callable_null_pointer_witness
#print axioms callable_null_pointer_inequality_witness
#print axioms callable_cast_witness
#print axioms callable_narrow_cast_witness
#print axioms callable_postfix_witness
#print axioms callable_compound_assignment_witness
#print axioms callable_assignment_witness
#print axioms callable_mixed_arithmetic_witness
#print axioms callable_mixed_compound_witness
#print axioms callable_mixed_comparison_witness
#print axioms callable_mixed_shift_witness
#print axioms callable_call_witness
#print axioms callable_call_conversion_witness
#print axioms callable_conditional_witness
#print axioms callable_logical_witness
#print axioms callable_logical_or_witness

end LeanModels.Cpp.CallableRung3Tests
