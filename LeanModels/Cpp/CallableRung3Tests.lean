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

#guard callableIncrementWitness

theorem callable_increment_witness : callableIncrementWitness = true := by
  rfl

#print axioms callable_increment_witness

end LeanModels.Cpp.CallableRung3Tests
