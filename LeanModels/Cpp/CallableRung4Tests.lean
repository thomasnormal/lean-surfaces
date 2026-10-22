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

#guard callableSwitchWitness

theorem callable_switch_witness : callableSwitchWitness = true := by
  rfl

#print axioms callable_switch_witness

end LeanModels.Cpp.CallableRung4Tests
