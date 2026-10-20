import Examples.cpp.tinyxml2.NodeGetLineNum
import Examples.cpp.tinyxml2.AttributeGetLineNum

namespace Examples.cpp.tinyxml2

open LeanModels.Cpp

/-- The caller supplies a valid live receiver/member binding and initialized value.
The generated original method returns that value and the identical caller memory. -/
theorem NodeGetLineNum.returns_member (state : IntegralMemberSnapshot)
    (access : IntegralObjectRef) (value : IntegralValue)
    (bound : state.bind NodeGetLineNum.getter = .ok access)
    (read : state.memory.read access = .ok value) :
    NodeGetLineNum.getter.invoke state = .ok (state.memory, value) :=
  IntegralMemberGetter.invoke_of_read NodeGetLineNum.getter state access value value (by decide) bound read rfl

/-- The second original class has the same source shape with distinct identities. -/
theorem AttributeGetLineNum.returns_member (state : IntegralMemberSnapshot)
    (access : IntegralObjectRef) (value : IntegralValue)
    (bound : state.bind AttributeGetLineNum.getter = .ok access)
    (read : state.memory.read access = .ok value) :
    AttributeGetLineNum.getter.invoke state = .ok (state.memory, value) :=
  IntegralMemberGetter.invoke_of_read AttributeGetLineNum.getter state access value value (by decide) bound read rfl

private def state (getter : IntegralMemberGetter) : IntegralMemberSnapshot := {
  memory := {
    profile := .lp64
    objects := {objects := [
      {duration := .automatic, type := .record getter.owner, phase := .aliveInitialized},
      {duration := .automatic, type := getter.field.type, phase := .aliveInitialized}]}
    values := [none, some ⟨.signed 32, 7⟩]}
  object := 0, member := 1, field := getter.field.declaration}

private def observed (getter : IntegralMemberGetter) : Option Int :=
  match getter.invoke (state getter) with
  | .ok (memory, value) =>
      if memory == (state getter).memory && value.format == .signed 32 then some value.value else none
  | _ => none

-- Kernel-reduced non-vacuity controls on the generated original bodies.
private theorem live_examples :
    observed NodeGetLineNum.getter = some 7 ∧
    observed AttributeGetLineNum.getter = some 7 := by decide

#print axioms NodeGetLineNum.returns_member
#print axioms AttributeGetLineNum.returns_member
#print axioms live_examples

end Examples.cpp.tinyxml2
