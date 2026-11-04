import LeanModels.Cpp.RecordObjects

namespace LeanModels.Cpp.RecordAliasTests

private def h (name : String) : FrontendHandle := ⟨name⟩
private def intType : CppTypeEvidence := .builtin .int
private def value (n : Int) : IntegralValue := ⟨.signed 32, n⟩
private def schema : IntegralRecordSchema := {
  declaration := h "Box", name := "Box", fields := [
    {declaration := h "left", name := "left", type := intType, isMutable := false},
    {declaration := h "fixed", name := "fixed", type := .qualified true false intType,
      isMutable := false},
    {declaration := h "cache", name := "cache", type := intType, isMutable := true}]}

private def aliasAndLifetime : Except IntegralRecordError Bool := do
  let empty ← IntegralRecordStore.empty .lp64
  let (first, one) ← empty.create schema .automatic [value 1, value 2, value 3]
  let (store, two) ← first.create schema .dynamic [value 1, value 2, value 3]
  let alias ← store.memberRef one (h "left")
  let other ← store.memberRef two (h "left")
  let before ← store.readMember one (h "left")
  let memory ← (store.memory.assign alias (value 7)).mapError IntegralRecordError.integral
  let store ← store.acceptMemory memory
  let after ← store.readMember one (h "left")
  let distinct ← store.readMember two (h "left")
  let ended ← store.endLifetime one
  let dynamicEnded ← ended.endLifetime two
  let released ← dynamicEnded.releaseStorage two
  pure (before == value 1 && after == value 7 && distinct == value 1 &&
    alias.object != other.object && released.records == store.records &&
    (ended.memory.read alias matches .error (.lifetime .lifetimeEnded)) &&
    (released.memory.read other matches .error (.lifetime .storageReleased)) &&
    (ended.readMember one (h "left") matches .error (.object .lifetimeEnded)) &&
    (released.readMember two (h "left") matches .error (.object .storageReleased)) &&
    (ended.releaseStorage one matches .error (.object .notDynamicStorage)))

def recordAliasLifetimeWitness : Bool := aliasAndLifetime.toOption == some true

#guard recordAliasLifetimeWitness

end LeanModels.Cpp.RecordAliasTests
