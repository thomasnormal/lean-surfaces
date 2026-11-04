import LeanModels.Cpp.RecordObjects
import LeanModels.Cpp.CallableObjectEvaluation

namespace LeanModels.Cpp.RecordObjectTests

private def h (name : String) : FrontendHandle := ⟨name⟩
private def intType : CppTypeEvidence := .builtin .int
private def value (n : Int) : IntegralValue := ⟨.signed 32, n⟩
private def schema : IntegralRecordSchema := {
  declaration := h "Box", name := "Box", fields := [
    {declaration := h "left", name := "left", type := intType, isMutable := false},
    {declaration := h "fixed", name := "fixed", type := .qualified true false intType, isMutable := false},
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

private def constViews : Except IntegralRecordError Bool := do
  let empty ← IntegralRecordStore.empty .lp64
  let (store, mutable) ← empty.create schema .automatic [value 1, value 2, value 3]
  let view ← store.borrow mutable.object true
  let denied := store.assignMember view (h "left") (value 7)
  let store ← store.assignMember view (h "cache") (value 8)
  let cache ← store.readMember mutable (h "cache")
  let (store, constant) ← store.create schema .automatic [value 1, value 2, value 3] true
  let field ← store.memberRef {constant with readOnly := false} (h "left")
  let forged := store.memory.assign {field with type := intType} (value 7)
  let store ← store.assignMember constant (h "cache") (value 9)
  let actualCache ← store.readMember constant (h "cache")
  pure ((denied matches .error (.integral .constWrite)) && cache == value 8 &&
    (forged matches .error .constWrite) && actualCache == value 9 &&
    (store.assignMember mutable (h "fixed") (value 7) matches .error (.integral .constWrite)))

private def malformed : Except IntegralRecordError Bool := do
  let empty ← IntegralRecordStore.empty .lp64
  let (store, access) ← empty.create schema .automatic [value 1, value 2, value 3]
  let duplicate := {store with records := store.records ++ store.records}
  let (two, _) ← store.create schema .automatic [value 4, value 5, value 6]
  let shared := {two with records := two.records.modify 1 (fun second =>
    {second with members := two.records[0]!.members})}
  let metadata := store.memory.objects.objects.modify 1 (fun object => {object with phase := .ended})
  let broken := {store.memory with objects := ⟨metadata⟩, values := store.memory.values.modify 1 (fun _ => none)}
  let wrong := {access with declaration := h "Other"}
  let conflicting := {schema with name := "Different"}
  let changedTarget := {store.memory with profile := {store.memory.profile with longWidth := 32}}
  let movedObjects := store.memory.objects.objects.map (fun object => {object with duration := .dynamic})
  let moved := {store.memory with objects := ⟨movedObjects⟩}
  pure ((duplicate.check matches .error .incoherentStore) &&
    (shared.check matches .error .incoherentStore) &&
    (({store with memory := broken} : IntegralRecordStore).check matches .error .incoherentStore) &&
    (IntegralRecordStore.fromMemory store.memory matches .error .incoherentStore) &&
    (store.create conflicting .automatic [value 1, value 2, value 3] matches .error .incoherentStore) &&
    (store.acceptMemory changedTarget matches .error .incoherentStore) &&
    (store.acceptMemory moved matches .error .incoherentStore) &&
    (store.acceptMemory broken matches .error .incoherentStore) &&
    (store.readMember wrong (h "left") matches .error .wrongRecordType) &&
    (store.readMember access (h "missing") matches .error (.missingMember _)) &&
    (empty.create schema .automatic [] matches .error .arityMismatch) &&
    (empty.create schema .automatic [value 1, value 2, ⟨.unsigned 32, 3⟩]
      matches .error (.integral .valueTypeMismatch)) &&
    (empty.create {schema with fields := schema.fields ++ schema.fields} .automatic []
      matches .error .invalidSchema))

private def callableLoan : Except IntegralRecordError Bool := do
  let empty ← IntegralRecordStore.empty .lp64
  let (store, access) ← empty.create schema .automatic [value 1, value 2, value 3]
  let member ← store.memberRef access (h "left")
  let function : CallableFunction := {
    occurrence := {
      id := "f", kind := "FunctionDecl", path := [], name := some "f", lexicalParents := [],
      semanticParent := none, previousDecl := none, mangledName := none, type := none,
      location := none, range := none},
    signature := {result := .void, parameters := [.lvalueReference intType], variadic := false},
    parameters := [{declaration := h "arg", name := none, type := .lvalueReference intType}],
    body := .assign (h "arg") ⟨.integer 11, intType, intType⟩}
  let result := CallableObjectEvaluation.evaluateCallableObjectResultInStore 32 store.memory function [.lvalue member]
  let updated ← store.acceptMemory result.frame.store
  let field ← updated.readMember access (h "left")
  pure ((result.result matches .ok (.ok none)) && field == value 11 &&
    result.frame.scopes.isEmpty && updated.records == store.records)

#guard aliasAndLifetime.toOption == some true
#guard constViews.toOption == some true
#guard malformed.toOption == some true
#guard callableLoan.toOption == some true

private theorem kernelRecords :
    (aliasAndLifetime.toOption == some true && constViews.toOption == some true &&
      malformed.toOption == some true && callableLoan.toOption == some true) = true := by decide
#print axioms kernelRecords
#print axioms IntegralRecordStore.acceptMemory_records

end LeanModels.Cpp.RecordObjectTests
