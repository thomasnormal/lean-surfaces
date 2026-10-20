import LeanModels.Cpp.MemberGetters

namespace LeanModels.Cpp.MemberGetterTests

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq first second := match first, second with
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

private def owner : FrontendHandle := ⟨"owner"⟩
private def field : FrontendHandle := ⟨"field"⟩
private def getter (constant : Bool := true) (mutable_ : Bool := false) : IntegralMemberGetter := {
  occurrence := {(default : Declaration) with kind := "CXXMethodDecl", name := some "read"}
  owner, field := {declaration := field, name := "value", type := .builtin .int, isMutable := mutable_}
  isConst := constant, conversions := [], result := .int}

private def snapshot (value : Int := 7) (constant : Bool := false)
    (mutable_ : Bool := false) : IntegralMemberSnapshot := {
  memory := {
    profile := .lp64
    objects := {objects := [
      {duration := .automatic, type := integralMemberViewType (.record owner) constant,
       phase := .aliveInitialized},
      {duration := .automatic, type := integralMemberViewType (.builtin .int) (constant && !mutable_),
       phase := .aliveInitialized}]}
    values := [none, some ⟨.signed 32, value⟩]}
  object := 0, member := 1, field}

private def changes (snapshot : IntegralMemberSnapshot) (object : ObjectId)
    (change : CppObject → CppObject) : IntegralMemberSnapshot :=
  {snapshot with memory := {snapshot.memory with objects :=
    {objects := snapshot.memory.objects.objects.modify object change}}}

private def rejected (snapshot : IntegralMemberSnapshot) : Bool :=
  match getter.invoke snapshot with | .error _ => true | .ok _ => false

-- Kernel decide checks fixed framework controls, not a native execution oracle.
set_option maxRecDepth 10000 in
private theorem kernelGetters :
    [
    getter.invoke (snapshot 7) == .ok ((snapshot 7).memory, ⟨.signed 32, 7⟩),
    getter.invoke (snapshot 7 true) == .ok ((snapshot 7 true).memory, ⟨.signed 32, 7⟩),
    (getter true true).invoke (snapshot 7 true true) ==
      .ok ((snapshot 7 true true).memory, ⟨.signed 32, 7⟩),
    (getter false).invoke (snapshot 7) == .ok ((snapshot 7).memory, ⟨.signed 32, 7⟩),
    (getter false).invoke (snapshot 7 true) == .error .constReceiver,
    (getter false).invoke {snapshot 7 with readOnly := true} == .error .constReceiver,
    rejected {snapshot with object := 1} == true,
    rejected {snapshot with field := ⟨"other"⟩} == true,
    rejected {snapshot with member := 99} == true,
    rejected (changes snapshot 0 (fun object => {object with type := .record ⟨"other"⟩})) == true,
    rejected (changes snapshot 1 (fun object => {object with duration := .dynamic})) == true,
    rejected (changes snapshot 1 (fun object => {object with type := .builtin .short})) == true,
    rejected (changes snapshot 0 (fun object => {object with phase := .ended})) == true,
    rejected (changes snapshot 1 (fun object => {object with phase := .ended})) == true,
    rejected (changes snapshot 0 (fun object => {object with phase := .released})) == true,
    rejected (changes snapshot 1 (fun object => {object with phase := .aliveUninitialized})) == true,
    rejected {snapshot with memory := {snapshot.memory with values := [none, none]}} == true,
    rejected {snapshot with memory := {snapshot.memory with values := [none]}} == true,
    rejected {snapshot with memory := {snapshot.memory with values :=
      [some ⟨.signed 32, 1⟩, some ⟨.signed 32, 7⟩]}} == true,
    rejected (snapshot 2147483648) == true,
    ({getter with conversions := [.boolean], result := .boolean}).invoke (snapshot (-9)) ==
      .ok ((snapshot (-9)).memory, ⟨.boolean, 1⟩),
    ({getter with conversions := [.unsignedChar, .int]}).invoke (snapshot (-1)) ==
      .ok ((snapshot (-1)).memory, ⟨.signed 32, 255⟩)
    ].all id = true := by
  decide

#print axioms kernelGetters
#print axioms IntegralMemberGetter.invoke_memory
#print axioms IntegralMemberGetter.invoke_of_read

end LeanModels.Cpp.MemberGetterTests
