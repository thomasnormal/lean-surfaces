# C++ reference type identity and binding

`LeanModels/Cpp/ReferenceTypes.lean` introduces value categories and explicit
lvalue/rvalue reference identities above the scalar, pointer and array type
layers. A `CppReferenceType` retains its reference kind and complete referent
type; a `ReferenceExpression` pairs an expression type with its lvalue,
xvalue or prvalue category.

The binding checker is deliberately exact. It validates the referent, rejects
`void` references and invalid composite types, requires exact type identity,
and admits only lvalue-to-lvalue bindings plus rvalue-to-xvalue/prvalue
bindings. Qualification conversions, temporary materialization, lifetime
extension, bit-fields, function references and user-defined conversions remain
loudly outside this slice rather than being approximated.

This independent checker is a type/category precondition. It does not
create aliases, mutate objects, extend temporary lifetimes or prove that a
compiled expression evaluates to the supplied category.

## Local reference execution boundary

N4950 §6.7.2 `[intro.object]`, §6.7.3 `[basic.life]` and §9.4.4
`[dcl.init.ref]` require an existing-object lvalue reference to designate its
referent rather than copy its value. The automatic-local execution extension
binds nonvolatile integral lvalue references to in-scope parameters, objects
or existing references of the same integral type, permitting added const
qualification. Copy, direct and list syntax retain the same binding rule.

A reference introduces a declaration binding and allocates no object or value
slot. Reads and writes resolve through the shared object identity; assigning
through a reference writes the referent rather than rebinding the reference.
A const view prevents writes, including through a further alias. Binding to
an uninitialized live object performs no read; a later write may initialize
it. Ending the reference's lexical scope removes its binding and never ends
the referent's lifetime. Ordinary owned locals still end once in reverse
declaration order. Every error retains the current frame.

Admission requires structured reference/referent types, variable evidence,
typed initializer subexpressions, an exact in-scope declaration handle and
Clang's lvalue category. Parentheses and qualification-only `NoOp` wrappers
retain identity. Rvalue references, temporary materialization/lifetime
extension, reference parameters/results, bit-fields, subobjects, conversions
to a different integral type, volatile referents and constexpr references
remain explicit boundaries until their rules are represented. This local
binding rule does not widen the independent exact type/category checker above.

## Checks

```sh
lake build LeanModels.Cpp.ReferenceTypeTests LeanModels.Cpp.IntegralObjectFrameTests
```

The guards cover valid lvalue/rvalue references, `void` refusal, incomplete
array referents, exact bindings, category mismatches and type mismatches.

Local execution guards also kernel-check shared identity, mutation visibility,
const rejection, uninitialized binding and ended-lifetime refusals. The generic
`IntegralObjectFrame.bindLocalReference_store` theorem covers every result.
The compiler differential and derived-evidence controls live in
`extractors/cpp/test_evidence_ingestion.py`.
