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

This is a type/category precondition, not an execution model. It does not
create aliases, mutate objects, extend temporary lifetimes or prove that a
compiled expression evaluates to the supplied category.

## Checks

```sh
lake build LeanModels.Cpp.ReferenceTypeTests
```

The guards cover valid lvalue/rvalue references, `void` refusal, incomplete
array referents, exact bindings, category mismatches and type mismatches.
