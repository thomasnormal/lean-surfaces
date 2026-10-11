# C++ integral expression typing

`LeanModels/Cpp/IntegralExpressionTypes.lean` adds the type-level expression
rules needed after scalar, composite and reference identities. It models the
integral unary operators plus/minus/complement/logical-not and the built-in
integral binary operators, including arithmetic, bitwise, shifts and
comparisons.

Arithmetic, bitwise and comparison operators use the existing target-profile
integral promotions and usual arithmetic conversions. Comparisons produce
`bool`; shifts preserve the promoted left operand type while independently
validating the count promotion. Unary arithmetic operators promote their
operand and logical-not produces `bool`. Every inferred result is a prvalue
`CppType`.

This slice only infers types. It does not evaluate values, perform
lvalue-to-rvalue conversion, sequence side effects, resolve overloads,
implement pointer arithmetic, or admit floating, enum, class or user-defined
operators. Invalid target profiles remain loud.

## Checks

```sh
lake build LeanModels.Cpp.IntegralExpressionTypeTests
```

The guards cover LP64 and 16-bit-`int` promotion cases, mixed signedness,
comparison results, shifts, unary operators, prvalue result construction and
invalid profiles.
