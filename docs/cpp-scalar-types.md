# C++ scalar type identities

`LeanModels/Cpp/ScalarTypes.lean` adds the first type-system slice after the
object/lifetime store. It keeps C++ scalar identity separate from value
formats: standard integer identity reuses `CppIntType`, while wide character
and floating families have their own constructors. Equal widths therefore do
not collapse distinct C++ types such as `long` and `long long`.

`CppQualifiedScalar` attaches independent `const` and `volatile` qualifiers.
The model exposes qualification operations, cv-insensitive identity, and the
standard arithmetic/integral/object predicates. `void` is not an object or an
arithmetic type; wide characters are integral for these predicates, and the
floating families are arithmetic but not integral.

`ScalarProfile` records implementation facts needed to talk about scalar
value widths. The development `lp64` profile uses the existing integer target
profile, 8/16/32-bit `char8_t`/`char16_t`/`char32_t` widths, and 32/64/80-bit
floating widths. `scalarWidthBits` validates the profile before resolving a
type and refuses `void`; the result is a value-width fact, not an object
layout or ABI claim. Alignment, padding, arrays, pointers, class layout and
execution remain outside this item.

## Checks

```sh
lake build LeanModels.Cpp.ScalarTypeTests
```

The guards cover type-category predicates, qualification changes, cv-erased
identity, profile validation, width resolution, `void` refusal and distinct
equal-width integer identities.
