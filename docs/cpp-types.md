# C++23 integral type resolution

`LeanModels/Cpp/Types.lean` is the target-profile bridge between named C++
standard integer types and the value formats in `LeanModels/Cpp/Integral.lean`.
It implements the type-level part of integral promotions (§7.3.7) and usual
arithmetic conversions (§7.4) from N4950. It does not parse AST type nodes,
resolve overloads, or admit a callable body.

## Explicit target profile

`TargetProfile` records the widths of `char`, `short`, `int`, `long` and
`long long`, plus the implementation-defined signedness of plain `char`.
`TargetProfile.lp64` is the development profile: 8/16/32/64/64 bits and signed
plain `char`. Widths are facts supplied by the frontend/toolchain profile, not
inferred from a host Lean ABI. Validation enforces N4950 §6.8.2's minimum
widths (8/16/16/32/64) and accepts equal widths at adjacent ranks, as the
standard permits; conversion rank remains a distinct named-type property.

`IntegralFormat` is only a value representation. `CppIntType` preserves the
C++ type identity needed for rank and signedness decisions, so equal-width
`long` and `long long` are not silently merged. The bridge currently admits
only the standard integer families listed by `CppIntType`; enums, character
families with distinct encoding rules, extended integer types, bit-fields and
floating types remain explicit future refusals.

## Resolution

`integralPromotion` first validates the profile and source type. `bool`, plain
`char`, signed/unsigned char, and signed/unsigned short promote to `int` when
`int` represents every source value, otherwise to `unsigned int`; the remaining
standard integer types are unchanged. `usualArithmeticType` applies those
promotions and follows N4950 §7.4: equal types stay equal; same-signed types
choose greater rank; mixed signed/unsigned types choose unsigned when its rank
is no lower, choose signed when it represents all unsigned values, and otherwise
choose the unsigned counterpart of the signed type. `resolveArithmeticFormats`
returns both the selected C++ type and its value format for the integral kernel.

Invalid profiles and unsupported type families refuse. No first-match name
lookup, equal-width shortcut, or host-dependent inference is used. This layer
therefore supplies a precondition for expression evaluation; it does not claim
that an AST operand was actually resolved to one of these types.

## Checks

```sh
lake build LeanModels.Cpp.TypeTests
python3 extractors/cpp/test_type_resolution.py
```

The Lean guards cover LP64 and a 16-bit-`int` profile, including the mixed
signed/unsigned rank cases. The independent C++23 oracle uses Clang's actual
`decltype` expressions and `std::is_same_v` assertions for the LP64 profile;
its width assertions fail loudly if the selected target does not match the
profile. This is a type-resolution/value-layer check only: no source AST or
whole-program execution is admitted.
