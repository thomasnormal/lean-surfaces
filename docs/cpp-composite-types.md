# C++ pointer and array type identities

`LeanModels/Cpp/CompositeTypes.lean` extends the scalar type slice with
pointer, array and top-level cv-qualified type identity. `CppType.pointer`
retains the complete pointee type, so a pointer to `const int` is distinct from
a pointer to `int`; nested pointers retain their depth. Arrays carry either a
positive fixed bound or `none` for an incomplete bound.

The structural helpers distinguish object and complete types, expose the
top-level array bound and pointer depth, and remove or compare only the
top-level cv wrapper. Validation refuses empty cv qualification, arrays of
`void`, and zero-sized fixed arrays. Pointers remain complete even when their
pointee is incomplete, while an incomplete array is not complete.

This is a type-identity and well-formedness boundary only. It does not infer
addresses, pointer arithmetic, object layout, alignment, array storage, class
subobjects or execution. Those facts remain future semantic slices.

## Checks

```sh
lake build LeanModels.Cpp.CompositeTypeTests
```

The guards cover scalar/pointer/array completeness, cv-sensitive pointer
identity, pointer depth, array bounds, incomplete arrays, and all three loud
validation refusals.
